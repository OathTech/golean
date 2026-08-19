# BUG-056 design memo — `&*p` nil collapse (bug-fix arc slice 3, 2026-08-19)

MEMO ONLY — no implementation. Slice 3 is design-gated
(`docs/2026-08-19_bugfix-arc-charter.md` §slice 3): any route that
touches GoCore requires Mike's sign-off on this memo before a line of
implementation. The probe matrix below IS landed (corpus rows, colors
recorded pre-fix); the mechanism is not.

## 0. The defect, re-verified at this tree

`emitAddressOf`'s `*ast.StarExpr` arm (tools/nativefrontend/emit.go:5075-5077)
is

```go
case *ast.StarExpr:
    // &(*p) is p.
    return e.emitExpr(ex.X)
```

so the wire for `&*p` and `&(*p)` is byte-identical to plain `p` — the
collapse is algebraically right for non-nil `p` (`&*p` IS `p`, pinned by
the new `alias-non-nil` row) and drops exactly one obligation:
spec#Address_operators — "If the evaluation of `x` would cause a
run-time panic, then the evaluation of `&x` does too", combined with
"If `x` is nil, an attempt to evaluate `*x` will cause a run-time
panic." The spec's own exhibit is the pinned case: `&*x  // causes a
run-time panic`.

The machine side has the panic machinery already: every consumer of a
pointer-as-location goes through `valueAsLoc` (GoLean/GoCore/Ops.lean:1376),
whose `.nil` arm panics with the exact runtime string. `.deref`,
`.fieldAddr` (Machine.lean:349, 359-360) and `indexTargetLoc`
(Machine.lean:213-216, BUG-038) all inherit it. Nothing in the semantic
core mishandles nil — the wire simply never presents the nil to it.

## 1. The probe matrix (landed: `spec-examples-decl/addr-deref-nil-matrix/`, 10 rows)

Every expectation computed from `go run` (go1.26.5, the pinned oracle)
BEFORE the differential ran (`artifacts/probe/addr056/matrix.go`,
scratch). All nil subjects panic with runtime.Error
`invalid memory address or nil pointer dereference` — verified both for
value (`recover()` type-checks as `error`) and message. Machine colors
from `scripts/coverage run --prefix spec-examples-decl/addr-deref-nil-matrix`
at this tree (pre-fix): 7 PASS / 3 FAIL, every color as predicted from
the wire reading before the run.

| row | shape | go | machine (pre-fix) | why |
| --- | --- | --- | --- | --- |
| `two-deref-outer-nil` | `&**pp`, `pp` nil | panic | PASS | the OPERAND `*pp` is a real `deref` load; `valueAsLoc(nil)` fires there, before the collapsed outer `&*` matters |
| `two-deref-inner-nil` | `&**pp`, `*pp` nil | panic | **FAIL** (ok/0) | inner load succeeds and yields nil; the collapsed outer `&*` never checks it |
| `index-slice-ptr-nil` | `&(*sp)[0]`, `sp` nil | panic | PASS | `*` not immediately under `&`: `index-addr(deref sp, 0)`, deref panics |
| `index-arr-ptr-nil` | `&(*ap)[0]`, `ap` nil (ptr-to-array) | panic | PASS | collapse fires INSIDE index-addr's base, but `indexTargetLoc` nil-checks its base itself (BUG-038) — benign composition, now pinned |
| `index-auto-deref` | `&ap[0]`, `ap` nil | panic | PASS | the BUG entry's record-only `&p[i]`, now witnessed |
| `field-explicit` | `&(*st).x`, `st` nil | panic | PASS | field-addr's base is the pointer VALUE; `valueAsLoc` fires |
| `field-auto-deref` | `&st.x`, `st` nil | panic | PASS | the entry's record-only `&p.f`, now witnessed |
| `alias-non-nil` | `q := &*p; *q = 42` | 42 | PASS | the identity the collapse gets RIGHT and the fix must keep: `&*p` is `p`, same cell, not a copy |
| `deref-arg` | `sink(&*p)`, `p` nil | panic | **FAIL** (ok/0) | argument position; must panic before the callee runs |
| `deref-call` | `&*retNil()` | panic | **FAIL** (ok/0) | call-result operand; the hoisted temp is nil, the `&*` never checks it |

With the two P3 pins (`address-op-nil-indirection/addr-deref-nil`,
`/addr-deref-nil-paren`) the red set is now **five**, and its boundary
is sharp: **exactly the compositions where the `*` is the immediate
operand of `&` and no enclosing address node re-checks the base**. Every
neighbor (field/index composition, either sugar direction, the
operand's own inner deref) is green because some OTHER node's
`valueAsLoc` fires — pinned green so the fix cannot regress them.

Masked-green sweep for this shape: `&*` / `&(*` appears in NO corpus
`.go` outside the two BUG-056 packages (grep, this tree), and
**deps/raft has zero occurrences** across its 89 files — like BUG-057,
the raft blast radius is the corpus signal's cleanliness, not raft code.

## 2. What gc actually does (the granularity ground truth)

Two probes, both decisive (scratch: `artifacts/probe/addr056/asm/`,
`.../race/`):

**Codegen** (`go build -gcflags=-S`, go1.26.5 linux/amd64):

```
func AddrDeref(p *int) *int { return &*p }      →  TESTB AL, (AX); RET
func AddrDerefBig(p *Big) *Big { return &*p }   →  TESTB AL, (AX); RET   (Big = 64 bytes)
func PlainDeref(p *int) int { return *p }       →  MOVQ (AX), AX; RET
```

gc's `&*p` is a single hardware nil-probe — a 1-byte `TESTB` against
the pointed-to address that faults on nil — and **no value load**, not
even for a 64-byte pointee. Contrast the real deref's `MOVQ`.

**Race instrumentation** (`go run -race`, concurrent writer to `*p`):
the loop `q = &*p` beside a goroutine writing `*p` is **TSan-green
(exit 0)**; replacing it with a real read `s += *p` is **TSan-red
(exit 66)**. gc's nil probe is not an instrumented access — `&*p`
touches the pointee's memory only at the hardware level, invisibly to
the race detector.

So the honest model of `&*p` is: **read the pointer value, decide
nil-ness on the value in hand, perform NO user-memory access on the
pointee.** Any mechanism that materializes a pointee load is wrong on
three counts at once: a step/access gc does not have (granularity
ledger's class — unobservable sequentially, real under concurrency,
BUG-002's family), a false-positive S3 race report on the probe's
TSan-green program above, and an O1-class whole-cell read of an
arbitrarily large pointee.

## 3. The mechanism options

### (a) Frontend desugar — REJECTED, with the candidates enumerated

- **(a1) hoist `_ = *p` before emitting `p`.** The obvious desugar and
  the one the charter names. Footprint: a full `deref` load of the
  pointee — one extra machine step carrying a **read access gc never
  performs** (§2: gc is TESTB, no load; TSan-green where this desugar
  is TSan-red). For a struct pointee it is a whole-cell read (O1). A
  granularity-ledger violation by construction. REJECT.
- **(a2) hoist `if p == nil { panic(...) }`.** No pointee load, but the
  wire `panic` builds a USER panic: the payload would be a string where
  Go delivers a `runtime.Error` — distinguishable by `recover()`
  type-assertion (probed: gc's payload satisfies `error`), by the abort
  line shape, and by BUG-004's whole rendering machinery. The frontend
  would be fabricating runtime-panic identity it does not own —
  exactly the class of semantic invention `NativeToIR` quarantine
  exists to forbid. REJECT.
- **(a3) reuse an existing checking node** (`field-addr` on a synthetic
  wrapper, `index-addr` on a fabricated array view). Type-model
  violence: there is no field or index to take; the emitted wire would
  lie about the program's shapes to borrow a nil check. REJECT.

No frontend-local desugar exists that is simultaneously load-free,
panic-identity-correct, and non-fabricating. This is why slice 3 was
design-gated rather than bundled with slices 1-2.

### (b) A GoCore strict op: `addrOfDeref` — RECOMMENDED

One new unary **strict operator** (not a statement, not a continuation
form): `Expr.addrOfDeref (ptr : Expr)`, strict-op table entry
`StrictOp.addrOfDeref`, apply arm

```lean
| .addrOfDeref, [v] => do return (.addr (← valueAsLoc v), s)
```

**Exact semantics:** evaluate the operand (the ordinary strict-operand
step); the apply step inspects the pointer VALUE already in hand —
`.addr loc` passes through unchanged, `.nil` panics via `valueAsLoc`'s
existing arm with the exact runtime string (same payload constructor as
every other nil-deref in the machine — abort rendering, `recover()`
identity, and message all inherited, nothing new to argue), anything
else is stuck (fail closed). **It reads and writes NO memory cell** —
the check consumes the value produced by the operand's own read step,
exactly the shape of gc's register-level TESTB.

- **Step footprint:** operand steps (unchanged — the same steps plain
  `p` costs today) + one pure apply step. The apply step performs zero
  loads/stores, so the granularity ledger gains no coarse spot and the
  interleaving surface is unchanged: the only racy window (pointer read
  vs. concurrent pointer write) already exists at the operand's
  `evalVar` step, identically to gc's own load of `p`.
- **Race-detector visibility:** no footprint arm. `strictOpAccesses`
  (Race.lean:366) already defaults uninstrumented ops to `[]`; the fix
  commit records the deliberate no-access decision in Race.lean's
  call-site inventory (gc's TESTB is a real 1-byte hardware probe that
  `-race` does not instrument — probe §2 — so "no access" is the
  lockstep-faithful model, not an omission; it is not even a
  READ-BUT-UNINSTRUMENTED row, since our model performs no load at
  all).
- **Mirror/Sym obligation:** one transcription arm in
  `applyStrictOp'` (proofs/GoLeanProofs/Sym/Mirror.lean:1301). The
  nil-vs-addr decision is on the value structure, not a scalar payload,
  so the arm can compute on concrete pointers and quit on anything the
  domain leaves undecided — either way the drift theorem forces the
  arm's fidelity, and no new QuitSite class is needed. One case each in
  `applyStrictOp_conc` (Sym/DriftApply.lean:235) and `applyStrictOp_sim`
  (Frame/StrictOps.lean:1664 — the renaming quotient; the arm renames
  one `Loc`, the same obligation `fieldAddr` already discharges).
- **Relation side: zero new rules.** Strict ops step through the
  generic `strictOp` frame machinery; `exprOp?` gets one row. No
  `MachineSound` completeness case beyond the generic strict-op path.

**Blast radius, complete file list:**

| surface | change |
| --- | --- |
| `tools/nativefrontend/emit.go` | the `StarExpr` arm of `emitAddressOf` emits `{"expr":"addr-of-deref","ptr":…}` instead of collapsing (keep collapsing is WRONG even under (c) below — see §4 note on optimization latitude) |
| wire schema | one new expr kind, `addr-of-deref`; old wires unaffected; unknown-node fail-closed behavior unchanged |
| `GoLean/NativeToIR.lean` | one decode arm (next to `"deref"`, line 216) |
| `GoLean/GoCore/Syntax.lean` | `Expr.addrOfDeref` constructor |
| `GoLean/GoCore/Machine.lean` | `StrictOp.addrOfDeref` + `exprOp?` row + one apply arm (the 3 lines above) |
| `GoLean/GoCore/Race.lean` | no arm; one inventory note |
| `GoLean/GoCore/StateWf.lean` | `Expr.locSup` arm (structural, = operand's) |
| `proofs/GoLeanProofs/Frame/Rename.lean` | `renameExpr` arm (structural) |
| `proofs/GoLeanProofs/Sym/Mirror.lean`, `Sym/DriftApply.lean`, `Frame/StrictOps.lean` | one arm each, per above |
| proofs elsewhere | nothing: no existing law mentions `&*` (grep: no proof spec exercises the shape) |
| corpus/baselines | the 5 reds flip green; the 7 matrix greens and every other case unmoved (non-nil behavior is value-identical to today's collapse) |

**Why this does not violate "GoCore stays pure":** the node is not a
frontend quirk — it is the spec's own composite (`spec#Address_operators`
gives `&`-of-indirection its own panic clause and its own exhibit), gc
gives it its own codegen shape, and no composition of existing GoCore
nodes expresses "assert non-nil, produce the same pointer, touch no
memory". The GoCore design rule ("reshapeable, not sacrosanct — judge
by reasoning support and emission fit") points the same way: the
frontend lowers `&*`/`&(*…)` to it in one arm, and the WP story for it
is a one-lemma strict-op law with an immediate witness.

### (c) What the probes suggest beyond (a)/(b) — nothing better

The probes CONFIRM (b)'s exact shape rather than suggesting a third
mechanism: gc itself implements `&*p` as "check the value in hand,
no load" (§2), which is precisely a pure strict op and precisely not a
desugar into loads. The only probe-derived refinement worth recording:
the five-red boundary in §1 means the frontend arm should emit
`addr-of-deref` for the immediate `&`-of-`*` composition ONLY — the
field/index compositions must keep their current (correct, pinned-green)
lowerings, so the new node's blast radius stays one emitter arm.

## 4. Two honesty notes

- **Is skipping the check "optimizer latitude"?** No. The spec clause
  is unconditional ("the evaluation of &x does too") and gc's exhibit
  panics at every optimization level (`TESTB` survives `-N -l` and
  default opt; the spec text lists `&*x // causes a run-time panic` as
  its own example). This is a FORCED point; there is no envelope to
  state and no member-choice inside the fix. (Contrast slice 4, where
  a genuine latitude lives inside the fix.)
- **Step-count fidelity is not step-count equality.** The machine
  spends an apply step where gc spends zero instructions beyond the
  probe; what the granularity ledger governs is memory-operation
  decomposition, and there the two are identical (one pointer read, no
  pointee access). No ledger entry is owed.

## 5. DECISION BLOCK

**Options:**
- (a) frontend desugar — rejected above (a1 materializes a load gc
  never performs and is TSan-divergent by probe; a2 fabricates panic
  identity; a3 fabricates types).
- (b) GoCore strict op `addrOfDeref` — evaluate pointer, panic on nil
  via the existing `valueAsLoc` arm, yield the pointer, touch no
  memory. One emitter arm, one decoder arm, one constructor + one
  apply arm, three mechanical proof arms. Flips exactly the 5 pinned
  reds.
- (c) status quo + document — leaves a spec-exhibit forced point
  violated; not compatible with the arc's end-state claim.

**Recommendation: (b)**, with the emitter arm scoped to the immediate
`&`-of-`*` composition only. The tradeoff, crisply: option (b) buys
exact gc-shaped semantics (no load, no race visibility, inherited panic
identity) at the price of the arc's first wire-schema + GoCore
constructor addition — ~10 small arms across the files in §3(b), all
mechanical, zero new relation rules, zero new QuitSite classes, no
granularity-ledger entry. Every alternative that avoids the GoCore
touch buys it back by corrupting semantics the probes can already
distinguish.

**Questions for Mike to rule on:**
1. Approve the GoCore-touching mechanism (b) (`Expr.addrOfDeref` +
   `StrictOp.addrOfDeref`, wire kind `addr-of-deref`)? This is the
   charter's designed hard pause — the arc's first semantic-core
   change.
2. (Only if 1 = yes) Any objection to the name / wire key? (Bikeshed
   guard: `nilAssertPtr` was the runner-up; `addrOfDeref` is
   source-shaped like `fieldAddr`/`indexAddr`.)

**On each answer:**
- **Yes:** implement (b); flip the 5 reds
  (`addr-deref-nil`, `addr-deref-nil-paren`, `two-deref-inner-nil`,
  `deref-arg`, `deref-call`) in one commit with the re-pin + reason;
  BUGS.md BUG-056 → fixed with mechanism one-liner and flip list; the
  7 matrix greens must not move.
- **No / defer:** BUG-056 is recorded as gated-deferred per the
  charter's DONE clause 3 (a legitimate end state); the 5 reds stay
  pinned; the matrix stays as the guardrail suite for whichever arc
  picks it up; slice 5's triage table carries it as category-(a)
  deferred-to-named-successor, never category-(c).
- **Modify (different node shape / different scoping):** re-probe the
  modified shape against §2's two ground truths (no load; no race
  visibility) before implementation — those two facts are the fix's
  acceptance tests regardless of mechanism.
