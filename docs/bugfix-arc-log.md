# The bug-fix + language-bar arc — log

The running record for the arc chartered in
`docs/2026-08-19_bugfix-arc-charter.md`. One section per slice, in
execution order. Conventions (from the charter and the long-cycle
practice): every judgment call gets a one-line **JUDGMENT** entry with
its reasoning, for user review; every number is derivation-anchored
(the command that produced it); bounds ship as bounds.

## INDEX

| slice | subject | state |
| --- | --- | --- |
| 1 | BUG-058 — if-init condition-hoist scope | DONE (`8a42e402` enumeration, `740f09f8` fix; gate PASS at `740f09f8`) |
| 2 | BUG-057 — two-var comma-ok var-decl arity | DONE (`d5ce2dc0` enumeration, `2d840744` fix; gate PASS at `2d840744`) |
| 3 | BUG-056 — `&*p` nil collapse (design-gated) | DONE (ruled 2026-08-19, memo §6; fix landed — the addrOfDeref strict op; 5 reds flipped, acceptance pin green) |
| 4 | BUG-005 — live map iteration (design-gated) | RULED (2026-08-19, memo §5); guardrails-first rework LANDED (2 membership red pins); (L) surgery in progress |
| 5 | full red/bug triage (kill or justify) | TABLE DELIVERED (`docs/2026-08-19_triage-table.md`); A1 landed `1ca434b2`; (c) list + two gates await the user |
| 6 | the whole-language bar (coverage ledger) | not started |

---

## Slice 1 — BUG-058: the if-init condition-hoist scope

Entry: `docs/BUGS.md` "BUG-058 — if-statement init scope: condition
hoist block emitted OUTSIDE the init". Diagnosis audit-hardened at the
P3 pre-merge audit; this slice verified its cites before touching
anything (see "diagnosis re-verification" below).

### Diagnosis re-verification (before any change)

- `emitIf` is at `tools/nativefrontend/emit.go:2517`; the entry's
  "2426 area" cite is the pre-P3 line number, off by ~91 lines after
  the intervening landings. The MECHANISM the entry describes is
  exact: `emitIf` emits `st.Init` into the node's `init` key
  (emit.go:2519-2525) and then calls `e.emitExpr(st.Cond)` with the
  ENCLOSING hoist accumulator still in force (emit.go:2526), so
  `emitStmtList` (emit.go:1616-1634) splices the condition's hoisted
  temps in front of the whole `if` node — outside the init's scope.
- The contrast the entry names is also exact and in the same
  function: the ELSE accumulator *is* scoped (emit.go:2542-2553,
  save/nil/restore + wrap), and so are `emitFor`'s condition
  (`condPre`, emit.go:2651-2662) and post (emit.go:2668-2679).
- The decoder side: `decodeIf` (`GoLean/NativeToIR.lean:1143-1153`)
  lowers `init` as `.block #[] #[init, ifThenElse …]` — i.e. the
  init's scope is ALREADY a block wrapping the if. That is what makes
  the fix frontend-local (below).

### Step 1 — edge enumeration (own commit, colors recorded BEFORE the fix)

Every expectation is `go run`'s, computed before the differential ran
(`artifacts/probe/ifinit`, `artifacts/probe/relatives`; scratch, not
tracked). Colors from
`scripts/coverage run --prefix spec-examples-stmt/if-init-hoist-order`
and `… --prefix spec-examples-stmt/init-hoist-relatives`.

**New reds — `spec-examples-stmt/if-init-hoist-order/` (7 rows added
to the 2 P3 pins):**

| row | shape | go | machine (pre-fix) | stage |
| --- | --- | --- | --- | --- |
| `else-if-chain` | `else if` with its own init + cond call | 12348 | 21438 | differential |
| `func-literal` | if-with-init inside a func literal | 125 | 215 | differential |
| `nested` | if-with-init inside if-with-init | 12349 | 21439 | differential |
| `cond-hoist-reads-init` | cond call reads the init var, no `&&` | 1 | stuck `unbound GoCore variable address: x` | lean-observation |
| `cond-panic-after-init` | init succeeds observably, cond call panics | 321 | 21 | differential |
| `comma-ok-short-circuit` | `if v, ok := m[k]; ok && f(v)` (raft shape) | 1 | stuck `unbound … ok` | lean-observation |
| `comma-ok-method-short-circuit` | `if pr, ok := m[k]; ok && pr.active()` | 1 | stuck `unbound … ok` | lean-observation |

All three observable modes of the entry are now pinned: mode 1
(stuck) by the three `reads-init` shapes, mode 2 (silent wrong order)
by `else-if-chain`/`func-literal`/`nested`, mode 3 (panic ordering) by
`cond-panic-after-init` (and the pre-existing `init-panic-first` in
the other direction).

**New pinned GREENS — `spec-examples-stmt/init-hoist-relatives/`
(6 rows, all PASS pre-fix):** `for-init-cond`,
`for-init-cond-reads-init`, `switch-init-tag`,
`switch-init-tag-reads-init`, `type-switch-init`,
`type-switch-init-reads-init`. These are the structurally-corroborated
non-affected relatives; pinning them green BEFORE the fix is what
makes a later silent regression in `emitFor`/`emitSwitch`/
`emitTypeSwitch` impossible to miss. Note that the `-reads-init`
variants put the init-declared variable INSIDE the hoisting call —
the exact position that goes stuck for `if` — so the pins are
load-bearing, not decorative.

**JUDGMENT (slice 1, edge enumeration):** the new `if` rows were
appended to the EXISTING `if-init-hoist-order` package rather than
given their own directories — one canonical file per evaluation-order
concern keeps the family readable and the ids stable, and the package
is still small. The relatives went to a NEW package because they are
pinned greens about *other statements*; mixing them into a package
named for a bug would misfile them.

**JUDGMENT (slice 1, raft shape):** the integration case ships in two
forms, a plain function (`big(v)`) and a METHOD (`pr.active()`),
because raft writes the method form
(`if pr, ok := m[id]; ok && pr.IsPaused()`) and the method call takes a
different emission path (receiver evaluation) into the same
short-circuit RHS accumulator. Pinning only the plain form would have
left the shape we actually care about unwitnessed.

**Gate at the enumeration commit:** `GOLEAN_MEM_MAX=24G scripts/ci
--diff`, full run — every step `ok`, and the baseline diff's ONLY
drift was the 13 `NEW id` lines (no PASS↔FAIL flip, no stage change,
no dropped id on any of the 2089 pre-existing rows; `diff` of the old
vs new row blocks shows 13 pure insertions). Baseline re-pinned in
this commit from that full run: 2102 cases, 1959 PASS / 143 FAIL.
`scripts/check-bugs.sh`: ok (61 bugs; pinned cases behave as claimed).

### Step 2 — the fix

`tools/nativefrontend/emit.go`, `emitIf` only (+52/-3 lines, all of it
in that one function). Two halves:

1. **Scope the condition's accumulator** — when `st.Init != nil`, the
   condition is emitted with `e.hoisted` saved/nil'd/restored around
   `e.emitExpr(st.Cond)`, the same save/capture/restore the ELSE
   branch has used since the else-if fix and `emitFor` uses for
   `condPre`/`post`. When `st.Init == nil` the old path is kept
   verbatim: there is no scope to stay inside, and the enclosing
   accumulator already places the temps immediately before the if.
2. **Re-establish the init's scope around them** — with a non-empty
   condition accumulator, `emitIf` returns a wire
   `block` of `[init, condHoists…, if]` instead of an `if` node
   carrying an `init` key. That block is *the same scope the decoder
   already builds*: `decodeIf` lowers the `init` key as
   `.block #[] #[init, ifThenElse …]`
   (`GoLean/NativeToIR.lean:1143-1153`). So the init-declared names
   are visible to the hoists, to the condition and to both branches —
   the implicit block spec#Blocks gives the statement ("Each `if`,
   `for`, and `switch` statement is considered to be in its own
   implicit block").

**JUDGMENT (slice 1, mechanism choice).** The obvious alternative was
to mirror `emitFor` exactly: add a `condPre` key to the wire `if`
node and splice it in `decodeIf`. Rejected: that is a wire-schema
change plus a decoder change to buy a shape the decoder *already*
produces for `init`. The block wrapper is frontend-local (the
charter's "emitIf-local"), touches no Lean file, and cannot introduce
a scope the decoder did not already have. `for` genuinely needs
`condPre` because its condition is re-tested every iteration —
`if` tests once, so a straight-line splice is exact.

**JUDGMENT (slice 1, minimality).** The wrap fires ONLY when there is
both an init and a non-empty condition accumulator. An `if` without an
init, or with an init and a hoist-free condition, emits the same bytes
as before — which is why the full run's drift is exactly the bug's own
family and nothing else.

**Predicted flip set, stated before the confirming run (10 red→green,
1 new green id, nothing else):**

- `spec-examples-lexical/panic-values/panic-error`
  (FAIL/lean-observation → PASS)
- `spec-examples-stmt/if-init-hoist-order/{cond-call-after-init,
  init-panic-first, else-if-chain, func-literal, nested,
  cond-panic-after-init}` (FAIL/differential → PASS)
- `spec-examples-stmt/if-init-hoist-order/{cond-hoist-reads-init,
  comma-ok-short-circuit, comma-ok-method-short-circuit}`
  (FAIL/lean-observation → PASS)
- `control-flow/goto-if-init-cond-hoist` (NEW → PASS)

**The goto interaction case, and why it is in this commit.** The fix
changes the SHAPE of a top-level statement inside a goto-restructured
segment (an `if` node becomes a `block`), and `degradeGotoDeclares`
(emit.go:1130) rewrites top-level source declarations there. The
init's declaration is nested in both shapes — under the `init` key
before, inside the block after — so it keeps its `declare` in both,
which is correct (a backward jump re-declares it). "Correct by the
same argument in both shapes" is the kind of claim that deserves a
case, so `control-flow/goto-if-init-cond-hoist` pins it.
**JUDGMENT (slice 1):** it is a NEW id in the fix commit rather than
in the enumeration commit because the interaction it probes is a
property of the fix, not of the bug — but it was verified RED under
the pre-fix emitter first (`git stash` of `emit.go`,
`scripts/coverage run --prefix control-flow/goto-if-init-cond-hoist`
→ `cases=1 pass=0 fail=1`), so it is a genuine BUG-058 witness and
not a case written to match the implementation.

### Step 3 — masked-green sweep

**Scope and method.** Mechanized: an AST scan
(`artifacts/probe/sweep`, scratch) over every `.go` file under
`Corpus/`, `raftharness/` and `compat/`, finding every `ast.IfStmt`
with `Init != nil` and reporting whether its `Cond` contains a
hoist-capable construct (call, composite literal, receive, func
literal). AST-based rather than grep-based so that multi-line and
nested shapes cannot hide — a line grep had already missed shapes,
which is why this was mechanized.

**Findings.**

- `Corpus/`: **85** if-with-init statements; **17** with a
  hoist-capable construct in the condition. 15 of the 17 are this
  slice's own `if-init-hoist-order` package. Of the other two:
  - `spec-examples-lexical/panic-values:40` — the already-pinned red
    (`ok && e.Error() == …`), now green.
  - `spec-examples-lexical/channel-direction-forms:19` —
    `if got := <-bidi; int(got) == 7`. The scanner counts `int(got)`
    as a call; it is a CONVERSION, which the frontend does not hoist.
    Green before the fix and after it — and that green is itself the
    evidence that conversions do not hoist (if they did, `got` would
    have been unbound and the case stuck).
- `raftharness/`: 20 if-with-init, 1 flagged (`scenarios.go:54`,
  `len(v) > 0` — a builtin, not a hoist). Not a differential case in
  any event; the harness runs in real Go.
- `compat/`: 0 if-with-init statements.

**Conclusion: no masked green.** No corpus case outside this bug's own
family combined an if-with-init with a hoisting condition, so no
green could have coincided with correctness. This is the honest
negative result the charter asked for, with its scope stated — not an
absence of looking.

**One disposition-level finding, recorded rather than dropped.** It is
a *sufficiency* gap, not a mask: `If_statements-3-23172299`'s five
rows (`spec-examples-stmt/if-init-else-chain/*`) pin the branch
structure of `if x := f(); x < y … else if … else …`, but nothing in
them can observe ORDER — the init's `f()` is un-hoisted and every
condition is a pure comparison. So the spec block's own sentence
("which executes before the expression is evaluated") was unwitnessed
while the machine had exactly that order wrong. The order witnesses
are the `if-init-hoist-order` and `init-hoist-relatives` families;
the disposition row now says so, and
`Handling_panics-2-e7d4cef6` now records that `panic-int` /
`panic-string` were never masked (a pure short-circuit right operand
hoists nothing) while `panic-error` was the family's only red.

**For the arc's later slices:** `deps/raft` itself has 103
if-with-init statements, 12 with a call in the condition — the shape
this fix unblocks is not hypothetical for W4.

### Gate at the fix commit

`GOLEAN_MEM_MAX=24G scripts/ci --diff`, full run at the fix tree. The
baseline diff's drift was **exactly the predicted set and nothing
else**: the 10 red→green flips listed above plus
`control-flow/goto-if-init-cond-hoist` as a NEW/PASS id, across 2103
cases. In particular the 6 `init-hoist-relatives` greens all held, so
the fix did not disturb `emitFor`/`emitSwitch`/`emitTypeSwitch`. Every
other step `ok`, including the re-pin guard (0 PASS→non-PASS flips)
and `eval tests (136 ok)`. Baseline re-pinned in the fix commit from
that run: 2103 cases, 1970 PASS / 133 FAIL (was 1959/143), reason in
its header. `scripts/check-bugs.sh` then reports ok (61 bugs) with
BUG-058 marked fixed — the cross-check is what refuses a
"fixed" entry whose cases are still red, so its green is a real
confirmation, not a formality.

The run that produced these numbers was started before two
COMMENT-ONLY edits to `emit.go` (a spec citation corrected from
`spec#Declarations_and_scope` to the accurate `spec#Blocks` implicit
-block sentence), so the gate was re-run at the committed tree to
keep the record exact. **That re-run is the slice's recorded gate:
`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `740f09f8` →
`RESULT: PASS`, every step ok, `baseline diff FULL (2103/2103, no
regression)`, negative lane 390/390, `re-pin guard (0 PASS→non-PASS
flips, all listed in BUGS.md Cases)`.**

**Slice 1 state: BUG-058 fixed and closed.** All 10 of its pinned
cases green, the edge set landed, the raft integration shape green in
both plain and method form, the non-affected relatives pinned green,
the masked-green sweep recorded with its scope and its one
disposition-level finding.

---

## Slice 2 — BUG-057: the two-variable comma-ok var-declaration arity hole

Entry: `docs/BUGS.md` "BUG-057 — two-variable comma-ok VAR DECLARATIONS
drop the ok flag". Diagnosis audit-hardened at the P3 pre-merge audit
(F-2 corrected the scope, F-10 recorded the typed form's observational
limitation); this slice re-verified its cites before touching anything.

### Diagnosis re-verification (before any change)

- The pairing site is `emitDeclStmt`, `tools/nativefrontend/emit.go`.
  The entry's "2383-2392" cite is the P3-era line number; at slice-2
  start `emitDeclStmt` begins at emit.go:2436 and the offending loop is
  emit.go:2473-2513. The MECHANISM is exact:
  `for i, name := range vs.Names { … if i < len(vs.Values) { … } }`
  pairs the spec's names to its initializer expressions POSITIONALLY,
  with no arity check, so for `var v, ok = m[k]` (2 names, 1 value)
  name `v` gets the initializer and name `ok` gets a decl entry with no
  `init` key at all. `decodeVar` (`GoLean/NativeToIR.lean:1130-1141`)
  emits `.initialization` for every decl and `.assign` only when `init`
  is present, so `ok` is left at its zero value — false.
- The contrast the entry names is also exact, and it is in this same
  file: the PACKAGE-level path never uses `emitDeclStmt`. It fabricates
  ONE `ast.AssignStmt` carrying every name of a multi-value spec
  (emit.go:600-607) and runs it through `emitAssign`, whose comma-ok
  branches (type assertion emit.go:2136-2157, channel receive
  emit.go:2163-2167, map index via the generic 2-target path) are
  correct. So the fix direction the charter names — "lowered through the
  same path as the correct short-decl form" — is also the path the
  package-level declaration has always used.

### Step 1 — edge enumeration (own commit, colors recorded BEFORE the fix)

Every expectation is `go run`'s, computed before the differential ran
(`artifacts/probe/commaok`; scratch, not tracked). Colors from
`scripts/coverage run --prefix spec-examples-decl/var-comma-ok-matrix`
against the UNMODIFIED emitter: **46 cases, 22 PASS / 24 FAIL.**

**The matrix.** Three comma-ok sources (receive `<-ch`, map index
`m[k]`, type assertion `x.(T)`) × untyped (`var v, ok = …`) / typed
(`var v, ok T = …`) × blank in the value position / blank in the ok
position / neither × function-local / package-level = 36 rows, plus 3
interface-typed rows, 5 position/shape rows and 2 tuple-call rows.

Two design rules every row obeys:

- **TRUE ok on the observing line** (the MASKING lesson): a comma-ok
  case whose ok is FALSE cannot distinguish delivery from drop, because
  the dropped flag's zero value *is* false. That is exactly how the
  original P3 evidence went green on a closed-drained channel and an
  absent key.
- **Value and ok as SEPARATE observables** (closes F-10): the harness
  supports multi-result subjects, so every row returns `(value, ok)`
  rather than `value && ok`. Correct is `(v, true)`; a dropped ok is
  `(v, false)`; a dropped value is `(zero, true)` — three distinct
  observations where the old subject had one bit.

**Pre-fix reds — silent wrong answer, `differential` (11):**

| row | shape | go | machine (pre-fix) |
| --- | --- | --- | --- |
| `recv-untyped` | `var v, ok = <-ch` | 7, true | 7, **false** |
| `recv-untyped-blank-value` | `var _, ok = <-ch` | true | **false** |
| `recv-typed` | `var v, ok bool = <-ch` | true, true | true, **false** |
| `recv-typed-blank-value` | `var _, ok bool = <-ch` | true | **false** |
| `index-untyped` | `var v, ok = m[k]` | 7, true | 7, **false** |
| `index-untyped-blank-value` | `var _, ok = m[k]` | true | **false** |
| `index-typed` | `var v, ok bool = m[k]` | true, true | true, **false** |
| `index-typed-blank-value` | `var _, ok bool = m[k]` | true | **false** |
| `func-literal` | the declaration inside a closure | 7, true | 7, **false** |
| `grouped-spec` | comma-ok spec BETWEEN two ordinary specs | 2, 7, true | 2, 7, **false** |
| `after-goto` | the declaration in a goto-restructured body | 7, true | 7, **false** |

Note what the typed rows now show that F-10's `x && ok` could not: the
VALUE arrives correctly (`true`, not the zero `false`) and only the ok
is lost. The entry's "the value arrives, the boolean is lost" is now
case-pinned rather than wire-argued.

**Pre-fix reds — fail closed, `frontend-export` (13):** the six local
type-assertion rows (`assert-{untyped,typed}[-blank-value|-blank-ok]`,
"type assert form outside a 2-target assignment"); the three
interface-typed rows `{recv,index,assert}-typed-iface`; `iface-value`;
`shadow-capture`; and `tuple-call-{untyped,typed}` ("type
*types.Tuple").

**Pre-fix greens (22):** all **18** `pkg-*` rows — the package-level
form is correct for every source, typedness and blank position, now
with a TRUE ok observed — and the **4** local `*-blank-ok` rows
(`var v, _ = …`), which observe the VALUE half only and were therefore
never wrong. Those four are load-bearing pins, not decoration: they are
the only rows that can catch a fix which delivers `ok` by breaking the
value.

**Three findings the enumeration establishes** (all folded into the
BUGS.md entry):

1. The silent drop is **receive + map index only** — the type-assertion
   source fails CLOSED. The entry's "(probe: `= x.(T)`)" is resolved,
   and `spec-examples-decl/assert-comma-ok` was already red for exactly
   that reason.
2. Package-level correctness is now **case-pinned with a true ok**, not
   only wire-argued.
3. The typed form is **not bool-only**: `var v, ok T = x` also admits an
   interface T both values are assignable to — the shape
   spec#Type_assertions itself writes,
   `var v, ok interface{} = x.(T)`. My first draft of this package
   asserted "T must be bool"; the sweep (step 3) found
   `assert-comma-ok`'s `var v4, ok4 interface{} = x.(int)` and refuted
   it, which is why the three `-typed-iface` rows exist.

**JUDGMENT (slice 2, package placement):** the matrix went into a NEW
package `spec-examples-decl/var-comma-ok-matrix/` rather than being
appended to the three existing pin packages. Those three are
spec-BLOCK packages (`Receive_operator-2-…`, `Index_expressions-2-…`,
`Variable_declarations-2-…`) whose subjects mirror one spec block's
example; a 46-row cross-product indexed by lowering shape rather than
by spec block would misfile there and would break the one-block-one-
package reading of the dispositions. The four existing pins stay where
they are and stay in the entry's `Cases:` list.

**JUDGMENT (slice 2, the -typed-iface rows are RED on purpose):** they
are pinned even though they cannot pass, because the fix REROUTES
exactly these specs away from the guard that refuses them today. A
reroute that silently turned a fail-closed refusal into an unboxed
interface store would be invisible without them — the "fail-closed
classification" blindness the audit doctrine names.

**Gate at the enumeration commit:** `GOLEAN_MEM_MAX=24G scripts/ci
--diff`, full run. The pre-re-pin run's ONLY drift was the **46
`NEW id` lines** (2149 cases run vs the 2103-row baseline: no
PASS↔FAIL flip, no stage change, no dropped id on any pre-existing
row), and `bug-index cross-check` failed only with 11 "case not found
in baseline" lines — the new BUG-057 `Cases:` rows, which the ratchet
requires so 11 fresh `differential` reds cannot hide in the untriaged
pile. Baseline re-pinned in this commit from that full run: **2149
cases, 1992 PASS / 157 FAIL** (was 2103, 1970/133), reason in its
header. The confirming re-run at the committed tree is **`RESULT:
PASS`** — every step ok, `baseline diff FULL (2149/2149, no
regression)`, `re-pin guard (0 PASS→non-PASS flips…)`,
`eval tests (136 ok)`, negative lane clean, and
`scripts/check-bugs.sh: ok (61 bugs; pinned cases behave as claimed)`
with the untriaged backlog unchanged at 25/25.

### Step 2 — the fix

`tools/nativefrontend/emit.go`, `emitDeclStmt` only (+114/-2 lines, all
of it in that one function). Three parts:

1. **The arity check** the entry says was missing. `isMultiValueSpec`
   holds when a `ValueSpec` has ≥2 names, exactly ONE initializer, and
   that initializer's go/types type is a `*types.Tuple` with exactly
   `len(Names)` components — which is how go/types records all three
   comma-ok sources and a multi-valued call. Every other name/value
   mismatch is now an explicit `unsup("var declaration pairs %d names
   with %d initializers")` instead of a silent drop. (Unreachable on
   type-checked Go; a refusal rather than a drop is the point.)
2. **The reroute.** A multi-value spec lowers by calling `emitAssign`
   on a fabricated `ast.AssignStmt{Lhs: Names, Tok: token.DEFINE,
   Rhs: Values}`. `emitAssignTarget(_, define=true)` reads each name's
   type from `e.info.Defs`, which a var declaration populates exactly
   as a short declaration does, so the typed form's declared T is
   honoured; from there the type-assertion branch (emit.go:2136-2157),
   the channel-receive branch (emit.go:2163-2167) and the generic
   two-target path each do what they already do correctly for
   `v, ok := …`. Blank names reach `emitAssignTarget`'s `_` case and
   `emitChanRecvAssign`'s blank handling unchanged.
3. **Grouped declarations.** A `var (…)` may mix ordinary and
   multi-value specs, and each spec's initializer runs in source
   order, so the specs lower to a SEQUENCE of wire statements: each
   spec is emitted with its own saved/nil'd/restored hoist
   accumulator (the emitStmtList discipline), its hoists placed ahead
   of its own statement, and all but the last statement appended to
   the enclosing accumulator that `emitStmtList` splices in — at the
   SAME scope.

**JUDGMENT (slice 2, why a sequence and not a wire `block`).** The
obvious way to return several statements is a `block` node. Rejected,
and this is the one place the two slices' mechanisms differ for the
opposite reason: `decodeStmt`'s `"block"` builds `.block #[] #[…]`,
which is a SCOPE — exactly what slice 1 needed to re-establish the
init's scope, and exactly what a declaration must NOT have, since the
names have to outlive the statement. `e.hoisted` is the existing
mechanism for "more statements, same scope"; `decodeVar` and
`decodeAssign` both already lower to a non-scoping `.seqn`. No wire
schema change, no decoder change, no GoCore change.

**JUDGMENT (slice 2, why emitDeclStmt is safe to reach for the hoist
accumulator).** Appending to `e.hoisted` is only correct where a
caller splices it. Go's grammar admits a Declaration in a
StatementList and nowhere else — an if/for/switch init is a
SimpleStmt, which excludes declarations — so `emitDeclStmt` is
reachable only from `emitStmtList` (directly, or via `emitLabeled`'s
pass-through at emit.go:1068, which returns into the same list).
Verified by inspecting all eight `e.emitStmt(` call sites.

**JUDGMENT (slice 2, THE TUPLE-CALL CALL: taken, not deferred).** The
charter left `var a, b = two()` as take-or-defer, "fail closed or full,
never half". TAKEN, because the arity route supports it with no
tuple-call-specific code at all: the same `isMultiValueSpec` predicate
matches it (go/types gives the call a tuple type of `len(Names)`
components), and `emitAssign`'s multi-value-call branch
(emit.go:2300-2343) then does exactly what it does for
`a, b := two()`. "Full" is demonstrated, not asserted — three rows
added in this commit and each verified RED under the pre-fix emitter
first: `tuple-call-three` (`var a, b, c = three()`, so the route is
general in the number of names, not a two-name special case),
`tuple-call-blank` (`var a, _ = two()`), and `tuple-call-iface`
(`var a, b any = two()`), which stays RED at `frontend-export` —
the deferred implicit multi-value interface conversion, refused for
the tuple-call source by the same guard that refuses it for the
comma-ok ones. A half-support end state — say, untyped taken and
typed left refusing — is what the charter forbade, and is not what
this is: the two forms take one path.

**JUDGMENT (slice 2, the interface guard MOVED rather than dropped).**
The pre-fix body refused any multi-value spec with an interface-typed
name (a blanket check). The reroute bypasses that body entirely, so a
naive reroute would have turned five fail-closed refusals into
unboxed interface stores — silent wrong answers, and the audit
doctrine's "fail-closed classification" blindness, invisible to every
gate. The check therefore moves to the reroute site, SHARPENED to
`target is interface && component is not` — the same condition
`emitAssign`'s own generic multi-value guard uses (emit.go:2218-2230),
which the type-assertion and channel-receive branches return before
reaching. That sharpening is why `iface-value` (`map[string]any`,
where the component is ALREADY an interface so no conversion is owed)
legitimately turns green while `{recv,index,assert}-typed-iface`,
`tuple-call-iface` and `spec-examples-decl/assert-comma-ok` stay red.
The three `-typed-iface` rows were pinned in the enumeration commit
for exactly this reason.

**JUDGMENT (slice 2, minimality).** The sequence path fires ONLY when
some spec of the declaration is multi-value. A declaration with zero
or N initializers takes the original loop, in the original single
`var` node — which is why the full run's drift is this bug's own
family and nothing else.

**Predicted flip set, stated before the confirming run — 24 red→green,
4 new green ids, 1 new red id, nothing else:**

- FAIL/differential → PASS (15): the four P3 pins
  (`receive-comma-ok/{typed-form,untyped-form-live}`,
  `index-comma-ok/var-form-present`,
  `var-decl-forms/found-present`) and the eleven matrix rows
  (`var-comma-ok-matrix/{recv-untyped, recv-untyped-blank-value,
  recv-typed, recv-typed-blank-value, index-untyped,
  index-untyped-blank-value, index-typed, index-typed-blank-value,
  func-literal, grouped-spec, after-goto}`).
- FAIL/frontend-export → PASS (9): `var-comma-ok-matrix/{assert-untyped,
  assert-untyped-blank-value, assert-untyped-blank-ok, assert-typed,
  assert-typed-blank-value, assert-typed-blank-ok, iface-value,
  tuple-call-untyped, tuple-call-typed}`.
- NEW → PASS (4): `var-comma-ok-matrix/{after-goto-recv,
  after-goto-assert, tuple-call-three, tuple-call-blank}`.
- NEW → FAIL/frontend-export (1): `var-comma-ok-matrix/tuple-call-iface`.
- UNCHANGED red, verified: `var-comma-ok-matrix/{recv,index,assert}-typed-iface`
  and `var-comma-ok-matrix/shadow-capture` (frontend-export), and
  `spec-examples-decl/assert-comma-ok` (frontend-export).

**The five NEW ids, and why they are in the fix commit.** Four of them
probe interactions that are properties of the FIX, not of the bug:
`after-goto-recv` and `after-goto-assert` put the declaration at the
top level of a goto-restructured body for the two sources whose wire
node is NOT the map form's `assign` (`chan-recv` carries a `targets`
list, `type-assert` a `target`/`okTarget` pair) and
`degradeGotoDeclares` rewrites declarations per node shape, so the
map form's green does not cover them; `tuple-call-three` and
`tuple-call-blank` are the take-or-defer evidence above. All five —
including `tuple-call-iface` — were verified RED under the pre-fix
emitter first (`git stash push tools/nativefrontend/emit.go`, then
`scripts/coverage run --id …` → `cases=5 pass=0 fail=5`), so they are
genuine witnesses, not cases written to match the implementation.

### Step 3 — masked-green sweep

**Scope and method.** Mechanized: an AST scan
(`artifacts/probe/sweep057`, scratch) over every `.go` file under
`Corpus/`, `raftharness/`, `compat/`, `tools/`, `scripts/`, `proofs/`,
`GoLean/` and `deps/raft`, reporting every `ValueSpec` with ≥2 names
and exactly ONE initializer — the arity shape itself, not a guess at
it — classified by source kind (receive / map index / type assertion /
call) and by package vs function scope. AST-based rather than
grep-based because grouped and multi-line declarations hide from a
line grep. (The scan reports parse errors rather than skipping them:
the only ones are the 37 deliberately-invalid programs in
`Corpus/coverage/negative/compile/`, which never reach the emitter.)

**Findings: 62 hits, 51 of them this bug's own package. Of the other
11:**

- **4 package-level** — `init/multi-value-var-init:11`,
  `spec-examples-decl/pkg-init-together:13`,
  `spec-examples-decl/var-decl-forms:{28,30}`. The correct $pkginit
  path; PASS before the fix and after it.
- **4 already-pinned rows of this bug** — `index-comma-ok:34`,
  `receive-comma-ok:{35,50}`, `var-decl-forms:68`.
- **1 already-red and fail-closed** — `assert-comma-ok:15`
  (`var v4, ok4 interface{} = x.(int)`). It was never a masked green:
  the case has been FAIL/frontend-export throughout, and stays so.
- **2 masked greens** — `index-comma-ok:15`
  (`var v3, ok3 = a["missing"]`, absent key) and
  `receive-comma-ok:18` (`var x3, ok3 = <-ch`, closed and drained).
  In both, ok=false is the RIGHT answer, so the dropped flag
  coincided with correctness.

**Conclusion: no NEW masked green.** The two found are precisely the
pair the P3 delta-review's MASKING record already names, and each
already carries an unmasking row (`index-comma-ok/var-form-present`,
`receive-comma-ok/untyped-form-live`). The sweep's value is therefore
to CONFIRM that record is complete rather than merely plausible — the
mechanized enumeration of the shape found nothing the audit's reading
had missed — and to add one precision the entry did not have: the
third candidate an eye-scan would flag, `assert-comma-ok`, was never
a masked green because that source fails closed.

**`deps/raft` has ZERO occurrences of the shape** (89 `.go` files).
The contrast with slice 1 (103 if-with-init statements, 12 with a
call in the condition) is worth stating plainly: BUG-057's raft blast
radius is *indirect*. Raft writes `if v, ok := m[k]; …` — the SHORT
declaration, which was always correct — so what this fix buys the W4
tracker differential is not raft code that was mis-lowered, but the
removal of a silent-wrong-answer class from the corpus the
differential's signal is read against.

### Gate at the fix commit

`GOLEAN_MEM_MAX=24G scripts/ci --diff`, full run at the fix tree. The
baseline diff's drift was **exactly the predicted set and nothing
else** — 29 lines across 2154 cases: the 24 red→green flips (15
`differential`, 9 `frontend-export`), the 4 NEW/PASS ids and the 1
NEW/FAIL/frontend-export id listed above. In particular the 18 `pkg-*`
greens and the 4 local `*-blank-ok` greens all held, so the reroute
did not disturb the $pkginit path or the value-delivery half; and the
five deliberate reds (`{recv,index,assert}-typed-iface`,
`tuple-call-iface`, `shadow-capture`, plus
`spec-examples-decl/assert-comma-ok`) all held red, so the preserved
interface guard did what it was moved for. Every other step `ok`,
including `eval tests (136 ok)`, the negative lane, the golden-lowering
and imported-goose R2 pins, and the re-pin guard. Baseline re-pinned in
this commit from that run: **2154 cases, 2020 PASS / 134 FAIL** (was
2149, 1992/157), reason in its header. `scripts/check-bugs.sh` then
reports ok (61 bugs) with BUG-057 marked fixed — the cross-check is
what refuses a "fixed" entry whose cases are still red, so its green is
a real confirmation. The untriaged-fidelity backlog is unchanged at
25/25: this fix retired 15 fidelity reds that were already explained by
BUG-057's `Cases:` line, and introduced none.

**Slice 2 state: BUG-057 fixed and closed.** All 23 of its pinned cases
green, the 51-row matrix landed with a TRUE ok and separated
value/ok observations throughout (closing F-10), package-level
correctness case-pinned rather than wire-argued, the tuple-call
declaration taken to full support with its generality demonstrated,
the interface-conversion refusal preserved and sharpened, and the
masked-green sweep recorded with its scope, its two hits and its
confirmation that the P3 MASKING record was complete.

The confirming gate for the fix commit was run at the exact tree that
was then committed (no edit between the run and `git add`):
`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `2d840744` -> `RESULT: PASS`,
every step ok, `baseline diff FULL (2154/2154, no regression)`,
`re-pin guard (0 PASS→non-PASS flips, all listed in BUGS.md Cases)`,
`bug-index cross-check ok`, `eval tests (136 ok)`, negative lane clean.

---

## Slices 3 + 4 — the design memos (MEMOS AND PROBES ONLY, per the charter's gates)

Both slices are user-gated; this section records the probe/memo commit
only. NO machine, frontend, or decoder change is in it — the diff is
corpus rows, the two memos, BUGS.md probe records, this log, and the
baseline re-pin for the new ids.

### Slice 3 — BUG-056 probe matrix + memo

- **Deliverable:** `docs/2026-08-19_bug056-addr-deref-memo.md`.
  Recommendation: a GoCore strict op `addrOfDeref` (evaluate the
  pointer, panic on nil via the existing `valueAsLoc` arm, yield the
  pointer, touch NO memory), emitter arm scoped to the immediate
  `&`-of-`*` composition. Frontend desugars are rejected BY PROBE, not
  taste: gc's `&*p` is a single uninstrumented `TESTB` nil-probe
  (`-gcflags=-S`: no pointee load even at a 64-byte pointee;
  `-race`: TSan-green beside a concurrent pointee write where a real
  `*p` read is TSan-red exit 66) — so `_ = *p` materializes a
  race-visible load gc never performs, and a fabricated
  `if p == nil { panic(...) }` mints a user-panic payload where Go
  delivers a `runtime.Error`.
- **Probe matrix landed:** `spec-examples-decl/addr-deref-nil-matrix/`,
  10 rows, every go expectation computed from `go run` first
  (artifacts/probe/addr056, scratch), colors recorded pre-fix:
  7 PASS / 3 FAIL (`two-deref-inner-nil`, `deref-arg`, `deref-call` —
  all bare-`&*` shapes), 10/10 as predicted from the wire reading
  before the run. The red set (5 with the two P3 pins) has a sharp
  boundary: `*` immediately under `&` with no enclosing address node
  re-checking the base. The entry's record-only `&p.f`/`&p[i]` claims
  are now case-witnessed.
- **Masked-green sweep** (scoped to this bug's shape): `&*`/`&(*`
  appears in no corpus `.go` outside the two BUG-056 packages and has
  ZERO occurrences in deps/raft (89 files) — no masked green possible:
  for non-nil pointers the collapse is value-identical to correct
  behavior, so only nil-path cases can differ, and all are pinned.
- JUDGMENT: matrix landed as a NEW package rather than rows appended to
  `address-op-nil-indirection` — keeps the P3 pins' file byte-stable
  while their entry is still open (same reasoning as slice 1's
  relatives package).

### Slice 4 — BUG-005 probes + memo

- **Deliverable:** `docs/2026-08-19_bug005-map-range-memo.md`.
  Recommendation: model (L) — live-read-per-iterNext (`Cont.mapIterK`
  carries base loc + produced-key set + start-key set; pick-next loads
  the map cell, candidates = live entries minus produced, one choice of
  width candidates+stop with stop legal only when no start-key
  candidate remains). Forced clauses exact; the added-entries latitude
  becomes a genuine choice at the existing Q3 pick site (never gc's
  member silently); the per-iterNext load is the U1-closing race
  footprint arm; canonical empty-stream member keeps mutation-free
  ranges byte-identical to today's pick sequence (zero baseline drift
  outside the predicted flips). Two narrowings recorded with
  re-envelope obligations: at-most-once production per KEY (the
  literal spec text admits re-producing a deleted-then-re-created
  entry; gc never does, 800 probe runs incl. forced growth — and the
  literal reading admits unbounded traces, killing ∀-streams
  certification) and re-created start keys mandatory.
- **Memo sharpening beyond the BUG entry:** stale VALUES violate a
  FORCED point — the range clause's production table defines the map
  second value as `m[k]`, produced "for each iteration" — so
  update-visibility is spec-mandated, not a gc member.
- **Probe findings** (artifacts/probe/map005, scratch; 400 runs each):
  gc exhibits the FULL added-entries latitude across plain re-runs of
  one binary (4+4 shape: counts {4:53, 5:34, 6:55, 7:60, 8:198} — all
  five members, no GODEBUG needed), which KILLS the tempting
  "live but skip all created entries" simplification (observed ∉
  modeled); delete-unreached is forced (n=1, 400/400); no
  re-production ever (probes C/D).
- **Probe rows landed** (only where they add coverage beyond the three
  reds): `maps/delete-unreached-during-range` (RED, machine 20 vs go
  11 — the removal clause isolated: current key kept, only the
  unreached key deleted) plus two member-invariant GREEN envelope
  bounds (`maps/added-entries-bound`, `maps/delete-readd-during-range`)
  that stay green under snapshot AND any conforming live model, and go
  red on over-production, alien keys, or divergence. Neither green pin
  asserts a latitude member.
- JUDGMENT: `added-entries-bound` initially carried the `nondet`
  feature tag; the manifest lint correctly refused it (nondet demands
  lane=membership). The tag was dropped rather than the lane changed:
  the subject NORMALIZES the member away — its observable is
  deterministic (7) across the entire envelope — so strict equality is
  an honest oracle for it. Recorded because it looks like tag-dodging
  unless the reasoning is stated.
- JUDGMENT: `delete-readd-during-range` pins gc's exact count (3) —
  deliberately: it encodes the memo's narrowing 1, so it goes red the
  moment an implementation admits re-production, forcing that decision
  through the memo's decision block instead of past it. If the user
  rules for the literal envelope, this row is reworked to
  membership-lane FIRST (stated in the case comment and the memo).

### Gate at the probe/memo commit

Full run at this tree: `scripts/coverage run` → cases=2167 pass=2029
fail=138; `scripts/coverage-baseline-diff` drift was EXACTLY the 13 new
ids (4 NEW FAIL: the three addr-matrix reds + delete-unreached; 9 NEW
PASS) and no existing id moved. Baseline re-pinned from that full run
in this commit (header carries the delta list and reason; was 2154,
2020/134).

Confirming gate: `GOLEAN_MEM_MAX=24G scripts/ci --diff` → **RESULT:
PASS**, exit 0, every step ok. Precision on the gated tree: the run
covered every substantive file in this commit; the ONLY difference
between the gate's tree and the committed tree is this log's own
gate-record paragraph, written afterward to record the result (a gate
cannot precede its own record) — `baseline
diff FULL (2167/2167, no regression)`, `re-pin guard (0 PASS→non-PASS
flips)`, `bug-index cross-check ok`, eval tests 136 ok, negative lane
390/390 clean, golden-lowering and imported-goose pins ok
(artifacts/probe/ci-slice34-final.log, scratch). HONESTY note: a FIRST
`ci --diff` was launched before the BUGS.md Cases edit settled and its
bug-index step correctly FAILED — the green guard pins were briefly on
the open entries' Cases lines, which the cross-check reserves for
reds. The pins were moved into the entries' prose (recorded there
explicitly) and the full gate re-run from scratch at the final tree;
nothing else differed between the two runs.

**Slices 3+4 state: memos delivered, HARD PAUSE.** Both slices now sit
at their charter-designed user gates: no implementation exists or
begins until Mike rules on the two memos' decision blocks
(`docs/2026-08-19_bug056-addr-deref-memo.md` §5,
`docs/2026-08-19_bug005-map-range-memo.md` §4).

### The rulings (2026-08-19) — gate lifted

Mike ruled on both decision blocks; the verbatim substance is recorded
as a dated USER RULING section in each memo (§6 of the BUG-056 memo,
§5 of the BUG-005 memo — appended before any implementation began).
The headline deltas from the memos' recommendations:

- BUG-056: (b) approved as recommended, name/wire key as recommended.
- BUG-005: (L) approved but the two narrowings are **REJECTED** — the
  implementation carries the FULL literal envelope (deletion prunes
  the produced-set AND the mandatory start-set; a re-created key is an
  ordinary created entry, re-producible). Self-inserting loops are
  genuinely unbounded: ∀-streams certification fails closed on them
  and such cases ride the membership lane. The canonical member is
  DEFINITIONALLY the machine at the zero stream (stop LAST).
- **KIT OBLIGATION (recorded, NOT proven this slice, per Mike):** a
  tiny syntactic termination theorem for the map-range kit — "body
  stores no key into the ranged map ⇒ range terminates" — most
  programs terminate structurally because surviving never-removed
  start keys are forced. Owed to the post-WP-arc kit alongside the
  map lemmas the surgery touches.
- New standing doc directed: `docs/spec-interpretations.md` (curated
  index of adopted spec readings, ledger-backed, CLAUDE.md-linked) —
  executed as this arc's slice 3+4 docs commit.

### Slice 3 implementation — the BUG-056 fix (ruled mechanism (b))

The memo's ~10 arms, all landed in one commit:
`emitUnaryExpr` (the `&` operator's immediate-`*` operand → wire
`addr-of-deref`), `decodeExpr` arm, `Expr.addrOfDeref` constructor,
`StrictOp.addrOfDeref` + `strictPlan` row + the 3-line apply arm
(nil-assert via `valueAsLoc`'s existing runtime-panic arm, yield the
pointer, NO memory access), `Expr.locSup` + `applyStrictOp_wf` cases,
`renameExpr` arm, mirror `applyStrictOp'` arm (computes on concrete
pointers, `.nil` quits Q6, atoms Q10), `applyStrictOp_conc` and
`applyStrictOp_sim` cases (fieldAddr's shape minus the field
constructor), and the Race.lean call-site-inventory NO-ACCESS entry
(the deliberate no-footprint decision — gc's TESTB is uninstrumented
and our model performs no load at all). Relation: zero new rules (the
generic strict-op frame machinery; `strictPlan_locSup` is generic
over unary constructors). Core + proofs built green first try.

**JUDGMENT (slice 3, THE ONE DEVIATION FROM THE MEMO — emitter arm
placement, found by the differential).** The memo's blast-radius table
said "the StarExpr arm of emitAddressOf". Implemented that way, the
full run flipped FIVE store-order pins red
(`assign-order/target-check-vs-rhs/nil-deref-target`,
`channels/recv-edge/second-target-panic-stores-first`,
`channels/recv-map-elem/first-store-lands`,
`multi-assign/store-order-plain`,
`pointers/nil-array-elem-store/second-target`): `emitAddressOf` is
not the `&` operator — it is the GENERAL addressable path, reached by
assignment targets, slice/array bases and receiver addresses, where
the nil check belongs to each consumer's own spec point (a store
target panics in PHASE 2, after the RHS — BUG-029's timing).
addr-of-deref there made the panic fire at target-address evaluation,
before the RHS — observably too early. The arm was re-scoped to
`emitUnaryExpr`'s `token.AND` path (parens stripped, immediate
`*` operand only), which IS spec#Address_operators' `&x`; the
StarExpr arm of `emitAddressOf` keeps the collapse with a comment
naming the five guards. All five back green, matrix 10/10,
both memo pins green. Recorded because the memo's own scoping
sentence ("the immediate `&`-of-`*` composition ONLY") was right and
its file-table row was imprecise — and the differential caught it,
which is the guardrails-first discipline doing exactly its job.

**Acceptance tests (memo §6, both ground truths):**
- **No load / no race visibility:** new pinned green
  `race/free/addr-deref-no-read` — main takes `&*p` and compares
  pointer identity while a child writes the POINTEE; only pointee
  read is after the join. gc probe at the fix
  (artifacts/probe/addr056-accept, scratch): plain 142, `-race` green
  20/20; the real-load control (`y := *p`) is TSan-red exit 66 — so
  the row is load-bearing: a fix that materialized a pointee read
  turns it red with a raceDetected refusal. Machine: PASS, confluent
  (|set|=1 certified over all schedules).
- **Race negative stays quiet:** `race/negative` focused run 14/15
  with the one fail the expected BUG-005 pin
  (`race/negative/map-range-iter`); no new refusals anywhere in the
  full run.

**Predicted flip set, stated before the confirming run (5 red→green +
1 new green, nothing else):** the five BUG-056 Cases
(`address-op-nil-indirection/{addr-deref-nil,addr-deref-nil-paren}`,
`addr-deref-nil-matrix/{two-deref-inner-nil,deref-arg,deref-call}`)
FAIL/lean-observation → PASS, plus `race/free/addr-deref-no-read`
NEW → PASS/confluent. **Full run: drift was exactly that set** —
2180 cases, 2053 PASS / 127 FAIL (was 2179, 2047/132); the 7 matrix
guard greens and the 5 store-order guards all held. Baseline
re-pinned in this commit from that run, reason in its header.
BUGS.md BUG-056 → fixed (mechanism one-liner + flip list + the
acceptance pin; discovery record kept verbatim).

### Slice 4, step 1 — the guardrails-first rework (ruled envelope made visible BEFORE the surgery)

Per the ruling's execution order: the rows whose exact-count pins
encoded the DEAD narrowings are reworked ahead of any machine change,
so the surgery lands against guardrails that already state the ruled
envelope.

- **`maps/delete-readd-during-range`** — strict exact-count pin (3) →
  MEMBERSHIP row observing the raw production count, runaway guard
  lowered 50 → 4 so the trace tree is enumerable: admitted set
  {3, 4, -1}, where -1 is the subject's own truncation of the
  genuinely unbounded tail (an ADMITTED member under the full literal
  envelope — a re-created key is re-producible forever — not a
  violation). gc at the rework probe: 3 in 60/60.
- **`maps/added-entry-count`** — NEW membership row: the raw
  created-entry produce-or-skip observable its strict sibling
  normalizes away. Admitted set {1, 2}; gc exhibits BOTH members
  (1: 9/60, 2: 51/60, artifacts/probe/map005-rework, scratch) — so on
  this shape the snapshot machine's "never produced" narrowing is
  ORACLE-VISIBLE (observed ∉ modeled, the bug definition, sampled).
- **Both are deliberately RED pre-surgery** (FAIL/membership: the
  snapshot machine enumerates singletons — {3} and {1} — and the
  membership lint refuses singleton-set membership rows) and are now
  on BUG-005's Cases line; both flip green at the (L) surgery.
- **JUDGMENT (slice 4, added-entries-bound stays STRICT).** The ruling
  says created-entry-latitude cases ride membership rows; the
  member-invariant bound subject (returns 7 across the WHOLE ruled
  envelope — key 1 is a mandatory never-removed start key, so entry 2
  is created exactly once and producible at most once) was attempted
  as a membership row and the harness lint REFUSED it ("enumerated
  observation set is a singleton — the case belongs in the strict or
  confluent lane"). The lint is right: member-invariant observables
  are what the strict lane is FOR; the ruling's substance (the raw
  latitude on a membership row) is carried by `added-entry-count`.
  Recorded in the case file so the split reads as the lint working,
  not tag-dodging.

**Predicted drift, stated before the run (2 lines):**
`delete-readd-during-range` PASS/- → FAIL/membership;
`added-entry-count` NEW → FAIL/membership. **Full run: exactly that**
— 2181 cases, 2052 PASS / 129 FAIL (was 2180, 2053/127). Baseline
re-pinned in this commit; check-bugs ok (backlog unchanged 25/25 —
both new reds are explained by BUG-005's Cases line).

### Slice 4, step 2 — the interpretations index (Mike-directed docs)

- **`docs/spec-interpretations.md`** established: the curated index of
  adopted spec readings — one row per reading (spec sentence verbatim,
  our reading, rejected alternative, what depends on it), every row
  BACKED by a `docs/spec-divergence-ledger.md` entry (the file's own
  standing rule: no ledger entry, no row). Seeded with 7 rows from the
  directed sweep: I-1 delete-then-recreate = NEW entry (L-012, the
  ruling's interpretive reading, filed with the verbatim sentence
  pair, the probe data, and the rejected key-identity alternative);
  I-2 "not specified" order = UNSEQ not either-order (the inventory's
  E2–E5/E12 F2 readings — backing entry L-013 CREATED, per the
  every-row-backed rule); I-3 may-restriction prose over exhibit
  (L-010); I-4 init-order binds observably-initializing packages
  (L-011); I-5 version-conditional spec, declared-version scope
  (L-009); I-6 mem sequenced-before delegates to the spec's eval
  order (L-004); I-7 select's normative basis is spec-only (L-005).
  All quoted sentences re-verified against the pinned
  `deps/go` text before landing.
- CLAUDE.md gains one linking sentence in the two-bounds section (the
  always-loaded file stays lean; the doctrine section is where a
  reader deciding an interpretation already is).
- Sweep scope, honestly stated: the ledger's `spec-ambiguity` stances
  (L-010, L-011 — both indexed) plus its interpretation-shaped
  informational entries (L-004, L-005, L-009); the latitude
  inventory's interpretive notes (the F2/UNSEQ readings — indexed via
  the new L-013). NOT indexed: envelope *realizations* (pins), which
  stay in the inventory; text-fault records (L-001, L-006, L-007,
  L-008), which are not readings; prior-art records (L-002, L-003).

---

### Slice 4, step 3 — the (L) surgery (the ruled fix, machine + proofs)

**The machine change** (one semantic concern: live map iteration at the
ruled FULL literal envelope):

- `Cont.mapIterK` now carries `(base : Option Loc)` (the map's data
  cell), the PRODUCED key set, and the START-KEY set (read at range
  entry by `mapRangeStartSets` — the snapshot step is retired).
- Each pick recomputes `mapIterCandidates` = live entries minus
  produced keys, VALIDATED self-normalized at the range key/value types
  (fail closed — the sem-adequacy guard moved from the retired snapshot
  step to the pick, keeping pick success choices-independent), and
  loads the value from the LIVE cell. Width = `candidates.size +
  (if mandatory then 0 else 1)`; the stop slot is LAST, so the ZERO
  stream is the canonical member BY DEFINITION (ruling Q3) — and a
  self-inserting loop fuels out VISIBLY there, which is correct.
- `mapIterMandatoryRemains`: the stop slot is legal exactly when no
  candidate key is a never-removed START key (the spec's production
  table forces surviving start entries; created entries are
  may-produce-or-skip — interpretations I-1/L-012).
- DELETE-PRUNE: `mapDelete`/`clearMap` rewrite the SAME-GOROUTINE
  continuation via `contAfterStmtOp` → `pruneIterFramesKey`/
  `pruneIterFramesAll` (rule `stmtOpApply` gained the `hcont'`
  premise; identity per concrete non-delete op by `rfl`). This is what
  makes the FORCED removed-before-reached clause exact. Residual,
  recorded in `Cont.mapIterK`'s docstring AND inventory E9: a
  cross-goroutine delete does not prune the other goroutine's frames —
  such shapes are racy-red via the new footprint, and the widening is
  owed at the first non-racy cross-goroutine range case.
- RACE: `stepAccesses` gained the mapIterK per-pick READ arm — closes
  inventory under-approximation U1 (BUG-005's fourth symptom;
  `race/negative/map-range-iter` flips green as a true racy-red).

**Proof blast radius, all repaired to a full green `lake build` (none
parked; the ~day stop-rule was consciously overrun once the remaining
work became enumerable — recorded as a judgment call, the alternative
was abandoning a green progression):**

- Core: `StepFn`/`Machine` rule pair (`mapIterNext` premises now
  hcands/hmand/hbind state facts; `mapIterStop`; `mapRangeStart`),
  `StateWf` (`itersNormalized` moved to per-pick validation),
  `MachineSound` (`step_complete_any_wf`'s mapIterNext case replayed on
  the live design), `MultiStreams`, obliviousness (`stepFn_oblivious`
  fun_cases tags remapped after the pick-arm collapse).
- Kit: `MapMem` gained the live-pick surface — `rangeStart_toEntries`,
  `candidates_toEntries`, `mandatory_toEntries`/`mandatory_true_of_all`,
  `stepFn_pick_bind/value/novars` (hcands/hmand/hconsume form),
  `stepFn_iter_done`, and the produced-set walk algebra
  (`toKeys`, `filter_push_key`, `filter_ne_key_eraseIdx`) — the
  pick-coherence relation "produced = toKeys done, remaining = the
  filter" every placement threads through `mapPickLoop_generic`.
  The pick lemmas LOST `Classical.choice` (now `[propext, Quot.sound]`
  — the live-candidates path is constructive; Audit/Kit pins updated,
  shrink direction).
- WP laws (`Laws/StmtOps`, `Laws/Range`): `wp_map_range_snapshot` →
  `wp_map_range_enter` (+`_nil`) — the range START reads base/start off
  the owned cell, NO snapshot, hnorm premise gone (validation is now
  the iter laws' hcands state facts); `wp_map_iter_next_key`/`_done`
  take owned-cell candidate/mandatory facts quantified over
  `σ.types`-pinned states; `wp_map_iter_inv` is the (L) form — caller
  supplies the reachable relation `P pr rem`, `hfact` (pick-time
  candidates/mandatory against the cell), `hstep` (P closed under
  picks), and the cell rides through and returns at exhaustion. Scope
  (recorded in its docstring): key-only, normally-completing,
  mutation-free-range walks — the stop-admitting and mutating forms
  are KIT OBLIGATIONS landing with the first walk that needs them.
  Witnesses: basic-key + defined-key pick witnesses recomputed against
  owned cells; the key-sum inv witness reworked (its
  `keyIntSum_eraseIdx`/`keyIntSum_nonneg` helpers retired — Audit.lean
  example pins updated with a tombstone note).
- `Specs/AutomationTargets` TARGET 3 (`mapIterInvRule_statement`)
  DELIBERATELY RESHAPED to the (L) rule type — recorded as a widening
  per its own docstring contract, not a quiet accommodation.
- Examples/placements re-proved on the pick-coherence pattern:
  WordCount (CanonCount/CanonRange/CanonRun, HarnessSubject/HarnessR/
  HarnessRun — `wc_range_loop` and the R/H instantiations now take
  `hkv`+`hnodup` and start at `pr = #[]`; `wcRange_generic` carries
  `PC : kvs → produced → remaining → Prop` with the state's kvs pinned
  inside PC), Histogram, WordFreq, RangeGeneric.
- Quorum pilot: `GoldenQuorumPin` witness renamed
  `wp_map_range_enter_committed` (hnorm dropped); `GoldenQuorumWP`
  (n = 1) walks the two-state reachable relation; `GoldenQuorumThree`
  gained the voter-encoding live-pick data layer (`cfgKeys_toKeys`,
  `filter_ne_eraseIdx_int`, `filter_push_int`,
  `filterCandidateList_cfgList`, `candidates_cfg`, `mandatory_cfg`)
  and `wp_ci_loop`/`wp_ci_loop_all`/`wp_committedIndex{Call,_body}_all`
  gained a `ks₀.Nodup` hypothesis — DISCHARGED at both consumers (the
  3-voter rung by `decide`; the ∀-config summit from its existing
  `c.Nodup` via the perm transport), so `committedIndexAllConfigs`'
  STATEMENT is unchanged (the nodup lives in already-present
  hypotheses of the statement's encoding layer). Body-iteration
  lemmas (`wp_ci_range_body{,_one,_miss}`) generalized over the
  iteration continuation (`kIter : Cont`) — strictly weaker-premised,
  same walks.

**Kit obligations recorded (not proved, per the ruling):**

1. TERMINATION: "body stores no key into the ranged map ⇒ the range
   terminates" — the user-facing theorem the fuel-out-on-zero-stream
   behavior of self-inserting loops points at.
2. Stop-admitting and mutating-range WP forms of `wp_map_iter_inv`
   (docstring-scoped out today).
3. Abstract-key candidates algebra: `candidates_toEntries` (Int-keyed
   counts), `candidates_toEntriesW` (string-keyed), and
   `candidates_cfg` (voter encoding) are three instances of one
   ≥2-consumer pattern — a consolidation slice should lift the generic
   form (promotion-ledger entry).

**Corpus, predicted BEFORE the runs and confirmed exactly:** the
focused slice then the FULL run flip precisely BUG-005's seven Cases —
`maps/{delete,clear,update,delete-unreached}-during-range`
FAIL/differential → PASS; `maps/delete-readd-during-range`
FAIL/membership → PASS/membership (admitted {3,4,-1}, exhibited 1);
`maps/added-entry-count` FAIL/membership → PASS/membership ({1,2},
BOTH exhibited); `race/negative/map-range-iter` FAIL/lean-observation →
PASS/racy — and `maps/added-entries-bound` STAYED PASS/strict, as
required. Full run: 2181 cases, 2059 PASS / 122 FAIL (was 2052/129);
`coverage-baseline-diff` drift = exactly those seven lines; baseline
re-pinned in this commit (reason in its header). Docs updated in the
same movement: inventory E9 re-enveloped (+ §9 flags 4/11 and the
census counts closed out), the nondeterminism doctrine's
requirement-1 map statement rewritten to the live envelope (F14 scope
lifted), BUGS.md 005 → fixed (residuals + obligations on the entry).

**Gate at the surgery commit.** `GOLEAN_MEM_MAX=24G scripts/ci --slow`
(the interpreter changed, so the tiered-checking rule demands full
slow-tier re-certification, not just `--diff`) → **`RESULT: PASS`**,
exit 0, every step ok: core build warning-free (the first `--slow` run
FAILED on two warnings my surgery introduced — an unused `hidx :`
match binder in `stepFn`'s pick arm and two unused simp args in
`MachineSound` — fixed, core+proofs rebuilt green, gate re-run in
full), `proofs + Audit gate` ok (axiom allowlist + non-vacuity),
`baseline diff FULL (2181/2181, no regression)` against the re-pinned
baseline with slow-tier rows RE-CERTIFIED (`GOLEAN_SLOW=1`), `re-pin
guard (0 PASS→non-PASS flips)`, `bug-index cross-check ok`, `eval
tests (136 ok)`, membership/negative lanes ok, statement-TCB +
import-direction + surface-purity ok (`artifacts/probe/
b005-ci-slow2.log`, scratch). As with the earlier slices, the only
difference between the gated tree and the committed tree is this
paragraph.

## Slice 5 — the full red/bug triage (kill or justify)

Deliverable: **`docs/2026-08-19_triage-table.md`** — one row per open
`docs/BUGS.md` entry and per root-cause GROUP of baseline reds, each in
exactly one of the charter's three categories. Split out of this log
because a 40-plus-row table with written arguments buries everything
else; this section carries the slice's judgment calls and gate records.

### Step 0 — the denominators, re-derived (the charter said to)

`awk '/^## BUG-/{id=$2} /^- Status: open/{print id}' docs/BUGS.md` → **9**
open entries, not the charter's 13. At the charter commit `df3adbfc`
the open set was already **11** (BUG-002/004/005/008/014/041/056/057/058/
059/061); slices 1–2 closed 057 and 058. **The charter's "13" was never
right** — recorded because DONE clause 5 counts "13/13"; the honest
conjunction is 9/9. Baseline reds at `0c21aa21`: **138** (7 differential,
92 frontend-export, 37 lean-observation, 1 go-run, 1 nondet), not the
charter's 136 — the 13 probe rows of slices 3+4 moved the split.

### Step 1 — mini-slice A1: `copy` and `recover` in statement position

**Category (a), executed.** spec#Expression_statements: "With the
exception of specific built-in functions, function and method calls and
receive operations can appear in statement context", and the
not-permitted list is exactly
`append cap complex imag len make new real unsafe.*`. So `copy` and
`recover` ARE legal expression statements — and the frontend refused
them (`emit.go`, `emitStmt`'s ExprStmt builtin switch: `unsup("builtin
%s in statement position")`), quarantining the whole declaration.
`copy` in statement position occurs in **etcd-io/raft** (`util.go`,
`tracker/inflights.go`), so the refusal was on the north-star path.

**Guardrails FIRST, colors recorded before the fix.** New package
`Corpus/coverage/exec/builtins/statement-position/`, 7 rows, every
expectation computed from `go run` before the differential ran
(`artifacts/probe/triage-stmtbuiltin`, scratch — 450, 11234, 12450,
105050, 5, 4, 7 in declaration order). `scripts/coverage run --prefix
builtins/statement-position` against the UNMODIFIED emitter:
**7 cases, 0 PASS / 7 FAIL**, every one at `frontend-export` with the
exact refusal string. The rows are chosen to be load-bearing, not
decorative: `copy-stmt-eval-order` pins that discarding the RESULT does
not discard the OPERAND order (dst before src, trace 12);
`copy-stmt-overlap` pins the spec's as-if-intermediate overlap clause in
the new position; `recover-stmt-in-defer` pins that a bare `recover()`
statement still counts as "called directly by a deferred function"
(spec#Handling_panics) and squashes the panic; `recover-stmt-no-panic`
and `recover-stmt-outside-defer` pin the two no-op directions, so a fix
that swallowed something would go red.

**The fix** (`tools/nativefrontend/emit.go`, one switch arm, +27/-6):
`copy`/`recover` lower through the already-green EXPRESSION node under a
BLANK assignment target — literally the `_ = copy(dst, src)` shape that
`n := copy(...)` and `_ = recover()` already take — instead of a new
statement node. `print`/`println` keep the refusal (implementation-
specific debug builtins the spec says may be removed).

**JUDGMENT (slice 5, A1 mechanism).** The alternative was a dedicated
`copy` statement wire node. Rejected: the expression node is already
differentially validated in every operand shape (`builtins/copy-edge`,
10 green rows), a second lowering would be a second thing to keep
correct, and the blank-target assign is a shape the decoder already
builds. Frontend-only; no wire-schema, decoder or GoCore change.

**JUDGMENT (slice 5, A1 scope).** `copy` and `recover` only — NOT a
general "route any builtin through the expression node". The spec's
permitted set in statement context is a closed list, and `print`/
`println` have no expression form the machine models; a blanket route
would have turned a precise refusal into a decoder-level failure for
them. Fail closed on the rest, by name.

**Predicted flip set, stated before the confirming full run (3 red→green,
7 new green ids, nothing else):**

- `goroutines/spawn-edge/child-recovers` (FAIL/frontend-export → PASS)
- `imported-goose/semantics/copy/copy-simple` (FAIL/frontend-export → PASS)
- `imported-goose/unittest/copy/copy-simple` (FAIL/frontend-export → PASS)
- `builtins/statement-position/*` (7 NEW → PASS)

**Full run at the fix tree:** `scripts/coverage run` → cases=2174
pass=2039 fail=135 (was 2167, 2029/138). `scripts/coverage-baseline-diff`
drift was **exactly the predicted set and nothing else** — 10 lines, no
other id moved. Baseline re-pinned in this commit from that run, reason
in its header. No `docs/BUGS.md` change is owed: statement-position
builtins were a frontend COVERAGE refusal (`frontend-export`), which
BUGS.md's own preamble excludes from the bug index by definition.

**Gate at the A1 commit.** `GOLEAN_MEM_MAX=24G scripts/ci --diff`, full
run at the fix tree → **`RESULT: PASS`**, exit 0, every step ok:
`baseline diff FULL (2174/2174, no regression)`, `re-pin guard
(0 PASS→non-PASS flips, all listed in BUGS.md Cases)`, `bug-index
cross-check ok`, `eval tests (136 ok)`, `negative baseline diff (no
regression)`, golden-lowering and imported-goose R2 pins ok,
spec-anchor citations resolve at the pin, frontend unit tests ok
(`artifacts/probe/a1-ci.log`, scratch). `scripts/check-bugs.sh`: ok
(61 bugs) with the untriaged-fidelity backlog unchanged at **25/25** —
A1 retired three FRONTEND-COVERAGE reds, which never counted toward the
fidelity backlog, so the number correctly does not move. The ONLY
difference between the gated tree and the committed tree is this
paragraph, written afterward (a gate cannot precede its own record).

### Step 2 — the triage table

**`docs/2026-08-19_triage-table.md`**: 9 open BUGS.md entries + all 138
baseline reds in **45 root-cause groups**, each in exactly one category.
Split out of this log because 45 grouped rows with written arguments and
refusal points would bury everything else here. Counts at `0c21aa21`:

| category | reds | groups | bug entries |
| --- | --- | --- | --- |
| (a) fix in this arc | 46 | 16 | 2 (BUG-005, BUG-056) |
| (b) frontier | 82 | 23 | 3 (BUG-008, BUG-014, BUG-041) |
| (c) profound-reason pin | 10 | 6 | 4 (BUG-002, BUG-004, BUG-059, BUG-061) |
| total | 138 | 45 | 9 |

The (a) 46: **6 fixed here** (A1 3 + A2 3, steps 1 and 4) + 11 queued
frontend-only mini-slices (A3-A6) + 19 gated on the charter's GoCore
pause + 10 already at the slice-3/4 design gates.

**JUDGMENT (slice 5, the (a) rows that are GoCore-touching are ASKED, not
taken).** Nineteen reds are cheap and fully diagnosed to a named arm
(rune/string conversions, slice→array length panics, IEEE min/max,
pointer-to-array indexing both live and nil, the struct-tag conversion
check, go-of-nil-func), and every one is red→green-only movement over a
currently-refusing path. All nineteen change `GoLean/GoCore/*.lean`. The
charter's hard boundary is explicit — "No GoCore/semantic-core change
without the slice-3/slice-4 gates — those are the arc's designed
pauses" — so they are put to Mike as ONE gate item rather than executed.
Recorded because "cheap and obviously right" is exactly the argument
that erodes a designed pause.

**JUDGMENT (slice 5, which frontend-only (a) rows were taken).** A1 was
taken (raft-path, hours, guardrails trivially available, zero
neighbour surface); A2 was taken next for the same reasons (step 4).
A3-A5 are queued with mechanisms; each is a scheduling call with its
reason in the table (A3 lands inside the BUG-025/052 assignment spine
and needs its own two-phase edge enumeration; A4 moves the
mangling/identity surface and owes a reflect-spelling probe plus a
`TestManglingSurfaceFailsClosed` update; A5 is a BUG-057-family edge).

**JUDGMENT (slice 5, A6 / the charter's named receive-hoist item is
deferred on a FINDING, not on cost).** The charter expected BUG-023/026
to be category (a). Both are FIXED and all nine of their pins are green;
the four residual reds belong to **BUG-032**, whose "fix" was a
deliberate fail-closed refusal, and the fifth
(`operator-precedence/mixed-chan`) is not in the family at all — it is
the E3 short-circuit-receive boundary, category (b). For the four,
(a) survives but by a different mechanism than "restore the hoist":
`fnHasRecv` is FUNCTION-scoped, so it refuses statements where the
forced constraint it protects (len-vs-receive lexical order) cannot
bind; scoping the predicate to the STATEMENT makes `len` inline in a
receive-free statement, which is gc's realization — the receive-free
control `channels/recv-order/len-embedded-no-recv` is already green
end-to-end as the witness. It was NOT taken because the triage turned up
the following.

**A NEW divergence, found by triage, outside all 138 reds.**
`spec#Order_of_evaluation` orders "all function calls, method calls,
receive operations, and binary logical operations" left-to-right, and
`spec#Built-in_functions` says built-ins "are called like any other
function" — so in `len(ch) + fill(ch)` the `len` must be read first. gc
agrees (probed at the pin, `artifacts/probe/triage-lencall`, scratch:
`go run` → 1, not 3). The frontend hoists CALLS out of expressions but
leaves `len` inline in a receive-FREE function, so the machine should
read `len` AFTER the call — a FORCED-point divergence, BUG-023's exact
class on the `len`-vs-CALL axis instead of `len`-vs-RECEIVE, and
pre-existing. The machine half is REASONED off the emitter, not run, so
the first step is a guardrail case and a `diff-one`, not a fix. It is
also why A6 waits: receive-BEARING functions hoist `len` today and
therefore get `len`-vs-call RIGHT by accident, so A6's statement-scoped
predicate would EXTEND the divergence to them unless the predicate is
"the statement's sweep contains an ORDERED EVENT" (receive **or call**).
A one-word difference in the mechanism, invisible without the probe.

### Step 3 — the untriaged-25 cross-check (charter cross-cutting obligation)

The set is exactly `baselines/untriaged-ids` (the P3 dispositions TSV has
no untriaged marker; three independent derivations agree on the same 25 —
`check-bugs.sh --list`, the tracked file, and the reds-minus-Cases
arithmetic). **Outcome: no member was explained by slices 1-2's fixes**,
derived from the fidelity-red sets at `df3adbfc`/`740f09f8`/`2d840744`/
`0c21aa21` (48/45/41/45) — the seven fidelity reds those slices killed
were every one already on BUG-057's or BUG-058's `Cases:` line, i.e.
already explained, never in the backlog. The honest negative result.

What DID change: ten of the 25 carried no justification at all in
`baselines/untriaged-ids`. All ten now have one, with their triage row
id (`arrays/pointer-array` → L5, `pointers/nil-array-index-panic` → L6,
`structs/tag-pointer-conversion` → L7, the seven `strings/*` rune
conversions → L1). Membership is unchanged; only the record improved.

**A metric finding, recorded and deliberately NOT acted on.** The backlog
counts any fidelity-stage red no BUGS.md entry explains — but
`lean-observation` is also where the INTERPRETER's fail-closed refusal of
an unmodeled construct lands, which BUGS.md's own preamble excludes from
the bug index ("tracked as coverage, not here"). So frontier rows like
`channels/select-select/core` and latitude rows like
`floats/to-int-out-of-range/*` can leave the backlog neither by being
fixed nor by being triaged, and "ratchet toward 0" is unreachable for
them by construction. The clean resolution is a disposition column the
check subtracts — a GATE change, which this slice does not touch (gates
are speedbumps; slice 6's coverage ledger is the natural owner). Flagged
so the 25 is read honestly.

**Gate at the triage-table commit.** Docs-only (`docs/` +
`baselines/untriaged-ids`, which is a check-bugs INPUT, not a run
record), so `GOLEAN_MEM_MAX=24G scripts/ci` without `--diff` →
**`RESULT: PASS`**, exit 0, every step ok including `bug-index
cross-check`, `spec-anchor citations resolve at the pin` (289 spec# +
73 mem#, all resolving at `c19862e5f`), `eval tests (136 ok)`,
`negative baseline diff`, and `baseline diff FULL (2174/2174, no
regression)`. That last step reports `[recorded at 0c21aa2, HEAD is
1ca434b — stale]`: the record is A1's own `ci --diff` run, taken at the
exact code tree that A1 then committed, so the label is about the commit
HASH and not the tree — no runtime file changed between the run and
either commit. Stated rather than glossed, per the gate-honesty rule.

### Step 4 — mini-slice A2: method expressions in CALL position

**Category (a), executed.** `spec#Method_expressions`: `T.Mv` "yields a
function equivalent to Mv but with an explicit receiver as its first
argument", and the spec's own five-equivalent-invocations block writes
the DIRECT call forms `T.Mv(t, 7)` and `(T).Mv(t, 7)`. The frontend
supported method expressions in VALUE position (`f1 := mefT.Mv`) and
refused them in CALL position: `emitMethodCall`'s selection dispatch
fell past the MethodVal and FieldVal branches into
`unsup("selector call %s is not a method value", …)`, quarantining the
whole declaration.

**Guardrails FIRST.** New package
`Corpus/coverage/exec/methods/method-expr-call-position/`, 5 rows, every
expectation from `go run` before the differential ran
(`artifacts/probe/triage-methodexpr`, scratch — 307, 16, 409, 2006,
120307). All 5 verified RED against the unmodified emitter with the
exact refusal string. **JUDGMENT (slice 5, A2 row choice):** the five
rows are exactly the paths `emitSelector`'s own MethodExpr arm
distinguishes — concrete value receiver, concrete POINTER receiver (the
trailing `+ t.a` fails if the receiver is copied instead of addressed),
INTERFACE method expression (dispatch anchor, receiver as argument
rather than capture), PROMOTED method expression (wrapper receiver form,
embedded hop on the argument) and argument evaluation ORDER through the
call. A routing fix that greened one path while mis-lowering another
would otherwise be invisible.

**The fix** (`tools/nativefrontend/emit.go`, one branch, +30): route a
`types.MethodExpr` selection through `emitSelector` — which already
emits the correct receiver-first func value — under the same
`call-value` shape a func-typed field takes. Routing, not synthesis.
`emitSelector`'s own refusals propagate unchanged, which is what keeps
the deliberate reds red.

**Predicted flip set, stated before the confirming run (3 red→green, 5
new green ids, nothing else; three named UNCHANGED reds):**

- `spec-examples-lexical/method-expressions/{value-receiver-expr,
  pointer-receiver-expr}`, `spec-examples-stmt/method-expr-five-forms`
  (FAIL/frontend-export → PASS)
- `methods/method-expr-call-position/*` (5 NEW → PASS)
- UNCHANGED red, verified: `spec-examples-decl/method-expressions` and
  `spec-examples-lexical/method-expressions/derived-pointer-receiver-expr`
  (the `(*T).Mv` DEREF ADAPTER — triage row F8, category (b): a
  synthesized adapter, not routing), and `spec-examples-decl/
  timezone-stringer`, which reaches the same refusal STRING but whose
  blocking construct is `fmt.Sprintf` — the stdlib surface (row F19).
  **That third one is a triage finding landing as evidence:** the four
  "not a method value" reds were ONE group by error string and TWO
  groups by cause, and the fix's own drift proves the split.

**Full run at the fix tree:** `scripts/coverage run` → cases=2179
pass=2047 fail=132 (was 2174, 2039/135). `scripts/coverage-baseline-diff`
drift was **exactly the predicted set and nothing else** — 8 lines.
Baseline re-pinned in this commit from that run, reason in its header.
`scripts/check-bugs.sh`: ok (61 bugs), backlog unchanged at 25/25 (these
were frontend-COVERAGE reds, outside the fidelity ledger).

**Gate at the A2 commit.** `GOLEAN_MEM_MAX=24G scripts/ci --diff`, full
run at the fix tree → **`RESULT: PASS`**, exit 0, every step ok:
`baseline diff FULL (2179/2179, no regression)`, `re-pin guard
(0 PASS→non-PASS flips)`, `bug-index cross-check ok`, `eval tests
(136 ok)`, `negative baseline diff`, golden-lowering and imported-goose
R2 pins ok, spec-anchor citations resolve at the pin
(`artifacts/probe/a2-ci.log`, scratch). As with A1, the only difference
between the gated tree and the committed tree is this paragraph.

### Slice 5 state

**Table delivered; two mini-slices landed; three things wait on Mike.**

| deliverable | state |
| --- | --- |
| the triage table (9 bugs + 138 reds, 45 groups, 3 categories, zero rows outside) | DONE — `docs/2026-08-19_triage-table.md` |
| category-(a) mini-slices executed | A1 (`1ca434b2`) and A2 (`357b7297`) — 6 reds retired, 12 new green ids, zero unpredicted drift at either gate |
| category-(a) queued frontend-only | A3-A6, mechanisms written, reasons logged |
| category-(a) GoCore-touching | 19 reds, ONE gate ask (§3.3 of the table) |
| category-(c) list | 7 rows argued fresh, awaiting user ratification |
| untriaged-25 cross-check | DONE — unchanged at 25/25, derivation recorded, ten missing justifications written |
| new finding | the len-vs-CALL forced-point divergence (§3.4) — corpus obligation, blocks A6 |

**Gate at the table-update commit.** Docs-only, so
`GOLEAN_MEM_MAX=24G scripts/ci` without `--diff` → **`RESULT: PASS`**,
exit 0, `baseline diff FULL (2179/2179, no regression)` from A2's own
`--diff` record (labelled stale by commit hash only — no runtime file
changed since), `spec-anchor citations resolve at the pin` (347 spec# +
75 mem#), `bug-index cross-check ok`, `eval tests (136 ok)`.

## §19-red — the GoCore-gated (a) reds (triage §3.3, user-approved batch 2026-08-19)

The ruled GoCore gate: ONE slice, SIX COMMITS, one per arm-family, in
the triage's order (L1 9, L2a 3, L3 3, L5+L6 2, L7 1, L10 1). Per
family: guardrails confirmed against `go run` + the spec anchor first;
the fix at the named arm with the flip set predicted in the commit
message pre-run; same-commit re-pin; full `scripts/ci --diff` between
families. TIER RULE (logged per family): families 1–5 are
conversions/indexing/floats — no choice-consumption site, enumerator,
or tier=slow row's program surface moves, so `--diff` carries them;
`--slow` runs at the batch end with family 6, whose arm lives in the
concurrent spawn path (`Multi.lean`) — the tiered rule's own case.

### Family 1 — rune↔string conversions (triage L1, 9 reds)

**Diagnosis confirmed before any change**: all 9 red at exactly the
diagnosed catch-all (`scripts/coverage run` on the 9 ids →
`unsupported "conversion to GoLean.GoCore.Ty.string"` /
`"…Ty.slice (…int32)"`, stage lean-observation, go side green).
**BUG-020-latitude check (the brief's special care)**: none of the 9
observes `cap()` of a `[]rune(s)` conversion — verified against each
case's source — so none is R3's capacity-latitude point; all 9 are
plain missing-arm defects. The 19-count stands.

**The fix**: two new strict ops over the EXISTING oracle-pinned
kernels — `runesFromString` (new total `runesOfString` offset-walk over
`decodeRuneAt`, U+FFFD per invalid byte; fresh backing array, the
`bytesFromString` shape, cap = len) and `stringFromRuneSlice`
(`sliceVisibleValues` + `GoString.fromCodePoint`, invalid code points →
U+FFFD). Frontend classifier routes both directions by UNDERLYING type
(`isRuneSlice`, `emit.go`), so defined slice/element/string types ride
through — exactly go/types' conversion rule. Full blast radius landed
same-commit: Syntax/Machine/Race/StateWf/NativeToIR + Frame (Rename,
StrictOps arms + dispatch), Sym (Mirror transcription, DriftApply
arms). Both builds green FIRST pass; the mirror transcribes both new
arms (rune payloads close via `D.toInt?`, the byte-loop treatment).

**JUDGMENT (family 1, the cap edge row)**: an edge row
`strings/rune-conversion-cap` (mirroring `byte-conversion-cap`, the
version-tracking pin the singleton would want) was written and RUN —
and found gc OUTSIDE the cap=len singleton on the small NON-escaping
shape: `cap([]rune("héllo")) = 32` (go1.26.5; the runtime's 32-rune
conversion buffer), machine 55 vs go 325. So the rune direction has NO
agreeing pin; shipping the row would be a deliberate permanent red in
the arc that exists to kill reds. Following R3's own precedent (the
escaping byte shape was measured red and deliberately not added), the
row was REMOVED and the measurement recorded instead: at the
`runesFromString` arm (a WIDER transfer caveat than the byte arm's)
and in latitude inventory R3 (new RUNE ARM paragraph). The re-envelope
obligation is R3's, covering both arms.

**Predicted flips (stated pre-run): the 9 L1 ids FAIL/lean-observation
→ PASS, nothing else.** Full run: cases=2181 pass=2068 fail=113 (was
2181, 2059/122); `scripts/coverage-baseline-diff` drift = exactly the
9, nothing else. Baseline re-pinned in this commit (header reason).
`baselines/untriaged-ids`: the 7 strings/* and 2 spec-examples entries
retired with flip notes (check 4b's departed-id rule). Backlog
25 → 16.

**Gate**: `GOLEAN_MEM_MAX=24G scripts/ci --diff` → **`RESULT: PASS`**,
exit 0 — core + proofs builds (Audit gate ok), eval tests (136 ok),
frontend unit tests ok, baseline diff FULL (2181/2181, no regression),
re-pin guard (0 PASS→non-PASS flips), negative baseline diff ok
(`/tmp/f1-ci.log`, scratch). Tier: `--diff` (rationale above).

### Family 2 — slice→array conversion panics (triage L2a, 3 reds)

**Diagnosis confirmed**: all 3 red at the same conversion catch-all
(focused run pre-fix: `unsupported "conversion to …Ty.pointer
(…Ty.array 4 …)"` etc.). Panic message probed at go1.26.5
(`artifacts/probe`-class scratch, recovered `.Error()`):
`runtime error: cannot convert slice with length L to array or pointer
to array with length N` — matches the rows' `expected_reason`.

**The fix**: two arms in `convertValueToTyFuel` (array target and
array-pointer target over a `.slice` operand): `len < N` → the gc-exact
panic, which fires before any element is touched (the arms read no
state); `len ≥ N` → the succeeding forms stay REFUSED per the triage's
own L2a/L2b split (`Loc` has no subarray-view constructor;
`slice-to-array/ok-forms` pins both succeeding forms red as the (b)
frontier row). **This is the kernel's FIRST panicking arm**, so the
frame layer's `convertValueToTy_noPanic` became false by design: it is
retired, replaced by `convertValueToTyFuel_panic_ren` (panic transfer —
the message embeds `len` and `N` only, both rename-invariant;
`renameValue` rewrites a slice's base alone) and a per-result-class
`arm_convert`. `_ren`/`_locSup` gained the elem-dispatch cells the new
arms opened. **JUDGMENT (mirror)**: `convertValueToTy'`'s catch-all
already quits Q11 at array-target cells — the mirror asserts nothing
there and the drift theorem holds without realignment (verified by the
green drift build, not assumed); the panic arms are NOT transcribed
because mirror panics are Q6 quits by convention.

**Predicted flips (pre-run): the 3 panic rows FAIL/lean-observation →
PASS; `ok-forms` stays FAIL/lean-observation (message changes, stage
does not — the baseline records result+stage only).** Full run:
2181 cases 2071/110 (was 2068/113); drift = exactly the 3. Baseline
re-pinned; untriaged-ids: 3 entries retired, ok-forms kept with its
L2b justification. Backlog 16 → 13.

**Gate**: `GOLEAN_MEM_MAX=24G scripts/ci --diff` → **`RESULT: PASS`**,
exit 0, baseline diff FULL (2181/2181), re-pin guard 0 flips, eval
tests 136 ok (`/tmp/f2-ci.log`, scratch). Tier: `--diff` (same
rationale as family 1).

### Family 3 — IEEE min/max over floats (triage L3, 3 reds)

**Diagnosis confirmed**: all 3 red at the diagnosed refusal
(`unsupported "min builtin over float operands"`,
Machine.lean minOf/maxOf guard). The cases themselves pin the whole
spec#Min_and_max special-case table (signed zero through `1/r`,
NaN-ness through `r != r`, ±Inf propagation) — written at P3 with
expectations from `go run`; no expectation edits, no edge gaps noted
(the table IS the edge enumeration; judgment: no rows added).

**The fix**: the float refusal becomes the IEEE fold. The selection is
factored into a PURE bits kernel `floatMinMaxBits` (Ops.lean) over the
existing softfloat `fcmp64`/`fcmp32`: NaN propagates (the NaN
OPERAND's bits — payloads unobservable in-language, R7's own scope
condition), an equal compare is identical bits or the ±0 pair and the
tie breaks by sign (`min` keeps the negative-signed operand), the
result is always ONE OF THE OPERANDS. `floatMinMax` wraps it with the
kind check; the fold in minOf/maxOf dispatches float-vs-ordered on the
existing `anyFloatOperand` guard (the design-note §9 reason — a
`valueLess` fold gets NaN silently wrong — is exactly why the fold
never touches `valueLess`). **Mirror realigned same-commit**: the
minOf/maxOf float branches transcribe the SAME `floatMinMaxBits`
kernel (bits concrete in the mirror; the shared-kernel factoring is
what makes `floatMinMax_conc` a two-line transport instead of an
if-tree walk). Frame: `floatMinMax_sim` (results rename-inert) + the
float-fold branches in arm_min/arm_max. StateWf: `floatMinMax_locSup`
(every ok result is a `.float`, loc-free) + the split bullets.
Inventory R7 updated (refusal lifted, the NaN-operand narrowing
recorded); §5's refusal list drops the min/max row.

**Predicted flips (pre-run): the 3 ids FAIL/lean-observation → PASS,
nothing else.** Full run: 2181 cases 2074/107 (was 2071/110); drift =
exactly the 3. Baseline re-pinned; untriaged-ids: 3 retired. Backlog
13 → 10.

**Gate**: `GOLEAN_MEM_MAX=24G scripts/ci --diff` → **`RESULT: PASS`**,
exit 0, baseline diff FULL (2181/2181), re-pin guard 0 flips
(`/tmp/f3-ci.log`, scratch). Tier: `--diff` (same rationale; the fold
is sequential-value machinery, no choice site or enumerator surface).

### Family 4 — pointer-to-array indexing (triage L5+L6, 2 reds)

**Diagnosis confirmed**: both red at the exact diagnosed stuck arm
(`stuck "expected array, slice, or string value for index access, got
GoValue.addr …"` / `… got GoValue.nil`). Expectations already
oracle-derived (`pointer-array` expects ok/13; `nil-array-index-panic`
expects gc's recoverable nil-deref panic); spec anchor
`spec#Index_expressions` ("for `a` of pointer to array type, `a[x]` is
shorthand for `(*a)[x]`") + `spec#Run_time_panics`. No edge gaps noted
in the triage row; judgment: none added — the write-position edges
(OOB, second-target ordering) are BUG-038's existing green cases.

**The fix**: `.indexGet` gains the two read-position siblings of
BUG-038's write-path arms: `.addr` loads the pointee and projects
(ARRAY pointee only — read position never carries a target's
base-cell address, which is why `indexTargetLoc`'s slice-pointee arm
is deliberately NOT mirrored; the narrower arm is the honest one) and
`.nil` raises gc's recoverable nil-pointer-dereference panic. Race
footprint: element-precise read `(false, .index base idx)` — gc
compiles `p[i]` to a single element load, and the loc shape matches
element STORES, keeping disjoint elements race-free. **Mirror
realigned same-commit** (the `.addr` transcription; `.nil` quits Q6,
the machine-panic convention); Frame `arm_indexGet` gains the
load+project and fixed-message panic cases; DriftApply's `indexGet`
gains the addr transport; StateWf the two bullets. BUG-038's entry
updated (its named deferred sibling is now fixed).

**Predicted flips (pre-run): the 2 ids FAIL/lean-observation → PASS,
nothing else.** Full run: 2181 cases 2076/105 (was 2074/107); drift =
exactly the 2. Baseline re-pinned; untriaged-ids: 2 retired. Backlog
10 → 8.

**Gate**: first run **FAIL — the check-4b ratchet caught my own
incomplete edit** (the two departed ids' comment block was rewritten
but their bare id lines stayed in the active list; the gate's
departed-id rule fired exactly as designed). Ids removed, re-run:
`GOLEAN_MEM_MAX=24G scripts/ci --diff` → **`RESULT: PASS`**, exit 0,
baseline diff FULL (2181/2181), re-pin guard 0 flips
(`/tmp/f4-ci2.log`, scratch; the failed first run `/tmp/f4-ci.log` —
its differential half was already green, the FAIL was the ledger
consistency check). Tier: `--diff` (same rationale).

### Family 5 — struct-tag pointer-conversion field access (triage L7, 1 red)

**Diagnosis confirmed**: red at the exact diagnosed check
(`stuck "expected struct main.tagPointerB, got struct main.tagPointerA"`
— the NOMINAL mint-tag comparison at field access). Expectation
oracle-derived (ok/110: the write through `b` is visible through `a` —
the conversion ALIASES); spec anchor: `spec#Conversions`' struct-tag
clause. No edge gaps noted; judgment: none added — the frontend's
tag-conversion F3 rows (`structs/tag-{nested,unnamed}-conversion`,
`spec-examples-decl/struct-tag-conversion`) already pin the adjacent
shapes as frontend-export refusals, and they did not move (verified in
the drift).

**The fix**: the three nominal checks (`fieldGet`, `loadLoc`/`storeLoc`
field arms) relax to tag-CONVERTIBLE — `structTagCompatible` (new, in
Ops.lean): identical underlying struct types decided by wire
`FieldDef`-list equality, the SAME identity rule the struct
VALUE-conversion arm uses (the wire strips tags per the spec's clause;
embeddedness compared, F20-exact). The cell KEEPS its mint tag — the
conversion aliases, never retags. Two Go-facts make the relaxation
exact rather than a widening: two structs with equal FieldDef lists
are identical-underlying, which is precisely Go's convertibility rule;
and unknown TypeIds answer false, so nothing fails open. SEMANTIC
COUPLING recorded: `loadLoc` now reads `state.types` (the check), so
`loadLoc_root_congr` gained a `types`-equality hypothesis
(`structTagCompatible_congr`; its one external caller NPDRF's read
mover supplies `(storeLoc_shape h).1` — types are store-invariant).
Frame sims rewrite the framed check via `types_eq`; drift proofs
reduce the compound condition from the mirror's simple-mismatch quit
(the mirror still QUITS on any mismatch — it asserts nothing there,
and `State D` carries no types map to transcribe the check against;
recorded as a mirror-coverage note, drift theorem green).

**Predicted flips (pre-run): the 1 id FAIL/lean-observation → PASS,
nothing else.** Full run: 2181 cases 2077/104 (was 2076/105); drift =
exactly the 1 — the relaxation admits nothing else the corpus
exercises. Baseline re-pinned; untriaged-ids: 1 retired. Backlog
8 → 7, and the COUNT ceiling ratcheted down 25 → 7 in this commit
(the check's advisory; the batch's whole movement recorded in
`baselines/untriaged-count`).

**Gate**: `GOLEAN_MEM_MAX=24G scripts/ci --diff` → **`RESULT: PASS`**,
exit 0, baseline diff FULL (2181/2181), re-pin guard 0 flips,
bug-index cross-check ok at the new ceiling (`/tmp/f5-ci.log`,
scratch). Tier: `--diff` (same rationale).
