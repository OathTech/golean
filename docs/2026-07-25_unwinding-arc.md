# The unwinding arc (W3 slice 2): panic-as-configuration + recover

Arc plan of record, fixed with the user 2026-07-25 (session end, pre-compact).
Starts from `main` @ 234301e (seq-coverage-scoping merged @ e2df353 + binary
cleanup). Design substrate: scoping note §9 (defer-in-frame, IMPLEMENTED) and
§10 (recover design, verbatim below in scope item 1); BUG-003 and the owed
proof-corpus entries are explicitly OUT.

Working name: **the unwinding arc**. It completes the W-ladder's one
outstanding machine-design item and retires panic-as-teleport, which §3.3
has quarantined since the ladder was scoped.

## Why all-or-nothing (§10's argument, restated)

The cheap half — `recover()` returns nil when not panicking — is exactly
true of today's machine, but shipping it alone would turn
`defer/defer-nil-function-recover-order` from a fail-closed frontend
rejection into a WRONG ANSWER (we would report a panic where Go returns 42).
Fail-closed-always forbids that. Recover lands whole or not at all.

## In scope

1. **`Config.panicking (value) (k)`** — panic becomes an UNWINDING
   configuration. All ~8 panic-producing rule sites (strict-apply panics,
   assignTargetPanic, assignStorePanic, call/value-call nil-callee panics,
   stmtOp panics, the defer-drain nil panic) carry their continuation
   instead of producing terminal `.panicked`. Unwinding rules mirror the
   `breaking`/`returning` families through `seq`/`loop`/`breakableK`/
   `mapIterK`. **`.panicking v .stop → .panicked` keeps NO outgoing rule**
   — the load-bearing detail: `Progress`'s STATEMENT is unchanged and its
   meaning sharpens from "no panics" to "no UNRECOVERED panics".

2. **Defers run on the panic path.**
   `.panicking v (.frame t r ((callee,args) :: ds) k)` enters the deferred
   call with continuation
   `.frame [] [] [] (.panicResumeK v (.frame t r ds k))`, and
   `.next (.panicResumeK v k) → .panicking v k`. Empty chain:
   `.panicking v (.frame _ _ [] k) → .panicking v k` — results NOT read
   (the call did not return). This closes the recorded divergence (defers
   skipped on panic — unobservable only while panic is terminal, an excuse
   that dies the moment recover exists; that is why they land together).

3. **The `panic` builtin** — in scope because recover without it covers
   only runtime panics. `panic(v)` for string/int/bool values, FAIL CLOSED
   on other value types. The panic VALUE is what recover returns; message
   rendering must match `go run`'s output per the fault-identity charter
   (`docs/2026-07-22_fault-model.md`).

4. **`recover()`** — a continuation-walk step implementing Go's
   called-directly-by-a-deferred-function rule: from the recover call's
   continuation, if crossing exactly ONE `.frame` lands on a
   `.panicResumeK v k'`, return `v` and REBUILD the continuation with the
   marker removed (cancelling the unwind); anything else returns nil.
   Frontend: emit the `recover` builtin (currently `unsupported`).

5. **Honesty, same commits**: #24's docstring (panicked-counts-as-stuck),
   the `Progress` reading, and §3.3's panic-as-teleport prohibition
   formally RETIRED (the construct ceases to exist).

6. **Validation ritual** (unchanged doctrine): guardrails first — the red
   recover cases (`defer/recover-normal-return`,
   `defer/defer-nil-function-recover-order`,
   `defer/defer-arg-panic-before-register`, `panic-recover/*`) become the
   flips; edge batch aimed at the interactions (recover OUTSIDE a defer →
   nil; recover in a function CALLED BY the deferred function → nil; panic
   DURING a deferred call while already panicking — the new value replaces
   the old; re-panic idiom `panic(recover())`; panic in defer ARGS before
   registration); eval tests for machine-level pins; zero-drift + flips
   enumerated per re-pin; MachineSound tags via STASH-ENUMERATE-RESTORE
   (stash handlers → build → parse unsolved-goal tags+shapes from the
   error output → restore with the mapping — never hand-count).

## Out of scope, explicitly

- **BUG-003** (for-clause per-iteration loop variables) — loop machinery,
  not unwinding; own arc. Its red pins stay red.
- **Interfaces lane / type switches** — biggest backlog block, separable.
- **Builtins family** (append/copy/delete/new).
- **Owed proof-corpus entries** (closures/switch/defer at GoFuncSpec —
  `docs/2026-07-24_proof-corpus.md` §5): real proof-layer work, own arc;
  the manifest explicitly allows rungs not to block on them.
- **Goroutines (R4)** — though this arc is a PREREQUISITE: unwinding must
  be per-goroutine-correct (it lives in the continuation, which is already
  per-goroutine by construction) before interleaving exists.

## Exit criteria

- Every defer/recover-tagged corpus case either PASSES or fails closed on
  a DIFFERENT named feature (e.g. interfaces).
- Gate 12/12; baseline re-pinned with flips enumerated; untriaged ceiling
  moves only DOWN or with per-case justification.
- This doc gains a build log; §3.3 and #24 are updated in the same commits
  as the machinery.
- Pre-merge audit ask (semantics primary — the unwinding rules and the
  recover walk are new trust surface), then user merge sign-off.

## Design addendum (2026-07-25, pre-implementation): the panic CHAIN

Written after re-deriving the design against the differential's actual
fault-identity contract and fresh oracle probes (Go 1.26.4). Three findings
refine §10's single-value sketch; all are oracle-pinned, none contradict
the plan's structure.

### A1. Fault identity pins the FIRST panic line — so `panicking` carries a chain

The harness does not recover: an aborting case emits Go's raw runtime
output, and `scripts/diff-coverage` extracts the **first** `^panic: ` line
as the observation message (continuation lines are tab-indented and do not
match). Go prints the goroutine's whole panic chain, oldest first, with
`[recovered]` marking entries that were recovered when a later panic
superseded them. Oracle:

- panic during a deferred call of an unrecovered panic:
  `panic: first` ⏎ `\tpanic: second` → observed message **`first`**
  (this is what `panic-recover/deferred-panic-replaces` will compare;
  its manifest `expected_reason` "second" is only a substring check
  against Go's full output).
- recover then re-panic inside the same deferred call:
  `panic: inner [recovered]` ⏎ `\tpanic: wrapped` → observed message
  **`inner [recovered]`** (`panic-recover/recover-repanic`).

A single-value `panicking v k` cannot produce either message. Therefore:

```
structure PanicEntry where
  value : GoValue      -- what recover returns (interface-wrapped, A2)
  recovered : Bool
Config.panicking (chain : List PanicEntry) (k : Cont)   -- oldest first
```

Rules (mirror shapes of `breaking`/`returning`, plus the marker):

- statement frames (`seq`/`loop`/`breakableK`/`mapIterK`) and all
  expression frames: strip, chain unchanged. (Expression frames too:
  a panic can surface mid-expression; `breaking` never could.)
- `panicking chain (.frame t r [] k) → panicking chain k` — no result
  read (the call did not return).
- `panicking chain (.frame t r (d::ds) k)` → enter the deferred call `d`
  with continuation `.frame [] [] [] (.panicResumeK chain (.frame t r ds k))`
  — the chain moves INTO the marker while the deferred call runs.
- `next (.panicResumeK chain k)` — the deferred call completed:
  - newest entry recovered → **`next k`**: the whole chain is discarded
    and the frame resumes its NORMAL exit path (drain remaining defers,
    then read pinned results — named results preserved, unnamed results
    stay at their defaults; Go's "the surrounding function returns
    normally").
  - newest entry not recovered → `panicking chain k` (unwinding resumes).
- `panicking newChain (.panicResumeK oldChain k) → panicking (oldChain ++
  newChain) k` — a NEW panic during a panic-path deferred call merges
  behind the suspended chain. This one rule produces both oracle
  renderings above.
- `panicking chain .stop → panicked (render chain.head)` — terminal;
  rendering below. `.panicked` stays terminal with no outgoing rule, so
  `Progress`'s statement is unchanged and its reading sharpens to "no
  UNRECOVERED panics" exactly as §1 promised.

`recover()` (own `Expr` constructor; needs the continuation): walk the
continuation crossing expression/statement frames; stop at the FIRST
`.frame`; if the continuation directly under it is `.panicResumeK chain k'`
with newest entry not yet recovered → return newest `.value` and rebuild
the continuation with that entry marked recovered; anything else → `.nil`.
One deterministic function, so `step_det` sees a function-premise rule.
This yields Go's called-directly-by-a-deferred-function rule (a nested
call's walk stops at the nested frame → nil; a normal-path drain has a
plain `.frame` under the inner frame, not a marker → nil —
`defer/recover-normal-return`), and marks-once (`recover-twice`: second
call sees recovered=true → nil).

### A2. Panic payloads are interface values (typed nil must recover non-nil)

`panic-recover/panic-typed-nil-recover` panics a nil `*T` and requires
`recover() != nil` to be TRUE (non-nil interface holding a nil pointer)
and `r.(*T)` to yield nil. A raw `.nil` payload gives the wrong answer at
the first check — silently. So `panic(e)` wraps its argument exactly as Go
converts to `any`: the frontend emits the static type; lowering builds
`.toInterface` over the existing machinery (`dynamicTypeName?` already
covers string/int/bool/pointer-to-defined — precisely the in-scope payload
types, failing closed elsewhere). An argument already of interface type is
passed through unwrapped (`panic(recover())` must not double-wrap). Runtime
panics (the 12 existing `.panicked` rule sites) carry `.interface
"runtime.Error" (.string msg)` — the dot-carrying dynamic name cannot
collide with a source-level `TypeId`.

**`panic(nil)` correction (found by the differential, first pipeline
run):** the oracle runs `go run` in GOPATH mode (no `go.mod`), where
`panic(nil)` keeps its LEGACY semantics — `recover()` returns **nil**
(`panic-recover/panic-nil-recover`, Go answer 0) and the abort line is
`panic: nil` — the "nil" rendering probed in §A3 is the legacy nil
payload, not a `*runtime.PanicNilError`. The machine models the oracle:
`panicPayload` is the identity, a `.nil` chain-entry payload renders
`nil`. Go 1.21's PanicNilError applies only under a module declaring
go ≥ 1.21; if the harness ever moves to module mode, `panicPayload` is
the knob and these two cases are the tripwire (they will flip loudly).
The in-file comment in `panic-nil-recover/main.go` claiming the 1.21
behavior predates this finding — the oracle, not the comment, is the
record.

**Superseded (arc-final audit F21, 2026-08-06):** the knob was turned,
in the MODERN direction. The audit judged the GOPATH-mode agreement an
agree-by-config-coincidence the differential structurally cannot see
(the north star's go.mod declares go 1.26, where the answer flips), and
`GODEBUG=panicnil=0` turns on the modern behavior in GOPATH mode
without touching module mode or anything else (probe-verified;
loop-variable semantics are language-version-driven and already modern
in GOPATH mode, BUG-003). So: `panicPayload` now maps a nil payload to
the `*runtime.PanicNilError` runtime error ("panic called with nil
argument"), every oracle `go run` sets `GODEBUG=panicnil=0`
(`scripts/diff-coverage` `go_run_oracle`), and the two tripwire cases
were re-pinned to the modern answers (`panic-nil-recover` → 1,
`panic-nil-abort` → "panic called with nil argument").
`panic-typed-nil-recover` (this section's own shape) is unaffected — a
typed nil is a non-nil interface either way.

Existing machinery this leans on, verified: `normalizeValueForTy` passes
any value through interface-typed cells (`r := recover()` stores fine);
`valueEq` at interface types discriminates exactly nil vs non-nil (what
the corpus compares); `typeAssertValue` unwraps `.interface dyn inner` by
dynamic-name match.

### A3. Oracle pins (Go 1.26.4, probes 2026-07-25)

- `defer recover()` does **not** recover (`panic: boom`, exit 2) — recover
  invoked AS the deferred function is not "called by" one. Lowering: a
  deferred no-op (synthetic empty function), pinned by
  `panic-recover/defer-recover-builtin` (expected: panic, reason boom).
- Abort renderings: `panic("s")` → `s`; `panic(4)` → `4`; `panic(true)` →
  `true`; `panic(nil)` → **`nil`** (Go 1.26 prints the PanicNilError as
  `nil`); runtime-error payloads → their message (unchanged from today).
- Typed nil pointer aborting: `panic: (*main.T) 0x0` — package-qualified;
  our dynamic names are not. Rendering a pointer payload at ABORT fails
  closed (unsupported) rather than approximating; recovering one works
  (A2). No corpus case aborts with a pointer payload; if one is ever
  added it must first decide the package-qualification story.
- Chain rendering: first line only, ` [recovered]` suffix from the
  entry's flag; deeper lines never observed by the harness.
- **`[recovered, repanicked]` (probe 2026-07-25) — CORRECTED by the
  pre-merge audit:** the collapse is decided by eface IDENTITY (bitwise
  type-word + data-pointer compare in `preprintpanics`), NOT semantic
  equality. The original probe was constant-folded: `"or"+"ig"` is one
  static eface, so it collapsed; `mk("or","ig")` computed at runtime does
  not (verified: Go prints `[recovered]` + a chained second line). The
  shipped rule (BUG-004): structurally UNEQUAL payloads render
  ` [recovered]` (identity implies equality, so this direction is
  certain); structurally EQUAL payloads are undecidable without an
  allocation-identity model — fail closed.
  `panic-recover/repanic-same-value-abort` flipped PASS→FAIL
  (intentional, listed in BUG-004) and `panic-recover/recover-repanic`
  (unequal values) stays green.
- Edge-batch value pins (same probe session): recover-in-defer-args of a
  nested defer INSIDE a panic-run deferred function DOES recover (arg
  evaluation is a direct call by that deferred function) → 32;
  loop-registered defers: only the first-drained (last-registered)
  recovers, the rest see nil → 312010; defer-args recover on the normal
  path → nil at registration → 5.

## Build log

- **2026-07-25, design addendum** (`e94b49a`): §A1–A3 — chain refinement,
  fault-identity first-line contract, oracle probes (Go 1.26.4).
- **2026-07-25, guardrails**: 9 new edge-batch cases (recover outside
  defer / store-local / in-defer-args ×2 / loop-defer;
  repanic-same-value-abort; panic-int/bool/nil-abort), all
  oracle-validated at add time; predictions 32 / 312010 / 5 confirmed.
- **2026-07-25, machine slice** (`5197aad`): the full §A1 rule set;
  MachineSound via stash-enumerate-restore (23 renumbered + 3 new
  handlers; `step_complete` gains `panicUnwind`; `step_det` simp set
  extended). **Constructive-pin incident:** core's `String.fromUTF8?`
  depends on `Classical.choice` and tainted `stepFn.fun_cases` — caught
  by the Audit axiom gate, fixed with a constructive ASCII decoder that
  fails closed on non-ASCII abort payloads. Eval tests +3 machine pins.
- **2026-07-25, frontend+decoder slice**: `panic`/`recover` wire nodes;
  `defer recover()` no-op lowering; IIFE call targets (unblocks
  `recover-indirect`'s two-frame walk pin); recover node carries its
  interface type (the untyped discard-cell fallback had typed it `int` —
  caught by `unnamed-recover-zero-return` going stuck).
  **Differential-caught design correction:** `panic(nil)` is LEGACY in
  the GOPATH-mode oracle (§A2 correction above) — the machine's
  PanicNilError mapping was a wrong answer against `panic-nil-recover`
  and was removed; `panicPayload` is the identity.
- Suite state after the slices: `panic-recover` 28/30 (2 red on
  interfaces-lane constructs: type assertion, type switch); `defer`
  14/15 (1 red on interface method values). Exit criterion "passes or
  fails closed on a DIFFERENT named feature" holds.
- **2026-07-25, PRE-MERGE AUDIT (user-approved full scale: 3 Opus
  reviewers + 2 refute-by-default Opus verifiers per finding, 29
  agents): 7 sustained (4 distinct defects — both semantics dimensions
  independently found the top two), 6 refuted.** All four fixed on the
  branch as BUG-004 (see docs/BUGS.md): (1) HIGH — the
  `[recovered, repanicked]` collapse is eface IDENTITY, not semantic
  equality (§A3 correction above; equal-payload case now fails closed;
  `repanic-same-value-abort` intentionally PASS→FAIL); (2) HIGH —
  defined-type payloads rendered bare (`panic(Code(7))` printed `7`, Go
  prints `main.Code(7)`); root cause is the alias lowering erasing the
  defined-type identity — frontend now fails closed at emit, machine
  name-checks as defense in depth (`panic-named-type-abort` red pin);
  (3) MEDIUM — multi-line string payloads have no one-line rendering
  (`asciiString?` rejects `\n`; `panic-newline-abort` red pin);
  (4) MEDIUM — stale PanicNilError comment at the emit.go lowering site
  (the exact knob §A2 warns about) corrected. The audit's verifiers
  compiled probes both ways; the two silent-wrong-answer HIGHs are again
  the unexercised-paths class no green gate can see.
- **2026-07-25, re-pin + honesty** (`d4c670a`, `175a806`, `7c99172`):
  panic(nil) legacy correction; baseline 772/333 → **781/368** — 26
  FAIL→PASS flips + 9 new PASSes, zero regressions, every flip
  enumerated in the baseline header; untriaged ceiling unchanged at 64
  (the flips were frontend-export gaps, not fidelity failures); #24
  sharpened, adequacy scope reworded, §3.3 retired. Gate 12/12 at the
  tip (the recorded full run predates the doc-only commits; runtime
  code identical). Awaiting the pre-merge audit ask.

## Standing session facts (for the fresh context)

`main` @ 234301e pushed except the binary-cleanup commit (ask user or
check `git log origin/main..main`). Corpus 772 cases / 333 passing.
Untriaged ceiling 64. BUGS: BUG-002 open (R4), BUG-003 open (loop vars).
The 8 pre-existing differential-stage wrong answers
(strings/variadic/interface classes) remain the triage backlog's fixed
point. Practices: CLAUDE.md is current (merge protocol; per-rung edge
batches; audit dimensions with semantics primary; reference checkouts in
`../deps/`).
