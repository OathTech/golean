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
passed through unwrapped (`panic(recover())` must not double-wrap). A
delivered `.nil` (untyped `panic(nil)` or a nil interface at runtime)
becomes the distinguished nil-panic payload. Runtime panics (the 12
existing `.panicked` rule sites) carry `.interface "runtime.Error"
(.string msg)` — the dot-carrying dynamic name cannot collide with a
source-level `TypeId`.

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

## Standing session facts (for the fresh context)

`main` @ 234301e pushed except the binary-cleanup commit (ask user or
check `git log origin/main..main`). Corpus 772 cases / 333 passing.
Untriaged ceiling 64. BUGS: BUG-002 open (R4), BUG-003 open (loop vars).
The 8 pre-existing differential-stage wrong answers
(strings/variadic/interface classes) remain the triage backlog's fixed
point. Practices: CLAUDE.md is current (merge protocol; per-rung edge
batches; audit dimensions with semantics primary; reference checkouts in
`../deps/`).
