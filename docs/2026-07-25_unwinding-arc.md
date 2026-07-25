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

## Standing session facts (for the fresh context)

`main` @ 234301e pushed except the binary-cleanup commit (ask user or
check `git log origin/main..main`). Corpus 772 cases / 333 passing.
Untriaged ceiling 64. BUGS: BUG-002 open (R4), BUG-003 open (loop vars).
The 8 pre-existing differential-stage wrong answers
(strings/variadic/interface classes) remain the triage backlog's fixed
point. Practices: CLAUDE.md is current (merge protocol; per-rung edge
batches; audit dimensions with semantics primary; reference checkouts in
`../deps/`).
