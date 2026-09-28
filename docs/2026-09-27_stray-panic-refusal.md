# Stray-panic refusal (packet A audit F1), 2026-09-27
[AGENT worker, lane `core/stray-panic-refusal-0927`; TRUST-SURFACE #1]. Disposition: the [AGENT] coordinator's
(audit F1, disclosed at the merge ask), under fail-closed. Investigation: `docs/2026-09-27_stray-panic-investigation.md`
(`records/stray-panic-investigation-0927` @ `b5d57d09`). Runtime commit `9862be1c`.

## The six sites

A Go panic from `loadLoc`'s `.index` arm (`arrayGet`, out of range) escaped `stepFn` with no `toResult`: a
`.terminal (.panic …)` WITHOUT unwinding (no defers, no `recover`), which the drivers report as an ordinary Go
panic abort — a wrong answer, not a refusal. S1 `stepFrameExit`'s targetless readout (`loadMany`), S2 its target
readout (`loadResults`), S3 `unseqStorePlan`'s binder values, S4 `unseqAtom .var` (via `unseqTargetPlan`), S5
`unseqGuard`'s test binder, S6 the `.var` read (`Mem.loadFor`; the audit's witness). Each reads a binding, a
pinned result cell or an unseq binder cell — always a fresh ROOT cell (`LocalEnv.declare`'s four callers bind
`Store.alloc`'s `.base`), so no lowered program reaches them. Writes already refused a formed out-of-range index
as `.internal`; reads did not.

## The fix

One root-only reader, `loadRoot` (`Ops.lean`, beside `loadLoc`): on `.base` it IS `loadLoc`; on a field/index
path it throws `.internal "binding cell is not a root location: <loc> (a variable, pinned result or unseq binder
cell is always a fresh root cell; machine invariant breached)"`. Emitting twins `Mem.loadBinding` (of `Mem.load`)
and `Mem.loadBindingFor` (of `Mem.loadFor`). Uses: S1 calls `loadResults` (discarded; on roots still the old
`stuck` refusal after the read); S2 `loadResults`, S4 `unseqAtom`, S5 `unseqGuard` use `Mem.loadBinding`; S3
`unseqStorePlan` uses `loadRoot`; S6 uses `Mem.loadBindingFor`. Relation, same commit: `Step.evalVar`'s premise is
`Mem.loadBindingFor … = .ok`; `frameReturnTargets`/`frameFallTargets`, `unseqComplete`, `unseqRunTarget`,
`unseqRunGuard` follow the shared helpers. Bridge lemmas `loadRoot_ok`,
`loadBinding_ok`, `loadBindingFor_ok` repair the four `StateWf.lean` consumers; `stepFn_sound`, `step_complete`
and every coherence module build otherwise untouched. No `sorry`/axiom/`native_decide`/`partial`.
`check-mem-callsites`: `loadRoot` joins the RAW ops (a strengthening); rows re-derived (+`loadRoot`, `Mem.loadBinding(For)`, `unseqStorePlan`; −`stepFrameExit`'s `loadMany`).

## Why a refusal, not a panic

A non-root binding breaches a machine invariant, not a Go behaviour; an unwound Go panic there is a wrong answer.
Read-side twin of `runCommit`'s commit-phase panic → named `.internal` (and the write path's formed-index
refusal); `Finish`'s refusal case covers it, so audit F1's statements need no new constructor for these sites.

## Controls (`Tests/GoCoreEval.lean`, `strayPanicRefusalFacts`; `#eval`ed first)

Negative: the audit witness (`x` ↦ `.index (.base 0) 5`, zero-length array) now yields `.error (.refusal
(.internal …))`, not `.terminal (.panic …)`; likewise non-root cells at S1, S2 (via `stepFn`) and S3, S4, S5 (the
helpers). Positive: the ordinary variable read and the frame-exit readout (values AND access labels), S1's old
`stuck` refusal on a root, the S3/S4 root reads. 11 facts, all `ok`.

## Gate (`docs/evidence/2026-09-27_stray-panic-refusal/`)

`lake build`, `lake build GoLean`, `check-core-audit`, `check-mem-callsites`, `check-unseq-scheduler`,
`check-wire-boundary`, `check-unseq-wire`, eval tests (285 ok): all EXIT=0. `GOLEAN_MEM_MAX=48G scripts/capped
scripts/ci --diff` at `9862be1c` under the box-wide lock: EXIT=1, 806 s, red on EXACTLY the 5a pair —
`certificate provenance` (STALE: changed dependency `Machine.lean`) and the one drift line
`imported-goose/channel/google-search PASS→FAIL/membership` (the same stale-certificate cause) over 3768 rows. NO
other baseline row moved; negative baseline: no regression. No candidate installed.

**No BUGS entry:** no reachable wrong answer (no lowered program binds a non-root location — the investigation's
Q2 and probe; the `--diff` moved no row). This is fail-closed hardening of an unreachable configuration.

## Changelog line (for the coordinator to merge into packet A's changelog)

- 2026-09-27 core/stray-panic-refusal-0927: root-only reader `loadRoot` (+ `Mem.loadBinding`/`loadBindingFor`) at
  the six binding-cell reads; a non-root location refuses as `.internal «binding cell is not a root location»`
  instead of escaping `stepFn` as an unwound Go panic (audit F1); `Step.evalVar`'s premise follows; no row moved.

## Merge train r51 — the 5a record ([AGENT] coordinator, 2026-09-28)

Landed with the prompt-audit edits and packet A ([USER] Mike 2026-09-28 «great, go ahead with both», relayed; rulings ledger
«Train r51»). Pre-merge main `7d2a62e5` → `refs/snapshots/r51/main`; train tip `50b446ce` fast-forwarded. Under the lock:
`scripts/build-certified` EXIT=0 (binary `c9f5822a…`); `release-check` EXIT=2 (EXPECTED — «STALE certification: changed
dependency build/files/GoLean.lean»); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1, 892 s — red on EXACTLY
the 5a pair (`certificate provenance`; the one drift line `imported-goose/channel/google-search PASS→FAIL/membership`); 3768
rows run, 3531 PASS / 237 FAIL = the pin 3532 / 236 with the one 5a-class row red; no other drift. Tail:
`docs/evidence/2026-09-27_stray-panic-refusal/r51-ci-slow.tail.txt`. Candidate vs tracked record: `claim` and
`observations_sha256` IDENTICAL; inputs differ in seven compiled modules (`GoLean.lean`, `BridgeSet`, `ExecutionStatement`,
`Machine`, `Ops`, `StateWf`, `StepFn`) and the two call-site inventory files, plus the receipt (`50b446ce`, 134.868 s) —
INSTALLED in this commit; a provenance refresh, not a re-pin.
