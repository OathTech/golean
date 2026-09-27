# Stray-panic investigation (packet A audit F1 follow-up), 2026-09-27

[AGENT stray-panic investigator], a read-only investigation at main `7d2a62e5`. It follows up F1 of
`docs/2026-09-27_packet-a-audit.md` (branch `review/packet-a-contract-0927` @ `e750e13c`). Witnesses:
`docs/evidence/2026-09-27_stray-panic-investigation/` (`probe.go`, `results.txt`). No builds, no gates.

## How a Go panic is supposed to leave `stepFn`

A helper's recoverable panic is `Stop.panic` (`Value.lean:255`). At each apply/entry site it is classified by
`toResult` (`Value.lean:394`). Then `deliverS`/`deliverV` (`StepFn.lean:74`, `:117`) turn it into
`.ok (.panicking …)`, which unwinds: defers run and `recover` can catch it. `enterFramePickV` classifies its entry
panic internally (`Machine.lean:921-929`). A panic from a commit phase goes through `runCommit`
(`Machine.lean:285`) and becomes the named `.internal` refusal. There are three designed terminal throws. The abort
`throw (.panic …)` fires only at `Config.abort?` (`StepFn.lean:386`). The blocked shapes throw `.deadlock`
(`:939-950`). `.fatal` passes through `toResult` on purpose (Finish.fatal). All three are by design and outside
this census.

## Q1: census of stray-panic sites (6 sites, one root cause)

I checked every un-`toResult`ed `←` bind in `stepFn` and its three sub-steppers for whether the callee can raise
`Stop.panic`. Every bind that can reaches it the same way: `loadLoc`'s `.index` arm → `arrayGet`
(`Ops.lean:1376-1378`, `:317`). The `.base` arm has no panic, only `stuck` refusals.

| # | site | operation | Loc read | converted? |
|---|------|-----------|----------|------------|
| S1 | `StepFn.lean:160` | `loadMany` (targetless frame exit with results) | pinned result cells | NO |
| S2 | `StepFn.lean:164` | `loadResults` → `Mem.load` (`Machine.lean:782`) | pinned result cells | NO |
| S3 | `StepFn.lean:242` | `unseqStorePlan` → `loadLoc` (`Machine.lean:2137`) | unseq binder cells | NO |
| S4 | `StepFn.lean:278` | `unseqTargetPlan` → `unseqAtom .var` → `Mem.load` (`Machine.lean:1980`) | env binding | NO |
| S5 | `StepFn.lean:282` | `unseqGuard` → `Mem.load` (`Machine.lean:2117`) | unseq binder cell | NO |
| S6 | `StepFn.lean:580` | `.var` read → `Mem.loadFor` → `loadLoc` | env binding | NO (audit F1's witness) |

These binds were checked and CANNOT raise `Stop.panic`:
- `enterFramePickV` (`:172 :339 :454 :650 :673 :694`): converts internally.
- `allocDecls`/`defaultValue`/`Store.alloc`/`bindIterVars` (`:200 :396 :402 :403 :894`): the normalizer and
  zero-value descent have no panic constructor (`Ops.lean:1160-1245`, `:2141-2192`).
- `Mem.store` (`:316`, and inside `unseqGuard`): `storeLoc` → `writeAt` refuses an out-of-range formed index as
  `.internal` (`arrayIndexNatFormed`, `Ops.lean:1525`). The WRITE path is already fail-closed and the READ path
  is not. That asymmetry is the defect.
- `valueAsBool` (`:624-640`), `mapRangeStartSets` (`:723`), `mapIterCandidates` (`:880`), `unseqCellLoc`
  (`:315`): stuck-only.
- `abortMsg` (`:386`): runs at the abort itself.

The pool calls `stepFn` directly (`Multi.lean:1579`). The drivers treat any `stepFn` `.error (.panic m)` as the
abort (e.g. `CLI.lean` `enumInitRun`). So if a stray were reached, it would be REPORTED as an ordinary Go panic
abort: status `panic`, with no defers run and no recover. That would be a wrong answer, not a refusal.

## Q2: reachability from real programs: NO (unreachable by construction)

All six sites read a Loc that came from a `LocalEnv` binding, a pinned result location (`pinResultLocs` reads the
env), or an unseq binder cell (`allocDecls` at unseq ENTER, `StepFn.lean:200`). The env is extended ONLY by
`LocalEnv.declare` (`State.lean:115`). That has exactly four executable callers: `allocDecls` (`Machine.lean:747`),
`bindParams` (`:757`), `.initialization` (`StepFn.lean:404`) and `bindIterVars` (`Machine.lean:1801`, `:1807`).
Each one binds the Loc just returned by `Store.alloc` → `Store.allocCell`, which is always
`.base ⟨heap.size⟩` (`Store.lean:36`). The wire carries no `Loc`: `NativeToIR.lean` emits only `Expr`s and
`Param`s, and globals are `.global gid` → `.addr (.base gid)` values, never bindings. Every program entry
(`runProgramSetupM`, the CLI mirrors, pool `spawnStep` via `enterFramePickV` → `bindParams`) starts from `[]`
and extends only through those callers. So on every reachable configuration, every env/result/binder Loc is
`.base`. `loadLoc (.base _)` cannot panic, and none of S1-S6 can fire.

What real programs do instead: `&a[i]`, element addresses in a range body, and receivers on element addresses all
produce an `.addr loc` VALUE. That value is stored in a fresh root cell and read back through the strict
deref/index applies (`StepFn.lean:611`, `:621`, under `toResult`). Those applies convert. Probe
(`probe.go`: `a[i]` on `[0]int`, `p := &a[i]; *p`, `q.xs[i]` through a pointer, `&a[i]` in a range body, each
with `defer`/`recover`): `go run` prints `100 200 300 6`. The machine gives `status ok, [100,200,300,6]`
(`results.txt`), which agrees. The ordinary panic path unwinds, runs defers and recovers. There is no wrong
answer on main.

## Q3: recommendation: (b), convert into a named `.internal` refusal [AGENT]

The class is unreachable by construction, so (c) does not apply: no fidelity bug, no BUGS entry, no red-first
row. (a) alone would make the four statements true by classifying a configuration that the machine answers
WRONGLY (a Go panic with no unwind). That writes the fail-open into the contract. The model is (b), `runCommit`'s
twin: a panic from these reads is a machine-invariant breach and must refuse BY NAME.

Preferred shape [AGENT, PENDING coordinator/[USER] choice]: fix it once, at the root of the class. Add a
root-only reader, e.g. `Mem.loadVar`: on `.base` it is `Mem.load`/`loadFor`; on a field/index path it throws
`.internal "variable/result/binder cell bound to a non-root location …"`. Use it at S1-S6 (for S4, S5, S3 in
their `Machine.lean` helpers). The relation's `Step` rules share these helpers, so the relation changes in the
same commit (merge invariant); the relation already has no successor there. Alternative: per-site
`toResult` + `.panic → .internal` wraps. That also works, but it is six copies of the same guard.

A proof-side complement (optional): an `EnvRoots` clause (every binding is `.base`) in `MachineWf`, which rules
out the F1 witness. Neither `StateWf` nor `MachineWf` excludes it today (audit F1). With (b) in place, the
classification statements hold without that clause: the stray becomes an `.internal` refusal, which the refusal
case already covers. Runtime-code change → `scripts/ci --diff`. No baseline row should move (the probe and the
argument above say the sites are dead on the corpus).
