# Reproducing I1 integration checks

Use a separate worktree at the implementation pin named in the
[integration stage](2026-10-15_relational-integration-stage.md). Inputs and old
audited pins are preserved there; never build in a peer worktree. Lean remains
4.32.2 and Go 1.26.5. All temporary state stays under this worktree.

## Current-main gates

```sh
mkdir -p .tmp/i1
export TMPDIR="$PWD/.tmp"
export LEAN_NUM_THREADS=2
export GOTOOLCHAIN=local GOPROXY=off GOTELEMETRY=off GOENV=off
export GOPATH="$PWD/.tmp/gopath" GOMODCACHE="$PWD/.tmp/gomodcache"
scripts/setup-deps --from /home/mike/projects/golean --only goose,go
capped -m 64G -- scripts/ci --diff
```

The deliberate cold-build cap is the documented 64 GB case. CI includes the
current-main exact GoLean kernel replay, exhaustive core axiom audit, frontend
checks and fresh positive/negative differential corpora. It retains the
current-main baselines and all failures. The retired equation API/check is
not restored. No toolchain upgrade or gate weakening is involved.

## D1 and concurrency reuse

```sh
capped experiments/2026-10-14-concurrency-compatibility/check-preservation
cd experiments/2026-10-14-concurrency-compatibility
capped lake build
capped lake env lean Concurrency/Audit.lean
```

The existing audit prints both the standard-axiom result and the separate
implementation scan. The latter must still be reported as **FAIL** while the
16 unresolved findings remain; a zero Lean exit is not a clean implementation
inventory. Compare every finding's name with the individual table in the stage.
The preservation script archives C1 into its own temporary directory, checks
old/new complete control output, then removes that temporary directory.

The current-main CI replay covers all 96 GoLean modules. Still in the
experiment directory, replay its eight modules and the four facade/audit
clients, and compare the exact twelve names and their multiplicities:

```sh
capped lake env leanchecker --verbose Concurrency Tests.RelationalContracts \
  Tests.RelationalOutcomes Tests.RelationalProgramOutcomes Tests.GoCoreAudit
```

Check every `REPLAY_MODULE` printed by the experiment audit is included in the
union of those eight experiment modules and CI's on-disk GoLean module set.
Thus imported upstream dependencies are covered by CI rather than redundantly
replayed for each experiment entry. No executable modules sharing a top-level
`main` are combined into one import environment.

## Frozen customer acceptance

Follow the [C2 recipe](2026-10-15-c2-consumer-reproduction.md) with these changes
confined to the new private package:

- Use `.tmp/i1-consumer` and set its `pins.json` GoLean value to this integration
  implementation pin. Keep logic `bbb372e2b97eec663f55a01ee4993f98be829e1b` and
  all three other dependency pins unchanged.
- Include all three exact Lean snippets, adding `OriginalAcceptance` alongside
  `C2Adapter` and `C2Acceptance` as a private library target. All 106 original
  files must match frozen inputs except the private pin and appended library
  targets. The original program header is preserved with explicit `InitAssembly`.
- Build `GoLean RelationalCodeX C2Adapter C2Acceptance OriginalAcceptance`, run
  the aggregate/acceptance axiom reports, and replay the exact requested roots
  with `OriginalAcceptance` included. Check all source modules have outputs;
  compare complete expected/replayed name multisets.

Dependencies must be exact independent clones without object alternates or
writable cache symlinks. Compatible caches may be copied only after verifying
source identity. The aggregate includes original RD6 local adequacy, closed
RD5 Add/Alias/Pair/Set/Keep, both frozen Add routes and the exact phase consumers.
It is not RD7 or a live migration. Keep the inherited Memory warning and recorded
live 35 NOT-PUBLIC failure visible; no fresh live gate is claimed.

## Dependency probe

The following disposable client follows kernel-visible declaration values and
reports unresolved opaque generated endpoints. It stops at opaque constants,
so it does not certify their compiled implementations or hidden dependencies.
Save as `.tmp/i1/DependencyProbe.lean`, then run
`capped lake env lean .tmp/i1/DependencyProbe.lean` from the upstream worktree.
It is a diagnostic used for this disposition, not a new project gate.

```lean
import GoLean.GoCore.Multi
import GoLean.GoCore.Race
import Lean
open Lean
set_option maxHeartbeats 8000000

def dependencyProbe (root : Name) : CoreM Unit := do
  let env ← getEnv
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut endpoints : Array Name := #[]
  for _ in [:200000] do
    match pending with
    | [] =>
      logInfo m!"VALUE_DEPENDENCIES {root}: {endpoints.qsort Name.lt}"
      return
    | n :: rest =>
      pending := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | throwError "missing declaration {n}"
      if n.getRoot == `GoLean then
        if let some (.defnInfo implementation) := env.find? (n.str "_unsafe_rec") then
          if implementation.safety == .partial then
            match info with
            | .defnInfo d => if d.safety != .safe then endpoints := endpoints.push n
            | _ => endpoints := endpoints.push n
      if let some value := info.value? then
        pending := value.getUsedConstants.toList ++ pending
  throwError "dependency probe exhausted its bound at {root}"

#eval dependencyProbe `GoLean.GoCore.Machine.raceUpdate
#eval dependencyProbe `GoLean.GoCore.Machine.stepFn
#eval dependencyProbe `GoLean.GoCore.Machine.stepMulti
#eval dependencyProbe `GoLean.GoCore.Machine.runProgramM
#eval dependencyProbe `GoLean.GoCore.Machine.preprintDispatch
#eval dependencyProbe `GoLean.GoCore.Machine.unseqAtom
#eval dependencyProbe `GoLean.GoCore.valueEq
```

Delete private packages, build products and logs after recording conclusions.
The checked source snippets and commands above reconstruct the evidence.
