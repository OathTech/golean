# Dedup certificate soundness restored

The default build again proves `GoLean.GoCore.Machine.checkCert_slowObs` on the
current `checkCert` and `SlowObs`, with its original hypotheses and both directions.
The concrete instance `checkCertM_slowObs` discharges the node-equality hypothesis
using `dedupNodeEqb_sound`, matching the checker called by the CLI.

Validated proof tip: `7db46e3629a7bde8a9ad3527f582a788f56706b7` on
`core/dedup-soundness-1026`, based on `7739cf9f`. The commit containing this report
adds documentation only; the theorem and validation inputs remain at that proof tip.

```lean
theorem checkCert_slowObs
    {ctx : ProgramCtx} {nodeEqb : DedupNode → DedupNode → Bool}
    (hEqb : ∀ a b, nodeEqb a b = true → a = b)
    {resultLocs : List Loc} {m₀ : MultiConfig} {r₀ : RaceState}
    {cert : DedupCert}
    (hc : checkCert ctx nodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs ctx resultLocs m₀ r₀ o
```

The witness half replays each member through `execProgLoop`. The completeness half
uses total branch-vector coverage and induction on arbitrary fuel, including the
main-exit window and race verdict. It covers every choice stream, not just the
certificate's witness streams.

## Changes from the archived proof

The proof donor is `relational/last-main-2026-10-20:GoLean/GoCore/EnumDedupSound.lean`.
Its headline statements and proof strategy are unchanged. The new
`EnumDedupStreams.lean` restores only the needed executable support from the
archived `MachineSound` and `MultiStreams`: configuration-shape inversions,
stream-oblivious and one-pick thread steps, and the pool-driver unfolding.
It imports the live `PoolFacts` and `Consumes`; the current `StepFnFacts` already
accounts for the intervening machine changes, so no per-arm semantic repair was
necessary in this restoration.

The restored proof uses `Choices.consume_fst_lt` and the current names
`ite_eq_left`/`ite_eq_right`. The old unused-simp warning suppressions and the
1,600,000-heartbeat override are removed; the added proofs compile warning-free
with default resource limits. Two unused simp arguments in the select proof were
removed.

There are **no checker, interpreter, frontend or baseline changes**. Both
headlines are in `GoLean`, required by the core audit, pinned in
`Tests/GoCoreContract.lean` §D, and included in the comparator's `dedup` family.
The challenge gains two explicitly written statements, for 385 total; existing
challenge statements are unchanged. Its proof holes are the existing challenge
format, outside the solution's trusted closure. The CLI documentation names the
concrete theorem and retains the compiled-runtime qualification.

## Trust check

Run an import of `GoLean` with these commands:

```lean
#print axioms GoLean.GoCore.Machine.checkCert_slowObs
#print axioms GoLean.GoCore.Machine.checkCertM_slowObs
```

Observed output:

```text
'GoLean.GoCore.Machine.checkCert_slowObs' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.GoCore.Machine.checkCertM_slowObs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No requested mathematical obligation remains unproved. There is no weakened
fallback statement, extra premise beyond the original node-equality soundness,
or added proof escape hatch.

## Validation

All Lean and Lake invocations used `capped`. Full builds and gates held the
primary checkout's box-wide build lock. The first fast gate failed because the
copied differential and negative metadata had stale manifest hashes; its build,
kernel replay, core audit and other tests passed. The first full invocation failed at the wrapper level (exit 127): its inner
`scripts/ci --diff` printed PASS, but editing the still-running wrapper to correct
an inherited primary-checkout `TMPDIR` made the shell read an unintended trailing
command. That invocation is not counted as a clean success. The final run used a
separate wrapper, left unchanged throughout, with explicitly worktree-local scratch.
It regenerated both corpora, changed no baseline, and exited 0 on the clean proof
commit above. Total wall time: 908 seconds.


Selected final gate lines (the failing differential rows are the unchanged,
classified baseline set):

```text
Kernel replay gate: PASS — 55 GoLean modules replayed through the kernel into a fresh environment of their imports by leanchecker (= the 55 modules on disk, = the 55 oleans on disk)
Core totality audit gate: PASS
ok:414  fail:0  exit:0
differential coverage summary: cases=4045 pass=3784 fail=261 export_status=0
no regression: 415 case(s) run in negative-latest.tsv match baselines/negative-full.tsv
no regression: 4045 case(s) run in latest.tsv match baselines/native-full.tsv
ok   negative baseline diff FULL (415/415, no regression)
ok   differential baseline diff FULL (4045/4045, no regression)
RESULT: PASS
CI total wall seconds: 908
```

All speedbumps passed. `lake check` accepted the default targets on standard
axioms, exporting 63 project modules (261.96 seconds). `lake comparator` accepted
all 385 frozen statements, including both dedup theorems, on standard axioms
(34.60 seconds); its verdicts were `Lean default kernel accepts the solution`
and `Your solution is okay!`.

Both export-based checks ran with `--inadvisably-no-sandbox`, as the charter
permits for the in-tree speedbumps. Their `bwrap` probe failed to create a
`NETLINK_ROUTE` socket with `Operation not permitted`; this output does not identify
the enforcing sandbox. Nono sandbox unconfirmed; this permission failure needs a
non-sandbox diagnosis. Owner-run sandboxed checks and an independent adversarial
audit have not been performed. The charter's pre-merge audit ask remains for the
owner to scope or waive; no merge, push, tag or charter edit was made.

## Reproduce

On a machine with the repository's documented toolchains, `scripts/ci --diff`
rebuilds and runs the complete gate. On this box, acquire the primary checkout's
build lock as specified in the mission brief, and run from the worktree:

```sh
TMPDIR="$PWD/.tmp" LC_ALL=C CAPPED_MEM_MAX=64G capped scripts/ci --diff
```

For the headline statements and axioms, put the following in a scratch `.lean`
file under `.tmp/` and run it with `capped lake env lean .tmp/<file>.lean` after
the build:

```lean
import GoLean
#check GoLean.GoCore.Machine.checkCert_slowObs
#check GoLean.GoCore.Machine.checkCertM_slowObs
#print axioms GoLean.GoCore.Machine.checkCert_slowObs
#print axioms GoLean.GoCore.Machine.checkCertM_slowObs
```

The named mission worktree was used for the proof and both full runs. Generated
logs, copied build state and other temporary artifacts are not part of this report
commit; the completed worktree is removed after committing the report. The branch
retains the proof and this conclusion for review and reconstruction.
