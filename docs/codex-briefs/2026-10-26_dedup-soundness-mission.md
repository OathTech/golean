# Codex mission brief — restore the dedup checker's soundness theorem (deep-clean DC04)

STATUS: **PREPARED** ([AGENT] coordinator, 2026-10-26; the owner asked the same day
for the theorem to be proved rather than the claim withdrawn, as a Codex mission).
Setup and the question only; scope is yours.

## The problem

The dedup enumerator (`golean coverage-observations --engine dedup`) prints
`certified=checkCert` and GoLean's code and CLI doc attribute the enumerated
observation set to the theorem `checkCert_slowObs`: every observation in the
certificate's set is in `SlowObs` (the ∃-fuel ∃-stream image of the machine's
runs — `GoLean/GoCore/EnumSpec.lean`) and conversely. That theorem lived in
`GoLean/GoCore/EnumDedupSound.lean` (1,079 lines) and was deleted from the build
on 2026-10-20 with the relational layer; the last main carrying it is tag
`relational/last-main-2026-10-20` (`git show relational/last-main-2026-10-20:GoLean/GoCore/EnumDedupSound.lean`).
The checker itself, `checkCert` in `GoLean/GoCore/EnumDedupCheck.lean`, is still
in the build and still runs. A records lane is rewording the live claims to say
the theorem is not in the build; your job is to put it back, honestly.

Statement at the tag (line 1017):

```
theorem checkCert_slowObs
    {nodeEqb : DedupNode → DedupNode → Bool}
    (hEqb : ∀ a b, nodeEqb a b = true → a = b)
    {resultLocs : List Loc} {m₀ : MultiConfig} {r₀ : RaceState}
    {cert : DedupCert}
    (hc : checkCert ctx nodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs ctx resultLocs m₀ r₀ o
```

## What is known

- The module's imports at the tag are `GoLean.GoCore.EnumDedupCheck` and
  `GoLean.GoCore.MachineEqb` — both executable modules, not the relation. It was
  retired because the retirement lane kept only what `Prefix`/`Finish` and the
  equation library needed, not because its proofs were relational; whether any
  of its lemmas reach a retired constant (through `MultiStreams`, whose executable
  definitions were re-homed into `GoLean/GoCore/Consumes.lean`) is yours to
  determine — the retirement review's method was a walk over proof terms with
  `ConstantInfo.value?` (`allowOpaque := true`) in the tag's environment.
- The machine changed since the tag in ways the proof covers: the append spill's
  default pick (train 16, `appendSpillCapAt`), the raise-time rendering mark moved
  to the abort phase (train 17: `panicEntryOf` takes no context, `Rewrite.raised`,
  `phaseMark`), the run-time `make` footprint guard (train 18), the sort
  intercept's `sortSlice` arm now reachable from the frontend (train 18). The
  tag's lemmas `stepFn_append_nospill`, `stepThread_append_oblivious`,
  `stepThread_total_covered`, `stepMulti_total_covered` and the per-arm sweeps
  will need rework where those arms moved.
- `SlowObs` and `checkCert` are on main unchanged in name; the current
  definitions are what the restored theorem must be about. The core is total:
  no `sorry`, no axiom, no `native_decide`, no `partial` anywhere under `GoLean/`;
  `#print axioms` on the theorem must show only `propext`, `Classical.choice`,
  `Quot.sound`; the kernel replay (`scripts/check-kernel-replay`) and
  `lake check` replay whatever you add.

## Where to work and how

- Worktree: `git -C /home/mike/projects/golean worktree add .claude/worktrees/dedup-sound-1026 -b core/dedup-soundness-1026 main`;
  copy `.lake` from the primary checkout; `ln -s <primary>/deps deps`.
- Every `lake`/`lean` run through the memory cap: `capped lake build <target>`,
  `capped lake env lean <file>`; `CAPPED_MEM_MAX=64G capped scripts/ci --diff`
  for the merge tier under the box-wide lock
  (`mkdir /home/mike/projects/golean/artifacts/build-lock.d` at the PRIMARY root,
  an `owner` file `dedup-sound <pid> <ISO date>`, released under a trap; wait and
  retry on failure, never take over). Exit 137 with a KILLED banner is a failure.
  Never set `CAPPED_MEM_MAX=none`. Never kill processes by name or pattern.
  Scratch under the worktree's `.tmp/`, never `/tmp`. The sandbox has no network.
  Set `LC_ALL=C` in your shells (a locale defect in `scripts/gen-contract` is
  being fixed by another lane).
- Deliverable: the theorem restored on main's definitions in a module of the
  build (`GoLean/GoCore/EnumDedupSound.lean` is the natural name), required by
  the core audit (`Tests/GoCoreAudit.lean`), pinned in `Tests/GoCoreContract.lean`
  §D, with its `#print axioms` output in the commit message; the records lane's
  wording in the CLI, the comments and `docs/cli.md` re-pointed at the live
  theorem; a changelog row (`docs/changelog/20d3946d-WINDOW.md`). If the theorem
  cannot be restored as stated against the current checker and definitions, stop
  at the strongest true statement, say precisely what fails and why, and leave
  the honest wording in place. No push, no merge, no tag, no `CLAUDE.md` edit,
  no change to the checker's behaviour to make the proof go through without
  saying so (a checker change is a trust-surface change the owner rules on).
- Report: the tip, the theorem's statement and axioms, what changed versus the
  tag's proof and why, the gate's result lines, anything left unproved.
