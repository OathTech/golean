# Codex mission brief — restore the dedup checker's soundness theorem (deep-clean DC04)

STATUS: **PREPARED** ([AGENT] coordinator, 2026-10-26; the owner asked the same day
for the theorem to be proved rather than the claim withdrawn, as a Codex mission.
Rewritten the same day for a long autonomous run: one end state, few hard rules,
everything else adaptable — [USER] direction, paraphrased.)

## The end state (this is the goal; everything else serves it)

On a branch off `main`, the build contains a theorem stating that the dedup
checker is sound and complete for the machine's observation set:

> if `checkCert … cert = true` then an observation is in `cert.obsSet` exactly
> when it is in `SlowObs …` (the ∃-fuel ∃-stream image of the machine's runs),

proved about the CURRENT definitions of `checkCert`
(`GoLean/GoCore/EnumDedupCheck.lean`) and `SlowObs` (`GoLean/GoCore/EnumSpec.lean`),
with `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`,
the merge gate green (`scripts/ci --diff`), and the live claims that cite it
(the CLI's `certified=` line, the comments in `GoLean/EnumDedup.lean`,
`GoLean/CLI.lean`, `GoLean/GoCore/EnumSpec.lean`, and `docs/cli.md`) true again.

That is the whole mission. Done means: the theorem in the build, the gate green,
the claims true, a report written. Anything that gets you there by an honest route
is in scope; anything that only looks like it does (a weakened statement
presented as the original, a checker edited so the proof goes through, a hole
hidden behind an option) is not.

## Hard rules (the few that are not yours to adapt)

- The core stays total: no `sorry`, no axiom, no `native_decide`, no `partial`
  under `GoLean/`; the statement is about the live `checkCert` and `SlowObs`,
  not copies of them. If you must change the checker's behaviour to make the
  theorem true, that is a trust-surface change: do it on the branch if it is
  clearly a bug fix, but say so prominently in the commit and the report — the
  owner rules on it. Weakening the statement is allowed only as the honest
  fallback described below, never silently.
- Box safety: every `lake`/`lean` run through the memory cap (`capped lake
  build …`, `capped lake env lean …`; never `CAPPED_MEM_MAX=none`; exit 137
  with a KILLED banner is a failure, not a pass); a full build or gate takes
  the box-wide lock first (`mkdir /home/mike/projects/golean/artifacts/build-lock.d`
  at the PRIMARY root, an `owner` file `dedup-sound <pid> <ISO date>`, released
  under a trap; wait and retry while another lane holds it, never take over);
  never kill processes by name or pattern. Scratch under the worktree's `.tmp/`.
- No push, no merge, no tag, no `CLAUDE.md` edit. Commit on your branch freely.
- Decisions in commit messages as `[AGENT]` with the date, paraphrased, never
  quoting the owner.

## What we know (useful, but check it; where it is wrong, adapt and move on)

- The theorem existed. The last main carrying it is tag
  `relational/last-main-2026-10-20`; the file is
  `git show relational/last-main-2026-10-20:GoLean/GoCore/EnumDedupSound.lean`
  (about 1,079 lines; the statement near line 1017 is `checkCert_slowObs`, with
  a `nodeEqb` injectivity premise and `resultLocs m₀ r₀ cert` arguments). It was
  deleted on 2026-10-20 because the retirement kept only what `Prefix`/`Finish`
  and the equation library needed — not, as far as we know, because its proofs
  depended on the retired relation. Its imports were `EnumDedupCheck` and
  `MachineEqb`, both still executable modules on main. Start by putting the file
  back and reading the errors; that is probably faster than any analysis.
- The machine has moved since the tag, so some lemmas will not go through as
  written. Known movements: the append spill's default pick (`appendSpillCapAt`),
  the raise-time mark now set in the abort phase (`Rewrite.raised`, `phaseMark`;
  `panicEntryOf` lost its context argument), a run-time `make` footprint guard,
  a `sortSlice` statement arm. Expect the per-arm coverage lemmas
  (`stepThread_total_covered`, `stepMulti_total_covered`, the `append` ones) to
  need the most work. There may be other drifts we have not listed.
- Useful neighbours on main: `GoLean/GoCore/StepFnFacts.lean` and
  `Equations.lean` (one proved equation per `stepFn` arm, `@[stepFn_eqns]`),
  `Consumes.lean` (the executable stream definitions that used to be in
  `MultiStreams`), `PoolFacts.lean`. The retired relational modules on the tag
  are design donors too (`docs/ARCHIVE.md` lists them).
- Where the theorem should live: `GoLean/GoCore/EnumDedupSound.lean` is the
  natural name; the core audit (`Tests/GoCoreAudit.lean`) and the contract pin
  set (`Tests/GoCoreContract.lean` §D; the comparator contract via
  `scripts/gen-contract`) are where kept theorems get registered — follow what
  the existing entries do. A changelog row goes in `docs/changelog/20d3946d-WINDOW.md`.
  If any of these conventions turn out to have shifted, follow the current one.
- The gate: `capped scripts/ci` is the fast tier (about 90 s), `CAPPED_MEM_MAX=64G
  capped scripts/ci --diff` the merge tier (10–16 min), both under the lock.
  Speedbumps print under their own heading and are not failures; name any red
  one in the report. The sandbox has no network. A locale defect in
  `scripts/gen-contract` under `C.UTF-8` is being fixed by another lane;
  `LC_ALL=C` in your shell avoids it meanwhile.

## How to work

Use your judgement. The brief above may be wrong in details — a line number, a
lemma name, a convention — and the codebase is the truth; fix the detail and keep
going rather than stopping. Break long proofs into lemmas as you see fit;
restructure the retired proof freely; keep intermediate commits so progress is
never lost. If the heartbeat limit bites, prefer a decomposition over raising it;
if you do raise it, one declaration at a time with the reason beside it.

Check-ins: the owner will look in from time to time. Leave a short, current
`.tmp/STATUS.md` in the worktree (what is proved, what is open, what you are doing
now) so a glance tells whether the run is on track. "Wildly off track" looks
like: rewriting the checker, proving a different theorem than the end state,
or a week of work on a lemma that could be sidestepped — if you notice that
yourself, step back and pick another route.

The honest fallback: if after real effort the full theorem cannot be restored
against the current definitions, stop at the strongest TRUE statement you can
prove (for instance one direction, or the theorem under an extra premise you can
name), keep the live wording honest about exactly what is and is not proved, and
say precisely what fails and why. A clear account of an obstacle is a successful
report; a theorem with a hole is not.

## Setup

```
git -C /home/mike/projects/golean worktree add .claude/worktrees/dedup-sound-1026 -b core/dedup-soundness-1026 main
cp -a /home/mike/projects/golean/.lake /home/mike/projects/golean/.claude/worktrees/dedup-sound-1026/.lake
ln -s /home/mike/projects/golean/deps /home/mike/projects/golean/.claude/worktrees/dedup-sound-1026/deps
mkdir -p /home/mike/projects/golean/.claude/worktrees/dedup-sound-1026/{.tmp,artifacts/coverage}
cp /home/mike/projects/golean/artifacts/coverage/{latest,negative-latest}.{tsv,meta.tsv} /home/mike/projects/golean/.claude/worktrees/dedup-sound-1026/artifacts/coverage/
```

## Report

The tip; the theorem's statement and its `#print axioms`; what changed versus the
tag's proof and why; any checker change, flagged; the gate's result lines; what,
if anything, is left unproved and what blocked it.
