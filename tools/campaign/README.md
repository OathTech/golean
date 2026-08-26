# tools/campaign — the raft campaign's generator + census tooling (TRACKED)

Tracked at the arc-4 landing fix round (2026-08-26, F6). The landing
audit found the entire generative/evidentiary base of the arc — the
generators behind ~1.23M generated proof lines, the corpus-split census
script, and the doctor+prune fixture tooling — living only in the
gitignored `artifacts/probe/`, while tracked docstrings cited those
paths as ground truth. A generated corpus that cannot be regenerated
from a clean clone is not a record. This directory is the durable copy;
the files are byte-identical to the `artifacts/probe/` originals at the
fix-round commit (plus `corpus-census.sh`, whose membership list was
corrected for the fix round's witness-return — see
`proofs/GoLeanProofsCorpus.lean`).

Probe OUTPUT artifacts (`*.out`, walk logs) remain gitignored by
design: they are re-derivable by running these tools, and the tracked
`.lean` modules + the lane log carry the verdicts. Old in-module
provenance headers cite `artifacts/probe/<Gen>.lean`; the fix round
deliberately did NOT rewrite those headers in place ([AGENT]: a
comment-only edit to ~90 generated modules would force a multi-hour
full re-elaboration of the generated corpus for zero semantic change) —
resolve any such citation to `tools/campaign/<Gen>.lean`, and use the
table below as the per-module provenance record (module → generator →
invocation).

## Invocation convention

Lean generators run against the built proofs package and print Lean
source to stdout:

    cd proofs && lake env lean ../tools/campaign/<Gen>.lean > <out>

(env-var knobs, e.g. `FRONTN`, `PVAR="k:v,..."` for perturbed choice
streams, are documented in each generator's header). The two Python
emitters post-process a generator's manifest output into `*Eq*` window
modules: `emit_mar_eq.py roundmargen.out`, `emit_vr_eq.py
roundvrgen.out`. `corpus-census.sh` takes no arguments.

## Script → generated modules (consumers)

| Tool | Generates / checks | Consuming chain |
|---|---|---|
| `SeedLitGen.lean` | `SeedLit.lean` (canonical stream), `SeedLitVar.lean` (`PVAR` perturbed stream) | SeedPin, SeedWitness (SP1 seed pin) |
| `SeedCFormGen.lean` | `SeedCFormLit.lean` | SeedPin (`seed_cform_pin`) |
| `BfLitGen.lean` | `BfLit.lean` (+ the shared literal-printer library reused by every later Gen) | Bf fixture chain (BfFixture/BfSteps/BfEquation) |
| `BcLitGen.lean` | `BcLit.lean` | Bc fixture chain |
| `Bf31Gen.lean` / `Bc31Gen.lean` | `Bf31Lit.lean` / `Bc31Lit.lean` | re-sited fixtures (Bf31/Bc31) |
| `HaeGen.lean` | `HaeLit.lean` | HaeEquation |
| `HaeRejGen.lean` | `HaeRejLit.lean` | HaeRejEquation |
| `StaleGen.lean` | `StaleLit.lean` | StaleEquation |
| `LaGen.lean` | `LaLit.lean` | LaEquation |
| `BlGen.lean` | `BlLit.lean` | BlEquation |
| `HhGen.lean` | `HhLit.lean` | HhEquation (live, ShapeWitness dep) |
| `HhAdvGen.lean` | `HhAdvLit.lean` | HhAdvEquation |
| `HhFromGen.lean` | `HhFromLit.lean` | HhFromEquation |
| `SfHbGen.lean` | `SfHbLit.lean` | SfHbEquation |
| `SfPdGen.lean` | `SfPdLit.lean` | SfPdEquation |
| `SCHbGen.lean` | `SCHbLit.lean` | SCHbEquation |
| `SlbGen.lean` | `SlbLit.lean` | SlbEquation |
| `MsgAppRingGen.lean` | `RingLit1..4` | RingEqW1/W2/W345, RingEquation, RingWitness (live since the fix round — `span_consume`'s witness chain) |
| `RoundMaGen.lean` | `RoundMaLit1..6` | RoundMaEqA-C, RoundMaEquation, RoundMaLemma (live since the fix round) |
| `RoundVoteGen2.lean` | `RoundVoteLit1..6` | RoundVote chain (live since the fix round) |
| `RoundMarGen.lean` + `emit_mar_eq.py` | `RoundMarLit1..7`, `RoundMarEqA-D` skeletons | RoundMar chain (live since the fix round) |
| `RoundVrGen.lean` + `emit_vr_eq.py` | `RoundVrLit1..14`, `RoundVrEqA-E` skeletons | RoundVr chain (live since the fix round) |
| `C2bWitnessGen.lean` | the C2b driver-net witness literals | DriverNetWitness |
| `TwinRoundFixProbe.lean` / `RoundFixDump.lean` | the doctor+prune fixture pipeline (heartbeat round, `RoundHbLit`) | RoundStatement's witness §4 |
| `TwinVoteFixProbe.lean` | RoundVote fixture (doctored anchor state) | RoundVoteLit* via RoundVoteGen2 |
| `TwinMarFixProbe.lean` | RoundMar fixture (anchor-3 doctor+prune, 49 cells) | RoundMarLit* via RoundMarGen |
| `TwinVrFixProbe.lean` | RoundVr fixture (anchor 2→3) | RoundVrLit* via RoundVrGen |
| `FixCollectFixProbe.lean` | (probe, not a generator) the pre-fix `collectFix` fail-open demonstration — run against the PRE-fix build it shows the two D-length states canonicalizing equal | `Frame/ChoiceCanonWitness.lean` documents + kernel-pins the fixed behavior |
| `corpus-census.sh` | the corpus split's importer-closure check (fail-closed direction) | `GoLeanProofsCorpus.lean`'s membership |

Provenance rule going forward: a new generator lands HERE (tracked) in
the same commit as its first generated module, and the generated
module's header cites `tools/campaign/<Gen>.lean` + the invocation.
