-- THE VALIDATION CORPUS (A4-U25 slice 0, 2026-08-26; the 2026-08-26 OOM
-- incident's correction (a), campaign log entry of that date).
--
-- WHAT THIS IS: the literal-mode corpus — the generated `*Lit` literal
-- modules and the `*Eq`/`*Equation`/`*Lemma`/witness chains consumed ONLY
-- by their own validation chain and Audit pins (census: A4-U25 lane log
-- entry; criterion = "no importer outside the corpus set + aggregators",
-- mechanically checked by artifacts/probe/corpus-census.sh at the split).
-- Per the flexibility redesign (docs/2026-08-26_campaign-flexibility-
-- redesign.md §2/§4): these are the compositional prover's VALIDATION
-- CORPUS — subject-exact scaffolds re-roled as I2's regression suite —
-- not live machinery. The live tree (transports, SliceWalk, FrameSimS,
-- the lens, TableExt, the Native chain, RoundStatement and every module
-- a live module imports — incl. RoundHbLit via RoundStatement, HhLit/
-- HhEquation via ShapeWitness, and the Bf/Bc fixture chains via
-- AllocEq/AbsStateV2) stays in the default `GoLeanProofs` target.
--
-- BUILD DISCIPLINE (the incident's structural fix): this library is NOT
-- in `defaultTargets` — `lake build` and the `scripts/ci` gate build the
-- live tree only. The corpus builds AT LANDMARKS (merge preparation,
-- comparator-judge runs, corpus-touching arcs) via
--
--     scripts/capped lake build AuditCorpus
--
-- (AuditCorpus imports this root, so one invocation builds + sweeps the
-- whole corpus; run it under the box-wide build-lock at full cap — it is
-- a full-scale build when cold). Fail-closed coverage is preserved:
-- `AuditCorpus.lean` re-runs the axiom sweep over this closure and hosts
-- the corpus Audit pin modules, and `scripts/ci`'s proofs-file coverage
-- step counts these files against THIS root's closure and prints a
-- visible note that their sweep is deferred to the corpus build — a file
-- in neither closure still FAILS the gate.
--
-- A NEW round-kind instance or literal chain lands its imports HERE (and
-- its Audit pins in a module imported by AuditCorpus.lean), never in
-- GoLeanProofs.lean.

-- C2c: the storage-resp sub-ring spans at the MsgApp append-family round
-- fixture (mirror-chain form; generated literals + equations + witness).
import GoLeanProofs.Specs.Raft.RingLit1
import GoLeanProofs.Specs.Raft.RingLit2
import GoLeanProofs.Specs.Raft.RingLit3
import GoLeanProofs.Specs.Raft.RingLit4
import GoLeanProofs.Specs.Raft.RingEquation
import GoLeanProofs.Specs.Raft.RingWitness
-- C2d (A4-U22): the MsgApp round lemma — the R-form's first proved
-- instance (full-round literals + segment spans + canonical run + lemma).
import GoLeanProofs.Specs.Raft.RoundMaLit1
import GoLeanProofs.Specs.Raft.RoundMaLit2
import GoLeanProofs.Specs.Raft.RoundMaLit3
import GoLeanProofs.Specs.Raft.RoundMaLit4
import GoLeanProofs.Specs.Raft.RoundMaLit5
import GoLeanProofs.Specs.Raft.RoundMaLit6
import GoLeanProofs.Specs.Raft.RoundMaEqA
import GoLeanProofs.Specs.Raft.RoundMaEqB
import GoLeanProofs.Specs.Raft.RoundMaEqC
import GoLeanProofs.Specs.Raft.RoundMaEquation
import GoLeanProofs.Specs.Raft.RoundMaLemma
-- A4-U23: the MsgVote round-kind instance (the R-form's second proved
-- instance; auto-discovered boundary schedule).
import GoLeanProofs.Specs.Raft.RoundVoteLit1
import GoLeanProofs.Specs.Raft.RoundVoteLit2
import GoLeanProofs.Specs.Raft.RoundVoteLit3
import GoLeanProofs.Specs.Raft.RoundVoteLit4
import GoLeanProofs.Specs.Raft.RoundVoteLit5
import GoLeanProofs.Specs.Raft.RoundVoteLit6
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.RoundVoteEqB
import GoLeanProofs.Specs.Raft.RoundVoteEqC
import GoLeanProofs.Specs.Raft.RoundVoteEquation
import GoLeanProofs.Specs.Raft.RoundVoteLemma
-- A4-U24: the MsgAppResp maybeCommit round-kind instance (the R-form's
-- third proved instance; commit-without-append).
import GoLeanProofs.Specs.Raft.RoundMarLit1
import GoLeanProofs.Specs.Raft.RoundMarLit2
import GoLeanProofs.Specs.Raft.RoundMarLit3
import GoLeanProofs.Specs.Raft.RoundMarLit4
import GoLeanProofs.Specs.Raft.RoundMarLit5
import GoLeanProofs.Specs.Raft.RoundMarLit6
import GoLeanProofs.Specs.Raft.RoundMarLit7
import GoLeanProofs.Specs.Raft.RoundMarEqA
import GoLeanProofs.Specs.Raft.RoundMarEqB
import GoLeanProofs.Specs.Raft.RoundMarEqC
import GoLeanProofs.Specs.Raft.RoundMarEqD
import GoLeanProofs.Specs.Raft.RoundMarEquation
import GoLeanProofs.Specs.Raft.RoundMarLemma
-- A4-U25: the MsgVoteResp election-completion round-kind instance (the
-- R-form's fourth proved instance; candidate → leader at anchor 2→3 —
-- the matrix's last structural ring shape; the S1 claim is born here).
import GoLeanProofs.Specs.Raft.RoundVrLit1
import GoLeanProofs.Specs.Raft.RoundVrLit2
import GoLeanProofs.Specs.Raft.RoundVrLit3
import GoLeanProofs.Specs.Raft.RoundVrLit4
import GoLeanProofs.Specs.Raft.RoundVrLit5
import GoLeanProofs.Specs.Raft.RoundVrLit6
import GoLeanProofs.Specs.Raft.RoundVrLit7
import GoLeanProofs.Specs.Raft.RoundVrLit8
import GoLeanProofs.Specs.Raft.RoundVrLit9
import GoLeanProofs.Specs.Raft.RoundVrLit10
import GoLeanProofs.Specs.Raft.RoundVrLit11
import GoLeanProofs.Specs.Raft.RoundVrLit12
import GoLeanProofs.Specs.Raft.RoundVrLit13
import GoLeanProofs.Specs.Raft.RoundVrLit14
import GoLeanProofs.Specs.Raft.RoundVrEqA
import GoLeanProofs.Specs.Raft.RoundVrEqB
import GoLeanProofs.Specs.Raft.RoundVrEqC
import GoLeanProofs.Specs.Raft.RoundVrEqD
import GoLeanProofs.Specs.Raft.RoundVrEqE
import GoLeanProofs.Specs.Raft.RoundVrEquation
import GoLeanProofs.Specs.Raft.RoundVrLemma
-- The handler-equation validation chains (A4-U10..U17; the "20 literal
-- equations" of the redesign's asset inventory §2). Interdependencies
-- (e.g. HaeEquation ← Stale/HaeRej/La; SfHbLit ← SCHb/Slb) are internal
-- to this set; equation roots suffice for the closure but every member
-- is listed explicitly so the census stays legible.
import GoLeanProofs.Specs.Raft.HaeLit
import GoLeanProofs.Specs.Raft.HaeEquation
import GoLeanProofs.Specs.Raft.StaleLit
import GoLeanProofs.Specs.Raft.StaleEquation
import GoLeanProofs.Specs.Raft.LaLit
import GoLeanProofs.Specs.Raft.LaEquation
import GoLeanProofs.Specs.Raft.BlLit
import GoLeanProofs.Specs.Raft.BlEquation
import GoLeanProofs.Specs.Raft.HhAdvLit
import GoLeanProofs.Specs.Raft.HhAdvEquation
import GoLeanProofs.Specs.Raft.MsResite
import GoLeanProofs.Specs.Raft.MsErrEquation
import GoLeanProofs.Specs.Raft.HaeRejLit
import GoLeanProofs.Specs.Raft.HaeRejEquation
import GoLeanProofs.Specs.Raft.HhFromLit
import GoLeanProofs.Specs.Raft.HhFromEquation
import GoLeanProofs.Specs.Raft.SfHbLit
import GoLeanProofs.Specs.Raft.SfHbEquation
import GoLeanProofs.Specs.Raft.SfPdLit
import GoLeanProofs.Specs.Raft.SfPdEquation
import GoLeanProofs.Specs.Raft.SCHbLit
import GoLeanProofs.Specs.Raft.SCHbEquation
import GoLeanProofs.Specs.Raft.SlbLit
import GoLeanProofs.Specs.Raft.SlbEquation
