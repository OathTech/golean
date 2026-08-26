-- THE VALIDATION CORPUS (A4-U25 slice 0, 2026-08-26; the 2026-08-26 OOM
-- incident's correction (a); MEMBERSHIP CORRECTED at the arc-4 landing
-- fix round, 2026-08-26).
--
-- WHAT THIS IS: the literal-mode corpus — generated `*Lit` literal
-- modules and `*Eq`/`*Equation` chains consumed ONLY by their own
-- validation chain and Audit pins. CRITERION (amended at the fix
-- round): a chain lives here iff BOTH its law AND its witness are
-- corpus-resident — i.e. the chain validates only itself. A witness
-- whose LAW is in the live target ships LIVE beside the law (the
-- non-vacuity gate: deleting a live law's witness must fail
-- `scripts/ci`, not a hand-invoked landmark build). The U25 criterion
-- ("no importer outside the corpus set + aggregators", checked by the
-- census script — now tracked at tools/campaign/corpus-census.sh) is
-- subordinate to that rule; applying it alone had moved RingWitness
-- (span_consume's only witness) and RoundInductionWitness (the round
-- induction's), plus the four proved round-kind instances they
-- consume, out of the per-gate closure — returned to the live target
-- at the fix round (see GoLeanProofs.lean's witness-return block).
-- Per the flexibility redesign (docs/2026-08-26_campaign-flexibility-
-- redesign.md §2/§4, tracked in this repo since the fix round): these
-- are the compositional prover's VALIDATION CORPUS — subject-exact
-- scaffolds re-roled as I2's regression suite — not live machinery.
--
-- BUILD DISCIPLINE (the incident's structural fix, unchanged): this
-- library is NOT in `defaultTargets` — `lake build` and the
-- `scripts/ci` gate build the live tree only. The corpus builds AT
-- LANDMARKS (merge preparation, comparator-judge runs, corpus-touching
-- arcs) via
--
--     scripts/capped lake build AuditCorpus
--
-- (AuditCorpus imports this root, so one invocation builds + sweeps the
-- whole corpus; run it under the box-wide build-lock at full cap).
-- Landmark corpus builds are RECORDED in the tracked
-- docs/corpus-landmark-record.md (fix-round F7 — artifacts/ is
-- gitignored and is not a record). Fail-closed coverage is preserved:
-- `AuditCorpus.lean` re-runs the axiom sweep over this closure, and
-- `scripts/ci`'s proofs-file coverage step counts these files against
-- THIS root's closure and prints a visible deferred-sweep note — a
-- file in neither closure still FAILS the gate.
--
-- A NEW validation chain whose law lives in ITS OWN modules lands its
-- imports HERE (and its Audit pins in a module imported by
-- AuditCorpus.lean). A witness or instance of a LIVE law lands in
-- GoLeanProofs.lean, whatever its size — the placement rule follows
-- the law, not the line count.

-- The handler-equation validation chains (A4-U10..U17; the "20 literal
-- equations" of the redesign's asset inventory §2). Laws AND witnesses
-- of each chain are internal to this set. Interdependencies
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
