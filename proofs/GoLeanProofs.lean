-- The executable frame theorem (verified-examples slice 2b;
-- docs/2026-08-13_executable-frame-theorem.md): the helper-commutation
-- layer (§5 steps 1-2), the store-spine glue (Ops2), the ~200-arm
-- per-step simulation (StepSim), and the iterated/driver-level transfer
-- corollaries (Transfer). All sorry-free; axiom footprint the classical
-- trio (Classical.choice inherited from the core MachineSound layer via
-- Machine.Heap.lookup_set_ne — recorded in the Audit gates below).
import GoLeanProofs.Frame.Rename
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Frame.TypeCongr
import GoLeanProofs.Frame.Values
import GoLeanProofs.Frame.Compare
import GoLeanProofs.Frame.NoPanic
import GoLeanProofs.Frame.Plans
import GoLeanProofs.Frame.ContOps
import GoLeanProofs.Frame.HeapOps
import GoLeanProofs.Frame.MachineRel
import GoLeanProofs.Frame.Builders
import GoLeanProofs.Frame.PanicFrame
import GoLeanProofs.Frame.ChanSync
import GoLeanProofs.Frame.StmtOps
import GoLeanProofs.Frame.StrictOps
import GoLeanProofs.Frame.Ops2
import GoLeanProofs.Frame.StepSim
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Frame.AllocIndep
-- A4-U6: the relocation seed (promotion lift from the A4-U5 ledger).
import GoLeanProofs.Frame.Relocate
-- A4-U9's Sym.PickTransport lift DELETED at the arc-4 landing fix
-- round (unconsumed byte-identical duplicate of the RaftSeam
-- original; ledger row closed — see Audit/Kit.lean's tombstone).
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Specs.Raft.HhLit
import GoLeanProofs.Specs.Raft.HhEquation
import GoLeanProofs.Specs.Raft.StaticCells
import GoLeanProofs.Specs.Raft.StaticCellsExt
-- THE VALIDATION-CORPUS SPLIT (A4-U25 slice 0, 2026-08-26; the OOM
-- incident's correction (a)), AS CORRECTED at the arc-4 landing fix
-- round: the corpus target holds ONLY validation chains whose LAWS
-- are corpus-resident (the Hae/Stale/La/Bl/HhAdv/MsErr+MsResite/
-- HaeRej/HhFrom/SfHb/SfPd/SCHb/Slb handler-equation chains). The
-- U25 split had also moved the WITNESSES of LIVE laws out of the
-- per-gate closure — RingWitness (span_consume's only discharge
-- witness) and RoundInductionWitness (the round induction's) — which
-- silently weakened the non-vacuity doctrine for live laws: a witness
-- ships WITH its law, in the gated build, so deleting either fails
-- `scripts/ci`. Those chains (and their Round*/Ring dependencies)
-- returned to THIS target at the fix round; the gate-wall cost of the
-- return is measured in the fix-round log entry.
-- Also live: HhLit/HhEquation (a ShapeWitness dependency), RoundHbLit
-- (a RoundStatement dependency), StaticCells(+Ext) (link-pin pattern
-- machinery), the Bf/Bc fixture chains (AllocEq/AbsStateV2
-- dependencies), and RoundStatement itself.
-- (The U25-era comment here undercounted its own commit: it said
-- "the three proved round-kind instances (RoundMa/RoundVote/RoundMar)"
-- in the commit that landed the FOURTH, RoundVr — reconciled at the
-- fix round; the count of proved round-kind instances is FOUR.)
-- A4-U14: the branch-crossing transport (path-condition splitting);
-- its From-symbolic equation witness chain is in the corpus target.
import GoLeanProofs.Sym.BranchTransport
import GoLeanProofs.Specs.Raft.RoundHbLit
import GoLeanProofs.Specs.Raft.RoundStatement
-- C2a: the completeness-strengthened frame simulation (FrameSimS) —
-- the mid-walk consumption instrument (layer-C design v2 §8 D1)
import GoLeanProofs.Frame.ShapeSim
import GoLeanProofs.Frame.ShapeOps
import GoLeanProofs.Frame.ShapeOps2
import GoLeanProofs.Frame.ShapeOps3
import GoLeanProofs.Frame.ShapeStrict
import GoLeanProofs.Frame.ShapeStep
import GoLeanProofs.Frame.ShapeSpan
import GoLeanProofs.Specs.Raft.ShapeWitness
import GoLeanProofs.SliceWalk
import GoLeanProofs.Specs.Raft.DriverNet
import GoLeanProofs.Specs.Raft.DriverNetWitness
-- THE WITNESS RETURN (arc-4 landing fix round): the C2c Ring span
-- chain and the FOUR proved round-kind instances (C2d RoundMa,
-- A4-U23 RoundVote, A4-U24 RoundMar, A4-U25 RoundVr) return from the
-- corpus target to the live tree — RingWitness discharges the LIVE
-- `span_consume` (ShapeSpan) and RoundInductionWitness discharges
-- the LIVE `round_induction`/`seeded_round_induction`, and a
-- non-vacuity witness ships in the same gated build as its law
-- (CLAUDE.md's gate; the U25 split had deferred these to landmark
-- corpus builds only). The checker-interface I2 bridges (A4-U23
-- slice 2) are LIVE below (NativeCheckerBridge).
import GoLeanProofs.Specs.Raft.RingLit1
import GoLeanProofs.Specs.Raft.RingLit2
import GoLeanProofs.Specs.Raft.RingLit3
import GoLeanProofs.Specs.Raft.RingLit4
import GoLeanProofs.Specs.Raft.RingEquation
import GoLeanProofs.Specs.Raft.RingWitness
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
-- arc4b landing (C2c slice 0, per the lane's landing manifest): the native
-- S1/S2/S3 chain over the obligation signature (SC1 + C3 + C4)
import GoLeanProofs.Specs.Raft.NativeObligations
import GoLeanProofs.Specs.Raft.NativeS23Route
import GoLeanProofs.Specs.Raft.NativeS1Chain
import GoLeanProofs.Specs.Raft.NativeEtcdDischarge
import GoLeanProofs.Specs.Raft.NativeS1CheckerLeaf
import GoLeanProofs.Specs.Raft.NativeS1Witness
import GoLeanProofs.Specs.Raft.NativeS23Chain
import GoLeanProofs.Specs.Raft.NativeS23Witness
import GoLeanProofs.Specs.Raft.NativeCheckerBridge
-- SP1 landing (arc4c lane, per its landing manifest — A4-U26 slice 0):
-- the choice-invariance carrier (~/~ₘ, CForm) + the seed pin. LIVE, not
-- corpus — placement re-justified at the landing fix round against the
-- corrected witness-with-law rule (the audit had flagged the U26-era
-- generated lines re-entering the default target as an unreconciled
-- rule violation; each line is justified here):
--   ChoiceCanon/ChoiceInv — live laws (the ~/~ₘ carrier + the
--     choice-invariance statement layer); namespace
--     GoLean.Frame.ChoiceErase since the fix round.
--   ChoiceCanonWitness — the collectFix view-fixpoint regression
--     witness (fix-round F2a; witness ships with the fixed law).
--   SeedLit (25,749 gen. lines) — SeedPin's literal; SeedPin is live
--     because seed_N₀/SeedFam discharge hypotheses of the LIVE
--     round induction and native chain.
--   SeedCFormLit (1,541 gen. lines) — seed_cform_pin's literal (live
--     law, same module).
--   SeedLitVar (22,532 gen. lines) + SeedWitness — the ~ₘ layer's
--     occupation witnesses (non-canonical stream landing CEquivM-equal):
--     witnesses of the LIVE equivalence, so live by the
--     witness-with-law rule (the U25 corpus criterion "no importer
--     outside the corpus set" is subordinate to that rule — corrected
--     at the fix round; GoLeanProofsCorpus.lean's header carries the
--     amended criterion).
-- Kernel cost joining the default build (measured at SP1): SeedPin
-- ≈262 s + SeedWitness ≈41 s.
import GoLeanProofs.Frame.ChoiceCanon
import GoLeanProofs.Frame.ChoiceCanonWitness
import GoLeanProofs.Frame.ChoiceInv
import GoLeanProofs.Specs.Raft.SeedLit
import GoLeanProofs.Specs.Raft.SeedLitVar
import GoLeanProofs.Specs.Raft.SeedCFormLit
import GoLeanProofs.Specs.Raft.SeedPin
import GoLeanProofs.Specs.Raft.SeedWitness
-- A4-U26 slice 2: THE ROUND INDUCTION (generic simulation induction
-- over round chains; consumes the R-form + the native chain + the seed
-- pin). Its witnesses are LIVE beside it since the landing fix round
-- (the witness return above).
import GoLeanProofs.Specs.Raft.RoundInduction
import GoLeanProofs.Specs.Raft.RoundInductionWitness
-- A4-U8: the field-lens layer (Perennial Access lineage; general half —
-- combinators + L1-L4 laws; per-field instances live in Specs/Raft).
import GoLeanProofs.Lens
import GoLeanProofs.Lang
import GoLeanProofs.LangC
import GoLeanProofs.LangD
import GoLeanProofs.HeapBridge
import GoLeanProofs.Ghost
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Loop
import GoLeanProofs.Laws.Range
import GoLeanProofs.Laws.Values
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Adequacy
import GoLeanProofs.Specs.GoldenProgram
import GoLeanProofs.Specs.GoldenTargets
import GoLeanProofs.Specs.GoldenSliceWP
import GoLeanProofs.Surface
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenSurface
import GoLeanProofs.Specs.GoldenRecover
import GoLeanProofs.Specs.GoldenQuorum
import GoLeanProofs.Specs.GoldenQuorumPin
import GoLeanProofs.Specs.QuorumTargets
-- The raft campaign's statement layer (Arc 1, 2026-08-22): the
-- wire-pin mechanism, the pinned twin lowering, and the T1/witness
-- statement Props — in the audited closure from birth.
import GoLeanProofs.Specs.WirePin
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Specs.RaftAgreement
-- Arc 2: the checkpoint reflector (route memo §4c) — meta-side
-- scaffolding + the shared table-carrying base def — and the
-- reflected mid-run checkpoint (route memo §6.1).
import GoLeanProofs.Specs.StateWire
import GoLeanProofs.Specs.TwinCheckpoints
-- Arc 2 U4: the trie-form checkpoints, the kernel-pinned prelude, and
-- the verified fast-twin evaluator (route (d) — untrusted method,
-- never in any statement closure).
import GoLeanProofs.Specs.TwinCheckpointsF
import GoLeanProofs.Specs.TwinPrelude
import GoLeanProofs.FastEval.Heap
import GoLeanProofs.FastEval.Ops
import GoLeanProofs.FastEval.Loops
import GoLeanProofs.FastEval.Shared
import GoLeanProofs.FastEval.Values
import GoLeanProofs.FastEval.Stores
import GoLeanProofs.FastEval.Frames
import GoLeanProofs.FastEval.Iter
import GoLeanProofs.FastEval.Step
import GoLeanProofs.FastEval.Congr
import GoLeanProofs.FastEval.Transfer
import GoLeanProofs.FastEval.TransferWitness
import GoLeanProofs.FastReplay
import GoLeanProofs.Specs.QuorumRefSpec
import GoLeanProofs.Specs.Statements
import GoLeanProofs.Specs.GoldenQuorumWP
import GoLeanProofs.Specs.AutomationTargets
import GoLeanProofs.Specs.GoldenQuorumThree
import GoLeanProofs.Specs.GoldenQuorumAll
import GoLeanProofs.Specs.TotalPins
import GoLeanProofs.Specs.ForkJoinTargets
import GoLeanProofs.Specs.GoldenForkJoin
import GoLeanProofs.Specs.GoldenSelectDone
import GoLeanProofs.Specs.ImportedGooseBlock
import GoLeanProofs.Specs.ImportedGooseDefer
import GoLeanProofs.Specs.ImportedGooseNil
import GoLeanProofs.Specs.ImportedGooseNew
import GoLeanProofs.Specs.ImportedGooseVars
import GoLeanProofs.Specs.ImportedGooseSelectTricky
import GoLeanProofs.Specs.ImportedGooseMuxer
import GoLeanProofs.Specs.ImportedGooseActris
import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.GooseParityNilWP
import GoLeanProofs.Specs.GooseParityBlockWP
import GoLeanProofs.Specs.GooseParityNewWP
import GoLeanProofs.Specs.GooseParityVarsWP
import GoLeanProofs.Specs.GooseParityChannels
import GoLeanProofs.Specs.ImportedGooseMapliteral
import GoLeanProofs.Specs.ImportedGooseConst
import GoLeanProofs.Specs.ImportedGooseRune
import GoLeanProofs.NegativeSpecs
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.FibProgram
import GoLeanProofs.Examples.Fib
import GoLeanProofs.SliceMem
import GoLeanProofs.StringMem
import GoLeanProofs.MapMem
import GoLeanProofs.Laws.Slice
import GoLeanProofs.Examples.ReverseProgram
import GoLeanProofs.Examples.Reverse
import GoLeanProofs.Examples.Reverse.HarnessV
import GoLeanProofs.Examples.GcdProgram
import GoLeanProofs.Examples.Gcd
import GoLeanProofs.Examples.MinMaxProgram
import GoLeanProofs.Examples.MinMax
import GoLeanProofs.Examples.MinMax.HarnessR
import GoLeanProofs.Examples.BinSearchProgram
import GoLeanProofs.Examples.BinSearch
import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.Examples.InsertionSort
import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.Examples.WordCount
-- The S3 relational harness carrying the designated headline
-- `wordcount_ok` (2026-08-14 designation): it was reachable only via
-- `Audit/WordCount.lean`, so `Solution.lean` — which imports this
-- aggregator — could not see it. Its two sibling S3 harnesses
-- (`Reverse.HarnessV`, `MinMax.HarnessR`) were already listed here.
-- STILL REQUIRED after the 2026-08-15 audit response (C-H5): all three
-- swap shards must be listed in this aggregator BY NAME, because each
-- one imports its example root rather than the other way round, so no
-- `Examples.<X>` import reaches its own designated headline. Removing
-- any of these three lines drops a designated theorem out of the
-- audited build. The direction is repaired only by the recorded
-- follow-up (split the roots into `Core` shards —
-- `docs/2026-08-15_phase2-premerge-audit.md`, C-H4/C-H5).
import GoLeanProofs.Examples.WordCount.HarnessR
-- The gallery campaign's flagship example (G1 unit 1, 2026-08-15). NOT
-- designated: it is deliberately absent from `Examples/Targets.lean`
-- and from the Comparator Challenge's trusted closure (charter §HARD
-- BOUNDARIES — designation is arc-end work under user sign-off).
import GoLeanProofs.Examples.HistogramProgram
import GoLeanProofs.Examples.Histogram
import GoLeanProofs.Examples.SortShared
import GoLeanProofs.Examples.BubbleSortProgram
import GoLeanProofs.Examples.BubbleSort
import GoLeanProofs.Examples.TwoSumProgram
import GoLeanProofs.Examples.TwoSum
import GoLeanProofs.Examples.RunLengthProgram
import GoLeanProofs.Examples.RunLength
import GoLeanProofs.Examples.PowModProgram
import GoLeanProofs.Examples.PowMod
import GoLeanProofs.Examples.ArrayPalindromeProgram
import GoLeanProofs.Examples.ArrayPalindrome
import GoLeanProofs.Examples.DedupAdjacentProgram
import GoLeanProofs.Examples.DedupAdjacent
import GoLeanProofs.Examples.KadaneProgram
import GoLeanProofs.Examples.Kadane
import GoLeanProofs.Examples.DotProductProgram
import GoLeanProofs.Examples.DotProduct
import GoLeanProofs.Examples.SieveProgram
import GoLeanProofs.Examples.Sieve
import GoLeanProofs.Examples.MatMulProgram
import GoLeanProofs.Examples.MatMul
import GoLeanProofs.Examples.SliceStackProgram
import GoLeanProofs.Examples.SliceStack
import GoLeanProofs.Examples.SliceQueueProgram
import GoLeanProofs.Examples.SliceQueue
import GoLeanProofs.Examples.StringReverseProgram
import GoLeanProofs.Examples.StringReverse
import GoLeanProofs.Examples.SteinProgram
import GoLeanProofs.Examples.Stein
import GoLeanProofs.Examples.FibMemoProgram
import GoLeanProofs.Examples.FibMemo
import GoLeanProofs.Examples.SelectionSortProgram
import GoLeanProofs.Examples.SelectionSort
import GoLeanProofs.Examples.WordFreqProgram
import GoLeanProofs.Examples.WordFreq
-- The mirror symbolic evaluator (WP arc slice 4, Route B; design
-- docs/2026-08-16_symbolic-domain-design.md, gate discharged
-- 2026-08-18). Proof AUTOMATION infrastructure, outside the statement
-- TCB: listed here so the default build elaborates it and the Audit
-- walker's third refusal class (no `GoLean.Sym` constant in any
-- designated statement closure) sees its environment.
-- SCOPE, corrected 2026-08-18 (pre-merge review finding A-F2 — the
-- old text said "NO example or headline module imports it", which
-- stopped being true at S4.11): `Examples/MatMul.lean` imports
-- `GoLeanProofs.Sym.Refine` PROOF-SIDE, to transport its measured
-- blocker segments. What holds is the property the refusal class
-- actually checks — every designated STATEMENT closure stays
-- Sym-free (walker-verified, plus the audit's by-hand matmul closure)
-- — so an import is not a statement dependency. The deletion test
-- extends to Sym at arc end.
import GoLeanProofs.Sym.Domain
import GoLeanProofs.Sym.Mirror
import GoLeanProofs.Sym.Conc
import GoLeanProofs.Sym.Drift
import GoLeanProofs.Sym.DriftOps
import GoLeanProofs.Sym.DriftApply
-- THE MASTER WALK: the drift theorem (`stepFn'_concrete_agrees`) and
-- the symbolic per-step soundness live here — in the DEFAULT build,
-- per the charter's drift-gate clause: an edit to ANY stepFn/stepFn'
-- arm that breaks their agreement breaks this import.
import GoLeanProofs.Sym.Walk
-- THE REFINEMENT THEOREM (`symEvalWindow_refines`): the window
-- driver's induction over the walk at the symbolic interpretation.
import GoLeanProofs.Sym.Refine
import GoLeanProofs.Sym.SpikeKadane
-- Campaign Arc 4 (A4-U1 pilot): the interpreter⇄invariant seam's
-- abstraction reader + per-callee span equations + pinned witness.
-- Proof infrastructure — never imported by the Specs statement modules.
import GoLeanProofs.Specs.Raft.AbsState
import GoLeanProofs.Specs.Raft.HandlerEq
import GoLeanProofs.Specs.Raft.BecomeFollowerWitness
-- A4-U2 slice 1: the handler-fragment Sym extension (class 1, the
-- type-table input) + the Sym-driven re-measure of the pilot leaf.
import GoLeanProofs.Sym.TableExt
import GoLeanProofs.Specs.Raft.HandlerEqSym
-- A4-U3: the populated becomeFollower fixture, the crossing facts,
-- and THE FIRST FULL HANDLER EQUATION.
import GoLeanProofs.Specs.Raft.BfLit
import GoLeanProofs.Specs.Raft.BfFixture
import GoLeanProofs.Specs.Raft.BfSteps
import GoLeanProofs.Specs.Raft.BfSteps2
import GoLeanProofs.Specs.Raft.BfEquation
import GoLeanProofs.Specs.Raft.BpcEquation
import GoLeanProofs.Specs.Raft.BcLit
import GoLeanProofs.Specs.Raft.BcFixture
import GoLeanProofs.Specs.Raft.BcSteps
import GoLeanProofs.Specs.Raft.BcEquation
import GoLeanProofs.Specs.Raft.MsEquation
-- A4-U5: the allocation-symbolic handler-equation layer (the frame-rule
-- re-base of the fixture-pinned equations; BPC proved end-to-end).
import GoLeanProofs.Specs.Raft.AllocEq
-- A4-U6: the remaining four re-bases + the re-sited fixture with the
-- non-identity placement witness.
import GoLeanProofs.Specs.Raft.AllocEqWave1
import GoLeanProofs.Specs.Raft.BpcResite
-- A4-U8: the lens instance table at the pinned tables (slice C) and
-- absState v2 (slice D — lens-consuming readers + L4 transports).
import GoLeanProofs.Specs.Raft.LensInst
import GoLeanProofs.Specs.Raft.AbsStateV2
-- A4-U8 part 2: the fixture re-siting consolidation (the U6 charter
-- residual): BC / Bf re-sited off the static locLit range with
-- placement-LIVE alloc equations. (MsResite — consumed only by
-- MsErrEquation — is in the corpus target with the A4-U25 split.)
import GoLeanProofs.Specs.Raft.Bc31Lit
import GoLeanProofs.Specs.Raft.Bc31
import GoLeanProofs.Specs.Raft.Bf31Lit
import GoLeanProofs.Specs.Raft.Bf31

/-!
# GoCore ⇒ Iris — the proof layer (root)

R3 REBUILD COMPLETE (2026-07-23, branch `reshape-smallstep`;
`docs/2026-07-23_reshape-r1r2-machine-design.md`): every stratum restored
over the fine-grained machine.

- **Infrastructure**: `Lang` (Config ⇒ Iris wiring), `HeapBridge`,
  `Ghost` (state interpretation, now pinning functions AND methods),
  `Lifting` (the four rule-agnostic step cores), `Inversions` (ONE
  generic `step_det` replaces the old per-form inversion family).
- **Laws/** — `Control` and `Init` (rules survived the reshape verbatim);
  NEW `Eval` (the expression-walk step laws — the machine's answer to
  `wp_bind`); `Assign`, `Call`, `Loop` rewritten as composed walks, each
  with same-commit witnesses (`wp_assign_lit`, the golden frame-entry
  instances, `wp_while_eq_once`).
- **Specs/** — `GoldenProgram` (the pure-syntax frontend pin),
  `GoldenSliceWP` (the golden walk: body lemmas + `wp_goldenCall`(/`_inv`)
  + `wp_goldenDriver`), `GoldenSurface` (all six step-0 targets
  re-proven).
- **Surface** stack — Layer S over the `execStmt`-shaped wrapper (two
  recorded statement deltas, both strengthenings: env as a wrapper
  argument after `ExecState.locals` died; the `HeapFrag` fragment
  side-condition retired because machine soundness is total),
  `SurfaceBridge` (untouched), `SurfaceExit` (fragment shape checks
  gone).
- `NegativeSpecs` — trivialization guards over the machine.

RETIRED at R3 (files deleted; the deleted content remains at git rev
5a9eab2 and in `Audit.lean`'s historical ledger): `Specs.Slice` and
`Specs.SliceCorrespondence` (the hand-model slice and its fragment-scoped
interpreter⇄relation bridge — superseded by the golden pipeline and the
total `stepFn_sound`/`step_complete`/`runConfig_sound`), `Specs.GoldenSlice`
(pin moved to `GoldenProgram`; walk rewritten in `GoldenSliceWP`; the
existential-address `*_computes` readouts superseded by the Surface
pinned forms).

The in-build gate is `Audit.lean` (a sibling default target); every module
here is in its sweep via the root import closure, which `scripts/ci`
enforces.
-/
