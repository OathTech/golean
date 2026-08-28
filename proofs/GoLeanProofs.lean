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
-- A4-U9's Sym.PickTransport lift DELETED at the arc-4 landing fix
-- round (unconsumed byte-identical duplicate of the RaftSeam
-- original; ledger row closed — see Audit/Kit.lean's tombstone).
import GoLeanProofs.Sym.SpillTransport
-- W0 RESET (2026-08-27, kill-list K-A executed in this commit; K-B/
-- K-C/K-D follow phase-by-phase): the fixed-trajectory era's literal
-- modules (57 Specs/Raft `*Lit*` + TwinCheckpoints(F); 1,184,100
-- lines) are DELETED, and every module in their import closure (the
-- handler-equation/fixture/round/seed chains, the round induction,
-- AbsStateV2 and the split donors) is unlinked from this root in the
-- same commit — the doomed files die in their own kill-list phases.
-- The era is preserved at archive/fixed-trajectory-era; the record is
-- docs/ARCHIVE.md. Nothing archived is ever cited by a proof.
-- A4-U14: the branch-crossing transport (path-condition splitting).
import GoLeanProofs.Sym.BranchTransport
-- W0 K-D: the Frame/Shape* splice-clause completeness layer (7
-- modules) is DELETED — layout-dependent, refuted at its one
-- chartered use (single-splice cannot place a pruned sub-fixture
-- into an interleaved outer frame; campaign log A4-U22). The
-- layout-free heap-quotient frame is the plan's replacement if/when
-- demanded. Archived.
import GoLeanProofs.SliceWalk
import GoLeanProofs.Specs.Raft.DriverNet
-- arc4b landing (C2c slice 0, per the lane's landing manifest): the native
-- S1/S2/S3 chain over the obligation signature (SC1 + C3 + C4).
-- W0 reset: NativeS1Witness/NativeS23Witness are RETAINED (professor
-- amendment) — the interface premises' non-vacuity demonstrations
-- until W5 supersedes them.
import GoLeanProofs.Specs.Raft.NativeObligations
import GoLeanProofs.Specs.Raft.NativeS23Route
import GoLeanProofs.Specs.Raft.NativeS1Chain
import GoLeanProofs.Specs.Raft.NativeEtcdDischarge
import GoLeanProofs.Specs.Raft.NativeS1CheckerLeaf
import GoLeanProofs.Specs.Raft.NativeS1Witness
import GoLeanProofs.Specs.Raft.NativeS23Chain
import GoLeanProofs.Specs.Raft.NativeS23Witness
import GoLeanProofs.Specs.Raft.NativeCheckerBridge
-- SP1 landing (arc4c lane) — FULLY RETIRED at the hygiene slice
-- (2026-08-28). The ChoiceInv statement layer went at the triage
-- (K-3, 2026-08-27: ChoiceInvariantToM had zero inhabitants and zero
-- consumers); the choice-erasure CARRIER itself (~/~ₘ, CForm, Mask —
-- Frame/ChoiceCanon.lean, 616 lines) is now DELETED too, by [USER]
-- ruling 2026-08-28: choice-invariance rolls up into the reasoning
-- layer — with a points-to, choices outside the footprint are
-- frame-irrelevant, so G-REPR's footprint subsumption replaces the
-- erasure instrument (iris-corpus plan §4.2, §6.3). Recoverable from
-- main's history at 05e81b70 (the pre-kill commit); see
-- docs/ARCHIVE.md. The parked SpanIso lane's `Mask` dependency
-- re-derives or harvests from that history at its resume.
-- A4-U8: the field-lens layer (Perennial Access lineage; general half —
-- combinators + L1-L4 laws).
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
-- Arc 2 U4: the verified fast-twin evaluator (route (d) — untrusted
-- method, never in any statement closure). KEPT (kill-list K-E): the
-- differential instrument's certified replay.
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
import GoLeanProofs.RunGlue
import GoLeanProofs.CondFor
import GoLeanProofs.Frame.Plug
import GoLeanProofs.Frame.PlugProbe
import GoLeanProofs.Frame.PlugWitness
import GoLeanProofs.Frame.PlugOps
import GoLeanProofs.Frame.PlugApply
import GoLeanProofs.Frame.PlugStep
import GoLeanProofs.Frame.PlugRule
import GoLeanProofs.Sym.ReflectConc
import GoLeanProofs.Specs.RaftPilot.InitSpec
-- # w3-m (the (M) mechanism — map-order pick-family composition;
-- design note docs/2026-08-27_m-mechanism-design.md; keep contiguous
-- — merged with the sibling lanes' additions by the coordinator)
import GoLeanProofs.MapPerm
import GoLeanProofs.Specs.Raft.MapPermRead
-- # w3-m end
import GoLeanProofs.Sym.KernelRfl
-- W3 crossing kit: data-branch window splits (path-condition
-- crossings; design note docs/2026-08-27_crossing-kit-design.md).
import GoLeanProofs.Sym.Crossing
import GoLeanProofs.Sym.CrossingWitness
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
-- Campaign Arc 4 (A4-U1 pilot): the seam's abstraction reader (v1) —
-- the pairing vocabulary's base (kill-list K-E keep).
import GoLeanProofs.Specs.Raft.AbsState
-- W0 K-C splits: the kept halves of the AbsStateV2/RoundStatement
-- donors — the rename-congruence lemmas (RenCongr), the v2 readers +
-- L4 transports (AbsStateV2), and the round-boundary twin reader
-- (AbsTwinRead). The pairing vocabulary, kill-list criterion (a).
import GoLeanProofs.Specs.Raft.RenCongr
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.AbsTwinRead
-- W3 U3.0b: the checker-state lens readers (leaderOf/byIndex/got/
-- cursors + the net entry-metadata reader) with their _ren
-- congruences and C1-definedness lemmas — the C3/C4 vocabulary.
import GoLeanProofs.Specs.Raft.AbsTwinCheckerRead
-- A4-U2 slice 1: the handler-fragment Sym extension (class 1, the
-- type-table input).
import GoLeanProofs.Sym.TableExt

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
