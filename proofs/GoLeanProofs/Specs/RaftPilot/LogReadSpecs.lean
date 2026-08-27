import GoLeanProofs.Specs.RaftPilot.SymBase
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Sym.KernelRfl

/-!
# W3 U3.1-F — the shared log/util read layer: `CallSpecR` instances

The first Wave 3.1 cluster (charter Amendment 1's partition table):
result-bearing CallSpecs for the raftLog/unstable/storage read family
that clusters C/D/E consume. This module holds the LANDED members;
the cluster's park record (per-function costing, the multi-window
data-branch pattern each parked member needs) lives in
`docs/w3-prover-log.md` §U3.1-F.

**QUANTIFIER AUDIT (per the charter's opening requirement):** each
CallSpecR here is a RULE discharging ∀-state at its callers' call
sites (∀ σ over the footprint family; ∀ plans/env/k — target- and
continuation-parametric; ∀ ch demonic; ∃ n) — consumed by the
cluster-C/D/E handler specs via `CallSpecR.consume`. No end-theorem
quantifier closes here.

**The pattern (the W1/W2 recipe at the result-bearing form):** the
spec is proved at the CANONICAL placement — the footprint cell at
`.base ⟨31⟩` (the first address above the twin's 31 globals, the
W2 layout-compliance rule: `bodies_inv` forces identity on 0..30,
so a compliant fixture keeps them free) — over an EXACT footprint
family (`uFam`) whose UNREAD positions are free `GoValue`/`Option Ty`
parameters (maximal width: any value shape rides opaquely through
the span) and whose READ positions carry the family's symbolic
scalars. The whole span closes by `kernel_rfl` at OPEN
`plans`/`env`/`k` (the W1 open-tail finding extended to the target
plans — the span never inspects them; reduction confirms it).
Placement transport to framed sites is the landed FrameSim +
plug-rule composition (the W2-gate recipe), applied by consumers.

**Statement hygiene:** the step counts (38/69) appear only in the
PRIVATE span lemmas (proof-body scaffolding, the W1 convention);
the exported `CallSpecR`s are count-free (∃ n). The addresses 31+
are canonical-placement constants (the layout-compliance rule), not
subject-run measurements; the field censuses are the pinned wire's
typeDefs (reflected-program shape constants).

LINEAGE: Hoare procedure specs by computational reflection
(certificate-style whole-span kernel reduction at open context —
the W1 pilot's route, at the `CallSpecR` form). No new mechanism
class.

Non-vacuity: `uFIPre_inhabited` (the ∃-discharge on concrete
values); the judgment form's first honest instance is
`unstable_maybeFirstIndex_callSpecR` itself.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The canonical unstable-read footprint family -/

/-- The `raft.unstable` embedded value at the family's parameters —
field census and order from the pinned wire's `raft.unstable`
typeDef. `snapshot` is the ONE pinned position (`.nil` — the T1
family: census §2.4, the snapshot family is dead; the invariant's C2
supplies exactly this); everything unread is free. -/
def unstableV (entsv offv sipv oipv ulgv : GoValue) : GoValue :=
  .struct ⟨"raft.unstable"⟩
    #[("snapshot", .nil),
      ("entries", entsv),
      ("offset", offv),
      ("snapshotInProgress", sipv),
      ("offsetInProgress", oipv),
      ("logger", ulgv)]

/-- The `raft.raftLog` cell value at the family's parameters — field
census and order from the pinned wire's `raft.raftLog` typeDef. -/
def logCellV (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv
    pzv : GoValue) : GoValue :=
  .struct ⟨"raft.raftLog"⟩
    #[("storage", stv),
      ("unstable", unstableV entsv offv sipv oipv ulgv),
      ("committed", cv),
      ("applying", apv),
      ("applied", adv),
      ("logger", lgv),
      ("maxApplyingEntsSize", mxv),
      ("applyingEntsSize", aszv),
      ("applyingEntsPaused", pzv)]

/-- **The canonical footprint family**: the raftLog cell at
`.base ⟨31⟩` (layout-compliant canonical anchor), the twin's pinned
tables, `nextAddr = 32`. One cell — the unstable read family's whole
footprint. -/
def uFam (dty : Option Ty)
    (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv :
      GoValue) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv entsv offv sipv oipv ulgv cv apv adv
            lgv mxv aszv pzv })]
      nextAddr := 32 }

/-- The receiver argument: `&l.unstable` at the canonical anchor (an
interior field location — the lowered `fieldAddr` shape every
unstable method receives). -/
def uArgV : GoValue :=
  .addr (Loc.field (Loc.base ⟨31⟩) ⟨"raft.raftLog"⟩ "unstable")

/-- The family's terminal state for the `maybeFirstIndex` span: the
footprint cell UNTOUCHED, plus the machine's own frame allocations —
the parameter cell (32) and the two pinned result cells (33/34)
carrying the nil-snapshot results `(0, false)`. -/
def uFamFI' (dty : Option Ty)
    (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv :
      GoValue) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv entsv offv sipv oipv ulgv cv apv adv
            lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := uArgV }),
       (Loc.base ⟨33⟩,
        { declaredTy := some (Ty.int .uint64)
          value := .int 0 .uint64 }),
       (Loc.base ⟨34⟩,
        { declaredTy := some Ty.bool
          value := .bool false })]
      nextAddr := 35 }

/-! ## `raft.unstable.maybeFirstIndex` (census: log_unstable.go:58;
reached by `raftLog.firstIndex` — cluster C/D/E's shared leaf) -/

/-- The whole `maybeFirstIndex` span at the nil-snapshot family
(PRIVATE count-bearing scaffolding — 38 machine steps, zero choices
consumed, at OPEN `plans`/`env`/`k`): frame entry, the snapshot≠nil
test (false), the result assignments `(0, false)`, return arrival at
the frame. -/
private theorem uFI_span (dty : Option Ty)
    (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv :
      GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 38
      (uFam dty stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv)
      (.retV uArgV
        (.callArgsK ⟨"raft.unstable.maybeFirstIndex"⟩ plans [] [] env k))
      ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩, Loc.base ⟨34⟩] [] k false),
        uFamFI' dty stv entsv offv sipv oipv ulgv cv apv adv lgv mxv
          aszv pzv,
        ch) := by
  kernel_rfl

/-- The footprint carrier (the precondition IS the exact family — the
`BfPre` shape at the result-bearing pattern; the invariant's C2
placement clause supplies it at use sites through FrameSim). -/
def UFIPre (dty : Option Ty)
    (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv :
      GoValue) (σm : ExecState) : Prop :=
  σm = uFam dty stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv
    pzv

/-- **THE `maybeFirstIndex` CallSpecR** (T1 family — snapshot nil):
at any family state, the call returns `(0, false)` — exactly the
subject's no-snapshot arm — with the footprint cell READ BACK
UNCHANGED (the read-only conclusion consumers chain on). ∀-state
over the family, ∀ plans/env/k, ∀ ch, ∃ n; count-free. -/
theorem unstable_maybeFirstIndex_callSpecR (dty : Option Ty)
    (stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv :
      GoValue) :
    CallSpecR
      (UFIPre dty stv entsv offv sipv oipv ulgv cv apv adv lgv mxv
        aszv pzv)
      ⟨"raft.unstable.maybeFirstIndex"⟩ [] uArgV
      (fun σ' vs =>
        vs = [.int 0 .uint64, .bool false] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv entsv offv sipv oipv ulgv cv
                     apv adv lgv mxv aszv pzv }) := by
  intro σ hP plans env k ch
  refine ⟨38,
    uFamFI' dty stv entsv offv sipv oipv ulgv cv apv adv lgv mxv aszv
      pzv,
    [Loc.base ⟨33⟩, Loc.base ⟨34⟩],
    [.int 0 .uint64, .bool false], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact uFI_span dty stv entsv offv sipv oipv ulgv cv apv adv lgv
      mxv aszv pzv plans env k ch
  · rfl
  · rfl

/-! ## `raft.unstable.maybeLastIndex` — the EMPTY-UNSTABLE member
(census: log_unstable.go:67)

PARTIAL COVERAGE, labeled at birth: this spec covers the
`len(u.entries) = 0 ∧ snapshot = nil` sub-family at a LIVE backing
slice (base `some b`, any offset/cap — the quiesced loop-head states,
every entry stabilized; the machine's `validateSlice` at the length
read forces the base constructor to be pinned — the nil-slice
sibling, the pre-first-append state, is a 5-line variant added on
consumer demand). The NONEMPTY arm is
PARKED with a record (W3 log §U3.1-F): its branch condition sits
under the machine's store-time `IntKind.normalize .int` on the free
length, which kernel reduction cannot decide — the arm needs the
bf-style multi-window chain (windows split at the branch, a
normalize-crossing lemma consuming a range premise), the same
mechanism every data-branching member of this cluster needs. Parking
the arm narrows the PREcondition family, never a conclusion. -/

/-- The empty-unstable terminal state: footprint untouched; param
cell (32), results `(0, false)` (33/34), and the body's `l` local
(35, the length read = 0). -/
def uFamLI0' (dty : Option Ty) (sb : Loc) (so sc : Nat)
    (stv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue) :
    ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv (.slice ⟨some sb, so, 0, sc⟩) offv sipv
            oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := uArgV }),
       (Loc.base ⟨33⟩,
        { declaredTy := some (Ty.int .uint64)
          value := .int 0 .uint64 }),
       (Loc.base ⟨34⟩,
        { declaredTy := some Ty.bool
          value := .bool false }),
       (Loc.base ⟨35⟩,
        { declaredTy := some (Ty.int .int)
          value := .int 0 .int })]
      nextAddr := 36 }

/-- The whole empty-arm span (PRIVATE count-bearing scaffolding — 69
machine steps, zero choices, open `plans`/`env`/`k`): frame entry,
`l := len(entries)` (0), the l≠0 test (false), the snapshot≠nil test
(false), results `(0, false)`, return arrival. -/
private theorem uLI0_span (dty : Option Ty) (sb : Loc)
    (so sc : Nat)
    (stv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 69
      (uFam dty stv (.slice ⟨some sb, so, 0, sc⟩) offv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv)
      (.retV uArgV
        (.callArgsK ⟨"raft.unstable.maybeLastIndex"⟩ plans [] [] env k))
      ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩, Loc.base ⟨34⟩] [] k false),
        uFamLI0' dty sb so sc stv offv sipv oipv ulgv cv apv adv lgv
          mxv aszv pzv,
        ch) := by
  kernel_rfl

/-- **THE `maybeLastIndex` CallSpecR, empty-unstable member**: at any
family state with no unstable entries and no pending snapshot, the
call returns `(0, false)` — the subject's fall-through arm — with the
footprint cell read back unchanged. (Partial coverage, labeled —
section note above.) -/
theorem unstable_maybeLastIndex_empty_callSpecR (dty : Option Ty)
    (sb : Loc) (so sc : Nat)
    (stv offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue) :
    CallSpecR
      (UFIPre dty stv (.slice ⟨some sb, so, 0, sc⟩) offv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv)
      ⟨"raft.unstable.maybeLastIndex"⟩ [] uArgV
      (fun σ' vs =>
        vs = [.int 0 .uint64, .bool false] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv (.slice ⟨some sb, so, 0, sc⟩) offv
                     sipv oipv ulgv cv apv adv lgv mxv aszv pzv }) := by
  intro σ hP plans env k ch
  refine ⟨69,
    uFamLI0' dty sb so sc stv offv sipv oipv ulgv cv apv adv lgv mxv
      aszv pzv,
    [Loc.base ⟨33⟩, Loc.base ⟨34⟩],
    [.int 0 .uint64, .bool false], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact uLI0_span dty sb so sc stv offv sipv oipv ulgv cv apv adv
      lgv mxv aszv pzv plans env k ch
  · rfl
  · rfl

/-- Non-vacuity of the footprint carrier (the ∃-discharge, concrete
values in every free slot). -/
theorem uFIPre_inhabited :
    UFIPre none (.nil) (.slice ⟨none, 0, 0, 0⟩) (.int 5 .uint64)
      (.bool false) (.int 5 .uint64) (.nil) (.int 3 .uint64)
      (.int 3 .uint64) (.int 3 .uint64) (.nil) (.int 1048576 .uint64)
      (.int 0 .uint64) (.bool false)
      (uFam none (.nil) (.slice ⟨none, 0, 0, 0⟩) (.int 5 .uint64)
        (.bool false) (.int 5 .uint64) (.nil) (.int 3 .uint64)
        (.int 3 .uint64) (.int 3 .uint64) (.nil) (.int 1048576 .uint64)
        (.int 0 .uint64) (.bool false)) := rfl

end GoLean.RaftSeam
