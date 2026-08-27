import GoLeanProofs.Specs.RaftPilot.SymBase
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.Sym.Crossing

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

/-! ## `raft.unstable.maybeLastIndex` — the NONEMPTY arm (the
crossing kit's first consumer; design note
`docs/2026-08-27_crossing-kit-design.md`)

The span has two kernel-stuck data points at a symbolic length
`k+1`: the `len` builtin's `validateSlice` (class 2) and the
store-normalized branch scalar at `l != 0` (class 1). The span is
split into three `kernel_rfl` windows; the crossings are
`stepFn_strict_apply` + `applyStrict_length_slice` (under the
`len ≤ cap` premise) and the normalize-collapse rewrite (under the
`len < 2^63` premise), after which the branch self-reduces. Range
premises are reader-vocabulary facts the invariant supplies. -/

section MaybeLastIndexNonempty

open GoLean.Surface

/-- The callee frame env after entry (probe-derived shape constant:
the three scopes of the lowered body). -/
private def uLIEnv3 : LocalEnv :=
  [[("l", Loc.base ⟨35⟩)], [],
   [("$res1", Loc.base ⟨34⟩), ("$res0", Loc.base ⟨33⟩),
    ("u", Loc.base ⟨32⟩)]]

private def uLIEnv2 : LocalEnv :=
  [[], [("$res1", Loc.base ⟨34⟩), ("$res0", Loc.base ⟨33⟩),
        ("u", Loc.base ⟨32⟩)]]

/-- The nonempty arm's then-block (reflected-program shape constant,
= the pinned wire's lowered body subterm). -/
private def uLIArm : Stmt :=
  .block #[] #[.seqn #[
    .assign (.var "$res0")
      (.sub
        (.add
          (.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
            ⟨"raft.unstable"⟩ "offset")
          (.convert (.int .uint64) (.var "l")))
        (.intLit 1 .uint64)),
    .assign (.var "$res1") (.boolLit true),
    .returnStmt]]

/-- The snapshot branch (dead in the T1 family — rides inertly in
the continuation). -/
private def uLISnapIf : Stmt :=
  .ifThenElse
    (.neqCmp (.pointer (.defined ⟨"raftpb.Snapshot"⟩))
      (.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
        ⟨"raft.unstable"⟩ "snapshot")
      (.nil none))
    (.block #[] #[
      .seqn #[
        .initialization
          ⟨"$c1087", .pointer (.defined ⟨"raftpb.SnapshotMetadata"⟩)⟩,
        .call #[.var "$c1087"] ⟨"raftpb.Snapshot.GetMetadata"⟩
          #[.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
              ⟨"raft.unstable"⟩ "snapshot"]],
      .seqn #[
        .initialization ⟨"$c1088", .int .uint64⟩,
        .call #[.var "$c1088"] ⟨"raftpb.SnapshotMetadata.GetIndex"⟩
          #[.var "$c1087"]],
      .seqn #[
        .assign (.var "$res0") (.var "$c1088"),
        .assign (.var "$res1") (.boolLit true),
        .returnStmt]])
    (.seqn #[])

private def uLITailSeq : Stmt :=
  .seqn #[
    .assign (.var "$res0") (.intLit 0 .uint64),
    .assign (.var "$res1") (.boolLit false),
    .returnStmt]

private def uLIIf1 : Stmt :=
  .ifThenElse (.neqCmp (.int .int) (.var "l") (.intLit 0 .int))
    uLIArm (.seqn #[])

/-- The continuation tower below the length read. -/
private def uLIK1 (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [uLIIf1] uLIEnv3
    (.seq [uLISnapIf, uLITailSeq] uLIEnv2
      (.frame plans env [Loc.base ⟨33⟩, Loc.base ⟨34⟩] [] k false))

/-- The store continuation the length result lands in. -/
private def uLIKrhs (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .rhsK .vals [.chain (.addr (Loc.base ⟨35⟩)) [] []] [] []
    (.seqn #[]) uLIEnv3 (uLIK1 plans env k)

/-- The branch boundary continuation (window 2's exit). -/
private def uLIKif (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK uLIArm (.seqn #[]) uLIEnv3
    (.seq [] uLIEnv3
      (.seq [uLISnapIf, uLITailSeq] uLIEnv2
        (.frame plans env [Loc.base ⟨33⟩, Loc.base ⟨34⟩] [] k false)))

/-- The in-span state former: footprint cell + the frame's cells at
their pinned addresses (param 32, results 33/34, the `l` local 35). -/
private def uFamLI1 (dty : Option Ty) (sb : Loc) (so ln sc : Nat)
    (offv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (r0 r1 lv : GoValue) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv (.slice ⟨some sb, so, ln, sc⟩) offv sipv
            oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := uArgV }),
       (Loc.base ⟨33⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨34⟩,
        { declaredTy := some Ty.bool, value := r1 }),
       (Loc.base ⟨35⟩,
        { declaredTy := some (Ty.int .int), value := lv })]
      nextAddr := 36 }

/-- Window 1 (PRIVATE count-bearing scaffolding — 18 steps, zero
choices, open `plans`/`env`/`k`, symbolic length/cap/offset): frame
entry, `l` initialization, the receiver walk, up to the config that
applies the `len` builtin (the class-2 stuck step). -/
private theorem uLI1_w1 (dty : Option Ty) (sb : Loc) (so kn sc : Nat)
    (off : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 18
      (uFam dty stv (.slice ⟨some sb, so, kn+1, sc⟩) (.int off .uint64)
        sipv oipv ulgv cv apv adv lgv mxv aszv pzv)
      (.retV uArgV
        (.callArgsK ⟨"raft.unstable.maybeLastIndex"⟩ plans [] [] env k))
      ch
      = .ok (.retV (.slice ⟨some sb, so, kn+1, sc⟩)
          (.strictK
            (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
            [] [] uLIEnv3 (uLIKrhs plans env k)),
        uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
          ulgv cv apv adv lgv mxv aszv pzv
          (.int 0 .uint64) (.bool false) (.int 0 .int),
        ch) := by
  kernel_rfl

/-- Window 2 (11 steps): store the length into `l` (the machine's
normalize), evaluate the branch condition, up to the `ifK` boundary
(the class-1 stuck step: the branch bool carries the stuck
normalize). -/
private theorem uLI1_w2 (dty : Option Ty) (sb : Loc) (so kn sc : Nat)
    (off : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 11
      (uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv
        (.int 0 .uint64) (.bool false) (.int 0 .int))
      (.retV (.int (Int.ofNat (kn+1)) .int) (uLIKrhs plans env k)) ch
      = .ok (.retV
          (.bool (!(IntKind.normalize .int (Int.ofNat (kn+1)) == 0)))
          (uLIKif plans env k),
        uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
          ulgv cv apv adv lgv mxv aszv pzv
          (.int 0 .uint64) (.bool false)
          (.int (IntKind.normalize .int (Int.ofNat (kn+1))) .int),
        ch) := by
  kernel_rfl

/-- Window 3 (41 steps, from the COLLAPSED branch boundary): the
branch self-reduces to the nonempty arm; offset read, the uint64
conversion/arithmetic (their normalizes ride as stuck payloads,
collapsed by the caller), result stores, return arrival. -/
private theorem uLI1_w3 (dty : Option Ty) (sb : Loc) (so kn sc : Nat)
    (off : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 41
      (uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv
        (.int 0 .uint64) (.bool false) (.int (Int.ofNat (kn+1)) .int))
      (.retV (.bool (!(Int.ofNat (kn+1) == 0))) (uLIKif plans env k))
      ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩, Loc.base ⟨34⟩] [] k false),
        uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
          ulgv cv apv adv lgv mxv aszv pzv
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (off + IntKind.normalize .uint64 (Int.ofNat (kn+1))) - 1)))
            .uint64)
          (.bool true) (.int (Int.ofNat (kn+1)) .int),
        ch) := by
  kernel_rfl

/-- **THE `maybeLastIndex` CallSpecR, nonempty member** (T1 family —
snapshot nil, `len = kn+1` entries at a live backing slice): the call
returns `(offset + len - 1, true)` — the subject's nonempty arm —
with the footprint cell read back unchanged. The range premises are
reader-vocabulary facts (`len ≤ cap` is slice well-formedness;
`len < 2^63` and the offset bounds are the log-size envelope the
invariant carries). Un-parks the U3.1-F nonempty arm via the
crossing kit. -/
theorem unstable_maybeLastIndex_nonempty_callSpecR (dty : Option Ty)
    (sb : Loc) (so kn sc : Nat) (off : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (hsc : kn + 1 ≤ sc) (hk : kn + 1 < 9223372036854775808)
    (hoff0 : 0 ≤ off)
    (hoffk : off + Int.ofNat (kn + 1) < 18446744073709551616) :
    CallSpecR
      (UFIPre dty stv (.slice ⟨some sb, so, kn+1, sc⟩)
        (.int off .uint64) sipv oipv ulgv cv apv adv lgv mxv aszv pzv)
      ⟨"raft.unstable.maybeLastIndex"⟩ [] uArgV
      (fun σ' vs =>
        vs = [.int (off + Int.ofNat (kn+1) - 1) .uint64, .bool true] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv
                     (.slice ⟨some sb, so, kn+1, sc⟩)
                     (.int off .uint64) sipv oipv ulgv cv apv adv lgv
                     mxv aszv pzv }) := by
  intro σ hP plans env k ch
  -- the collapse facts
  have hofc : Int.ofNat (kn + 1) = ((kn + 1 : Nat) : Int) := rfl
  have hcolI : IntKind.normalize .int (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_int_ofNat hk
  have hcolU : IntKind.normalize .uint64 (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_uint64_ofNat (by omega)
  have hcolA : IntKind.normalize .uint64 (off + Int.ofNat (kn+1))
      = off + Int.ofNat (kn+1) :=
    normalize_uint64_eq (by rw [hofc] at hoffk ⊢; omega)
      (by rw [hofc] at hoffk ⊢; omega)
  have hcolS : IntKind.normalize .uint64 (off + Int.ofNat (kn+1) - 1)
      = off + Int.ofNat (kn+1) - 1 :=
    normalize_uint64_eq (by rw [hofc] at hoffk ⊢; omega)
      (by rw [hofc] at hoffk ⊢; omega)
  -- the windows and crossings
  have h1 := uLI1_w1 dty sb so kn sc off stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv plans env k ch
  have hx : stepFn
      (uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv
        (.int 0 .uint64) (.bool false) (.int 0 .int))
      (.retV (.slice ⟨some sb, so, kn+1, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] uLIEnv3 (uLIKrhs plans env k))) ch
      = .ok (.retV (.int (Int.ofNat (kn+1)) .int) (uLIKrhs plans env k),
          uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv
            ulgv cv apv adv lgv mxv aszv pzv
            (.int 0 .uint64) (.bool false) (.int 0 .int),
          ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h2 := uLI1_w2 dty sb so kn sc off stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv plans env k ch
  rw [hcolI] at h2
  have h3 := uLI1_w3 dty sb so kn sc off stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv plans env k ch
  rw [hcolU, hcolA, hcolS, hcolS] at h3
  -- assemble
  refine ⟨18 + (1 + (11 + 41)),
    uFamLI1 dty sb so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
      cv apv adv lgv mxv aszv pzv
      (.int (off + Int.ofNat (kn+1) - 1) .uint64) (.bool true)
      (.int (Int.ofNat (kn+1)) .int),
    [Loc.base ⟨33⟩, Loc.base ⟨34⟩],
    [.int (off + Int.ofNat (kn+1) - 1) .uint64, .bool true], ch,
    ?_, ?_, ⟨rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1
      (stepFnIter_chain (stepFnIter_one hx) (stepFnIter_chain h2 h3))
  · rfl
  · rfl

end MaybeLastIndexNonempty

/-- **THE `maybeLastIndex` JOIN** (full T1-family coverage at a live
backing slice — the partial-coverage label of the empty member is
upgraded here): at ANY length `n`, the call returns the subject's arm
result — `(0, false)` when empty, `(offset + n - 1, true)` when not.
The two arms recombine by case analysis on `n` (the program's own
branch structure — the crossing kit's join rule; constructor-complete,
never a subject-run enumeration). -/
theorem unstable_maybeLastIndex_callSpecR (dty : Option Ty)
    (sb : Loc) (so n sc : Nat) (off : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (hsc : n ≤ sc) (hk : n < 9223372036854775808)
    (hoff0 : 0 ≤ off)
    (hoffn : off + Int.ofNat n < 18446744073709551616) :
    CallSpecR
      (UFIPre dty stv (.slice ⟨some sb, so, n, sc⟩)
        (.int off .uint64) sipv oipv ulgv cv apv adv lgv mxv aszv pzv)
      ⟨"raft.unstable.maybeLastIndex"⟩ [] uArgV
      (fun σ' vs =>
        vs = [.int (if n = 0 then 0 else off + Int.ofNat n - 1)
                .uint64,
              .bool (decide (n ≠ 0))] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv (.slice ⟨some sb, so, n, sc⟩)
                     (.int off .uint64) sipv oipv ulgv cv apv adv lgv
                     mxv aszv pzv }) := by
  cases n with
  | zero =>
      exact (unstable_maybeLastIndex_empty_callSpecR dty sb so sc stv
        (.int off .uint64) sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv).conseq (fun σ h => h) (fun σ vs h => by
          simpa using h)
  | succ kn =>
      exact (unstable_maybeLastIndex_nonempty_callSpecR dty sb so kn sc
        off stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv hsc hk hoff0
        hoffn).conseq (fun σ h => h) (fun σ vs h => by
          simpa using h)

/-! ## `raft.unstable.maybeTerm` (census: log_unstable.go:82) — the
kit's SYMBOLIC-COMPARISON consumer

The T1 family (snapshot nil) at the canonical placement extended
with the entry-storage cells: backing array at `.base ⟨32⟩`, one
entry cell at `.base ⟨33⟩` (field census from the pinned wire's
`raftpb.Entry` typeDef — the proto-optional fields are POINTERS:
`Term : *uint64`), the Term target at `.base ⟨34⟩`. Cells 32-34 ride
FREE (any `HeapCell`) in the members that never read them.

The branch `i < u.offset` compares two free scalars — undecidable by
reduction at any window; the crossing is `stepFn_ifK_true/false`
under a `decide`-bridged reader-vocabulary range fact (the kit's
class-A route). Members are PER-ARM (the path-condition split at the
spec boundary — the program's own branch structure); the in-range
arm additionally consumes the class-2/3 read crossings. -/

section MaybeTerm

open GoLean.Surface

/-- The maybeTerm footprint family former: the raftLog cell at the
canonical anchor with the entries slice based at `.base ⟨32⟩`;
cells 32/33/34 are free `HeapCell` parameters (pinned by the members
that read them). -/
def mtFam (dty : Option Ty) (so ln sc : Nat) (offv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
            offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32), (Loc.base ⟨33⟩, c33),
       (Loc.base ⟨34⟩, c34)]
      nextAddr := 35 }

/-- The footprint carrier for the maybeTerm members. -/
def MTPre (dty : Option Ty) (so ln sc : Nat) (offv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell) (σm : ExecState) : Prop :=
  σm = mtFam dty so ln sc offv stv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv c32 c33 c34

/-- The callee frame env (probe-derived shape constant). -/
private def mtEnv : LocalEnv :=
  [[], [("$res1", Loc.base ⟨38⟩), ("$res0", Loc.base ⟨37⟩),
        ("i", Loc.base ⟨36⟩), ("u", Loc.base ⟨35⟩)]]

private def mtRet0 : Stmt :=
  .seqn #[.assign (.var "$res0") (.intLit 0 .uint64),
          .assign (.var "$res1") (.boolLit false),
          .returnStmt]

/-- The below-offset arm's block (reflected-program shape constant). -/
private def mtArmA : Stmt :=
  .block #[] #[
    .seqn #[.initialization ⟨"$c1091", .bool⟩,
      .assign (.var "$c1091")
        (.neqCmp (.pointer (.defined ⟨"raftpb.Snapshot"⟩))
          (.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
            ⟨"raft.unstable"⟩ "snapshot")
          (.nil none))],
    .ifThenElse (.var "$c1091")
      (.block #[] #[
        .seqn #[
          .initialization
            ⟨"$c1089", .pointer (.defined ⟨"raftpb.SnapshotMetadata"⟩)⟩,
          .call #[.var "$c1089"] ⟨"raftpb.Snapshot.GetMetadata"⟩
            #[.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
                ⟨"raft.unstable"⟩ "snapshot"]],
        .seqn #[
          .initialization ⟨"$c1090", .int .uint64⟩,
          .call #[.var "$c1090"] ⟨"raftpb.SnapshotMetadata.GetIndex"⟩
            #[.var "$c1089"]],
        .seqn #[.assign (.var "$c1091")
          (.eqCmp (.int .uint64) (.var "$c1090") (.var "i"))]])
      (.seqn #[]),
    .ifThenElse (.var "$c1091")
      (.block #[] #[
        .seqn #[
          .initialization
            ⟨"$c1092", .pointer (.defined ⟨"raftpb.SnapshotMetadata"⟩)⟩,
          .call #[.var "$c1092"] ⟨"raftpb.Snapshot.GetMetadata"⟩
            #[.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
                ⟨"raft.unstable"⟩ "snapshot"]],
        .seqn #[
          .initialization ⟨"$c1093", .int .uint64⟩,
          .call #[.var "$c1093"] ⟨"raftpb.SnapshotMetadata.GetTerm"⟩
            #[.var "$c1092"]],
        .seqn #[.assign (.var "$res0") (.var "$c1093"),
          .assign (.var "$res1") (.boolLit true),
          .returnStmt]])
      (.seqn #[]),
    mtRet0]

private def mtCallSeq : Stmt :=
  .seqn #[.initialization ⟨"last", .int .uint64⟩,
          .initialization ⟨"ok", .bool⟩,
          .call #[.var "last", .var "ok"]
            ⟨"raft.unstable.maybeLastIndex"⟩ #[.var "u"]]

private def mtRet0Block : Stmt := .block #[] #[mtRet0]

private def mtIfNotOk : Stmt :=
  .ifThenElse (.not (.var "ok")) mtRet0Block (.seqn #[])

private def mtIfGt : Stmt :=
  .ifThenElse (.greaterCmp (.var "i") (.var "last")) mtRet0Block
    (.seqn #[])

private def mtIdxSeq : Stmt :=
  .seqn #[.initialization ⟨"$c1094", .int .uint64⟩,
    .call #[.var "$c1094"] ⟨"raftpb.Entry.GetTerm"⟩
      #[.indexGet
          (.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
            ⟨"raft.unstable"⟩ "entries")
          (.sub (.var "i")
            (.fieldGet (.deref (.var "u") (.defined ⟨"raft.unstable"⟩))
              ⟨"raft.unstable"⟩ "offset"))]]

private def mtResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c1094"),
          .assign (.var "$res1") (.boolLit true),
          .returnStmt]

/-- The continuation below the `i < offset` branch boundary. -/
private def mtKif (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK mtArmA (.seqn #[]) mtEnv
    (.seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq] mtEnv
      (.frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k false))

/-- The in-span state former (frame cells 35-38 + optional extras). -/
private def mtFamIn (dty : Option Ty) (so ln sc : Nat) (offv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell) (iv r0 r1 : GoValue) (extra : Heap)
    (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV stv (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
            offv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32), (Loc.base ⟨33⟩, c33),
       (Loc.base ⟨34⟩, c34),
       (Loc.base ⟨35⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := uArgV }),
       (Loc.base ⟨36⟩,
        { declaredTy := some (Ty.int .uint64), value := iv }),
       (Loc.base ⟨37⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨38⟩,
        { declaredTy := some Ty.bool, value := r1 })] ++ extra
      nextAddr := na }

/-- Window 1 (13 steps): frame entry (the `i` argument stored
normalized — the class-1 stuck payload), the offset read, the
comparison, up to the `i < offset` branch boundary. -/
private theorem mtA_w1 (dty : Option Ty) (so ln sc : Nat)
    (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 13
      (mtFam dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv apv
        adv lgv mxv aszv pzv c32 c33 c34)
      (.retV (.int ii .uint64)
        (.callArgsK ⟨"raft.unstable.maybeTerm"⟩ plans [uArgV] [] env k))
      ch
      = .ok (.retV
          (.bool (decide (IntKind.normalize .uint64 ii < off)))
          (mtKif plans env k),
        mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv
          apv adv lgv mxv aszv pzv c32 c33 c34
          (.int (IntKind.normalize .uint64 ii) .uint64)
          (.int 0 .uint64) (.bool false) [] 39,
        ch) := by
  kernel_rfl

/-- Window 2 of the below-offset arm (56 steps, from the crossed
branch): the snapshot test (nil — reduces), the two dead metadata
branches, `(0, false)`, return arrival. -/
private theorem mtA_w2 (dty : Option Ty) (so ln sc : Nat)
    (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 56
      (mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false) [] 39)
      (.exec mtArmA mtEnv
        (.seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq] mtEnv
          (.frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k false)))
      ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k false),
        mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv
          apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          [(Loc.base ⟨39⟩,
            { declaredTy := some Ty.bool, value := .bool false })] 40,
        ch) := by
  kernel_rfl

/-- **THE `maybeTerm` CallSpecR, below-offset member** (T1 family —
snapshot nil; the compacted-index read): under the reader-vocabulary
range facts `0 ≤ i < 2^64` and `i < offset`, the call returns
`(0, false)` — the subject's compacted arm — with the footprint cell
read back unchanged. Cells 32-34 ride free (never read on this
path). The `i < offset` crossing is the kit's class-A rule at a
genuinely symbolic two-scalar comparison. -/
theorem unstable_maybeTerm_below_callSpecR (dty : Option Ty)
    (so ln sc : Nat) (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (hii0 : 0 ≤ ii) (hii64 : ii < 18446744073709551616)
    (hlt : ii < off) :
    CallSpecR
      (MTPre dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv apv
        adv lgv mxv aszv pzv c32 c33 c34)
      ⟨"raft.unstable.maybeTerm"⟩ [uArgV] (.int ii .uint64)
      (fun σ' vs =>
        vs = [.int 0 .uint64, .bool false] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv
                     (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
                     (.int off .uint64) sipv oipv ulgv cv apv adv lgv
                     mxv aszv pzv }) := by
  intro σ hP plans env k ch
  have hcol : IntKind.normalize .uint64 ii = ii :=
    normalize_uint64_eq hii0 hii64
  have h1 := mtA_w1 dty so ln sc off ii stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv c32 c33 c34 plans env k ch
  rw [hcol] at h1
  have hx : stepFn
      (mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false) [] 39)
      (.retV (.bool (decide (ii < off))) (mtKif plans env k)) ch
      = .ok (.exec mtArmA mtEnv
          (.seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq]
            mtEnv
            (.frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k
              false)),
        mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv
          apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false) [] 39,
        ch) :=
    stepFn_ifK_true (decide_eq_true hlt)
  have h2 := mtA_w2 dty so ln sc off ii stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv c32 c33 c34 plans env k ch
  refine ⟨13 + (1 + 56),
    mtFamIn dty so ln sc (.int off .uint64) stv sipv oipv ulgv cv apv
      adv lgv mxv aszv pzv c32 c33 c34
      (.int ii .uint64) (.int 0 .uint64) (.bool false)
      [(Loc.base ⟨39⟩,
        { declaredTy := some Ty.bool, value := .bool false })] 40,
    [Loc.base ⟨37⟩, Loc.base ⟨38⟩],
    [.int 0 .uint64, .bool false], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx) h2)
  · rfl
  · rfl

/-! ### The ≥offset arms (the inner `maybeLastIndex` call INLINED —
within-family composition re-walks the callee at the caller's
extended heap; the callee's own two crossings recur and are crossed
by the same kit pieces) -/

private def mtInEnv3 : LocalEnv :=
  [[("l", Loc.base ⟨44⟩)], [],
   [("$res1", Loc.base ⟨43⟩), ("$res0", Loc.base ⟨42⟩),
    ("u", Loc.base ⟨41⟩)]]

private def mtInEnv2 : LocalEnv :=
  [[], [("$res1", Loc.base ⟨43⟩), ("$res0", Loc.base ⟨42⟩),
        ("u", Loc.base ⟨41⟩)]]

private def mtEnvOk : LocalEnv :=
  [[("ok", Loc.base ⟨40⟩), ("last", Loc.base ⟨39⟩)],
   [("$res1", Loc.base ⟨38⟩), ("$res0", Loc.base ⟨37⟩),
    ("i", Loc.base ⟨36⟩), ("u", Loc.base ⟨35⟩)]]

private def mtEnvC : LocalEnv :=
  [[("$c1094", Loc.base ⟨45⟩), ("ok", Loc.base ⟨40⟩),
    ("last", Loc.base ⟨39⟩)],
   [("$res1", Loc.base ⟨38⟩), ("$res0", Loc.base ⟨37⟩),
    ("i", Loc.base ⟨36⟩), ("u", Loc.base ⟨35⟩)]]

private def mtKfr (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k false

private def mtKafter (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq] mtEnvOk
    (mtKfr plans env k)

private def mtInFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "last"]), (.chain [], [.ref "ok"])]
    mtEnvOk [Loc.base ⟨42⟩, Loc.base ⟨43⟩] []
    (mtKafter plans env k) false

private def mtInKrhs (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .rhsK .vals [.chain (.addr (Loc.base ⟨44⟩)) [] []] [] []
    (.seqn #[]) mtInEnv3
    (.seq [uLIIf1] mtInEnv3
      (.seq [uLISnapIf, uLITailSeq] mtInEnv2 (mtInFrame plans env k)))

private def mtInKif (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK uLIArm (.seqn #[]) mtInEnv3
    (.seq [] mtInEnv3
      (.seq [uLISnapIf, uLITailSeq] mtInEnv2 (mtInFrame plans env k)))

private def mtKgt (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK mtRet0Block (.seqn #[]) mtEnvOk
    (.seq [mtIdxSeq, mtResSeq] mtEnvOk (mtKfr plans env k))

private def mtKidx (so ln sc : Nat)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) : Cont :=
  .strictK .indexGet [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] []
    mtEnvC
    (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
      [(.chain [], [.ref "$c1094"])] [] [] mtEnvC
      (.seq [mtResSeq] mtEnvC (mtKfr plans env k)))

/-- The inner-call frame cell block (39-44), parameterized by the
`last`/`ok` cells and the inner results/local. -/
private def mtInCells (lastv okv r0'v r1'v lv : GoValue) : Heap :=
  [(Loc.base ⟨39⟩,
    { declaredTy := some (Ty.int .uint64), value := lastv }),
   (Loc.base ⟨40⟩, { declaredTy := some Ty.bool, value := okv }),
   (Loc.base ⟨41⟩,
    { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
      value := uArgV }),
   (Loc.base ⟨42⟩,
    { declaredTy := some (Ty.int .uint64), value := r0'v }),
   (Loc.base ⟨43⟩, { declaredTy := some Ty.bool, value := r1'v }),
   (Loc.base ⟨44⟩,
    { declaredTy := some (Ty.int .int), value := lv })]

/-- Window 2 of the ≥offset path (28 steps, from the crossed
`i < offset` branch, FALSE arm): `last`/`ok` initialization, the
inner `maybeLastIndex` call entry, up to the inner length-read
boundary (the class-2 stuck step, again). -/
private theorem mtB_w2 (dty : Option Ty) (so kn sc : Nat)
    (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 28
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false) [] 39)
      (.exec (.seqn #[]) mtEnv
        (.seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq] mtEnv
          (mtKfr plans env k))) ch
      = .ok (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
          (.strictK
            (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
            [] [] mtInEnv3 (mtInKrhs plans env k)),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
            (.bool false) (.int 0 .int)) 45,
        ch) := by
  kernel_rfl

/-- Window 3 (11 steps): the inner length store + inner branch
condition, to the inner `ifK` boundary (class-1 stuck bool). -/
private theorem mtB_w3 (dty : Option Ty) (so kn sc : Nat)
    (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 11
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
          (.bool false) (.int 0 .int)) 45)
      (.retV (.int (Int.ofNat (kn+1)) .int) (mtInKrhs plans env k)) ch
      = .ok (.retV
          (.bool (!(IntKind.normalize .int (Int.ofNat (kn+1)) == 0)))
          (mtInKif plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
            (.bool false)
            (.int (IntKind.normalize .int (Int.ofNat (kn+1))) .int))
          45,
        ch) := by
  kernel_rfl

/-- Window 4 (64 steps, from the COLLAPSED inner branch): the inner
nonempty arm (offset arithmetic riding as stuck normalizes), inner
return + frame exit, the `last`/`ok` stores, `!ok` (reduces), the
comparison, up to the `i > last` boundary (class-A stuck: two
symbolic scalars). -/
private theorem mtB_w4 (dty : Option Ty) (so kn sc : Nat)
    (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 64
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
          (.bool false) (.int (Int.ofNat (kn+1)) .int)) 45)
      (.retV (.bool (!(Int.ofNat (kn+1) == 0))) (mtInKif plans env k))
      ch
      = .ok (.retV
          (.bool (decide (ii >
            IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (off + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                    - 1))))))
          (mtKgt plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells
            (.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (off + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                    - 1)))) .uint64)
            (.bool true)
            (.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (off + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                  - 1))) .uint64)
            (.bool true) (.int (Int.ofNat (kn+1)) .int)) 45,
        ch) := by
  kernel_rfl

/-- Window 5 of the above-last arm (25 steps, from the crossed
`i > last` branch, TRUE arm): `(0, false)`, return arrival. -/
private theorem mtB_w5 (dty : Option Ty) (so kn sc : Nat)
    (off ii lastv : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 25
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int lastv .uint64) (.bool true)
          (.int lastv .uint64) (.bool true)
          (.int (Int.ofNat (kn+1)) .int)) 45)
      (.exec mtRet0Block mtEnvOk
        (.seq [mtIdxSeq, mtResSeq] mtEnvOk (mtKfr plans env k))) ch
      = .ok (.returning (mtKfr plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells (.int lastv .uint64) (.bool true)
            (.int lastv .uint64) (.bool true)
            (.int (Int.ofNat (kn+1)) .int)) 45,
        ch) := by
  kernel_rfl

/-- **THE `maybeTerm` CallSpecR, above-last member** (T1 nonempty
family): under `offset ≤ i` and `i > offset + len - 1`, the call
returns `(0, false)` — the subject's out-of-range arm. Consumes THREE
kit crossings (the two symbolic comparisons + the inner length read)
and the collapse family. -/
theorem unstable_maybeTerm_aboveLast_callSpecR (dty : Option Ty)
    (so kn sc : Nat) (off ii : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (hsc : kn + 1 ≤ sc) (hk : kn + 1 < 9223372036854775808)
    (hoff0 : 0 ≤ off)
    (hoffk : off + Int.ofNat (kn + 1) < 18446744073709551616)
    (hii64 : ii < 18446744073709551616)
    (hge : off ≤ ii)
    (hgt : ii > off + Int.ofNat (kn + 1) - 1) :
    CallSpecR
      (MTPre dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv c32 c33 c34)
      ⟨"raft.unstable.maybeTerm"⟩ [uArgV] (.int ii .uint64)
      (fun σ' vs =>
        vs = [.int 0 .uint64, .bool false] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv
                     (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
                     (.int off .uint64) sipv oipv ulgv cv apv adv lgv
                     mxv aszv pzv }) := by
  intro σ hP plans env k ch
  have hofc := int_ofNat_cast (kn + 1)
  -- collapses
  have hcolIi : IntKind.normalize .uint64 ii = ii :=
    normalize_uint64_eq (by omega) hii64
  have hcolI : IntKind.normalize .int (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_int_ofNat hk
  have hcolU : IntKind.normalize .uint64 (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_uint64_ofNat (by omega)
  have hcolA : IntKind.normalize .uint64 (off + Int.ofNat (kn+1))
      = off + Int.ofNat (kn+1) :=
    normalize_uint64_eq (by rw [hofc]; omega) (by rw [hofc] at hoffk ⊢; omega)
  have hcolS : IntKind.normalize .uint64 (off + Int.ofNat (kn+1) - 1)
      = off + Int.ofNat (kn+1) - 1 :=
    normalize_uint64_eq (by rw [hofc]; omega) (by rw [hofc] at hoffk ⊢; omega)
  -- windows
  have h1 := mtA_w1 dty so (kn+1) sc off ii stv sipv oipv ulgv cv apv
    adv lgv mxv aszv pzv c32 c33 c34 plans env k ch
  rw [hcolIi] at h1
  have hx1 :=
    stepFn_ifK_false (b := decide (ii < off)) (t := mtArmA)
      (e := .seqn #[]) (env := mtEnv)
      (k := .seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq]
        mtEnv (mtKfr plans env k))
      (σ := mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false) [] 39)
      (ch := ch)
      (decide_eq_false (by omega))
  have h2 := mtB_w2 dty so kn sc off ii stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv c32 c33 c34 plans env k ch
  have hx2 : stepFn
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
          (.bool false) (.int 0 .int)) 45)
      (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] mtInEnv3 (mtInKrhs plans env k))) ch
      = .ok (.retV (.int (Int.ofNat (kn+1)) .int)
          (mtInKrhs plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
            (.bool false) (.int 0 .int)) 45,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h3 := mtB_w3 dty so kn sc off ii stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv c32 c33 c34 plans env k ch
  rw [hcolI] at h3
  have h4 := mtB_w4 dty so kn sc off ii stv sipv oipv ulgv cv apv adv
    lgv mxv aszv pzv c32 c33 c34 plans env k ch
  rw [hcolU, hcolA, hcolS, hcolS, hcolS] at h4
  have hx3 :=
    stepFn_ifK_true (b := decide (ii > off + Int.ofNat (kn+1) - 1))
      (t := mtRet0Block) (e := .seqn #[]) (env := mtEnvOk)
      (k := .seq [mtIdxSeq, mtResSeq] mtEnvOk (mtKfr plans env k))
      (σ := mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (Int.ofNat (kn+1)) .int)) 45)
      (ch := ch)
      (decide_eq_true hgt)
  have h5 := mtB_w5 dty so kn sc off ii (off + Int.ofNat (kn+1) - 1)
    stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv c32 c33 c34 plans
    env k ch
  refine ⟨13 + (1 + (28 + (1 + (11 + (64 + (1 + 25)))))),
    mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv cv
      apv adv lgv mxv aszv pzv c32 c33 c34
      (.int ii .uint64) (.int 0 .uint64) (.bool false)
      (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
        (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
        (.bool true) (.int (Int.ofNat (kn+1)) .int)) 45,
    [Loc.base ⟨37⟩, Loc.base ⟨38⟩],
    [.int 0 .uint64, .bool false], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2)
        (stepFnIter_chain h3 (stepFnIter_chain h4
          (stepFnIter_chain (stepFnIter_one hx3) h5))))))
  · rfl
  · rfl

/-! ### The in-range arm (the class-3 symbolic-heap read: the
backing-array read outcome is a family-carried hypothesis) -/

private def mtKgetterm (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetTerm"⟩
    [(.chain [], [.ref "$c1094"])] [] [] mtEnvC
    (.seq [mtResSeq] mtEnvC (mtKfr plans env k))

private def mtArrCell (adty : Option Ty) (values : Array GoValue) :
    HeapCell :=
  { declaredTy := adty, value := .array values }

private def mtTermCell (tdty : Option Ty) (tv : Int) : HeapCell :=
  { declaredTy := tdty, value := .int tv .uint64 }

/-- The pinned entry cell (field census from the wire's
`raftpb.Entry` typeDef; the proto-optional `Term` is a pointer —
target pinned at the canonical `.base ⟨34⟩`; the other fields ride
free). -/
private def mtEntryCell (edty : Option Ty) (ivv typv dvv : GoValue) :
    HeapCell :=
  { declaredTy := edty
    value := .struct ⟨"raftpb.Entry"⟩
      #[("Term", .addr (Loc.base ⟨34⟩)), ("Index", ivv),
        ("Type", typv), ("Data", dvv)] }

/-- Window 5 of the in-range arm (23 steps, from the crossed
`i > last` branch, FALSE arm): `$c1094` initialization, the entries
read, the index subtraction (its normalize riding), up to the
`indexGet` boundary (the class-2/3 stuck step). -/
private theorem mtC_w5 (dty : Option Ty) (so kn sc : Nat)
    (off ii lastv : Int)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 c33 c34 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 23
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32 c33 c34
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int lastv .uint64) (.bool true)
          (.int lastv .uint64) (.bool true)
          (.int (Int.ofNat (kn+1)) .int)) 45)
      (.exec (.seqn #[]) mtEnvOk
        (.seq [mtIdxSeq, mtResSeq] mtEnvOk (mtKfr plans env k))) ch
      = .ok (.retV
          (.int (IntKind.normalize .uint64 (ii - off)) .uint64)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩] [] mtEnvC
            (mtKgetterm plans env k)),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32 c33 c34
          (.int ii .uint64) (.int 0 .uint64) (.bool false)
          (mtInCells (.int lastv .uint64) (.bool true)
            (.int lastv .uint64) (.bool true)
            (.int (Int.ofNat (kn+1)) .int) ++
           [(Loc.base ⟨45⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int 0 .uint64 })]) 46,
        ch) := by
  kernel_rfl

/-- Window 6 of the in-range arm (73 steps, from the crossed index
read): the `GetTerm` call on the (concrete-addressed) entry cell —
the nil checks reduce, the two Term dereferences read the pinned
cells, result stores (normalizes riding), return arrival. -/
private theorem mtC_w6 (dty : Option Ty) (so kn sc : Nat)
    (off ii lastv tv : Int) (edty tdty : Option Ty)
    (ivv typv dvv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (c32 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 73
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv c32
        (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int ii .uint64) (.int 0 .uint64) (.bool false)
        (mtInCells (.int lastv .uint64) (.bool true)
          (.int lastv .uint64) (.bool true)
          (.int (Int.ofNat (kn+1)) .int) ++
         [(Loc.base ⟨45⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 46)
      (.retV (.addr (Loc.base ⟨33⟩)) (mtKgetterm plans env k)) ch
      = .ok (.returning (mtKfr plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv c32
          (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
          (.int ii .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 tv)))
            .uint64)
          (.bool true)
          (mtInCells (.int lastv .uint64) (.bool true)
            (.int lastv .uint64) (.bool true)
            (.int (Int.ofNat (kn+1)) .int) ++
           [(Loc.base ⟨45⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int (IntKind.normalize .uint64
                 (IntKind.normalize .uint64 tv)) .uint64 }),
            (Loc.base ⟨46⟩,
             { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
               value := .addr (Loc.base ⟨33⟩) }),
            (Loc.base ⟨47⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int (IntKind.normalize .uint64 tv) .uint64 })])
          48,
        ch) := by
  kernel_rfl

/-- **THE `maybeTerm` CallSpecR, in-range member** (T1 nonempty
family; `i = offset + j`, `j < len`): the call returns
`(entry.Term, true)` — the subject's unstable-read arm — with the
footprint read back unchanged. The backing-array read is a
family-carried hypothesis (`hget`, the class-3 symbolic-heap-read
discipline); the entry/Term cells sit at the canonical addresses
32-34 with free payloads. -/
theorem unstable_maybeTerm_inRange_callSpecR (dty : Option Ty)
    (so kn sc : Nat) (off tv : Int) (j : Nat)
    (adty edty tdty : Option Ty) (values : Array GoValue)
    (ivv typv dvv : GoValue)
    (stv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (hsc : kn + 1 ≤ sc) (hk : kn + 1 < 9223372036854775808)
    (hoff0 : 0 ≤ off)
    (hoffk : off + Int.ofNat (kn + 1) < 18446744073709551616)
    (hj : j < kn + 1)
    (hget : values[so + j]? = some (.addr (Loc.base ⟨33⟩)))
    (htv0 : 0 ≤ tv) (htv64 : tv < 18446744073709551616) :
    CallSpecR
      (MTPre dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv cv
        apv adv lgv mxv aszv pzv
        (mtArrCell adty values) (mtEntryCell edty ivv typv dvv)
        (mtTermCell tdty tv))
      ⟨"raft.unstable.maybeTerm"⟩ [uArgV]
      (.int (off + Int.ofNat j) .uint64)
      (fun σ' vs =>
        vs = [.int tv .uint64, .bool true] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV stv
                     (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
                     (.int off .uint64) sipv oipv ulgv cv apv adv lgv
                     mxv aszv pzv }) := by
  intro σ hP plans env k ch
  have hofc := int_ofNat_cast (kn + 1)
  have hofj := int_ofNat_cast j
  -- collapses
  have hcolIi : IntKind.normalize .uint64 (off + Int.ofNat j)
      = off + Int.ofNat j :=
    normalize_uint64_eq (by rw [hofj]; omega)
      (by rw [hofj]; rw [hofc] at hoffk; omega)
  have hcolI : IntKind.normalize .int (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_int_ofNat hk
  have hcolU : IntKind.normalize .uint64 (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_uint64_ofNat (by omega)
  have hcolA : IntKind.normalize .uint64 (off + Int.ofNat (kn+1))
      = off + Int.ofNat (kn+1) :=
    normalize_uint64_eq (by rw [hofc]; omega) (by rw [hofc] at hoffk ⊢; omega)
  have hcolS : IntKind.normalize .uint64 (off + Int.ofNat (kn+1) - 1)
      = off + Int.ofNat (kn+1) - 1 :=
    normalize_uint64_eq (by rw [hofc]; omega) (by rw [hofc] at hoffk ⊢; omega)
  have hcolT : IntKind.normalize .uint64 tv = tv :=
    normalize_uint64_eq htv0 htv64
  have hcolJ : IntKind.normalize .uint64 (Int.ofNat j)
      = Int.ofNat j := normalize_uint64_ofNat (by omega)
  have hsubj : (off + Int.ofNat j) - off = Int.ofNat j := by
    rw [hofj]; omega
  -- windows and crossings
  have h1 := mtA_w1 dty so (kn+1) sc off (off + Int.ofNat j) stv sipv
    oipv ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv) plans env k ch
  rw [hcolIi] at h1
  have hx1 :=
    stepFn_ifK_false (b := decide ((off + Int.ofNat j) < off))
      (t := mtArmA) (e := .seqn #[]) (env := mtEnv)
      (k := .seq [mtCallSeq, mtIfNotOk, mtIfGt, mtIdxSeq, mtResSeq]
        mtEnv (mtKfr plans env k))
      (σ := mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
        (.bool false) [] 39)
      (ch := ch)
      (decide_eq_false (by rw [hofj]; omega))
  have h2 := mtB_w2 dty so kn sc off (off + Int.ofNat j) stv sipv oipv
    ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv) plans env k ch
  have hx2 : stepFn
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
        (.bool false)
        (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
          (.bool false) (.int 0 .int)) 45)
      (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] mtInEnv3 (mtInKrhs plans env k))) ch
      = .ok (.retV (.int (Int.ofNat (kn+1)) .int)
          (mtInKrhs plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
          (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
          (.bool false)
          (mtInCells (.int 0 .uint64) (.bool false) (.int 0 .uint64)
            (.bool false) (.int 0 .int)) 45,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h3 := mtB_w3 dty so kn sc off (off + Int.ofNat j) stv sipv oipv
    ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv) plans env k ch
  rw [hcolI] at h3
  have h4 := mtB_w4 dty so kn sc off (off + Int.ofNat j) stv sipv oipv
    ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv) plans env k ch
  rw [hcolU, hcolA, hcolS, hcolS, hcolS] at h4
  have hx3 :=
    stepFn_ifK_false
      (b := decide ((off + Int.ofNat j) > off + Int.ofNat (kn+1) - 1))
      (t := mtRet0Block) (e := .seqn #[]) (env := mtEnvOk)
      (k := .seq [mtIdxSeq, mtResSeq] mtEnvOk (mtKfr plans env k))
      (σ := mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv
        ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
        (.bool false)
        (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (Int.ofNat (kn+1)) .int)) 45)
      (ch := ch)
      (decide_eq_false (by rw [hofj, hofc]; omega))
  have h5 := mtC_w5 dty so kn sc off (off + Int.ofNat j)
    (off + Int.ofNat (kn+1) - 1) stv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv) plans env k ch
  rw [hsubj, hcolJ] at h5
  have hload : loadLoc
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
        (.bool false)
        (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (Int.ofNat (kn+1)) .int) ++
         [(Loc.base ⟨45⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 46)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx4 : stepFn
      (mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
        cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
        (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
        (.bool false)
        (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
          (.bool true) (.int (Int.ofNat (kn+1)) .int) ++
         [(Loc.base ⟨45⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 46)
      (.retV (.int (Int.ofNat j) .uint64)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩] [] mtEnvC
          (mtKgetterm plans env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨33⟩)) (mtKgetterm plans env k),
        mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv
          cv apv adv lgv mxv aszv pzv (mtArrCell adty values) (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
          (.int (off + Int.ofNat j) .uint64) (.int 0 .uint64)
          (.bool false)
          (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
            (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
            (.bool true) (.int (Int.ofNat (kn+1)) .int) ++
           [(Loc.base ⟨45⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int 0 .uint64 })]) 46,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice hsc hj hload hget)
  have h6 := mtC_w6 dty so kn sc off (off + Int.ofNat j)
    (off + Int.ofNat (kn+1) - 1) tv edty tdty ivv typv dvv stv sipv
    oipv ulgv cv apv adv lgv mxv aszv pzv (mtArrCell adty values) plans env k ch
  rw [hcolT, hcolT, hcolT] at h6
  refine ⟨13 + (1 + (28 + (1 + (11 + (64 + (1 + (23 + (1 + 73)))))))),
    mtFamIn dty so (kn+1) sc (.int off .uint64) stv sipv oipv ulgv cv
      apv adv lgv mxv aszv pzv (mtArrCell adty values)
      (mtEntryCell edty ivv typv dvv) (mtTermCell tdty tv)
      (.int (off + Int.ofNat j) .uint64) (.int tv .uint64) (.bool true)
      (mtInCells (.int (off + Int.ofNat (kn+1) - 1) .uint64)
        (.bool true) (.int (off + Int.ofNat (kn+1) - 1) .uint64)
        (.bool true) (.int (Int.ofNat (kn+1)) .int) ++
       [(Loc.base ⟨45⟩,
         { declaredTy := some (Ty.int .uint64)
           value := .int tv .uint64 }),
        (Loc.base ⟨46⟩,
         { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
           value := .addr (Loc.base ⟨33⟩) }),
        (Loc.base ⟨47⟩,
         { declaredTy := some (Ty.int .uint64)
           value := .int tv .uint64 })]) 48,
    [Loc.base ⟨37⟩, Loc.base ⟨38⟩],
    [.int tv .uint64, .bool true], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2)
        (stepFnIter_chain h3 (stepFnIter_chain h4
          (stepFnIter_chain (stepFnIter_one hx3)
            (stepFnIter_chain h5 (stepFnIter_chain
              (stepFnIter_one hx4) h6))))))))
  · rfl
  · rfl

end MaybeTerm

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
