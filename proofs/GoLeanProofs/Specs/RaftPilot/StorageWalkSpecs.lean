import GoLeanProofs.Specs.RaftPilot.LogReadSpecs

/-!
# W3 F-remainder — the exported MemoryStorage walk pair
(`LastIndex`, `Term`): `CallSpecRD` instances

Unit A of the F-remainder close-out (charter Amendment 1, cluster
U3.1-F; the two mechanical parks of the crossing-kit session's park
record). Both members are Lock/`defer Unlock` walks — the machine's
defer-tail exit geometry (`CallSpecRD`) — over the canonical
MemoryStorage family of `LogReadSpecs` (`msCellVL`/`msStatsV`/
`msEntryCell`), at the landed window-split convention.

**QUANTIFIER AUDIT:** each CallSpecRD here is a RULE discharging
∀-state at its callers' call sites (∀ σ over the footprint family;
∀ plans-shape/env/k; ∀ ch demonic; ∃ n) — consumed by the raftLog
read tier (this cluster) and clusters C/D/E via `CallSpecRD.consume`.
No end-theorem quantifier closes here.

**Coverage labels (stated at birth):**
- `Term`'s three members are the subject's own branch trichotomy
  (compacted / unavailable / in-range) — per-arm members at the
  program's branch structure, the maybeTerm convention; a trichotomy
  join is consumer-demand (callers know their side).
- The `aboveLast` member's family carries `i - offset < 2^63` (the
  reader-vocabulary log-size envelope): beyond that bound the
  subject's `int(i-offset)` conversion wraps negative and the body
  would fall into the index read — a region no invariant-constrained
  caller can reach. Precondition family bound, not a conclusion
  narrowing.
- The error arms conclude "returns the value stored in the error
  GLOBAL" (cells 23/25 — `ErrCompacted`/`ErrUnavailable`, inside the
  forced-identity static region): the globals ride as free-payload
  cells in the family, the exact landed park-record plan.

**Statement hygiene:** step counts (59/67/50; 50/57/36/18/1/19/82)
live only in the PRIVATE window lemmas + the log; exports are
count-free; addresses 31+ are canonical-placement constants; field
censuses are the pinned wire's typeDefs.

LINEAGE: Hoare procedure specs by computational reflection at the
window-split convention (crossing-kit design note). No new mechanism.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec
open GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## Shared: the atLeastCmp value fact (member-local conditioned
step fodder; promotion-ledger candidate if a third comparison class
bites — the kit's class-A bridge family) -/

private theorem applyStrict_atLeast_int {σ : ExecState} {l r : Int}
    {k1 k2 : IntKind} :
    applyStrictOp σ .atLeastCmp [.int l k1, .int r k2]
      = .ok (.bool (decide (l ≥ r)), σ) := rfl

/-! ## `raft.MemoryStorage.LastIndex` — the exported Lock/defer walk
(mechanical mirror of the landed `FirstIndex` CallSpecRD: the inner
`lastIndex` adds the length crossing, so the walk is three windows +
two crossings instead of two + one) -/

section LastIndexWalk

/-- Stats with the `lastIndex` slot explicit and per-round wraps
riding (the in-window form; the `msStatsV'` sibling at slot 3). -/
def msStatsVL' (a1 a2 : Int) (liE : Int) (a4 a5 a6 : Int)
    (w : Int → Int) : GoValue :=
  .struct ⟨"raft.inMemStorageCallStats"⟩
    #[("initialState", .int (w a1) .int), ("firstIndex", .int (w a2) .int),
      ("lastIndex", .int liE .int), ("entries", .int (w a4) .int),
      ("term", .int (w a5) .int), ("snapshot", .int (w a6) .int)]

private def msEnvXL : LocalEnv :=
  [[("$c1958", Loc.base ⟨39⟩)],
   [("$res1", Loc.base ⟨38⟩), ("$res0", Loc.base ⟨37⟩),
    ("ms", Loc.base ⟨36⟩)]]

private def msEnvXLin : LocalEnv :=
  [[("$c1959", Loc.base ⟨42⟩)],
   [("$res0", Loc.base ⟨41⟩), ("ms", Loc.base ⟨40⟩)]]

/-- The outer LastIndex frame with its pending unlock defer. -/
private def msXLFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨37⟩, Loc.base ⟨38⟩]
    [(.funcVal ⟨"raft.MemoryStorage.LastIndex$deferSync0"⟩ [],
      [.addr (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩ "Mutex")])]
    k false

private def msXLGlue : Stmt :=
  .seqn #[
    .assign (.var "$res0") (.var "$c1958"),
    .assign (.var "$res1") (.nil none),
    .returnStmt]

/-- The inner `lastIndex` frame (result cell 41, target `$c1958`). -/
private def msXLinFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "$c1958"])] msEnvXL [Loc.base ⟨41⟩] []
    (.seq [msXLGlue] msEnvXL (msXLFrame plans env k)) false

/-- The inner `lastIndex` result assignment (reflected-program shape
constant, = the pinned wire's lowered body subterm). -/
private def msXLAssign : Stmt :=
  .seqn #[
    .assign (.var "$res0")
      (.sub
        (.add (.var "$c1959")
          (.convert (.int .uint64)
            (.length
              (.fieldGet
                (.deref (.var "ms") (.defined ⟨"raft.MemoryStorage"⟩))
                ⟨"raft.MemoryStorage"⟩ "ents")
              (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))))
        (.intLit 1 .uint64)),
    .returnStmt]

/-- The continuation below the inner `ents[0]` boundary. -/
private def msXLKget (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetIndex"⟩
    [(.chain [], [.ref "$c1959"])] [] [] msEnvXLin
    (.seq [msXLAssign] msEnvXLin (msXLinFrame plans env k))

/-- The continuation at the inner length boundary: the arithmetic
spine above the inner result store. -/
private def msXLKlen (c1959v : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) : Cont :=
  .strictK (.convert (.int .uint64)) [] [] msEnvXLin
    (.strictK .add [c1959v] [] msEnvXLin
      (.strictK .sub [] [.intLit 1 .uint64] msEnvXLin
        (.rhsK .vals [.chain (.addr (Loc.base ⟨41⟩)) [] []] [] []
          (.seqn #[]) msEnvXLin
          (.seq [.returnStmt] msEnvXLin (msXLinFrame plans env k)))))

/-- The LastIndex in-span state former (outer cells 36-39 + extras). -/
private def msLFam (so ln sc : Nat) (mb : Bool) (hsL snL : Loc)
    (csv : GoValue) (c32 c33 c34 c35 : HeapCell)
    (r0 r1 c1958 : GoValue) (extra : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := none
          value := msCellVL mb hsL snL csv so ln sc }),
       (Loc.base ⟨32⟩, c32), (Loc.base ⟨33⟩, c33),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := msArgV }),
       (Loc.base ⟨37⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨38⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := r1 }),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.int .uint64), value := c1958 })]
        ++ extra
      nextAddr := na }

private def msLInner (r0' c1959 : GoValue) : Heap :=
  [(Loc.base ⟨40⟩,
    { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
      value := msArgV }),
   (Loc.base ⟨41⟩,
    { declaredTy := some (Ty.int .uint64), value := r0' }),
   (Loc.base ⟨42⟩,
    { declaredTy := some (Ty.int .uint64), value := c1959 })]

private def msLGetIdxCells (idxv : GoValue) : Heap :=
  [(Loc.base ⟨43⟩,
    { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
      value := .addr (Loc.base ⟨33⟩) }),
   (Loc.base ⟨44⟩,
    { declaredTy := some (Ty.int .uint64), value := idxv })]

/-- Window 1 (59 steps): entry, Lock (coerce round 1), the defer
registration, the `callStats.lastIndex` increment (round 2), the
inner `lastIndex` entry, to the inner `ents[0]` boundary. -/
private theorem msXLI_w1 (so kn sc : Nat)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (c32 c33 c34 c35 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 59
      (msFamX0 so (kn+1) sc hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) c32 c33 c34 c35)
      (.retV msArgV
        (.callArgsK ⟨"raft.MemoryStorage.LastIndex"⟩ plans [] [] env k))
      ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩] [] msEnvXLin
            (msXLKget plans env k)),
        msLFam so (kn+1) sc true hsL snL
          (msStatsVL' a1 a2
            (IntKind.normalize .int
              (IntKind.normalize .int
                (IntKind.normalize .int a3 + 1)))
            a4 a5 a6
            (fun x => IntKind.normalize .int (IntKind.normalize .int x)))
          c32 c33 c34 c35
          (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (msLInner (.int 0 .uint64) (.int 0 .uint64)) 43,
        ch) := by
  kernel_rfl

/-- Window 2 (67 steps, from the crossed index read): the `GetIndex`
call on the pinned entry cell, the ents re-read, to the inner length
boundary. -/
private theorem msXLI_w2 (so kn sc : Nat)
    (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 67
      (msLFam so (kn+1) sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35
        (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (msLInner (.int 0 .uint64) (.int 0 .uint64)) 43)
      (.retV (.addr (Loc.base ⟨33⟩)) (msXLKget plans env k)) ch
      = .ok (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
          (.strictK
            (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
            [] [] msEnvXLin
            (msXLKlen
              (.int (IntKind.normalize .uint64
                (IntKind.normalize .uint64 iv)) .uint64)
              plans env k)),
        msLFam so (kn+1) sc true hsL snL
          (msStatsV a1 a2 a3 a4 a5 a6) c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35
          (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (msLInner (.int 0 .uint64)
            (.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64 iv)) .uint64) ++
           msLGetIdxCells
             (.int (IntKind.normalize .uint64 iv) .uint64)) 45,
        ch) := by
  kernel_rfl

/-- Window 3 (50 steps, from the crossed length read; SHAPED plans —
the defer-drain arm scrutinizes the targets column): the arithmetic
spine, inner return + result glue, the outer results, the DEFERRED
UNLOCK (coerce round 3), exit through the `.next`-frame arm. -/
private theorem msXLI_w3 (so kn sc : Nat)
    (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 : HeapCell)
    (sh : TargetShape) (e : Expr) (ops : List Expr)
    (rest : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 50
      (msLFam so (kn+1) sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35
        (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (msLInner (.int 0 .uint64) (.int iv .uint64) ++
         msLGetIdxCells (.int iv .uint64)) 45)
      (.retV (.int (Int.ofNat (kn+1)) .int)
        (msXLKlen (.int iv .uint64) ((sh, e :: ops) :: rest) env k)) ch
      = .ok (.next
          (.frame ((sh, e :: ops) :: rest) env
            [Loc.base ⟨37⟩, Loc.base ⟨38⟩] [] k false),
        msLFam so (kn+1) sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          c32 (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                    - 1))))) .uint64)
          (.nil)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                  - 1)))) .uint64)
          (msLInner
            (.int (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                  - 1))) .uint64)
            (.int iv .uint64) ++
           msLGetIdxCells (.int iv .uint64) ++
           [(Loc.base ⟨45⟩,
             { declaredTy := some (Ty.pointer (Ty.sync .mutex))
               value := .addr
                 (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩
                   "Mutex") })]) 46,
        ch) := by
  kernel_rfl

/-- **THE `MemoryStorage.LastIndex` CallSpecRD** (the exported read:
Lock + `defer Unlock` + callStats + the internal `lastIndex`):
returns `(ents[0].Index + len(ents) - 1, nil)`; the footprint reads
back with the mutex UNLOCKED again and the ONE honest mutation — the
`callStats.lastIndex` counter incremented. Counter/range facts are
reader vocabulary (the invariant's C1 counters + log-size
envelope). -/
theorem memoryStorage_LastIndex_callSpecRD
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (adty edty idty : Option Ty) (values : Array GoValue)
    (tmv typv dvv : GoValue) (c35 : HeapCell)
    (hsc : kn + 1 ≤ sc) (hk : kn + 1 < 9223372036854775808)
    (hget : values[so]? = some (.addr (Loc.base ⟨33⟩)))
    (hiv0 : 0 ≤ iv)
    (hivk : iv + Int.ofNat (kn + 1) < 18446744073709551616)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2) (ha2b : a2 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5) (ha5b : a5 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3)
    (ha3b : a3 + 1 < 9223372036854775808) :
    CallSpecRD
      (MSPreX so (kn+1) sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35)
      ⟨"raft.MemoryStorage.LastIndex"⟩ [] msArgV
      (fun σ' vs =>
        vs = [.int (iv + Int.ofNat (kn+1) - 1) .uint64, .nil] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := none
                   value := msCellVL false hsL snL
                     (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
                     so (kn+1) sc }) := by
  intro σ hP sh e ops rest env k ch
  have hofc := int_ofNat_cast (kn + 1)
  have hA1 : IntKind.normalize .int a1 = a1 := normalize_int_eq ha1a ha1b
  have hA2 : IntKind.normalize .int a2 = a2 := normalize_int_eq ha2a ha2b
  have hA4 : IntKind.normalize .int a4 = a4 := normalize_int_eq ha4a ha4b
  have hA5 : IntKind.normalize .int a5 = a5 := normalize_int_eq ha5a ha5b
  have hA6 : IntKind.normalize .int a6 = a6 := normalize_int_eq ha6a ha6b
  have hA3 : IntKind.normalize .int a3 = a3 :=
    normalize_int_eq ha3a (by omega)
  have hA31 : IntKind.normalize .int (a3 + 1) = a3 + 1 :=
    normalize_int_eq (by omega) ha3b
  have hIv : IntKind.normalize .uint64 iv = iv :=
    normalize_uint64_eq hiv0 (by rw [hofc] at hivk; omega)
  have hcolU : IntKind.normalize .uint64 (Int.ofNat (kn+1))
      = Int.ofNat (kn+1) := normalize_uint64_ofNat (by omega)
  have hAdd : IntKind.normalize .uint64 (iv + Int.ofNat (kn+1))
      = iv + Int.ofNat (kn+1) :=
    normalize_uint64_eq (by rw [hofc]; omega)
      (by rw [hofc] at hivk ⊢; omega)
  have hSub : IntKind.normalize .uint64 (iv + Int.ofNat (kn+1) - 1)
      = iv + Int.ofNat (kn+1) - 1 :=
    normalize_uint64_eq (by rw [hofc]; omega)
      (by rw [hofc] at hivk ⊢; omega)
  have h1 := msXLI_w1 so kn sc a1 a2 a3 a4 a5 a6 hsL snL
    { declaredTy := adty, value := .array values }
    (msEntryCell edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 } c35
    ((sh, e :: ops) :: rest) env k ch
  simp only [msStatsVL', hA1, hA2, hA3, hA31, hA4, hA5, hA6] at h1
  have hload : loadLoc
      (msLFam so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35
        (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (msLInner (.int 0 .uint64) (.int 0 .uint64)) 43)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx1 : stepFn
      (msLFam so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35
        (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (msLInner (.int 0 .uint64) (.int 0 .uint64)) 43)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩] [] msEnvXLin
          (msXLKget ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨33⟩))
          (msXLKget ((sh, e :: ops) :: rest) env k),
        msLFam so (kn+1) sc true hsL snL
          (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35
          (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (msLInner (.int 0 .uint64) (.int 0 .uint64)) 43,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc (Nat.succ_pos kn) hload
        hget)
  have h2 := msXLI_w2 so kn sc iv a1 a2 (a3 + 1) a4 a5 a6 hsL snL
    { declaredTy := adty, value := .array values } edty idty
    tmv typv dvv c35 ((sh, e :: ops) :: rest) env k ch
  rw [hIv, hIv] at h2
  have hx2 : stepFn
      (msLFam so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35
        (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (msLInner (.int 0 .uint64) (.int iv .uint64) ++
         msLGetIdxCells (.int iv .uint64)) 45)
      (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, kn+1, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] msEnvXLin
          (msXLKlen (.int iv .uint64) ((sh, e :: ops) :: rest) env k)))
        ch
      = .ok (.retV (.int (Int.ofNat (kn+1)) .int)
          (msXLKlen (.int iv .uint64) ((sh, e :: ops) :: rest) env k),
        msLFam so (kn+1) sc true hsL snL
          (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35
          (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (msLInner (.int 0 .uint64) (.int iv .uint64) ++
           msLGetIdxCells (.int iv .uint64)) 45,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h3 := msXLI_w3 so kn sc iv a1 a2 (a3 + 1) a4 a5 a6 hsL snL
    { declaredTy := adty, value := .array values } edty idty
    tmv typv dvv c35 sh e ops rest env k ch
  rw [hcolU, hAdd, hSub, hSub, hSub, hSub] at h3
  simp only [hA1, hA2, hA31, hA4, hA5, hA6] at h3
  refine ⟨59 + (1 + (67 + (1 + 50))),
    msLFam so (kn+1) sc false hsL snL
      (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c35
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64) (.nil)
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (msLInner (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
        (.int iv .uint64) ++
       msLGetIdxCells (.int iv .uint64) ++
       [(Loc.base ⟨45⟩,
         { declaredTy := some (Ty.pointer (Ty.sync .mutex))
           value := .addr
             (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩
               "Mutex") })]) 46,
    [Loc.base ⟨37⟩, Loc.base ⟨38⟩],
    [.int (iv + Int.ofNat (kn+1) - 1) .uint64, .nil], ch,
    ?_, ?_, ⟨rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2) h3)))
  · rfl
  · rfl

end LastIndexWalk

/-! ## `raft.MemoryStorage.Term` — the exported walk at the subject's
own branch trichotomy (compacted / unavailable / in-range)

The family extends the canonical layout with TWO entry cells (the
`ents[0]` entry at 33 with `Index → 34`, the `ents[j]` entry at 35
with `Term → 36` — distinct cells, so a consumer's real heap
instantiates honestly) and the two error GLOBALS at their true
static addresses (23 = ErrCompacted, 25 = ErrUnavailable; free
payloads — the error arms conclude "returns the global's value"). -/

section TermWalk

/-- Stats with the `term` slot explicit and per-round wraps riding. -/
def msStatsVT' (a1 a2 a3 a4 : Int) (tE : Int) (a6 : Int)
    (w : Int → Int) : GoValue :=
  .struct ⟨"raft.inMemStorageCallStats"⟩
    #[("initialState", .int (w a1) .int), ("firstIndex", .int (w a2) .int),
      ("lastIndex", .int (w a3) .int), ("entries", .int (w a4) .int),
      ("term", .int tE .int), ("snapshot", .int (w a6) .int)]

/-- The `ents[j]` entry cell (proto-optional `Term` pointer pinned to
the canonical `.base ⟨36⟩`; the other fields ride free). -/
def msTEntryJ (edty : Option Ty) (ixv typv dvv : GoValue) : HeapCell :=
  { declaredTy := edty
    value := .struct ⟨"raftpb.Entry"⟩
      #[("Term", .addr (Loc.base ⟨36⟩)), ("Index", ixv),
        ("Type", typv), ("Data", dvv)] }

/-- **The Term footprint family former**: the ms cell at the
canonical anchor, backing array at 32, the two entry cells at 33/35,
their scalar targets at 34/36, and the two error globals at their
TRUE static addresses 23/25 (free-payload cells). -/
def msTFam (so ln sc : Nat) (mb : Bool) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c33 c34 c35 c36 : HeapCell) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := none
          value := msCellVL mb hsL snL csv so ln sc }),
       (Loc.base ⟨32⟩, c32), (Loc.base ⟨33⟩, c33),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36)]
      nextAddr := 37 }

/-- The Term footprint carrier. -/
def MSTPre (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c33 c34 c35 c36 : HeapCell) (σm : ExecState) : Prop :=
  σm = msTFam so ln sc false hsL snL csv e23 e25 c32 c33 c34 c35 c36

private def tEnv : LocalEnv :=
  [[("offset", Loc.base ⟨41⟩)],
   [("$res1", Loc.base ⟨40⟩), ("$res0", Loc.base ⟨39⟩),
    ("i", Loc.base ⟨38⟩), ("ms", Loc.base ⟨37⟩)]]

private def tEnvC : LocalEnv :=
  [[("$c1957", Loc.base ⟨44⟩), ("offset", Loc.base ⟨41⟩)],
   [("$res1", Loc.base ⟨40⟩), ("$res0", Loc.base ⟨39⟩),
    ("i", Loc.base ⟨38⟩), ("ms", Loc.base ⟨37⟩)]]

/-- The compacted arm (reflected-program shape constant): the error
global at the TRUE static address 23. -/
private def tArmA : Stmt :=
  .block #[] #[.seqn #[
    .assign (.var "$res0") (.intLit 0 .uint64),
    .assign (.var "$res1")
      (.deref (.locLit (Loc.base ⟨23⟩)) (.interface ⟨"error"⟩)),
    .returnStmt]]

/-- The unavailable arm: the error global at 25. -/
private def tArmB : Stmt :=
  .block #[] #[.seqn #[
    .assign (.var "$res0") (.intLit 0 .uint64),
    .assign (.var "$res1")
      (.deref (.locLit (Loc.base ⟨25⟩)) (.interface ⟨"error"⟩)),
    .returnStmt]]

private def tIfLt : Stmt :=
  .ifThenElse (.lessCmp (.var "i") (.var "offset")) tArmA (.seqn #[])

private def tIfGe : Stmt :=
  .ifThenElse
    (.atLeastCmp
      (.convert (.int .int)
        (.sub (.var "i") (.var "offset")))
      (.length
        (.fieldGet
          (.deref (.var "ms") (.defined ⟨"raft.MemoryStorage"⟩))
          ⟨"raft.MemoryStorage"⟩ "ents")
        (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))))))
    tArmB (.seqn #[])

private def tIdxSeq : Stmt :=
  .seqn #[
    .initialization ⟨"$c1957", .int .uint64⟩,
    .call #[.var "$c1957"] ⟨"raftpb.Entry.GetTerm"⟩
      #[.indexGet
          (.fieldGet
            (.deref (.var "ms") (.defined ⟨"raft.MemoryStorage"⟩))
            ⟨"raft.MemoryStorage"⟩ "ents")
          (.sub (.var "i") (.var "offset"))]]

private def tResSeq : Stmt :=
  .seqn #[
    .assign (.var "$res0") (.var "$c1957"),
    .assign (.var "$res1") (.nil none),
    .returnStmt]

/-- The outer Term frame with its pending unlock defer. -/
private def tFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨39⟩, Loc.base ⟨40⟩]
    [(.funcVal ⟨"raft.MemoryStorage.Term$deferSync0"⟩ [],
      [.addr (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩ "Mutex")])]
    k false

/-- The continuation below the `ents[0]` boundary. -/
private def tKget (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetIndex"⟩
    [(.chain [], [.ref "offset"])] [] [] tEnv
    (.seq [tIfLt, tIfGe, tIdxSeq, tResSeq] tEnv (tFrame plans env k))

/-- The `i < offset` branch boundary. -/
private def tKif1 (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK tArmA (.seqn #[]) tEnv
    (.seq [tIfGe, tIdxSeq, tResSeq] tEnv (tFrame plans env k))

/-- The tail below the length boundary (the atLeastCmp spine over the
`≥ len` branch). -/
private def tKlen (cnv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) : Cont :=
  .strictK .atLeastCmp [cnv] [] tEnv
    (.ifK tArmB (.seqn #[]) tEnv
      (.seq [tIdxSeq, tResSeq] tEnv (tFrame plans env k)))

/-- The continuation below the `ents[i-offset]` boundary (arm C). -/
private def tKgett (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetTerm"⟩
    [(.chain [], [.ref "$c1957"])] [] [] tEnvC
    (.seq [tResSeq] tEnvC (tFrame plans env k))

/-- The Term in-span state former (outer cells 37-41 + extras). -/
private def msTIn (so ln sc : Nat) (mb : Bool) (hsL snL : Loc)
    (csv : GoValue) (e23 e25 c32 c33 c34 c35 c36 : HeapCell)
    (iv2 r0 r1 offv : GoValue) (extra : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := none
          value := msCellVL mb hsL snL csv so ln sc }),
       (Loc.base ⟨32⟩, c32), (Loc.base ⟨33⟩, c33),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36),
       (Loc.base ⟨37⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := msArgV }),
       (Loc.base ⟨38⟩,
        { declaredTy := some (Ty.int .uint64), value := iv2 }),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨40⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := r1 }),
       (Loc.base ⟨41⟩,
        { declaredTy := some (Ty.int .uint64), value := offv })]
        ++ extra
      nextAddr := na }

/-- The GetIndex-frame extra cells (42: the receiver pointer, 43: the
inner result). -/
private def tGetIdxCells (idxv : GoValue) : Heap :=
  [(Loc.base ⟨42⟩,
    { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
      value := .addr (Loc.base ⟨33⟩) }),
   (Loc.base ⟨43⟩,
    { declaredTy := some (Ty.int .uint64), value := idxv })]

private def tMutexPtrCell : Loc × HeapCell :=
  (Loc.base ⟨44⟩,
   { declaredTy := some (Ty.pointer (Ty.sync .mutex))
     value := .addr
       (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩ "Mutex") })

/-- Window 1 (50 steps): entry (the `i` argument stored normalized),
Lock (coerce round 1), the defer registration, the `callStats.term`
increment (round 2), to the `ents[0]` boundary. -/
private theorem msT_w1 (so ln sc : Nat) (ii : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c33 c34 c35 c36 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 50
      (msTFam so ln sc false hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32 c33 c34 c35 c36)
      (.retV (.int ii .uint64)
        (.callArgsK ⟨"raft.MemoryStorage.Term"⟩ plans [msArgV] [] env k))
      ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnv
            (tKget plans env k)),
        msTIn so ln sc true hsL snL
          (msStatsVT' a1 a2 a3 a4
            (IntKind.normalize .int
              (IntKind.normalize .int
                (IntKind.normalize .int a5 + 1)))
            a6
            (fun x => IntKind.normalize .int (IntKind.normalize .int x)))
          e23 e25 c32 c33 c34 c35 c36
          (.int (IntKind.normalize .uint64 ii) .uint64)
          (.int 0 .uint64) (.nil) (.int 0 .uint64) [] 42,
        ch) := by
  kernel_rfl

/-- Window 2 (57 steps, from the crossed `ents[0]` read): the
`GetIndex` call, the offset store, the `i < offset` comparison, to
the first branch boundary. -/
private theorem msT_w2 (so ln sc : Nat) (ii iv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 57
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        [] 42)
      (.retV (.addr (Loc.base ⟨33⟩)) (tKget plans env k)) ch
      = .ok (.retV
          (.bool (decide (ii <
            IntKind.normalize .uint64 (IntKind.normalize .uint64 iv))))
          (tKif1 plans env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 iv)) .uint64)
          (tGetIdxCells (.int (IntKind.normalize .uint64 iv) .uint64))
          44,
        ch) := by
  kernel_rfl

/-- Window A (36 steps, from the crossed TRUE branch; SHAPED plans):
the compacted arm — result `(0, *ErrCompacted-global)`, return, the
deferred unlock (coerce round 3), exit at the `.next`-frame arm. -/
private theorem msT_wA (so ln sc : Nat) (ii iv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23ty e25ty : Option Ty) (ev23 ev25 : GoValue)
    (c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (sh : TargetShape) (e : Expr) (ops : List Expr)
    (rest : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 36
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 } c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.exec tArmA tEnv
        (.seq [tIfGe, tIdxSeq, tResSeq] tEnv
          (tFrame ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.next
          (.frame ((sh, e :: ops) :: rest) env
            [Loc.base ⟨39⟩, Loc.base ⟨40⟩] [] k false),
        msTIn so ln sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 } c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) ev23 (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64) ++ [tMutexPtrCell]) 45,
        ch) := by
  kernel_rfl

/-- Window B1 (18 steps, from the crossed FALSE branch): the
`i - offset` subtraction, the int conversion, the ents re-read, to
the length boundary. -/
private theorem msT_wB1 (so ln sc : Nat) (ii iv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 18
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.exec (.seqn #[]) tEnv
        (.seq [tIfGe, tIdxSeq, tResSeq] tEnv (tFrame plans env k))) ch
      = .ok (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
          (.strictK
            (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
            [] [] tEnv
            (tKlen
              (.int (IntKind.normalize .int
                (IntKind.normalize .uint64 (ii - iv))) .int)
              plans env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64)) 44,
        ch) := by
  kernel_rfl

/-- Window B2 (1 step): the `≥ len` comparison applies at a free
scalar (the crossing that follows is the branch, not this apply). -/
private theorem msT_wB2 (cr : Int) (lnv : Int)
    (σm : ExecState)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 1 σm
      (.retV (.int lnv .int)
        (tKlen (.int cr .int) plans env k)) ch
      = .ok (.retV (.bool (decide (cr ≥ lnv)))
          (.ifK tArmB (.seqn #[]) tEnv
            (.seq [tIdxSeq, tResSeq] tEnv (tFrame plans env k))),
        σm, ch) := by
  kernel_rfl

/-- Window B3 (36 steps, from the crossed TRUE branch; SHAPED plans):
the unavailable arm — `(0, *ErrUnavailable-global)`, return, unlock,
the `.next`-frame exit. -/
private theorem msT_wB3 (so ln sc : Nat) (ii iv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23ty e25ty : Option Ty) (ev23 ev25 : GoValue)
    (c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (sh : TargetShape) (e : Expr) (ops : List Expr)
    (rest : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 36
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 } c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.exec tArmB tEnv
        (.seq [tIdxSeq, tResSeq] tEnv
          (tFrame ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.next
          (.frame ((sh, e :: ops) :: rest) env
            [Loc.base ⟨39⟩, Loc.base ⟨40⟩] [] k false),
        msTIn so ln sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 } c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) ev25 (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64) ++ [tMutexPtrCell]) 45,
        ch) := by
  kernel_rfl

/-- Window C1 (19 steps, from the crossed FALSE `≥ len` branch): the
`$c1957` initialization, the ents re-read, the index subtraction, to
the `ents[i-offset]` boundary. -/
private theorem msT_wC1 (so ln sc : Nat) (ii iv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 19
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.exec (.seqn #[]) tEnv
        (.seq [tIdxSeq, tResSeq] tEnv (tFrame plans env k))) ch
      = .ok (.retV
          (.int (IntKind.normalize .uint64 (ii - iv)) .uint64)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnvC
            (tKgett plans env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64) ++
           [(Loc.base ⟨44⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int 0 .uint64 })]) 45,
        ch) := by
  kernel_rfl

/-- Window C2 (82 steps, from the crossed `ents[j]` read; SHAPED
plans): the `GetTerm` call on the pinned `ents[j]` entry cell (nil
checks reduce, the Term dereference reads the pinned target), the
result glue chain, return, unlock, the `.next`-frame exit. -/
private theorem msT_wC2 (so ln sc : Nat) (ii iv tv : Int)
    (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (edty idty ejty tdty : Option Ty)
    (tmv typv dvv ixv typv2 dvv2 : GoValue)
    (sh : TargetShape) (e : Expr) (ops : List Expr)
    (rest : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 82
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64) ++
         [(Loc.base ⟨44⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 45)
      (.retV (.addr (Loc.base ⟨35⟩))
        (tKgett ((sh, e :: ops) :: rest) env k)) ch
      = .ok (.next
          (.frame ((sh, e :: ops) :: rest) env
            [Loc.base ⟨39⟩, Loc.base ⟨40⟩] [] k false),
        msTIn so ln sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          e23 e25 c32
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int ii .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 tv)))
            .uint64)
          (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64) ++
           [(Loc.base ⟨44⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int (IntKind.normalize .uint64
                 (IntKind.normalize .uint64 tv)) .uint64 }),
            (Loc.base ⟨45⟩,
             { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
               value := .addr (Loc.base ⟨35⟩) }),
            (Loc.base ⟨46⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int (IntKind.normalize .uint64 tv) .uint64 }),
            (Loc.base ⟨47⟩,
             { declaredTy := some (Ty.pointer (Ty.sync .mutex))
               value := .addr
                 (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩
                   "Mutex") })]) 48,
        ch) := by
  kernel_rfl

/-! ### The three exported Term members (the subject's branch
trichotomy; each a count-free `CallSpecRD`) -/

/-- **THE `MemoryStorage.Term` CallSpecRD, compacted member**
(`i < ents[0].Index`): returns `(0, the ErrCompacted GLOBAL's
value)` — the subject's compacted arm reads the error interface out
of the static cell 23, which rides in the family with a FREE payload;
the footprint reads back with the mutex unlocked and the
`callStats.term` counter incremented. -/
theorem memoryStorage_Term_below_callSpecRD
    (so ln sc : Nat) (ii iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23ty e25ty : Option Ty) (ev23 ev25 : GoValue)
    (adty edty idty : Option Ty) (values : Array GoValue)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (hsc : ln ≤ sc) (hln0 : 0 < ln)
    (hget0 : values[so]? = some (.addr (Loc.base ⟨33⟩)))
    (hii0 : 0 ≤ ii) (hii64 : ii < 18446744073709551616)
    (hiv0 : 0 ≤ iv) (hiv64 : iv < 18446744073709551616)
    (hlt : ii < iv)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2) (ha2b : a2 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3) (ha3b : a3 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5)
    (ha5b : a5 + 1 < 9223372036854775808) :
    CallSpecRD
      (MSTPre so ln sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36)
      ⟨"raft.MemoryStorage.Term"⟩ [msArgV] (.int ii .uint64)
      (fun σ' vs =>
        vs = [.int 0 .uint64, ev23] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := none
                   value := msCellVL false hsL snL
                     (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
                     so ln sc }) := by
  intro σ hP sh e ops rest env k ch
  have hA1 : IntKind.normalize .int a1 = a1 := normalize_int_eq ha1a ha1b
  have hA2 : IntKind.normalize .int a2 = a2 := normalize_int_eq ha2a ha2b
  have hA3 : IntKind.normalize .int a3 = a3 := normalize_int_eq ha3a ha3b
  have hA4 : IntKind.normalize .int a4 = a4 := normalize_int_eq ha4a ha4b
  have hA6 : IntKind.normalize .int a6 = a6 := normalize_int_eq ha6a ha6b
  have hA5 : IntKind.normalize .int a5 = a5 :=
    normalize_int_eq ha5a (by omega)
  have hA51 : IntKind.normalize .int (a5 + 1) = a5 + 1 :=
    normalize_int_eq (by omega) ha5b
  have hIi : IntKind.normalize .uint64 ii = ii :=
    normalize_uint64_eq hii0 hii64
  have hIv : IntKind.normalize .uint64 iv = iv :=
    normalize_uint64_eq hiv0 hiv64
  have h1 := msT_w1 so ln sc ii a1 a2 a3 a4 a5 a6 hsL snL
    { declaredTy := e23ty, value := ev23 }
    { declaredTy := e25ty, value := ev25 }
    { declaredTy := adty, value := .array values }
    (msEntryCell edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 } c35 c36
    ((sh, e :: ops) :: rest) env k ch
  simp only [msStatsVT', hA1, hA2, hA3, hA4, hA5, hA51, hA6] at h1
  rw [hIi] at h1
  have hload : loadLoc
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        [] 42)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx1 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        [] 42)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnv
          (tKget ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨33⟩))
          (tKget ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
          [] 42,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc hln0 hload hget0)
  have h2 := msT_w2 so ln sc ii iv a1 a2 a3 a4 (a5 + 1) a6 hsL snL
    { declaredTy := e23ty, value := ev23 }
    { declaredTy := e25ty, value := ev25 }
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c35 c36
    ((sh, e :: ops) :: rest) env k ch
  rw [hIv, hIv] at h2
  have hx2 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.bool (decide (ii < iv)))
        (tKif1 ((sh, e :: ops) :: rest) env k)) ch
      = .ok (.exec tArmA tEnv
          (.seq [tIfGe, tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_ifK_true (decide_eq_true hlt)
  have h3 := msT_wA so ln sc ii iv a1 a2 a3 a4 (a5 + 1) a6 hsL snL
    e23ty e25ty ev23 ev25
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c35 c36 sh e ops rest env k ch
  simp only [hA1, hA2, hA3, hA4, hA51, hA6] at h3
  refine ⟨50 + (1 + (57 + (1 + 36))),
    msTIn so ln sc false hsL snL
      (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
      { declaredTy := e23ty, value := ev23 }
      { declaredTy := e25ty, value := ev25 }
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c35 c36
      (.int ii .uint64) (.int 0 .uint64) ev23 (.int iv .uint64)
      (tGetIdxCells (.int iv .uint64) ++ [tMutexPtrCell]) 45,
    [Loc.base ⟨39⟩, Loc.base ⟨40⟩],
    [.int 0 .uint64, ev23], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2) h3)))
  · rfl
  · rfl

/-- **THE `MemoryStorage.Term` CallSpecRD, unavailable member**
(`offset ≤ i`, `len(ents) ≤ i - offset < 2^63` — the upper bound is
the reader-vocabulary log-size envelope, section note): returns
`(0, the ErrUnavailable GLOBAL's value)`; mutex unlocked again,
`callStats.term` incremented. -/
theorem memoryStorage_Term_aboveLast_callSpecRD
    (so ln sc : Nat) (ii iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23ty e25ty : Option Ty) (ev23 ev25 : GoValue)
    (adty edty idty : Option Ty) (values : Array GoValue)
    (tmv typv dvv : GoValue) (c35 c36 : HeapCell)
    (hsc : ln ≤ sc) (hln0 : 0 < ln)
    (hget0 : values[so]? = some (.addr (Loc.base ⟨33⟩)))
    (hii64 : ii < 18446744073709551616)
    (hiv0 : 0 ≤ iv) (hiv64 : iv < 18446744073709551616)
    (hge : iv ≤ ii)
    (hcrB : Int.ofNat ln ≤ ii - iv)
    (hcr63 : ii - iv < 9223372036854775808)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2) (ha2b : a2 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3) (ha3b : a3 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5)
    (ha5b : a5 + 1 < 9223372036854775808) :
    CallSpecRD
      (MSTPre so ln sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36)
      ⟨"raft.MemoryStorage.Term"⟩ [msArgV] (.int ii .uint64)
      (fun σ' vs =>
        vs = [.int 0 .uint64, ev25] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := none
                   value := msCellVL false hsL snL
                     (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
                     so ln sc }) := by
  intro σ hP sh e ops rest env k ch
  have hA1 : IntKind.normalize .int a1 = a1 := normalize_int_eq ha1a ha1b
  have hA2 : IntKind.normalize .int a2 = a2 := normalize_int_eq ha2a ha2b
  have hA3 : IntKind.normalize .int a3 = a3 := normalize_int_eq ha3a ha3b
  have hA4 : IntKind.normalize .int a4 = a4 := normalize_int_eq ha4a ha4b
  have hA6 : IntKind.normalize .int a6 = a6 := normalize_int_eq ha6a ha6b
  have hA5 : IntKind.normalize .int a5 = a5 :=
    normalize_int_eq ha5a (by omega)
  have hA51 : IntKind.normalize .int (a5 + 1) = a5 + 1 :=
    normalize_int_eq (by omega) ha5b
  have hIi : IntKind.normalize .uint64 ii = ii :=
    normalize_uint64_eq (by omega) hii64
  have hIv : IntKind.normalize .uint64 iv = iv :=
    normalize_uint64_eq hiv0 hiv64
  have hCr1 : IntKind.normalize .uint64 (ii - iv) = ii - iv :=
    normalize_uint64_eq (by omega) (by omega)
  have hCr2 : IntKind.normalize .int (ii - iv) = ii - iv :=
    normalize_int_eq (by omega) hcr63
  have h1 := msT_w1 so ln sc ii a1 a2 a3 a4 a5 a6 hsL snL
    { declaredTy := e23ty, value := ev23 }
    { declaredTy := e25ty, value := ev25 }
    { declaredTy := adty, value := .array values }
    (msEntryCell edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 } c35 c36
    ((sh, e :: ops) :: rest) env k ch
  simp only [msStatsVT', hA1, hA2, hA3, hA4, hA5, hA51, hA6] at h1
  rw [hIi] at h1
  have hload : loadLoc
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        [] 42)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx1 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        [] 42)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnv
          (tKget ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨33⟩))
          (tKget ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
          [] 42,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc hln0 hload hget0)
  have h2 := msT_w2 so ln sc ii iv a1 a2 a3 a4 (a5 + 1) a6 hsL snL
    { declaredTy := e23ty, value := ev23 }
    { declaredTy := e25ty, value := ev25 }
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c35 c36
    ((sh, e :: ops) :: rest) env k ch
  rw [hIv, hIv] at h2
  have hxF : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.bool (decide (ii < iv)))
        (tKif1 ((sh, e :: ops) :: rest) env k)) ch
      = .ok (.exec (.seqn #[]) tEnv
          (.seq [tIfGe, tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_ifK_false (decide_eq_false (by omega))
  have h3 := msT_wB1 so ln sc ii iv a1 a2 a3 a4 (a5 + 1) a6 hsL snL
    { declaredTy := e23ty, value := ev23 }
    { declaredTy := e25ty, value := ev25 }
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c35 c36
    ((sh, e :: ops) :: rest) env k ch
  rw [hCr1, hCr2] at h3
  have hx2 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] tEnv
          (tKlen (.int (ii - iv) .int)
            ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.int (Int.ofNat ln) .int)
          (tKlen (.int (ii - iv) .int) ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h4 := msT_wB2 (ii - iv) (Int.ofNat ln)
    (msTIn so ln sc true hsL snL
      (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
      { declaredTy := e23ty, value := ev23 }
      { declaredTy := e25ty, value := ev25 }
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c35 c36
      (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
      (tGetIdxCells (.int iv .uint64)) 44)
    ((sh, e :: ops) :: rest) env k ch
  have hx3 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
        { declaredTy := e23ty, value := ev23 }
        { declaredTy := e25ty, value := ev25 }
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c35 c36
        (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.bool (decide ((ii - iv) ≥ Int.ofNat ln)))
        (.ifK tArmB (.seqn #[]) tEnv
          (.seq [tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)))) ch
      = .ok (.exec tArmB tEnv
          (.seq [tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
          { declaredTy := e23ty, value := ev23 }
          { declaredTy := e25ty, value := ev25 }
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c35 c36
          (.int ii .uint64) (.int 0 .uint64) (.nil) (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_ifK_true (decide_eq_true hcrB)
  have h5 := msT_wB3 so ln sc ii iv a1 a2 a3 a4 (a5 + 1) a6 hsL snL
    e23ty e25ty ev23 ev25
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c35 c36 sh e ops rest env k ch
  simp only [hA1, hA2, hA3, hA4, hA51, hA6] at h5
  refine ⟨50 + (1 + (57 + (1 + (18 + (1 + (1 + (1 + 36))))))),
    msTIn so ln sc false hsL snL
      (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
      { declaredTy := e23ty, value := ev23 }
      { declaredTy := e25ty, value := ev25 }
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c35 c36
      (.int ii .uint64) (.int 0 .uint64) ev25 (.int iv .uint64)
      (tGetIdxCells (.int iv .uint64) ++ [tMutexPtrCell]) 45,
    [Loc.base ⟨39⟩, Loc.base ⟨40⟩],
    [.int 0 .uint64, ev25], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hxF)
        (stepFnIter_chain h3 (stepFnIter_chain (stepFnIter_one hx2)
          (stepFnIter_chain h4
            (stepFnIter_chain (stepFnIter_one hx3) h5)))))))
  · rfl
  · rfl

/-- **THE `MemoryStorage.Term` CallSpecRD, in-range member**
(`i = ents[0].Index + j`, `j < len(ents)`): returns
`(ents[j].Term, nil)` — the subject's read arm; the two entry reads
land on DISTINCT pinned cells (33 = the `ents[0]` entry, 35 = the
`ents[j]` entry), the backing-array read outcomes are family-carried
hypotheses (the class-3 symbolic-heap-read discipline); mutex
unlocked again, `callStats.term` incremented. -/
theorem memoryStorage_Term_inRange_callSpecRD
    (so ln sc : Nat) (j : Nat) (iv tv a1 a2 a3 a4 a5 a6 : Int)
    (hsL snL : Loc)
    (e23 e25 : HeapCell)
    (adty edty idty ejty tdty : Option Ty) (values : Array GoValue)
    (tmv typv dvv ixv typv2 dvv2 : GoValue)
    (hsc : ln ≤ sc) (hln63 : ln < 9223372036854775808)
    (hj : j < ln)
    (hget0 : values[so]? = some (.addr (Loc.base ⟨33⟩)))
    (hgetj : values[so + j]? = some (.addr (Loc.base ⟨35⟩)))
    (hiv0 : 0 ≤ iv)
    (hivln : iv + Int.ofNat ln < 18446744073709551616)
    (htv0 : 0 ≤ tv) (htv64 : tv < 18446744073709551616)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2) (ha2b : a2 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3) (ha3b : a3 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5)
    (ha5b : a5 + 1 < 9223372036854775808) :
    CallSpecRD
      (MSTPre so ln sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 })
      ⟨"raft.MemoryStorage.Term"⟩ [msArgV]
      (.int (iv + Int.ofNat j) .uint64)
      (fun σ' vs =>
        vs = [.int tv .uint64, .nil] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := none
                   value := msCellVL false hsL snL
                     (msStatsV a1 a2 a3 a4 (a5 + 1) a6)
                     so ln sc }) := by
  intro σ hP sh e ops rest env k ch
  have hofl := int_ofNat_cast ln
  have hofj := int_ofNat_cast j
  have hA1 : IntKind.normalize .int a1 = a1 := normalize_int_eq ha1a ha1b
  have hA2 : IntKind.normalize .int a2 = a2 := normalize_int_eq ha2a ha2b
  have hA3 : IntKind.normalize .int a3 = a3 := normalize_int_eq ha3a ha3b
  have hA4 : IntKind.normalize .int a4 = a4 := normalize_int_eq ha4a ha4b
  have hA6 : IntKind.normalize .int a6 = a6 := normalize_int_eq ha6a ha6b
  have hA5 : IntKind.normalize .int a5 = a5 :=
    normalize_int_eq ha5a (by omega)
  have hA51 : IntKind.normalize .int (a5 + 1) = a5 + 1 :=
    normalize_int_eq (by omega) ha5b
  have hIi : IntKind.normalize .uint64 (iv + Int.ofNat j)
      = iv + Int.ofNat j :=
    normalize_uint64_eq (by rw [hofj]; omega)
      (by rw [hofj]; rw [hofl] at hivln; omega)
  have hIv : IntKind.normalize .uint64 iv = iv :=
    normalize_uint64_eq hiv0 (by rw [hofl] at hivln; omega)
  have hsubj : iv + Int.ofNat j - iv = Int.ofNat j := by
    rw [hofj]; omega
  have hJu : IntKind.normalize .uint64 (Int.ofNat j) = Int.ofNat j :=
    normalize_uint64_ofNat (by omega)
  have hJi : IntKind.normalize .int (Int.ofNat j) = Int.ofNat j :=
    normalize_int_ofNat (by omega)
  have hT : IntKind.normalize .uint64 tv = tv :=
    normalize_uint64_eq htv0 htv64
  have h1 := msT_w1 so ln sc (iv + Int.ofNat j) a1 a2 a3 a4 a5 a6
    hsL snL e23 e25
    { declaredTy := adty, value := .array values }
    (msEntryCell edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 }
    (msTEntryJ ejty ixv typv2 dvv2)
    { declaredTy := tdty, value := .int tv .uint64 }
    ((sh, e :: ops) :: rest) env k ch
  simp only [msStatsVT', hA1, hA2, hA3, hA4, hA5, hA51, hA6] at h1
  rw [hIi] at h1
  have hload : loadLoc
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int 0 .uint64) [] 42)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx1 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int 0 .uint64) [] 42)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnv
          (tKget ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨33⟩))
          (tKget ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
          (.int 0 .uint64) [] 42,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc (by omega) hload hget0)
  have h2 := msT_w2 so ln sc (iv + Int.ofNat j) iv a1 a2 a3 a4
    (a5 + 1) a6 hsL snL e23 e25
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv
    (msTEntryJ ejty ixv typv2 dvv2)
    { declaredTy := tdty, value := .int tv .uint64 }
    ((sh, e :: ops) :: rest) env k ch
  rw [hIv, hIv] at h2
  have hxF1 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.bool (decide ((iv + Int.ofNat j) < iv)))
        (tKif1 ((sh, e :: ops) :: rest) env k)) ch
      = .ok (.exec (.seqn #[]) tEnv
          (.seq [tIfGe, tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
          (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_ifK_false (decide_eq_false (by rw [hofj]; omega))
  have h3 := msT_wB1 so ln sc (iv + Int.ofNat j) iv a1 a2 a3 a4
    (a5 + 1) a6 hsL snL e23 e25
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv
    (msTEntryJ ejty ixv typv2 dvv2)
    { declaredTy := tdty, value := .int tv .uint64 }
    ((sh, e :: ops) :: rest) env k ch
  rw [hsubj, hJu, hJi] at h3
  have hx2 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] tEnv
          (tKlen (.int (Int.ofNat j) .int)
            ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.int (Int.ofNat ln) .int)
          (tKlen (.int (Int.ofNat j) .int)
            ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
          (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h4 := msT_wB2 (Int.ofNat j) (Int.ofNat ln)
    (msTIn so ln sc true hsL snL
      (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 }
      (msTEntryJ ejty ixv typv2 dvv2)
      { declaredTy := tdty, value := .int tv .uint64 }
      (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
      (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44)
    ((sh, e :: ops) :: rest) env k ch
  have hxF2 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44)
      (.retV (.bool (decide ((Int.ofNat j) ≥ Int.ofNat ln)))
        (.ifK tArmB (.seqn #[]) tEnv
          (.seq [tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)))) ch
      = .ok (.exec (.seqn #[]) tEnv
          (.seq [tIdxSeq, tResSeq] tEnv
            (tFrame ((sh, e :: ops) :: rest) env k)),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
          (.int iv .uint64) (tGetIdxCells (.int iv .uint64)) 44,
        ch) :=
    stepFn_ifK_false (decide_eq_false (by rw [hofj, hofl]; omega))
  have h5 := msT_wC1 so ln sc (iv + Int.ofNat j) iv a1 a2 a3 a4
    (a5 + 1) a6 hsL snL e23 e25
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv
    (msTEntryJ ejty ixv typv2 dvv2)
    { declaredTy := tdty, value := .int tv .uint64 }
    ((sh, e :: ops) :: rest) env k ch
  rw [hsubj, hJu] at h5
  have hloadC : loadLoc
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64) ++
         [(Loc.base ⟨44⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 45)
      (Loc.base ⟨32⟩) = .ok (.array values) := rfl
  have hx4 : stepFn
      (msTIn so ln sc true hsL snL
        (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
        { declaredTy := adty, value := .array values }
        (msEntryCell edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 }
        (msTEntryJ ejty ixv typv2 dvv2)
        { declaredTy := tdty, value := .int tv .uint64 }
        (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
        (.int iv .uint64)
        (tGetIdxCells (.int iv .uint64) ++
         [(Loc.base ⟨44⟩,
           { declaredTy := some (Ty.int .uint64)
             value := .int 0 .uint64 })]) 45)
      (.retV (.int (Int.ofNat j) .uint64)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨32⟩), so, ln, sc⟩] [] tEnvC
          (tKgett ((sh, e :: ops) :: rest) env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨35⟩))
          (tKgett ((sh, e :: ops) :: rest) env k),
        msTIn so ln sc true hsL snL
          (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
          { declaredTy := adty, value := .array values }
          (msEntryCell edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 }
          (msTEntryJ ejty ixv typv2 dvv2)
          { declaredTy := tdty, value := .int tv .uint64 }
          (.int (iv + Int.ofNat j) .uint64) (.int 0 .uint64) (.nil)
          (.int iv .uint64)
          (tGetIdxCells (.int iv .uint64) ++
           [(Loc.base ⟨44⟩,
             { declaredTy := some (Ty.int .uint64)
               value := .int 0 .uint64 })]) 45,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice hsc hj hloadC hgetj)
  have h6 := msT_wC2 so ln sc (iv + Int.ofNat j) iv tv a1 a2 a3 a4
    (a5 + 1) a6 hsL snL e23 e25
    { declaredTy := adty, value := .array values }
    edty idty ejty tdty tmv typv dvv ixv typv2 dvv2
    sh e ops rest env k ch
  rw [hT, hT, hT] at h6
  simp only [hA1, hA2, hA3, hA4, hA51, hA6] at h6
  refine ⟨50 + (1 + (57 + (1 + (18 + (1 + (1 + (1 + (19 + (1 + 82))))))))),
    msTIn so ln sc false hsL snL
      (msStatsV a1 a2 a3 a4 (a5 + 1) a6) e23 e25
      { declaredTy := adty, value := .array values }
      (msEntryCell edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 }
      (msTEntryJ ejty ixv typv2 dvv2)
      { declaredTy := tdty, value := .int tv .uint64 }
      (.int (iv + Int.ofNat j) .uint64) (.int tv .uint64) (.nil)
      (.int iv .uint64)
      (tGetIdxCells (.int iv .uint64) ++
       [(Loc.base ⟨44⟩,
         { declaredTy := some (Ty.int .uint64)
           value := .int tv .uint64 }),
        (Loc.base ⟨45⟩,
         { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
           value := .addr (Loc.base ⟨35⟩) }),
        (Loc.base ⟨46⟩,
         { declaredTy := some (Ty.int .uint64)
           value := .int tv .uint64 }),
        (Loc.base ⟨47⟩,
         { declaredTy := some (Ty.pointer (Ty.sync .mutex))
           value := .addr
             (.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩
               "Mutex") })]) 48,
    [Loc.base ⟨39⟩, Loc.base ⟨40⟩],
    [.int tv .uint64, .nil], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hxF1)
        (stepFnIter_chain h3 (stepFnIter_chain (stepFnIter_one hx2)
          (stepFnIter_chain h4 (stepFnIter_chain (stepFnIter_one hxF2)
            (stepFnIter_chain h5 (stepFnIter_chain
              (stepFnIter_one hx4) h6)))))))))
  · rfl
  · rfl

/-- Non-vacuity of the Term footprint carrier (the ∃-discharge,
concrete values in every free slot; the `LastIndex` member's carrier
is the landed `MSPreX`, inhabited the same way). -/
theorem msTPre_inhabited :
    MSTPre 1 3 5 (.base ⟨10⟩) (.base ⟨11⟩) (msStatsV 3 4 5 6 7 8)
      ⟨none, .int 777 .int⟩ ⟨none, .int 777 .int⟩
      ⟨none, .array #[.nil, .addr (.base ⟨33⟩), .addr (.base ⟨35⟩),
        .addr (.base ⟨35⟩), .nil]⟩
      (msEntryCell none .nil (.int 0 .int32) .nil)
      ⟨none, .int 101 .uint64⟩
      (msTEntryJ none .nil (.int 0 .int32) .nil)
      ⟨none, .int 9 .uint64⟩
      (msTFam 1 3 5 false (.base ⟨10⟩) (.base ⟨11⟩)
        (msStatsV 3 4 5 6 7 8)
        ⟨none, .int 777 .int⟩ ⟨none, .int 777 .int⟩
        ⟨none, .array #[.nil, .addr (.base ⟨33⟩), .addr (.base ⟨35⟩),
          .addr (.base ⟨35⟩), .nil]⟩
        (msEntryCell none .nil (.int 0 .int32) .nil)
        ⟨none, .int 101 .uint64⟩
        (msTEntryJ none .nil (.int 0 .int32) .nil)
        ⟨none, .int 9 .uint64⟩) := rfl

end TermWalk

end GoLean.RaftSeam
