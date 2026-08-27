import GoLeanProofs.Specs.RaftPilot.StorageWalkSpecs

/-!
# W3 F-remainder — the raftLog read tier: `CallSpecR` instances at
the QUIESCED family

Unit A of the F-remainder close-out, the census-U3 range-obligation
tier (charter Amendment 1, cluster U3.1-F → consumed by C/D/E). The
members compose the landed unstable/MemoryStorage leaves by INLINE
window-sums (the recorded composition finding: within-family
composition re-walks the callee at the caller's extended heap; the
callee's crossings recur and are crossed by the same kit pieces).
The storage interface dispatch is CONCRETE once the family pins the
`.interface (*raft.MemoryStorage) (.addr ⟨33⟩)` field — exactly the
park record's un-parking route.

**THE QUIESCED FAMILY (coverage label, stated at birth):** the
family pins the unstable EMPTY (`len 0` at a live backing slice,
snapshot nil) — the loop-head states (every entry stabilized; the
invariant's C2 supplies exactly this shape at harvest quiescence).
Members over unstable-nonempty states are consumer-demand variants
(handlers mid-Ready processing), added when a caller bites —
recorded, not silently absorbed.

**QUANTIFIER AUDIT:** each CallSpecR here discharges ∀-state at the
raftLog call sites of clusters C/D/E (∀ σ over the family; ∀
plans/env/k; ∀ ch; ∃ n). No end-theorem quantifier closes here.

**Statement hygiene:** step counts (140/138; 171/67/82) live only in
the private window lemmas + the log; exports count-free; addresses
31-38 are canonical-placement constants; field censuses are the
pinned wire's typeDefs.

LINEAGE: window-split symbolic execution over computational
reflection (the crossing-kit design note); Hoare procedure specs.
No new mechanism.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec
open GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The quiesced raftLog footprint family
Layout: 23/25 = the error globals (free-payload cells); 31 = the
raftLog cell; 32 = the (unread) unstable backing; 33 = the ms cell;
34 = the ms backing array; 35 = the `ents[0]` entry (Index → 36);
36 = the first index; 37 = the `ents[j]` entry (Term → 38); 38 = the
term value. `nextAddr = 39`. -/

/-- The pinned storage interface value (dynamic type
`*raft.MemoryStorage`, payload = the canonical ms cell). -/
def rlStorageIfaceV : GoValue :=
  .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩))
    (.addr (Loc.base ⟨33⟩))

/-- The ms cell value at the raftLog placement (backing at 34). -/
def msCellV34 (mb : Bool) (hsL snL : Loc) (csv : GoValue)
    (so ln sc : Nat) : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩
    #[("Mutex", .syncData (.mutex mb)),
      ("hardState", .addr hsL), ("snapshot", .addr snL),
      ("ents", .slice ⟨some (Loc.base ⟨34⟩), so, ln, sc⟩),
      ("callStats", csv)]

/-- The `ents[0]` entry at the raftLog placement (Index → 36). -/
def rlEntry0 (edty : Option Ty) (tmv typv dvv : GoValue) : HeapCell :=
  { declaredTy := edty
    value := .struct ⟨"raftpb.Entry"⟩
      #[("Term", tmv), ("Index", .addr (Loc.base ⟨36⟩)),
        ("Type", typv), ("Data", dvv)] }

/-- The `ents[j]` entry at the raftLog placement (Term → 38). -/
def rlEntryJ (edty : Option Ty) (ixv typv dvv : GoValue) : HeapCell :=
  { declaredTy := edty
    value := .struct ⟨"raftpb.Entry"⟩
      #[("Term", .addr (Loc.base ⟨38⟩)), ("Index", ixv),
        ("Type", typv), ("Data", dvv)] }

/-- **The quiesced raftLog family former.** The raftLog cell reuses
`logCellV` (the canonical field census); the unstable entries slice
is pinned empty at a live backing (`⟨some 32, uo, 0, uc⟩`); every
genuinely-unread position is free. -/
def rlFam (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV rlStorageIfaceV
            (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
            uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32),
       (Loc.base ⟨33⟩,
        { declaredTy := none
          value := msCellV34 false hsL snL csv so ln sc }),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36), (Loc.base ⟨37⟩, c37),
       (Loc.base ⟨38⟩, c38)]
      nextAddr := 39 }

/-- The quiesced-family footprint carrier. -/
def RLPre (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (σm : ExecState) : Prop :=
  σm = rlFam dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
    pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38

/-- The raftLog receiver value: `&l` at the canonical anchor. -/
def rlArgV : GoValue := .addr (Loc.base ⟨31⟩)

private def rlUnstableFieldAddr : GoValue :=
  .addr (.field (Loc.base ⟨31⟩) ⟨"raft.raftLog"⟩ "unstable")

private def msMutexAddr33 : GoValue :=
  .addr (.field (Loc.base ⟨33⟩) ⟨"raft.MemoryStorage"⟩ "Mutex")

/-! ## `raft.raftLog.firstIndex` (census log.go:300) -/

section RlFirstIndex

private def rFEnvIn : LocalEnv :=
  [[("$c1961", Loc.base ⟨54⟩)],
   [("$res0", Loc.base ⟨53⟩), ("ms", Loc.base ⟨52⟩)]]

private def rFEnvOut : LocalEnv :=
  [[("$c1960", Loc.base ⟨51⟩)],
   [("$res1", Loc.base ⟨50⟩), ("$res0", Loc.base ⟨49⟩),
    ("ms", Loc.base ⟨48⟩)]]

private def rFEnvL : LocalEnv :=
  [[("err", Loc.base ⟨47⟩), ("index", Loc.base ⟨46⟩)],
   [("$res0", Loc.base ⟨40⟩), ("l", Loc.base ⟨39⟩)]]

/-- The raftLog outer frame (defer-FREE — the `CallSpecR`
terminal). -/
private def rFFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨40⟩] [] k false

private def rFKl (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [.ifThenElse
          (.neqCmp (.interface ⟨"error"⟩) (.var "err") (.nil none))
          (.block #[] #[.panicStmt (.var "err")])
          (.seqn #[]),
        .seqn #[.assign (.var "$res0") (.var "index"), .returnStmt]]
    rFEnvL (rFFrame plans env k)

/-- The inlined FirstIndex-walk outer frame (with its pending unlock
defer, at the raftLog placement — mutex field of cell 33). -/
private def rFFrameFI (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "index"]), (.chain [], [.ref "err"])]
    rFEnvL [Loc.base ⟨49⟩, Loc.base ⟨50⟩]
    [(.funcVal ⟨"raft.MemoryStorage.FirstIndex$deferSync0"⟩ [],
      [msMutexAddr33])]
    (rFKl plans env k) false

private def rFKglue (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [.seqn #[
          .assign (.var "$res0") (.var "$c1960"),
          .assign (.var "$res1") (.nil none),
          .returnStmt]]
    rFEnvOut (rFFrameFI plans env k)

private def rFFrameIn (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "$c1960"])] rFEnvOut [Loc.base ⟨53⟩] []
    (rFKglue plans env k) false

/-- The continuation below the inner `ents[0]` boundary. -/
private def rFKget (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetIndex"⟩
    [(.chain [], [.ref "$c1961"])] [] [] rFEnvIn
    (.seq [.seqn #[
        .assign (.var "$res0")
          (.add (.var "$c1961") (.intLit 1 .uint64)),
        .returnStmt]]
      rFEnvIn (rFFrameIn plans env k))

/-- The rl.firstIndex in-span state former (frame cells 39-54 +
extras; the mid-span constants — the maybeFirstIndex results and the
caller's i/ok — pinned at their post-W1 values). -/
private def rFIn (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (mb : Bool) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (r0 idxv errv fir0 c1960 ir0 c1961 : GoValue)
    (extra : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV rlStorageIfaceV
            (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
            uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32),
       (Loc.base ⟨33⟩,
        { declaredTy := none
          value := msCellV34 mb hsL snL csv so ln sc }),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36), (Loc.base ⟨37⟩, c37),
       (Loc.base ⟨38⟩, c38),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raftLog"⟩))
          value := rlArgV }),
       (Loc.base ⟨40⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨41⟩,
        { declaredTy := some (Ty.int .uint64), value := .int 0 .uint64 }),
       (Loc.base ⟨42⟩,
        { declaredTy := some Ty.bool, value := .bool false }),
       (Loc.base ⟨43⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := rlUnstableFieldAddr }),
       (Loc.base ⟨44⟩,
        { declaredTy := some (Ty.int .uint64), value := .int 0 .uint64 }),
       (Loc.base ⟨45⟩,
        { declaredTy := some Ty.bool, value := .bool false }),
       (Loc.base ⟨46⟩,
        { declaredTy := some (Ty.int .uint64), value := idxv }),
       (Loc.base ⟨47⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := errv }),
       (Loc.base ⟨48⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := .addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨49⟩,
        { declaredTy := some (Ty.int .uint64), value := fir0 }),
       (Loc.base ⟨50⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := .nil }),
       (Loc.base ⟨51⟩,
        { declaredTy := some (Ty.int .uint64), value := c1960 }),
       (Loc.base ⟨52⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := .addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨53⟩,
        { declaredTy := some (Ty.int .uint64), value := ir0 }),
       (Loc.base ⟨54⟩,
        { declaredTy := some (Ty.int .uint64), value := c1961 })]
        ++ extra
      nextAddr := na }

/-- Window 1 (140 steps): entry, the inlined `maybeFirstIndex`
(snapshot nil → `(0,false)`), the `ok` branch (false), the storage
interface DISPATCH (concrete at the pinned interface value), the
inlined FirstIndex walk's Lock + defer + counter increment, to the
inner `ents[0]` boundary. -/
private theorem rF_w1 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 140
      (rlFam dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        e23 e25 c32 c34 c35 c36 c37 c38)
      (.retV rlArgV
        (.callArgsK ⟨"raft.raftLog.firstIndex"⟩ plans [] [] env k)) ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩] [] rFEnvIn
            (rFKget plans env k)),
        rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsV' a1
            (IntKind.normalize .int
              (IntKind.normalize .int
                (IntKind.normalize .int a2 + 1)))
            a3 a4 a5 a6
            (fun x => IntKind.normalize .int (IntKind.normalize .int x)))
          e23 e25 c32 c34 c35 c36 c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 55,
        ch) := by
  kernel_rfl

/-- Window 2 (138 steps, from the crossed index read): the `GetIndex`
call, the `+ 1`, the walk's return + DEFERRED UNLOCK, the storage
frame exit (`index`/`err` stores), the err≠nil test (nil → false),
the raftLog result store, RETURN ARRIVAL at the defer-free outer
frame. -/
private theorem rF_w2 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c34 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c37 c38 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 138
      (rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32 c34
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 55)
      (.retV (.addr (Loc.base ⟨35⟩)) (rFKget plans env k)) ch
      = .ok (.returning (rFFrame plans env k),
        rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          e23 e25 c32 c34 (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (IntKind.normalize .uint64
                      (IntKind.normalize .uint64
                        (IntKind.normalize .uint64 iv) + 1)))))))
            .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (IntKind.normalize .uint64
                      (IntKind.normalize .uint64 iv) + 1))))))
            .uint64)
          (.nil)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (IntKind.normalize .uint64 iv) + 1)))))
            .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64 iv) + 1))))
            .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64 iv) + 1)))
            .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 iv)) .uint64)
          [(Loc.base ⟨55⟩,
            { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
              value := .addr (Loc.base ⟨35⟩) }),
           (Loc.base ⟨56⟩,
            { declaredTy := some (Ty.int .uint64)
              value := .int (IntKind.normalize .uint64 iv) .uint64 }),
           (Loc.base ⟨57⟩,
            { declaredTy := some (Ty.pointer (Ty.sync .mutex))
              value := msMutexAddr33 })] 58,
        ch) := by
  kernel_rfl

/-- **THE `raftLog.firstIndex` CallSpecR** (quiesced family): returns
`ents[0].Index + 1` — the storage route's exact result (the unstable
has no snapshot, by the family); the raftLog cell reads back
UNCHANGED, the ms cell with the mutex unlocked again and exactly the
`callStats.firstIndex` counter incremented — the census-U3 tier's
first-index fact clusters C/D/E consume. -/
theorem raftLog_firstIndex_callSpecR (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (adty edty idty : Option Ty)
    (values : Array GoValue) (tmv typv dvv : GoValue)
    (c37 c38 : HeapCell)
    (hsc : kn + 1 ≤ sc)
    (hget : values[so]? = some (.addr (Loc.base ⟨35⟩)))
    (hiv0 : 0 ≤ iv) (hiv64 : iv + 1 < 18446744073709551616)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3) (ha3b : a3 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5) (ha5b : a5 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2)
    (ha2b : a2 + 1 < 9223372036854775808) :
    CallSpecR
      (RLPre dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38)
      ⟨"raft.raftLog.firstIndex"⟩ [] rlArgV
      (fun σ' vs =>
        vs = [.int (iv + 1) .uint64] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV rlStorageIfaceV
                     (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
                     uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
                     pzv } ∧
        Heap.lookup σ'.heap (Loc.base ⟨33⟩)
          = some { declaredTy := none
                   value := msCellV34 false hsL snL
                     (msStatsV a1 (a2 + 1) a3 a4 a5 a6)
                     so (kn+1) sc }) := by
  intro σ hP plans env k ch
  have hA1 : IntKind.normalize .int a1 = a1 := normalize_int_eq ha1a ha1b
  have hA3 : IntKind.normalize .int a3 = a3 := normalize_int_eq ha3a ha3b
  have hA4 : IntKind.normalize .int a4 = a4 := normalize_int_eq ha4a ha4b
  have hA5 : IntKind.normalize .int a5 = a5 := normalize_int_eq ha5a ha5b
  have hA6 : IntKind.normalize .int a6 = a6 := normalize_int_eq ha6a ha6b
  have hA2 : IntKind.normalize .int a2 = a2 :=
    normalize_int_eq ha2a (by omega)
  have hA21 : IntKind.normalize .int (a2 + 1) = a2 + 1 :=
    normalize_int_eq (by omega) ha2b
  have hIv : IntKind.normalize .uint64 iv = iv :=
    normalize_uint64_eq hiv0 (by omega)
  have hIv1 : IntKind.normalize .uint64 (iv + 1) = iv + 1 :=
    normalize_uint64_eq (by omega) hiv64
  have h1 := rF_w1 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so kn sc a1 a2 a3 a4 a5 a6 hsL snL e23 e25 c32
    { declaredTy := adty, value := .array values }
    (rlEntry0 edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 } c37 c38
    plans env k ch
  simp only [msStatsV', hA1, hA2, hA21, hA3, hA4, hA5, hA6] at h1
  have hload : loadLoc
      (rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 (a2 + 1) a3 a4 a5 a6) e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 55)
      (Loc.base ⟨34⟩) = .ok (.array values) := rfl
  have hx : stepFn
      (rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 (a2 + 1) a3 a4 a5 a6) e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 55)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩] [] rFEnvIn
          (rFKget plans env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨35⟩)) (rFKget plans env k),
        rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsV a1 (a2 + 1) a3 a4 a5 a6) e23 e25 c32
          { declaredTy := adty, value := .array values }
          (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.nil) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 55,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc (Nat.succ_pos kn) hload
        hget)
  have h2 := rF_w2 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so kn sc iv a1 (a2 + 1) a3 a4 a5 a6 hsL snL e23 e25 c32
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c37 c38 plans env k ch
  rw [hIv, hIv] at h2
  rw [hIv1, hIv1, hIv1, hIv1, hIv1, hIv1] at h2
  simp only [hA1, hA21, hA3, hA4, hA5, hA6] at h2
  refine ⟨140 + (1 + 138),
    rFIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv
      so (kn+1) sc false hsL snL
      (msStatsV a1 (a2 + 1) a3 a4 a5 a6) e23 e25 c32
      { declaredTy := adty, value := .array values }
      (rlEntry0 edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c37 c38
      (.int (iv + 1) .uint64) (.int (iv + 1) .uint64) (.nil)
      (.int (iv + 1) .uint64) (.int (iv + 1) .uint64)
      (.int (iv + 1) .uint64) (.int iv .uint64)
      [(Loc.base ⟨55⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
          value := .addr (Loc.base ⟨35⟩) }),
       (Loc.base ⟨56⟩,
        { declaredTy := some (Ty.int .uint64)
          value := .int iv .uint64 }),
       (Loc.base ⟨57⟩,
        { declaredTy := some (Ty.pointer (Ty.sync .mutex))
          value := msMutexAddr33 })] 58,
    [Loc.base ⟨40⟩], [.int (iv + 1) .uint64], ch,
    ?_, ?_, ⟨rfl, rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx) h2)
  · rfl
  · rfl

end RlFirstIndex

/-! ## `raft.raftLog.lastIndex` (census log.go:311) -/

section RlLastIndex

private def rLEnvIn : LocalEnv :=
  [[("$c1959", Loc.base ⟨55⟩)],
   [("$res0", Loc.base ⟨54⟩), ("ms", Loc.base ⟨53⟩)]]

private def rLEnvOut : LocalEnv :=
  [[("$c1958", Loc.base ⟨52⟩)],
   [("$res1", Loc.base ⟨51⟩), ("$res0", Loc.base ⟨50⟩),
    ("ms", Loc.base ⟨49⟩)]]

private def rLEnvL : LocalEnv :=
  [[("err", Loc.base ⟨48⟩), ("i", Loc.base ⟨47⟩)],
   [("$res0", Loc.base ⟨40⟩), ("l", Loc.base ⟨39⟩)]]

private def rLFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨40⟩] [] k false

private def rLKl (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [.ifThenElse
          (.neqCmp (.interface ⟨"error"⟩) (.var "err") (.nil none))
          (.block #[] #[.panicStmt (.var "err")])
          (.seqn #[]),
        .seqn #[.assign (.var "$res0") (.var "i"), .returnStmt]]
    rLEnvL (rLFrame plans env k)

private def rLFrameLI (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "i"]), (.chain [], [.ref "err"])]
    rLEnvL [Loc.base ⟨50⟩, Loc.base ⟨51⟩]
    [(.funcVal ⟨"raft.MemoryStorage.LastIndex$deferSync0"⟩ [],
      [msMutexAddr33])]
    (rLKl plans env k) false

private def rLKglue (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .seq [.seqn #[
          .assign (.var "$res0") (.var "$c1958"),
          .assign (.var "$res1") (.nil none),
          .returnStmt]]
    rLEnvOut (rLFrameLI plans env k)

private def rLFrameIn (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame [(.chain [], [.ref "$c1958"])] rLEnvOut [Loc.base ⟨54⟩] []
    (rLKglue plans env k) false

private def rLAssign : Stmt :=
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

private def rLKget (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .callArgsK ⟨"raftpb.Entry.GetIndex"⟩
    [(.chain [], [.ref "$c1959"])] [] [] rLEnvIn
    (.seq [rLAssign] rLEnvIn (rLFrameIn plans env k))

private def rLKlen (c1959v : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) : Cont :=
  .strictK (.convert (.int .uint64)) [] [] rLEnvIn
    (.strictK .add [c1959v] [] rLEnvIn
      (.strictK .sub [] [.intLit 1 .uint64] rLEnvIn
        (.rhsK .vals [.chain (.addr (Loc.base ⟨54⟩)) [] []] [] []
          (.seqn #[]) rLEnvIn
          (.seq [.returnStmt] rLEnvIn (rLFrameIn plans env k)))))

/-- The rl.lastIndex in-span state former (frame cells 39-55 +
extras; the maybeLastIndex-era constants pinned at their post-W1
values — note the inlined length local at 46 is `.int`-kinded). -/
private def rLIn (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (mb : Bool) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (r0 iw lir0 c1958 ir0 c1959 : GoValue)
    (extra : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV rlStorageIfaceV
            (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
            uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32),
       (Loc.base ⟨33⟩,
        { declaredTy := none
          value := msCellV34 mb hsL snL csv so ln sc }),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36), (Loc.base ⟨37⟩, c37),
       (Loc.base ⟨38⟩, c38),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raftLog"⟩))
          value := rlArgV }),
       (Loc.base ⟨40⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 }),
       (Loc.base ⟨41⟩,
        { declaredTy := some (Ty.int .uint64), value := .int 0 .uint64 }),
       (Loc.base ⟨42⟩,
        { declaredTy := some Ty.bool, value := .bool false }),
       (Loc.base ⟨43⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.unstable"⟩))
          value := rlUnstableFieldAddr }),
       (Loc.base ⟨44⟩,
        { declaredTy := some (Ty.int .uint64), value := .int 0 .uint64 }),
       (Loc.base ⟨45⟩,
        { declaredTy := some Ty.bool, value := .bool false }),
       (Loc.base ⟨46⟩,
        { declaredTy := some (Ty.int .int), value := .int 0 .int }),
       (Loc.base ⟨47⟩,
        { declaredTy := some (Ty.int .uint64), value := iw }),
       (Loc.base ⟨48⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := .nil }),
       (Loc.base ⟨49⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := .addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨50⟩,
        { declaredTy := some (Ty.int .uint64), value := lir0 }),
       (Loc.base ⟨51⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := .nil }),
       (Loc.base ⟨52⟩,
        { declaredTy := some (Ty.int .uint64), value := c1958 }),
       (Loc.base ⟨53⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩))
          value := .addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨54⟩,
        { declaredTy := some (Ty.int .uint64), value := ir0 }),
       (Loc.base ⟨55⟩,
        { declaredTy := some (Ty.int .uint64), value := c1959 })]
        ++ extra
      nextAddr := na }

/-- Window 1 (171 steps): entry, the inlined `maybeLastIndex` on the
EMPTY unstable (the length read reduces at the pinned len-0 live
slice — the landed empty-member escape), the `ok` branch (false),
the storage dispatch, the LastIndex walk's Lock + defer + counter
increment, to the inner `ents[0]` boundary. -/
private theorem rL_w1 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 171
      (rlFam dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        e23 e25 c32 c34 c35 c36 c37 c38)
      (.retV rlArgV
        (.callArgsK ⟨"raft.raftLog.lastIndex"⟩ plans [] [] env k)) ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet
            [.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩] [] rLEnvIn
            (rLKget plans env k)),
        rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsVL' a1 a2
            (IntKind.normalize .int
              (IntKind.normalize .int
                (IntKind.normalize .int a3 + 1)))
            a4 a5 a6
            (fun x => IntKind.normalize .int (IntKind.normalize .int x)))
          e23 e25 c32 c34 c35 c36 c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 56,
        ch) := by
  kernel_rfl

/-- Window 2 (67 steps, from the crossed index read): the `GetIndex`
call, the ents re-read, to the inner length boundary. -/
private theorem rL_w2 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c34 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c37 c38 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 67
      (rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32 c34
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 56)
      (.retV (.addr (Loc.base ⟨35⟩)) (rLKget plans env k)) ch
      = .ok (.retV (.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩)
          (.strictK
            (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
            [] [] rLEnvIn
            (rLKlen
              (.int (IntKind.normalize .uint64
                (IntKind.normalize .uint64 iv)) .uint64)
              plans env k)),
        rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32 c34
          (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 iv)) .uint64)
          [(Loc.base ⟨56⟩,
            { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
              value := .addr (Loc.base ⟨35⟩) }),
           (Loc.base ⟨57⟩,
            { declaredTy := some (Ty.int .uint64)
              value := .int (IntKind.normalize .uint64 iv) .uint64 })]
          58,
        ch) := by
  kernel_rfl

/-- Window 3 (82 steps, from the crossed length read): the arithmetic
spine, the walk's return + result glue + DEFERRED UNLOCK, the
storage frame exit, the err≠nil test (nil), the raftLog result
store, RETURN ARRIVAL at the defer-free outer frame. -/
private theorem rL_w3 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 c34 : HeapCell) (edty idty : Option Ty)
    (tmv typv dvv : GoValue) (c37 c38 : HeapCell)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 82
      (rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 a3 a4 a5 a6) e23 e25 c32 c34
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int iv .uint64)
        [(Loc.base ⟨56⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
            value := .addr (Loc.base ⟨35⟩) }),
         (Loc.base ⟨57⟩,
          { declaredTy := some (Ty.int .uint64)
            value := .int iv .uint64 })] 58)
      (.retV (.int (Int.ofNat (kn+1)) .int)
        (rLKlen (.int iv .uint64) plans env k)) ch
      = .ok (.returning (rLFrame plans env k),
        rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc false hsL snL
          (msStatsV (IntKind.normalize .int a1)
            (IntKind.normalize .int a2) (IntKind.normalize .int a3)
            (IntKind.normalize .int a4) (IntKind.normalize .int a5)
            (IntKind.normalize .int a6))
          e23 e25 c32 c34 (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (IntKind.normalize .uint64
                      (IntKind.normalize .uint64
                        (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                        - 1))))))) .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (IntKind.normalize .uint64
                      (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                      - 1)))))) .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (IntKind.normalize .uint64
                    (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                    - 1))))) .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (IntKind.normalize .uint64
                  (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                  - 1)))) .uint64)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64
                (iv + IntKind.normalize .uint64 (Int.ofNat (kn+1)))
                - 1))) .uint64)
          (.int iv .uint64)
          [(Loc.base ⟨56⟩,
            { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
              value := .addr (Loc.base ⟨35⟩) }),
           (Loc.base ⟨57⟩,
            { declaredTy := some (Ty.int .uint64)
              value := .int iv .uint64 }),
           (Loc.base ⟨58⟩,
            { declaredTy := some (Ty.pointer (Ty.sync .mutex))
              value := msMutexAddr33 })] 59,
        ch) := by
  kernel_rfl

/-- **THE `raftLog.lastIndex` CallSpecR** (quiesced family): returns
`ents[0].Index + len(ents) - 1` — the storage route's exact result
(the unstable is empty, by the family); the raftLog cell reads back
UNCHANGED, the ms cell with the mutex unlocked again and exactly the
`callStats.lastIndex` counter incremented. -/
theorem raftLog_lastIndex_callSpecR (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so kn sc : Nat) (iv a1 a2 a3 a4 a5 a6 : Int) (hsL snL : Loc)
    (e23 e25 c32 : HeapCell) (adty edty idty : Option Ty)
    (values : Array GoValue) (tmv typv dvv : GoValue)
    (c37 c38 : HeapCell)
    (hsc : kn + 1 ≤ sc) (hk : kn + 1 < 9223372036854775808)
    (hget : values[so]? = some (.addr (Loc.base ⟨35⟩)))
    (hiv0 : 0 ≤ iv)
    (hivk : iv + Int.ofNat (kn + 1) < 18446744073709551616)
    (ha1a : -9223372036854775808 ≤ a1) (ha1b : a1 < 9223372036854775808)
    (ha2a : -9223372036854775808 ≤ a2) (ha2b : a2 < 9223372036854775808)
    (ha4a : -9223372036854775808 ≤ a4) (ha4b : a4 < 9223372036854775808)
    (ha5a : -9223372036854775808 ≤ a5) (ha5b : a5 < 9223372036854775808)
    (ha6a : -9223372036854775808 ≤ a6) (ha6b : a6 < 9223372036854775808)
    (ha3a : -9223372036854775808 ≤ a3)
    (ha3b : a3 + 1 < 9223372036854775808) :
    CallSpecR
      (RLPre dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc hsL snL (msStatsV a1 a2 a3 a4 a5 a6)
        e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38)
      ⟨"raft.raftLog.lastIndex"⟩ [] rlArgV
      (fun σ' vs =>
        vs = [.int (iv + Int.ofNat (kn+1) - 1) .uint64] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV rlStorageIfaceV
                     (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
                     uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
                     pzv } ∧
        Heap.lookup σ'.heap (Loc.base ⟨33⟩)
          = some { declaredTy := none
                   value := msCellV34 false hsL snL
                     (msStatsV a1 a2 (a3 + 1) a4 a5 a6)
                     so (kn+1) sc }) := by
  intro σ hP plans env k ch
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
  have h1 := rL_w1 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so kn sc a1 a2 a3 a4 a5 a6 hsL snL e23 e25 c32
    { declaredTy := adty, value := .array values }
    (rlEntry0 edty tmv typv dvv)
    { declaredTy := idty, value := .int iv .uint64 } c37 c38
    plans env k ch
  simp only [msStatsVL', hA1, hA2, hA3, hA31, hA4, hA5, hA6] at h1
  have hload : loadLoc
      (rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 56)
      (Loc.base ⟨34⟩) = .ok (.array values) := rfl
  have hx1 : stepFn
      (rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 56)
      (.retV (.int 0 .int)
        (.strictK .indexGet
          [.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩] [] rLEnvIn
          (rLKget plans env k))) ch
      = .ok (.retV (.addr (Loc.base ⟨35⟩)) (rLKget plans env k),
        rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
          { declaredTy := adty, value := .array values }
          (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64) [] 56,
        ch) :=
    stepFn_strict_apply
      (applyStrict_indexGet_slice (j := 0) hsc (Nat.succ_pos kn) hload
        hget)
  have h2 := rL_w2 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so kn sc iv a1 a2 (a3 + 1) a4 a5 a6 hsL snL e23 e25 c32
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c37 c38 plans env k ch
  rw [hIv, hIv] at h2
  have hx2 : stepFn
      (rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so (kn+1) sc true hsL snL
        (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
        { declaredTy := adty, value := .array values }
        (rlEntry0 edty tmv typv dvv)
        { declaredTy := idty, value := .int iv .uint64 } c37 c38
        (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
        (.int 0 .uint64) (.int 0 .uint64) (.int iv .uint64)
        [(Loc.base ⟨56⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
            value := .addr (Loc.base ⟨35⟩) }),
         (Loc.base ⟨57⟩,
          { declaredTy := some (Ty.int .uint64)
            value := .int iv .uint64 })] 58)
      (.retV (.slice ⟨some (Loc.base ⟨34⟩), so, kn+1, sc⟩)
        (.strictK
          (.lengthOf (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩)))))
          [] [] rLEnvIn
          (rLKlen (.int iv .uint64) plans env k))) ch
      = .ok (.retV (.int (Int.ofNat (kn+1)) .int)
          (rLKlen (.int iv .uint64) plans env k),
        rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so (kn+1) sc true hsL snL
          (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
          { declaredTy := adty, value := .array values }
          (rlEntry0 edty tmv typv dvv)
          { declaredTy := idty, value := .int iv .uint64 } c37 c38
          (.int 0 .uint64) (.int 0 .uint64) (.int 0 .uint64)
          (.int 0 .uint64) (.int 0 .uint64) (.int iv .uint64)
          [(Loc.base ⟨56⟩,
            { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
              value := .addr (Loc.base ⟨35⟩) }),
           (Loc.base ⟨57⟩,
            { declaredTy := some (Ty.int .uint64)
              value := .int iv .uint64 })] 58,
        ch) :=
    stepFn_strict_apply (applyStrict_length_slice hsc)
  have h3 := rL_w3 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so kn sc iv a1 a2 (a3 + 1) a4 a5 a6 hsL snL e23 e25 c32
    { declaredTy := adty, value := .array values }
    edty idty tmv typv dvv c37 c38 plans env k ch
  rw [hcolU, hAdd, hSub, hSub, hSub, hSub, hSub, hSub] at h3
  simp only [hA1, hA2, hA31, hA4, hA5, hA6] at h3
  refine ⟨171 + (1 + (67 + (1 + 82))),
    rLIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv
      so (kn+1) sc false hsL snL
      (msStatsV a1 a2 (a3 + 1) a4 a5 a6) e23 e25 c32
      { declaredTy := adty, value := .array values }
      (rlEntry0 edty tmv typv dvv)
      { declaredTy := idty, value := .int iv .uint64 } c37 c38
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (.int (iv + Int.ofNat (kn+1) - 1) .uint64)
      (.int iv .uint64)
      [(Loc.base ⟨56⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))
          value := .addr (Loc.base ⟨35⟩) }),
       (Loc.base ⟨57⟩,
        { declaredTy := some (Ty.int .uint64)
          value := .int iv .uint64 }),
       (Loc.base ⟨58⟩,
        { declaredTy := some (Ty.pointer (Ty.sync .mutex))
          value := msMutexAddr33 })] 59,
    [Loc.base ⟨40⟩], [.int (iv + Int.ofNat (kn+1) - 1) .uint64], ch,
    ?_, ?_, ⟨rfl, rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2) h3)))
  · rfl
  · rfl

end RlLastIndex

/-! ## `raft.raftLog.zeroTermOnOutOfBounds` (census log.go:567 —
reachable via log-ARGUMENT evaluation, census §1 NB) at the subject's
own error trichotomy (nil / ErrCompacted / ErrUnavailable)

The error-global comparisons are INTERFACE equalities: same concrete
dynamic type (`*errors.errorString` — the $pkginit `errors.New`
shape, program text), payload-ADDRESS comparison. The family pins
the globals' interface SHAPE with FREE payload addresses; the
identical-global crossing closes by `LawfulBEq Loc` reflexivity, the
distinct-globals crossing by a reader-vocabulary distinctness fact
(statics at distinct addresses — the invariant's C1). The Panicf arm
(any OTHER error) is the census-U3 obligation: unreachable for the
three family shapes by construction (no member covers it — a caller
passing a non-log error is outside every family). -/

section RlZeroTerm

/-- The error-global interface shape (`errors.New` product): dynamic
type `*errors.errorString`, free payload address. -/
def errIfaceV (p : Loc) : GoValue :=
  .interface (.pointer (.defined ⟨"errors.errorString"⟩)) (.addr p)

/-- Interface equality at the SAME error global: reduces to the
payload-address `BEq`, closed by `LawfulBEq Loc`. -/
private theorem valueEq_err_same (σ : ExecState) (p : Loc) :
    valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV p)
      = .ok true := by
  have h1 : valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV p)
      = .ok (p == p) := by kernel_rfl
  rw [h1, beq_self_eq_true]

/-- Interface equality at DISTINCT error globals (the reader-vocabulary
distinctness fact — statics at distinct addresses). -/
private theorem valueEq_err_ne (σ : ExecState) {p q : Loc}
    (hne : p ≠ q) :
    valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV q)
      = .ok false := by
  have h1 : valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV q)
      = .ok (p == q) := by kernel_rfl
  rw [h1, beq_eq_false_iff_ne.mpr hne]

private theorem applyStrict_eqCmp_err_same {σ : ExecState} (p : Loc) :
    applyStrictOp σ (.eqCmp (.interface ⟨"error"⟩))
      [errIfaceV p, errIfaceV p] = .ok (.bool true, σ) := by
  have h1 : applyStrictOp σ (.eqCmp (.interface ⟨"error"⟩))
      [errIfaceV p, errIfaceV p]
      = (valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV p)
          >>= fun b => pure (.bool b, σ)) := rfl
  rw [h1, valueEq_err_same]
  rfl

private theorem applyStrict_eqCmp_err_ne {σ : ExecState} {p q : Loc}
    (hne : p ≠ q) :
    applyStrictOp σ (.eqCmp (.interface ⟨"error"⟩))
      [errIfaceV p, errIfaceV q] = .ok (.bool false, σ) := by
  have h1 : applyStrictOp σ (.eqCmp (.interface ⟨"error"⟩))
      [errIfaceV p, errIfaceV q]
      = (valueEq σ (.interface ⟨"error"⟩) (errIfaceV p) (errIfaceV q)
          >>= fun b => pure (.bool b, σ)) := rfl
  rw [h1, valueEq_err_ne σ hne]
  rfl

private def ztEnv : LocalEnv :=
  [[], [("$res0", Loc.base ⟨42⟩), ("err", Loc.base ⟨41⟩),
        ("t", Loc.base ⟨40⟩), ("l", Loc.base ⟨39⟩)]]

private def ztFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨42⟩] [] k false

private def ztArm : Stmt :=
  .block #[] #[.seqn #[
    .assign (.var "$res0") (.intLit 0 .uint64),
    .returnStmt]]

private def ztPanicSeq1 : Stmt :=
  .seqn #[
    .initialization ⟨"$c1084", .slice (.interface ⟨"any"⟩)⟩,
    .makeSlice (.var "$c1084") (.interface ⟨"any"⟩)
      (.intLit 1 .int) (some (.intLit 1 .int)),
    .assign
      (.addr (.indexAddr (.var "$c1084") (.intLit 0 .int)))
      (.var "err")]

private def ztPanicCall : Stmt :=
  .call #[] ⟨"raft.Logger.Panicf"⟩
    #[.fieldGet (.deref (.var "l") (.defined ⟨"raft.raftLog"⟩))
        ⟨"raft.raftLog"⟩ "logger",
      .stringLit ⟨#[117, 110, 101, 120, 112, 101, 99, 116, 101, 100,
        32, 101, 114, 114, 111, 114, 32, 40, 37, 118, 41]⟩,
      .var "$c1084"]

private def ztTail : Stmt :=
  .seqn #[.assign (.var "$res0") (.intLit 0 .uint64), .returnStmt]

private def ztKif (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .ifK ztArm (.seqn #[]) ztEnv
    (.seq [ztPanicSeq1, ztPanicCall, ztTail] ztEnv
      (ztFrame plans env k))

private def ztKor (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .orK
    (.eqCmp (.interface ⟨"error"⟩) (.var "err")
      (.deref (.locLit (Loc.base ⟨25⟩)) (.interface ⟨"error"⟩)))
    ztEnv (ztKif plans env k)

/-- The zeroTerm in-span state former (frame cells 39-42). -/
private def ztIn (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (tvv errvv r0 : GoValue) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨23⟩, e23), (Loc.base ⟨25⟩, e25),
       (Loc.base ⟨31⟩,
        { declaredTy := dty
          value := logCellV rlStorageIfaceV
            (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
            uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv }),
       (Loc.base ⟨32⟩, c32),
       (Loc.base ⟨33⟩,
        { declaredTy := none
          value := msCellV34 false hsL snL csv so ln sc }),
       (Loc.base ⟨34⟩, c34), (Loc.base ⟨35⟩, c35),
       (Loc.base ⟨36⟩, c36), (Loc.base ⟨37⟩, c37),
       (Loc.base ⟨38⟩, c38),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raftLog"⟩))
          value := rlArgV }),
       (Loc.base ⟨40⟩,
        { declaredTy := some (Ty.int .uint64), value := tvv }),
       (Loc.base ⟨41⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := errvv }),
       (Loc.base ⟨42⟩,
        { declaredTy := some (Ty.int .uint64), value := r0 })]
      nextAddr := 43 }

/-- The nil-arm span (PRIVATE — 26 steps, one window: the err = nil
comparison reduces, the arm returns `t`). -/
private theorem zt_nil (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell) (tv : Int)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 26
      (rlFam dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38)
      (.retV .nil
        (.callArgsK ⟨"raft.raftLog.zeroTermOnOutOfBounds"⟩ plans
          [rlArgV, .int tv .uint64] [] env k)) ch
      = .ok (.returning (ztFrame plans env k),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
          (.int (IntKind.normalize .uint64 tv) .uint64) (.nil)
          (.int (IntKind.normalize .uint64
            (IntKind.normalize .uint64 tv)) .uint64),
        ch) := by
  kernel_rfl

/-- **THE `zeroTermOnOutOfBounds` CallSpecR, nil-error member**:
returns `t` unchanged (the subject's pass-through arm). -/
theorem raftLog_zeroTerm_nil_callSpecR (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell) (tv : Int)
    (htv0 : 0 ≤ tv) (htv64 : tv < 18446744073709551616) :
    CallSpecR
      (RLPre dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38)
      ⟨"raft.raftLog.zeroTermOnOutOfBounds"⟩
      [rlArgV, .int tv .uint64] .nil
      (fun σ' vs =>
        vs = [.int tv .uint64] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV rlStorageIfaceV
                     (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
                     uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
                     pzv }) := by
  intro σ hP plans env k ch
  have hTv : IntKind.normalize .uint64 tv = tv :=
    normalize_uint64_eq htv0 htv64
  have h1 := zt_nil dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38 tv
    plans env k ch
  rw [hTv, hTv] at h1
  refine ⟨26,
    ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv
      so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
      (.int tv .uint64) (.nil) (.int tv .uint64),
    [Loc.base ⟨42⟩], [.int tv .uint64], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]; exact h1
  · rfl
  · rfl

/-- Window 1 of the error arms (20 steps): entry, the err = nil
comparison (interface vs nil — reduces at a free payload), the FALSE
branch, the ErrCompacted-global dereference, to the first
interface-equality boundary. -/
private theorem zt_w1 (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23ty e25ty : Option Ty) (pA : Loc) (ev25 : GoValue)
    (c32 c34 c35 c36 c37 c38 : HeapCell) (ep : Loc) (tv : Int)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 20
      (rlFam dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := ev25 }
        c32 c34 c35 c36 c37 c38)
      (.retV (errIfaceV ep)
        (.callArgsK ⟨"raft.raftLog.zeroTermOnOutOfBounds"⟩ plans
          [rlArgV, .int tv .uint64] [] env k)) ch
      = .ok (.retV (errIfaceV pA)
          (.strictK (.eqCmp (.interface ⟨"error"⟩)) [errIfaceV ep] []
            ztEnv (ztKor plans env k)),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv
          { declaredTy := e23ty, value := errIfaceV pA }
          { declaredTy := e25ty, value := ev25 }
          c32 c34 c35 c36 c37 c38
          (.int (IntKind.normalize .uint64 tv) .uint64)
          (errIfaceV ep) (.int 0 .uint64),
        ch) := by
  kernel_rfl

/-- Window 2 of the COMPACTED arm (18 steps, from the crossed TRUE
comparison): the or short-circuits, the zero arm, return arrival. -/
private theorem zt_w2C (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (errvv : GoValue) (tvv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 18
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
        tvv errvv (.int 0 .uint64))
      (.retV (.bool true) (ztKor plans env k)) ch
      = .ok (.returning (ztFrame plans env k),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
          tvv errvv (.int 0 .uint64),
        ch) := by
  kernel_rfl

/-- Window 2 of the UNAVAILABLE arm (7 steps, from the crossed FALSE
comparison): the or evaluates its second disjunct — the
ErrUnavailable-global dereference — to the second equality
boundary. -/
private theorem zt_w2U (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 : HeapCell) (e25ty : Option Ty) (pB : Loc)
    (c32 c34 c35 c36 c37 c38 : HeapCell)
    (errvv : GoValue) (tvv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 7
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv e23
        { declaredTy := e25ty, value := errIfaceV pB }
        c32 c34 c35 c36 c37 c38 tvv errvv (.int 0 .uint64))
      (.retV (.bool false) (ztKor plans env k)) ch
      = .ok (.retV (errIfaceV pB)
          (.strictK (.eqCmp (.interface ⟨"error"⟩)) [errvv] []
            ztEnv (.boolK (ztKif plans env k))),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv e23
          { declaredTy := e25ty, value := errIfaceV pB }
          c32 c34 c35 c36 c37 c38 tvv errvv (.int 0 .uint64),
        ch) := by
  kernel_rfl

/-- Window 3 of the UNAVAILABLE arm (18 steps, from the crossed TRUE
second comparison): the boolK/ifK, the zero arm, return arrival. -/
private theorem zt_w3U (dty : Option Ty) (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23 e25 c32 c34 c35 c36 c37 c38 : HeapCell)
    (errvv : GoValue) (tvv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 18
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
        tvv errvv (.int 0 .uint64))
      (.retV (.bool true) (.boolK (ztKif plans env k))) ch
      = .ok (.returning (ztFrame plans env k),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv e23 e25 c32 c34 c35 c36 c37 c38
          tvv errvv (.int 0 .uint64),
        ch) := by
  kernel_rfl

/-- **THE `zeroTermOnOutOfBounds` CallSpecR, ErrCompacted member**
(the error IS the compacted global's value — the same free payload
address): returns `0`. -/
theorem raftLog_zeroTerm_compacted_callSpecR (dty : Option Ty)
    (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23ty e25ty : Option Ty) (pA : Loc) (ev25 : GoValue)
    (c32 c34 c35 c36 c37 c38 : HeapCell) (tv : Int)
    (htv0 : 0 ≤ tv) (htv64 : tv < 18446744073709551616) :
    CallSpecR
      (RLPre dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := ev25 }
        c32 c34 c35 c36 c37 c38)
      ⟨"raft.raftLog.zeroTermOnOutOfBounds"⟩
      [rlArgV, .int tv .uint64] (errIfaceV pA)
      (fun σ' vs =>
        vs = [.int 0 .uint64] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV rlStorageIfaceV
                     (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
                     uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
                     pzv }) := by
  intro σ hP plans env k ch
  have hTv : IntKind.normalize .uint64 tv = tv :=
    normalize_uint64_eq htv0 htv64
  have h1 := zt_w1 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv e23ty e25ty pA ev25
    c32 c34 c35 c36 c37 c38 pA tv plans env k ch
  rw [hTv] at h1
  have hx : stepFn
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := ev25 }
        c32 c34 c35 c36 c37 c38
        (.int tv .uint64) (errIfaceV pA) (.int 0 .uint64))
      (.retV (errIfaceV pA)
        (.strictK (.eqCmp (.interface ⟨"error"⟩)) [errIfaceV pA] []
          ztEnv (ztKor plans env k))) ch
      = .ok (.retV (.bool true) (ztKor plans env k),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv
          { declaredTy := e23ty, value := errIfaceV pA }
          { declaredTy := e25ty, value := ev25 }
          c32 c34 c35 c36 c37 c38
          (.int tv .uint64) (errIfaceV pA) (.int 0 .uint64),
        ch) :=
    stepFn_strict_apply (applyStrict_eqCmp_err_same pA)
  have h2 := zt_w2C dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv
    { declaredTy := e23ty, value := errIfaceV pA }
    { declaredTy := e25ty, value := ev25 }
    c32 c34 c35 c36 c37 c38 (errIfaceV pA) (.int tv .uint64)
    plans env k ch
  refine ⟨20 + (1 + 18),
    ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv
      so ln sc hsL snL csv
      { declaredTy := e23ty, value := errIfaceV pA }
      { declaredTy := e25ty, value := ev25 }
      c32 c34 c35 c36 c37 c38
      (.int tv .uint64) (errIfaceV pA) (.int 0 .uint64),
    [Loc.base ⟨42⟩], [.int 0 .uint64], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx) h2)
  · rfl
  · rfl

/-- **THE `zeroTermOnOutOfBounds` CallSpecR, ErrUnavailable member**
(the error IS the unavailable global's value; the two globals'
payload addresses are DISTINCT — the reader-vocabulary statics
fact): returns `0`. -/
theorem raftLog_zeroTerm_unavailable_callSpecR (dty : Option Ty)
    (uo uc : Nat)
    (uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv : GoValue)
    (so ln sc : Nat) (hsL snL : Loc) (csv : GoValue)
    (e23ty e25ty : Option Ty) (pA pB : Loc)
    (c32 c34 c35 c36 c37 c38 : HeapCell) (tv : Int)
    (htv0 : 0 ≤ tv) (htv64 : tv < 18446744073709551616)
    (hne : pB ≠ pA) :
    CallSpecR
      (RLPre dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := errIfaceV pB }
        c32 c34 c35 c36 c37 c38)
      ⟨"raft.raftLog.zeroTermOnOutOfBounds"⟩
      [rlArgV, .int tv .uint64] (errIfaceV pB)
      (fun σ' vs =>
        vs = [.int 0 .uint64] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := logCellV rlStorageIfaceV
                     (.slice ⟨some (Loc.base ⟨32⟩), uo, 0, uc⟩)
                     uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
                     pzv }) := by
  intro σ hP plans env k ch
  have hTv : IntKind.normalize .uint64 tv = tv :=
    normalize_uint64_eq htv0 htv64
  have h1 := zt_w1 dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv e23ty e25ty pA (errIfaceV pB)
    c32 c34 c35 c36 c37 c38 pB tv plans env k ch
  rw [hTv] at h1
  have hx1 : stepFn
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := errIfaceV pB }
        c32 c34 c35 c36 c37 c38
        (.int tv .uint64) (errIfaceV pB) (.int 0 .uint64))
      (.retV (errIfaceV pA)
        (.strictK (.eqCmp (.interface ⟨"error"⟩)) [errIfaceV pB] []
          ztEnv (ztKor plans env k))) ch
      = .ok (.retV (.bool false) (ztKor plans env k),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv
          { declaredTy := e23ty, value := errIfaceV pA }
          { declaredTy := e25ty, value := errIfaceV pB }
          c32 c34 c35 c36 c37 c38
          (.int tv .uint64) (errIfaceV pB) (.int 0 .uint64),
        ch) :=
    stepFn_strict_apply (applyStrict_eqCmp_err_ne hne)
  have h2 := zt_w2U dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv
    { declaredTy := e23ty, value := errIfaceV pA } e25ty pB
    c32 c34 c35 c36 c37 c38 (errIfaceV pB) (.int tv .uint64)
    plans env k ch
  have hx2 : stepFn
      (ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
        pzv so ln sc hsL snL csv
        { declaredTy := e23ty, value := errIfaceV pA }
        { declaredTy := e25ty, value := errIfaceV pB }
        c32 c34 c35 c36 c37 c38
        (.int tv .uint64) (errIfaceV pB) (.int 0 .uint64))
      (.retV (errIfaceV pB)
        (.strictK (.eqCmp (.interface ⟨"error"⟩)) [errIfaceV pB] []
          ztEnv (.boolK (ztKif plans env k)))) ch
      = .ok (.retV (.bool true) (.boolK (ztKif plans env k)),
        ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv
          pzv so ln sc hsL snL csv
          { declaredTy := e23ty, value := errIfaceV pA }
          { declaredTy := e25ty, value := errIfaceV pB }
          c32 c34 c35 c36 c37 c38
          (.int tv .uint64) (errIfaceV pB) (.int 0 .uint64),
        ch) :=
    stepFn_strict_apply (applyStrict_eqCmp_err_same pB)
  have h3 := zt_w3U dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv
    aszv pzv so ln sc hsL snL csv
    { declaredTy := e23ty, value := errIfaceV pA }
    { declaredTy := e25ty, value := errIfaceV pB }
    c32 c34 c35 c36 c37 c38 (errIfaceV pB) (.int tv .uint64)
    plans env k ch
  refine ⟨20 + (1 + (7 + (1 + 18))),
    ztIn dty uo uc uoffv sipv oipv ulgv cv apv adv lgv mxv aszv pzv
      so ln sc hsL snL csv
      { declaredTy := e23ty, value := errIfaceV pA }
      { declaredTy := e25ty, value := errIfaceV pB }
      c32 c34 c35 c36 c37 c38
      (.int tv .uint64) (errIfaceV pB) (.int 0 .uint64),
    [Loc.base ⟨42⟩], [.int 0 .uint64], ch, ?_, ?_, ⟨rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx1)
      (stepFnIter_chain h2 (stepFnIter_chain (stepFnIter_one hx2) h3)))
  · rfl
  · rfl

end RlZeroTerm

/-- Non-vacuity of the quiesced-family carrier (the ∃-discharge,
concrete values in every free slot). -/
theorem rlPre_inhabited :
    RLPre none 0 3 (.int 104 .uint64) (.bool false) (.int 104 .uint64)
      .nil (.int 103 .uint64) (.int 103 .uint64) (.int 103 .uint64)
      .nil (.int 1048576 .uint64) (.int 0 .uint64) (.bool false)
      1 3 5 (.base ⟨10⟩) (.base ⟨11⟩) (msStatsV 3 4 5 6 7 8)
      ⟨none, .int 777 .int⟩ ⟨none, .int 777 .int⟩
      ⟨none, .array #[.nil, .nil, .nil]⟩
      ⟨none, .array #[.nil, .addr (.base ⟨35⟩), .addr (.base ⟨37⟩),
        .addr (.base ⟨37⟩), .nil]⟩
      (rlEntry0 none .nil (.int 0 .int32) .nil)
      ⟨none, .int 101 .uint64⟩
      (rlEntryJ none .nil (.int 0 .int32) .nil)
      ⟨none, .int 9 .uint64⟩
      (rlFam none 0 3 (.int 104 .uint64) (.bool false)
        (.int 104 .uint64) .nil (.int 103 .uint64) (.int 103 .uint64)
        (.int 103 .uint64) .nil (.int 1048576 .uint64)
        (.int 0 .uint64) (.bool false)
        1 3 5 (.base ⟨10⟩) (.base ⟨11⟩) (msStatsV 3 4 5 6 7 8)
        ⟨none, .int 777 .int⟩ ⟨none, .int 777 .int⟩
        ⟨none, .array #[.nil, .nil, .nil]⟩
        ⟨none, .array #[.nil, .addr (.base ⟨35⟩), .addr (.base ⟨37⟩),
          .addr (.base ⟨37⟩), .nil]⟩
        (rlEntry0 none .nil (.int 0 .int32) .nil)
        ⟨none, .int 101 .uint64⟩
        (rlEntryJ none .nil (.int 0 .int32) .nil)
        ⟨none, .int 9 .uint64⟩) := rfl

end GoLean.RaftSeam
