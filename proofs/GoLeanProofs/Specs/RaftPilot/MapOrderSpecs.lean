import GoLeanProofs.Specs.RaftPilot.SymBase
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.MapPerm

/-!
# W3 w3-m — the (M)-mechanism member specs (first consumers)

The first REAL consumers of the (M) permutation-family carrier
(`GoLeanProofs/MapPerm.lean`; design note
`docs/2026-08-27_m-mechanism-design.md`): the parked init-chain
member `quorum.JointConfig.IDs` (census §2.6 — called by
`checkInvariants` at every `Simple` round and by `VoterNodes`),
proved at the FULL permutation family — ∀ id lists (arbitrary
length and order, nodup, u64-normalized), concluding the built map's
entries as an ∃-packaged `List.Perm` family member — plus the
order-insensitive READBACK consumers (the U3.2f Base-clause
vocabulary shape: population + lookup-defined, transferred across
the family by the layer-1 quotient-crossing lemmas).

**QUANTIFIER AUDIT (the charter's opening requirement):** the
`CallSpecR` here discharges ∀-state over the member's footprint
family — which now INCLUDES the ∀ over the source map's association
order (the (M) family, demonically re-quantified at consumption) —
∀ plans/env/k, ∀ ch (the map-range draws discharged by
`mapPickLoop_perm`, the W2 pick-loop rule at the Perm-conservation
invariant — never by instances), ∃ n. The built order is ∃-packaged
in the postcondition as a `List.Perm` member in reader vocabulary.
No end-theorem quantifier closes here.

**The pattern:** the U3.1-A recipe (canonical placement from
`.base ⟨31⟩`, probe-first — trace `artifacts/w3m/probe-ids*.out`,
untracked scaffolding; every transcription re-checked by the span
lemmas' `kernel_rfl`), EXTENDED by the (M) treatment: the source
map's entry list and the built map's entry list ride SYMBOLICALLY
through every kernel window (values are never scrutinized by the
walked steps — the U3.1-F symbolic-memory discipline extended by one
list parameter per map), the range picks go through the value-generic
pick-step family, and the loop closes by `mapPickLoop_perm`.

Statement hygiene: step counts only in private span lemmas; exports
count-free (∃ n). No `SpecJudgment` change (the w3-m serialization
rule).
-/

namespace GoLean.RaftSeam.MOrder

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec
open GoLean.Surface
open GoLean.MapMem (toKeys)
open GoLean.MapPerm
open GoLean.RaftSeam (wBase)

set_option maxRecDepth 8000000
set_option maxHeartbeats 256000000
set_option smartUnfolding false

/-! ## Shared formers (types/values; the census: `quorum.JointConfig`
= `[2]MajorityConfig`, `MajorityConfig` = `map[uint64]struct{}`) -/

def tU64 : Ty := .int .uint64
def tUnit : Ty := .defined ⟨"struct{}"⟩
def tMaj : Ty := .defined ⟨"quorum.MajorityConfig"⟩
def tJoint : Ty := .defined ⟨"quorum.JointConfig"⟩
def tMapUS : Ty := .map tU64 tUnit

/-- The `struct{}{}` value (the machine's struct-lit at the empty
struct type — probe-confirmed shape). -/
def unitV : GoValue := .struct ⟨"struct{}"⟩ #[]

/-- An id list as a `map[uint64]struct{}` association list (the (M)
family's canonical spelling: the ORDER of `ids` is the family
parameter). -/
def idKV (ids : List Int) : List (Int × GoValue) :=
  ids.map (fun i => (i, unitV))

theorem idKV_keys : ∀ ids : List Int, (idKV ids).map Prod.fst = ids := by
  intro ids
  induction ids with
  | nil => rfl
  | cons a t ih => simpa [idKV] using ih

theorem idKV_filter (ids done : List Int) :
    (idKV ids).filter (fun p => !done.contains p.1)
      = idKV (ids.filter (fun i => !done.contains i)) := by
  simp [idKV, List.filter_map]
  rfl

/-! ## The lowered-body statement vocabulary (transcribed from the
pinned wire via the probe at step granularity; a wrong transcription
fails the kernel spans loudly) -/

/-- The inner range body: `m[id] = struct{}{}`. -/
def asgnBody : Stmt :=
  .mapAssign (.var "m") (.var "id") (.structLit tUnit #[]) tU64 tUnit
def rBody : Stmt := .block #[] #[asgnBody]

/-- The outer (array-range desugar) loop body. -/
def outerBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$rfirst")
        (.assign (.var "$rfirst") (.boolLit false))
        (.assign (.var "$ridx")
          (.add (.var "$ridx") (.intLit 1 .int))),
      .ifThenElse (.atLeastCmp (.var "$ridx") (.var "$rlen"))
        (.breakStmt) (.seqn #[]),
      .initialization { id := "cc", typ := tMaj },
      .assign (.var "cc") (.indexGet (.var "$rcoll") (.var "$ridx")),
      .block #[]
        #[.mapRange (some "id") none (.var "cc") tU64 tUnit rBody]]

def retSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "m"), .returnStmt]

/-! ## The environment tower (probe step 118) -/

def env0 : LocalEnv := [[("$res0", .base ⟨33⟩), ("c", .base ⟨32⟩)]]
def env1 : LocalEnv :=
  [("m", .base ⟨36⟩), ("$c3", .base ⟨34⟩)] :: env0
def env2 : LocalEnv :=
  [("$rfirst", .base ⟨40⟩), ("$ridx", .base ⟨39⟩),
   ("$rlen", .base ⟨38⟩), ("$rcoll", .base ⟨37⟩)] :: env1
def env3 : LocalEnv := [("cc", .base ⟨41⟩)] :: env2
def env4 : LocalEnv := ([] : List (String × Loc)) :: env3
/-- The per-iteration env: the pick's key binder over the pushed
scope (`bindIterVars` at key-only binding; `na` = the key cell). -/
def envIter (na : Nat) : LocalEnv := [("id", .base ⟨na⟩)] :: env4
def envBody (na : Nat) : LocalEnv :=
  ([] : List (String × Loc)) :: envIter na

/-! ## The continuation tower (probe step 118) -/

/-- The post-loop tail: scope pop, the return sequence, the
CallSpecR frame (plans/caller-env/k OPEN — target- and
continuation-parametric). -/
def kRet (plans : List (TargetShape × List Expr)) (envC : LocalEnv)
    (kC : Cont) : Cont :=
  .seq [retSeqn] env1 (.frame plans envC [.base ⟨33⟩] [] kC false)
def kLoop (plans : List (TargetShape × List Expr)) (envC : LocalEnv)
    (kC : Cont) : Cont :=
  .loop (.boolLit true) outerBody env2 (.seq [] env2 (kRet plans envC kC))
def kTail (plans : List (TargetShape × List Expr)) (envC : LocalEnv)
    (kC : Cont) : Cont :=
  .seq [] env4 (.seq [] env3 (kLoop plans envC kC))
/-- The inner range head at produced set `pr` and start set `st`. -/
def iterK (plans : List (TargetShape × List Expr)) (envC : LocalEnv)
    (kC : Cont) (pr st : Array GoValue) : Cont :=
  .mapIterK (some "id") none tU64 tUnit rBody (some (.base ⟨31⟩))
    pr st env4 (kTail plans envC kC)

/-! ## The heap family -/

/-- The source-map data cell (the (M) family input: `es` rides
symbolically through every window). -/
def srcCell (es : List (Int × GoValue)) : HeapCell :=
  ⟨none, .mapData (toEntriesV es)⟩

def recvV : GoValue :=
  .array #[.map ⟨some (.base ⟨31⟩)⟩, .map ⟨none⟩]

/-- The fixed loop-phase cells 31–41 (probe heap at step 118),
parameterized by the two riding map-data VALUES. `res0v`
distinguishes the loop phase (nil) from the post-return phase
(`map@35`); `ridx` likewise. -/
def coreCells (v31 b35 res0v : GoValue) (ridx : Int) : Heap :=
  [(.base ⟨31⟩, ⟨none, v31⟩),
   (.base ⟨32⟩, ⟨some tJoint, recvV⟩),
   (.base ⟨33⟩, ⟨some tMapUS, res0v⟩),
   (.base ⟨34⟩, ⟨some tMapUS, .map ⟨some (.base ⟨35⟩)⟩⟩),
   (.base ⟨35⟩, ⟨none, b35⟩),
   (.base ⟨36⟩, ⟨some tMapUS, .map ⟨some (.base ⟨35⟩)⟩⟩),
   (.base ⟨37⟩, ⟨some tJoint, recvV⟩),
   (.base ⟨38⟩, ⟨some (.int .int), .int 2 .int⟩),
   (.base ⟨39⟩, ⟨some (.int .int), .int ridx .int⟩),
   (.base ⟨40⟩, ⟨some .bool, .bool false⟩),
   (.base ⟨41⟩, ⟨some tMaj, .map ⟨some (.base ⟨31⟩)⟩⟩)]

/-- The loop-phase state family: source order `ids`, built-so-far
order `done`, the dead per-iteration key cells `tail`, the
allocation front `na`. -/
def SL (ids done : List Int) (tail : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0 ++ tail,
      nextAddr := na }

/-- The pre-state heap: the source cell alone at the canonical
anchor. -/
def preHeapV (v31 : GoValue) : Heap := [(.base ⟨31⟩, ⟨none, v31⟩)]

/-- The pre-state: the source cell alone at the canonical anchor. -/
def IDsPre (ids : List Int) (σm : ExecState) : Prop :=
  σm = { wBase with
          heap := preHeapV (.mapData (toEntriesV (idKV ids)))
          nextAddr := 32 }

/-! ## W1 — the entry window (117 steps, kernel, zero draws): frame
entry, `m := map[uint64]struct{}{}`, the outer-range prelude
(`$rcoll`/`$rlen`/`$ridx`/`$rfirst`), the first outer iteration's
head and `cc := c[0]`, up to the range-START delivery. The source
cell's VALUE rides fully symbolic (`v31`) — the window never reads
it. -/
private theorem ids_w1_span (v31 : GoValue)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv)
    (kC : Cont) (ch : Choices) :
    stepFnIter 117
      { wBase with
          heap := preHeapV v31
          nextAddr := 32 }
      (.retV recvV
        (.callArgsK ⟨"quorum.JointConfig.IDs"⟩ plans [] [] envC kC)) ch
      = .ok (.retV (.map ⟨some (.base ⟨31⟩)⟩)
            (.mapRangeK (some "id") none tU64 tUnit rBody env4
              (kTail plans envC kC)),
          { wBase with
              heap := coreCells v31 (.mapData #[]) (.map ⟨none⟩) 0
              nextAddr := 42 }, ch) := by
  kernel_rfl



/-! ## The pick-loop machinery (the (M) treatment: value-generic pick
steps + `mapPickLoop_perm`) -/

/-- The post-pick state: the key-binder cell appended past the dead
tail. -/
def SLK (ids done : List Int) (tail : Heap) (na : Nat) (kv : Int) :
    ExecState :=
  { wBase with
      heap := coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0
          ++ tail ++ [(.base ⟨na⟩, ⟨some tU64, .int kv .uint64⟩)]
      nextAddr := na + 1 }

/-- `struct{}{}` is self-normalized at its defined type (concrete
table walk). -/
private theorem unitV_norm :
    isNormalForTy wBase.types tUnit unitV = true := by
  with_unfolding_all rfl

private theorem unitV_normVal (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int) :
    normalizeValueForTy (SLK ids done tail na kv) tUnit unitV
      = .ok unitV := by
  with_unfolding_all rfl

private theorem toKeys_push (l : List Int) (a : Int) :
    (toKeys l).push (.int a .uint64) = toKeys (l ++ [a]) := by
  apply Array.toList_inj.mp
  simp [GoLean.MapMem.toKeys]

private theorem idKV_append_one (l : List Int) (a : Int) :
    idKV (l ++ [a]) = idKV l ++ [(a, unitV)] := by
  simp [idKV]

private theorem setkV_fresh {done : List Int} {a : Int}
    (h : a ∉ done) :
    setkV (idKV done) a unitV = idKV (done ++ [a]) := by
  rw [← idxOfV?_none_setkV (idxOfV?_none_of_not_mem (by
      rw [idKV_keys]; exact h)) unitV, idKV_append_one]

/-- Cells 31–41 miss every address ≥ 42 (executable key bound). -/
private theorem coreMiss (v31 b35 res0v : GoValue) (ridx : Int)
    {x : Nat} (hx : 42 ≤ x) :
    Heap.lookup (coreCells v31 b35 res0v ridx) (.base ⟨x⟩) = none :=
  lookup_of_keysBelow (by rfl) hx

/-- The loop-phase heap misses the allocation front. -/
private theorem slMiss (ids done : List Int) {tail : Heap} {na : Nat}
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    Heap.lookup (coreCells (.mapData (toEntriesV (idKV ids)))
        (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0 ++ tail)
      (.base ⟨na⟩) = none := by
  rw [lookup_append_right (coreMiss _ _ _ _ hna)]
  exact hdead na (Nat.le_refl na)

/-- THE PICK at the family (the value-generic key-only pick):
consumes one choice of width `rem.length` (the mandatory bit is
`true` — every candidate key is a start key), binds the key cell at
the front. -/
private theorem ids_pick (ids done : List Int)
    (rem : List (Int × GoValue)) (tail : Heap) (na idx : Nat)
    (p : Int × GoValue) (ch ch₂ : Choices)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (hnorm : ∀ i ∈ ids, IntKind.normalize .uint64 i = i)
    (hrem : rem = (idKV ids).filter (fun q => !done.contains q.1))
    (hcons : Choices.consume ch rem.length = (idx, ch₂))
    (hidx : idx < rem.length) (hp : rem[idx]? = some p)
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFn (SL ids done tail na)
      (.next (iterK plans envC kC (toKeys done) (toKeys ids))) ch
      = .ok (.exec rBody (envIter na)
            (iterK plans envC kC ((toKeys done).push (.int p.1 .uint64))
              (toKeys ids)),
          SLK ids done tail na p.1, ch₂) := by
  have hkv : ∀ q ∈ idKV ids, IntKind.normalize .uint64 q.1 = q.1
      ∧ isNormalForTy (SL ids done tail na).types tUnit q.2 = true := by
    intro q hq
    obtain ⟨i, hi, hqe⟩ := List.mem_map.mp hq
    subst hqe
    exact ⟨hnorm i hi, unitV_norm⟩
  have hcands : mapIterCandidates (SL ids done tail na) tU64 tUnit
      (some (.base ⟨31⟩)) (toKeys done) = .ok (toEntriesV rem) := by
    rw [hrem]
    exact candidates_toEntriesV (by rfl) hkv
  have hall : ∀ q ∈ rem, ids.contains q.1 := by
    intro q hq
    rw [hrem] at hq
    have hmem := (List.mem_filter.mp hq).1
    obtain ⟨i, hi, hqe⟩ := List.mem_map.mp hmem
    subst hqe
    simpa using hi
  have hne : rem ≠ [] := by
    intro hc
    rw [hc] at hidx
    exact absurd hidx (by simp)
  have hmand : mapIterMandatoryRemains (SL ids done tail na) tU64
      (toEntriesV rem) (toKeys ids) = .ok true :=
    mandatory_true_of_allV _ hne hall
  have hknorm : IntKind.normalize .uint64 p.1 = p.1 := by
    have hmem : p ∈ rem := by
      obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hp
      exact hg ▸ List.getElem_mem hlt
    rw [hrem] at hmem
    obtain ⟨i, hi, hqe⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
    rw [← hqe]
    exact hnorm i hi
  have hcons' : Choices.consume ch
      (rem.length + (if true then 0 else 1)) = (idx, ch₂) := by
    simpa using hcons
  have h := stepFn_pick_keyV (body := rBody) (env := env4)
    (k := kTail plans envC kC) (kv := "id") (ch := ch) (ch' := ch₂)
    hcands hmand hcons' hidx hp hknorm
  refine h.trans ?_
  have hheap : Heap.set (SL ids done tail na).heap
      (.base ⟨(SL ids done tail na).nextAddr⟩)
      (⟨some (.int .uint64), .int p.1 .uint64⟩ : HeapCell)
      = (coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0 ++ tail)
        ++ [(.base ⟨na⟩, ⟨some tU64, .int p.1 .uint64⟩)] := by
    show Heap.set (coreCells (.mapData (toEntriesV (idKV ids)))
        (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0 ++ tail)
        (.base ⟨na⟩) _ = _
    exact set_fresh (slMiss ids done hna hdead)
  rw [hheap]
  rfl

/-- Window₁ (5 steps, kernel): block entry through the `m` read to
the key-var read point. The three riding symbolic lists (`ids`,
`done` in the map cells, `tail`, the key cell) are never
scrutinized. -/
private theorem ids_win1 (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (pr : Array GoValue) (ch : Choices) :
    stepFnIter 5 (SLK ids done tail na kv)
      (.exec rBody (envIter na) (iterK plans envC kC pr (toKeys ids))) ch
      = .ok (.evalE (.var "id") (envBody na)
            (.stmtOpK (.mapAssign tU64 tUnit) 0
              [.map ⟨some (.base ⟨35⟩)⟩]
              [.structLit tUnit #[]] (envBody na)
              (.seq [] (envBody na)
                (iterK plans envC kC pr (toKeys ids)))),
          SLK ids done tail na kv, ch) := by
  kernel_rfl

/-- The key-var read (conditioned: the cell sits past the symbolic
tail). -/
private theorem ids_keyread (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int) (k : Cont) (ch : Choices)
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFn (SLK ids done tail na kv)
      (.evalE (.var "id") (envBody na) k) ch
      = .ok (.retV (.int kv .uint64) k, SLK ids done tail na kv, ch) := by
  have hlook : Heap.lookup (SLK ids done tail na kv).heap (.base ⟨na⟩)
      = some ⟨some tU64, .int kv .uint64⟩ := by
    show Heap.lookup ((_ ++ tail) ++ _) _ = _
    rw [lookup_append_right (slMiss ids done hna hdead),
      lookup_singleton_self]
  exact stepFn_var (by rfl) hlook

/-- Window₂ (2 steps, kernel): the picked key delivered → the
`struct{}{}` literal built. -/
private theorem ids_win2 (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (pr : Array GoValue) (ch : Choices) :
    stepFnIter 2 (SLK ids done tail na kv)
      (.retV (.int kv .uint64)
        (.stmtOpK (.mapAssign tU64 tUnit) 0
          [.map ⟨some (.base ⟨35⟩)⟩]
          [.structLit tUnit #[]] (envBody na)
          (.seq [] (envBody na)
            (iterK plans envC kC pr (toKeys ids))))) ch
      = .ok (.retV unitV
            (.stmtOpK (.mapAssign tU64 tUnit) 0
              [.int kv .uint64, .map ⟨some (.base ⟨35⟩)⟩] []
              (envBody na)
              (.seq [] (envBody na)
                (iterK plans envC kC pr (toKeys ids)))),
          SLK ids done tail na kv, ch) := by
  kernel_rfl

/-- The INSERT (conditioned): `mapAssignValue` on the built cell is
the value-generic update-or-append — at a fresh key, the APPEND (the
persistence primitive: built order = pick order). -/
private theorem ids_insert (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (pr : Array GoValue) (ch : Choices)
    (hknorm : IntKind.normalize .uint64 kv = kv)
    (hfresh : kv ∉ done) :
    stepFn (SLK ids done tail na kv)
      (.retV unitV
        (.stmtOpK (.mapAssign tU64 tUnit) 0
          [.int kv .uint64, .map ⟨some (.base ⟨35⟩)⟩] []
          (envBody na)
          (.seq [] (envBody na)
            (iterK plans envC kC pr (toKeys ids))))) ch
      = .ok (.next (.seq [] (envBody na)
            (iterK plans envC kC pr (toKeys ids))),
          SLK ids (done ++ [kv]) tail na kv, ch) := by
  have hlook : Heap.lookup (SLK ids done tail na kv).heap (.base ⟨35⟩)
      = some ⟨none, .mapData (toEntriesV (idKV done))⟩ := by
    show Heap.lookup ((_ ++ tail) ++ _) _ = _
    exact lookup_append_left (lookup_append_left (by rfl))
  have hassign := mapAssignValue_toEntriesV (valTy := tUnit)
    (v := unitV) hlook hknorm (unitV_normVal ids done tail na kv)
  rw [setkV_fresh hfresh] at hassign
  have h := stepFn_mapAssign_apply (env := envBody na)
    (k := .seq [] (envBody na) (iterK plans envC kC pr (toKeys ids)))
    (ch := ch) hassign
  refine h.trans ?_
  have hheap : Heap.set (SLK ids done tail na kv).heap (.base ⟨35⟩)
      (⟨none, .mapData (toEntriesV (idKV (done ++ [kv])))⟩ : HeapCell)
      = (coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV (done ++ [kv])))) (.map ⟨none⟩) 0
          ++ tail)
        ++ [(.base ⟨na⟩, ⟨some tU64, .int kv .uint64⟩)] := by
    show Heap.set ((coreCells (.mapData (toEntriesV (idKV ids)))
        (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0 ++ tail)
        ++ [(.base ⟨na⟩, ⟨some tU64, .int kv .uint64⟩)])
        (.base ⟨35⟩) _ = _
    rw [set_append_left (lookup_append_left
        (by rfl : Heap.lookup (coreCells
          (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0)
          (.base ⟨35⟩) = some ⟨none, .mapData (toEntriesV (idKV done))⟩)),
      set_append_left
        (by rfl : Heap.lookup (coreCells
          (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 0)
          (.base ⟨35⟩) = some ⟨none, .mapData (toEntriesV (idKV done))⟩)]
    rfl
  rw [hheap]
  rfl

/-- Window₃ (1 step, kernel): the scope pop back to the range
head. -/
private theorem ids_win3 (ids done : List Int) (tail : Heap)
    (na : Nat) (kv : Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (pr : Array GoValue) (ch : Choices) :
    stepFnIter 1 (SLK ids done tail na kv)
      (.next (.seq [] (envBody na)
        (iterK plans envC kC pr (toKeys ids)))) ch
      = .ok (.next (iterK plans envC kC pr (toKeys ids)),
          SLK ids done tail na kv, ch) := by
  kernel_rfl

/-- ONE ITERATION (11 steps): pick + body + back to the head — the
`mapPickLoop_perm` iteration shape. -/
private theorem ids_iteration (ids done : List Int)
    (rem : List (Int × GoValue)) (tail : Heap) (na idx : Nat)
    (p : Int × GoValue) (ch ch₂ : Choices)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (hnorm : ∀ i ∈ ids, IntKind.normalize .uint64 i = i)
    (hrem : rem = (idKV ids).filter (fun q => !done.contains q.1))
    (hcons : Choices.consume ch rem.length = (idx, ch₂))
    (hidx : idx < rem.length) (hp : rem[idx]? = some p)
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFnIter 11 (SL ids done tail na)
      (.next (iterK plans envC kC (toKeys done) (toKeys ids))) ch
      = .ok (.next (iterK plans envC kC (toKeys (done ++ [p.1]))
            (toKeys ids)),
          SL ids (done ++ [p.1])
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int p.1 .uint64⟩)])
            (na + 1), ch₂) := by
  have hpmem : p ∈ rem := by
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hp
    exact hg ▸ List.getElem_mem hlt
  have hfresh : p.1 ∉ done := by
    have := (List.mem_filter.mp (hrem ▸ hpmem)).2
    simpa using this
  have hknorm : IntKind.normalize .uint64 p.1 = p.1 := by
    obtain ⟨i, hi, hqe⟩ :=
      List.mem_map.mp (List.mem_filter.mp (hrem ▸ hpmem)).1
    rw [← hqe]
    exact hnorm i hi
  have h1 := stepFnIter_one
    (ids_pick ids done rem tail na idx p ch ch₂ plans envC kC
      hnorm hrem hcons hidx hp hna hdead)
  have h2 := stepFnIter_chain h1
    (ids_win1 ids done tail na p.1 plans envC kC
      ((toKeys done).push (.int p.1 .uint64)) ch₂)
  have h3 := stepFnIter_chain h2 (stepFnIter_one
    (ids_keyread ids done tail na p.1 _ ch₂ hna hdead))
  have h4 := stepFnIter_chain h3
    (ids_win2 ids done tail na p.1 plans envC kC
      ((toKeys done).push (.int p.1 .uint64)) ch₂)
  have h5 := stepFnIter_chain h4 (stepFnIter_one
    (ids_insert ids done tail na p.1 plans envC kC
      ((toKeys done).push (.int p.1 .uint64)) ch₂ hknorm hfresh))
  have h6 := stepFnIter_chain h5
    (ids_win3 ids (done ++ [p.1]) tail na p.1 plans envC kC
      ((toKeys done).push (.int p.1 .uint64)) ch₂)
  rw [toKeys_push] at h6
  show stepFnIter (1 + 5 + 1 + 2 + 1 + 1) _ _ _ = _
  exact h6

/-- The DONE step (1 step): no candidate remains — the range head
pops to the loop tail, no choice consumed. -/
private theorem ids_done_step (ids done : List Int) (tail : Heap)
    (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices)
    (hnorm : ∀ i ∈ ids, IntKind.normalize .uint64 i = i)
    (hall : (idKV ids).filter (fun q => !done.contains q.1) = []) :
    stepFnIter 1 (SL ids done tail na)
      (.next (iterK plans envC kC (toKeys done) (toKeys ids))) ch
      = .ok (.next (kTail plans envC kC), SL ids done tail na, ch) := by
  have hkv : ∀ q ∈ idKV ids, IntKind.normalize .uint64 q.1 = q.1
      ∧ isNormalForTy (SL ids done tail na).types tUnit q.2 = true := by
    intro q hq
    obtain ⟨i, hi, hqe⟩ := List.mem_map.mp hq
    subst hqe
    exact ⟨hnorm i hi, unitV_norm⟩
  have hcands : mapIterCandidates (SL ids done tail na) tU64 tUnit
      (some (.base ⟨31⟩)) (toKeys done) = .ok #[] := by
    have h := candidates_toEntriesV (ks := done)
      (a := ⟨31⟩) (dty := none) (valTy := tUnit)
      (kvs := idKV ids) (σ := SL ids done tail na) (by rfl) hkv
    rw [hall] at h
    exact h
  exact stepFnIter_one (stepFn_iter_doneV hcands)

/-- **THE DRAINED RANGE** — `mapPickLoop_perm` at this member: from
the empty produced set, the whole source map is visited in SOME pick
order `done'` (a permutation of `ids`, ∃-packaged), the built map's
entries are exactly `idKV done'`, at EVERY choice stream. -/
private theorem ids_loop (ids : List Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices)
    (hnd : ids.Nodup)
    (hnorm : ∀ i ∈ ids, IntKind.normalize .uint64 i = i) :
    ∃ (k : Nat) (done' : List Int) (tail' : Heap) (ch' : Choices),
      k ≤ 11 * ids.length + 1
      ∧ List.Perm done' ids
      ∧ DeadFrom tail' (42 + done'.length)
      ∧ ch' <:+ ch
      ∧ stepFnIter k (SL ids [] [] 42)
          (.next (iterK plans envC kC (toKeys []) (toKeys ids))) ch
        = .ok (.next (kTail plans envC kC),
            SL ids done' tail' (42 + done'.length), ch') := by
  have hnodupk : ((idKV ids).map (·.1)).Nodup := by
    have h : ((idKV ids).map (·.1)) = ids := idKV_keys ids
    rw [h]; exact hnd
  obtain ⟨k, d', ch', hk, hQ, hperm, hsuf, hrun⟩ :=
    mapPickLoop_perm
      (T := fun d : List Int × Heap =>
        SL ids d.1 d.2 (42 + d.1.length))
      (cfg := fun d _ =>
        .next (iterK plans envC kC (toKeys d.1) (toKeys ids)))
      (exitCfg := .next (kTail plans envC kC))
      (Q := fun d rem =>
        rem = (idKV ids).filter (fun q => !d.1.contains q.1)
        ∧ DeadFrom d.2 (42 + d.1.length))
      (acc := fun d => d.1) (g := fun p => p.1)
      (c := 11) (e := 1)
      (hIter := by
        intro d rem idx p ch₀ ch₂ hcons hidx hp hQd
        obtain ⟨hrem, hdead⟩ := hQd
        refine ⟨11, (d.1 ++ [p.1],
          d.2 ++ [(.base ⟨42 + d.1.length⟩,
            ⟨some tU64, .int p.1 .uint64⟩)]), Nat.le_refl _,
          ⟨?_, ?_⟩, rfl, ?_⟩
        · -- rem-coherence closes under the pick (the κ-generic
          -- produced-set algebra: filtering by one more key is
          -- erasing its unique entry)
          have hpk : ((idKV ids).filter
              (fun q => !d.1.contains q.1))[idx]? = some p := by
            rw [← hrem]; exact hp
          have hfp := GoLean.MapMem.filter_push_key
            (kvs := idKV ids) (done := d.1) hnodupk hpk
          rw [hrem, hfp]
        · rw [show (d.1 ++ [p.1]).length = d.1.length + 1 from by simp,
            ← Nat.add_assoc]
          exact hdead.push (c := ⟨some tU64, .int p.1 .uint64⟩)
        · rw [show (d.1 ++ [p.1]).length = d.1.length + 1 from by simp,
            ← Nat.add_assoc]
          exact ids_iteration ids d.1 rem d.2 (42 + d.1.length)
            idx p ch₀ ch₂ plans envC kC hnorm hrem hcons hidx hp
            (by omega) hdead)
      (hExit := by
        intro d ch₀ hQd
        obtain ⟨hrem, _⟩ := hQd
        exact ids_done_step ids d.1 d.2 (42 + d.1.length)
          plans envC kC ch₀ hnorm hrem.symm)
      (idKV ids).length (idKV ids) rfl ([], []) ch
      ⟨(List.filter_eq_self.mpr (fun q _ => rfl)).symm,
       by intro x _; rfl⟩
  have hlen : (idKV ids).length = ids.length := by simp [idKV]
  have hpermIds : List.Perm d'.1 ids := by
    have h1 : List.Perm d'.1 ([] ++ (idKV ids).map fun p => p.1) := hperm
    have h2 : ((idKV ids).map fun p => p.1) = ids := idKV_keys ids
    simpa [h2] using h1
  refine ⟨k, d'.1, d'.2, ch', by omega, hpermIds, hQ.2, hsuf, ?_⟩
  simpa using hrun



/-! ## W2 — the post-loop tail (103 steps): outer backedge, the
second (nil-map) range — zero draws — the exit head, `$res0 := m`,
the return walk to the CallSpecR terminal. Kernel windows split at
the three symbolic-address seams (the `cc` re-declaration at the
moved allocation front). -/

def asgnCC : Stmt :=
  .assign (.var "cc") (.indexGet (.var "$rcoll") (.var "$ridx"))
def innerBlock : Stmt :=
  .block #[] #[.mapRange (some "id") none (.var "cc") tU64 tUnit rBody]
def env2b : LocalEnv := ([] : List (String × Loc)) :: env2
def env2c (na : Nat) : LocalEnv := [("cc", .base ⟨na⟩)] :: env2
def env2d (na : Nat) : LocalEnv :=
  ([] : List (String × Loc)) :: env2c na

/-- The W2-phase state before the `cc` re-declaration. -/
def SLW (ids done : List Int) (tail : Heap) (na : Nat) (ridx : Int) :
    ExecState :=
  { wBase with
      heap := coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) ridx ++ tail
      nextAddr := na }

/-- The W2-phase state after it (the fresh `cc` cell at the moved
front; `res0v`/`ridx` distinguish the pre/post return phases). -/
def SLC (ids done : List Int) (tail : Heap) (na : Nat) (ridx : Int)
    (res0v : GoValue) : ExecState :=
  { wBase with
      heap := (coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) res0v ridx ++ tail)
          ++ [(.base ⟨na⟩, ⟨some tMaj, .map ⟨none⟩⟩)]
      nextAddr := na + 1 }

private theorem slwMiss (ids done : List Int) (ridx : Int)
    {tail : Heap} {na : Nat}
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    Heap.lookup (coreCells (.mapData (toEntriesV (idKV ids)))
        (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) ridx ++ tail)
      (.base ⟨na⟩) = none := by
  rw [lookup_append_right (coreMiss _ _ _ _ hna)]
  exact hdead na (Nat.le_refl na)

/-- W2a (33 steps, kernel): loop backedge + the second head (the
`$rfirst` else-arm bumps `$ridx` to 1) down to the `cc`
re-declaration. -/
private theorem ids_w2a (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFnIter 33 (SLW ids done tail na 0)
      (.next (kTail plans envC kC)) ch
      = .ok (.exec (.initialization { id := "cc", typ := tMaj }) env2b
            (.seq [asgnCC, innerBlock] env2b (kLoop plans envC kC)),
          SLW ids done tail na 1, ch) := by
  kernel_rfl

/-- The `cc` re-declaration (conditioned: allocation at the moved
front). -/
private theorem ids_ccinit (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFn (SLW ids done tail na 1)
      (.exec (.initialization { id := "cc", typ := tMaj }) env2b
        (.seq [asgnCC, innerBlock] env2b (kLoop plans envC kC))) ch
      = .ok (.next (.seq [asgnCC, innerBlock] (env2c na)
            (kLoop plans envC kC)),
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  have hdef : defaultValue (SLW ids done tail na 1) tMaj
      = .ok (.map ⟨none⟩) := by
    with_unfolding_all rfl
  have h := stepFn_init_seq (p := { id := "cc", typ := tMaj })
    (rest := [asgnCC, innerBlock]) (env := env2b)
    (k := kLoop plans envC kC) (ch := ch) hdef
  refine h.trans ?_
  have hheap : Heap.set (SLW ids done tail na 1).heap
      (.base ⟨(SLW ids done tail na 1).nextAddr⟩)
      (⟨some tMaj, .map ⟨none⟩⟩ : HeapCell)
      = (coreCells (.mapData (toEntriesV (idKV ids)))
          (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 1 ++ tail)
        ++ [(.base ⟨na⟩, ⟨some tMaj, .map ⟨none⟩⟩)] := by
    show Heap.set (coreCells (.mapData (toEntriesV (idKV ids)))
        (.mapData (toEntriesV (idKV done))) (.map ⟨none⟩) 1 ++ tail)
        (.base ⟨na⟩) _ = _
    exact set_fresh (slwMiss ids done 1 hna hdead)
  rw [hheap]
  rfl

/-- W2b (10 steps, kernel): `cc := $rcoll[$ridx]` down to the store
delivery ($ridx = 1 → the NIL second half). -/
private theorem ids_w2b (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFnIter 10 (SLC ids done tail na 1 (.map ⟨none⟩))
      (.next (.seq [asgnCC, innerBlock] (env2c na)
        (kLoop plans envC kC))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.map ⟨none⟩] (.seqn #[]) (env2c na)
            (.seq [innerBlock] (env2c na) (kLoop plans envC kC))),
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  kernel_rfl

private theorem slcLook (ids done : List Int) (ridx : Int)
    (res0v : GoValue) {tail : Heap} {na : Nat}
    (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    Heap.lookup (SLC ids done tail na ridx res0v).heap (.base ⟨na⟩)
      = some ⟨some tMaj, .map ⟨none⟩⟩ := by
  show Heap.lookup ((_ ++ tail) ++ _) _ = _
  rw [lookup_append_right (by
    rw [lookup_append_right (coreMiss _ _ _ _ hna)]
    exact hdead na (Nat.le_refl na)), lookup_singleton_self]

/-- The `cc` store (conditioned: the target cell sits at the moved
front; the stored nil handle re-normalizes to itself). -/
private theorem ids_ccstore (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFn (SLC ids done tail na 1 (.map ⟨none⟩))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.map ⟨none⟩] (.seqn #[]) (env2c na)
        (.seq [innerBlock] (env2c na) (kLoop plans envC kC)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (env2c na)
            (.seq [innerBlock] (env2c na) (kLoop plans envC kC))),
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  have hnorm : normalizeValueForTy (SLC ids done tail na 1 (.map ⟨none⟩))
      tMaj (.map ⟨none⟩) = .ok (.map ⟨none⟩) := by
    with_unfolding_all rfl
  have hst := storeTarget_addr
    (hlook := slcLook ids done 1 (.map ⟨none⟩) hna hdead) (hnorm := hnorm)
  have h := stepFn_store_step (rs := []) (vs := [])
    (body := .seqn #[]) (env := env2c na)
    (k := .seq [innerBlock] (env2c na) (kLoop plans envC kC))
    (ch := ch) hst
  refine h.trans ?_
  have hheap : Heap.set (SLC ids done tail na 1 (.map ⟨none⟩)).heap
      (.base ⟨na⟩) (⟨some tMaj, .map ⟨none⟩⟩ : HeapCell)
      = (SLC ids done tail na 1 (.map ⟨none⟩)).heap := by
    show Heap.set ((_ ++ tail) ++ _) _ _ = _
    rw [set_append_right (by
      rw [lookup_append_right (coreMiss _ _ _ _ hna)]
      exact hdead na (Nat.le_refl na)), set_cons_self]
    rfl
  rw [hheap]

/-- W2c-tail (4 steps, kernel): the spliced inner block opens to the
nil range's collection read point. -/
private theorem ids_w2c2 (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFnIter 4 (SLC ids done tail na 1 (.map ⟨none⟩))
      (.next (.seq [innerBlock] (env2c na) (kLoop plans envC kC))) ch
      = .ok (.evalE (.var "cc") (env2d na)
            (.mapRangeK (some "id") none tU64 tUnit rBody (env2d na)
              (.seq [] (env2d na)
                (.seq [] (env2c na) (kLoop plans envC kC)))),
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  kernel_rfl

/-- W2c (6 steps): the store drains, the empty `seqn` splices (the
P9 conditioned step — the environment DecidableEq is stuck at the
symbolic front), the inner block opens to the collection read. -/
private theorem ids_w2c (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFnIter 6 (SLC ids done tail na 1 (.map ⟨none⟩))
      (.next (.storeK [] [] (.seqn #[]) (env2c na)
        (.seq [innerBlock] (env2c na) (kLoop plans envC kC)))) ch
      = .ok (.evalE (.var "cc") (env2d na)
            (.mapRangeK (some "id") none tU64 tUnit rBody (env2d na)
              (.seq [] (env2d na)
                (.seq [] (env2c na) (kLoop plans envC kC)))),
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := SLC ids done tail na 1 (.map ⟨none⟩)) (body := .seqn #[])
    (env := env2c na)
    (k := .seq [innerBlock] (env2c na) (kLoop plans envC kC)) (ch := ch))
  have h2 := stepFnIter_chain h1 (stepFnIter_one (stepFn_seqn_splice
    (σ := SLC ids done tail na 1 (.map ⟨none⟩)) (ss := #[])
    (env := env2c na) (rest := [innerBlock])
    (k := kLoop plans envC kC) (ch := ch)))
  have h3 := stepFnIter_chain h2
    (ids_w2c2 ids done tail na plans envC kC ch)
  exact h3

/-- The `cc` read (conditioned: the fresh cell past the symbolic
tail) — delivers the NIL handle, so the second range starts with no
base and zero candidates. -/
private theorem ids_ccread (ids done : List Int) (tail : Heap) (na : Nat)
    (k : Cont) (ch : Choices) (hna : 42 ≤ na) (hdead : DeadFrom tail na) :
    stepFn (SLC ids done tail na 1 (.map ⟨none⟩))
      (.evalE (.var "cc") (env2d na) k) ch
      = .ok (.retV (.map ⟨none⟩) k,
          SLC ids done tail na 1 (.map ⟨none⟩), ch) := by
  exact stepFn_var (by rfl) (slcLook ids done 1 (.map ⟨none⟩) hna hdead)

/-- W2d (51 steps, kernel): the nil range's START and immediate
exhaustion (zero draws — the base is `none`), the third head's break,
`$res0 := m`, the return walk to the CallSpecR return-arrival
terminal. -/
private theorem ids_w2d (ids done : List Int) (tail : Heap) (na : Nat)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFnIter 51 (SLC ids done tail na 1 (.map ⟨none⟩))
      (.retV (.map ⟨none⟩)
        (.mapRangeK (some "id") none tU64 tUnit rBody (env2d na)
          (.seq [] (env2d na)
            (.seq [] (env2c na) (kLoop plans envC kC))))) ch
      = .ok (.returning (.frame plans envC [.base ⟨33⟩] [] kC false),
          SLC ids done tail na 2 (.map ⟨some (.base ⟨35⟩)⟩), ch) := by
  kernel_rfl



/-! ## The assembly: the range-START step, the whole span, THE EXPORT -/

/-- The range-START step (conditioned on the value-generic start
fact): base cell + start keys = the source's key column. -/
private theorem ids_start (ids : List Int)
    (plans : List (TargetShape × List Expr)) (envC : LocalEnv) (kC : Cont)
    (ch : Choices) :
    stepFn (SL ids [] [] 42)
      (.retV (.map ⟨some (.base ⟨31⟩)⟩)
        (.mapRangeK (some "id") none tU64 tUnit rBody env4
          (kTail plans envC kC))) ch
      = .ok (.next (iterK plans envC kC (toKeys []) (toKeys ids)),
          SL ids [] [] 42, ch) := by
  have hlook : Heap.lookup (SL ids [] [] 42).heap (.base ⟨31⟩)
      = some ⟨none, .mapData (toEntriesV (idKV ids))⟩ := rfl
  have hstart := rangeStart_toEntriesV (σ := SL ids [] [] 42)
    (a := ⟨31⟩) (kvs := idKV ids) (dty := none) hlook
  rw [show (idKV ids).map (·.1) = ids from idKV_keys ids] at hstart
  exact stepFn_mapRangeStart hstart

/-- **THE `quorum.JointConfig.IDs` CallSpecR** — the first (M)-family
member: at ANY association order of the source `Voters[0]` map (the
∀-in half: `ids` carries the order; nodup, u64-normalized — a Go
map's own well-formedness), the call returns a fresh
`map[uint64]struct{}` whose entry list is `idKV ids'` for an
∃-PACKAGED permutation `ids'` of `ids` (the ∃-out half: the built
order is exactly the machine's pick order, never re-converged). ∀
plans/env/k, ∀ ch — the per-range draws discharged by
`mapPickLoop_perm`, ∃ n; count-free. The downstream readbacks cross
the family by the layer-1 quotient lemmas (`lookupP_perm`,
membership, `sortedLT_eq_of_perm` — the consumers below). -/
theorem jointConfigIDs_callSpecR (ids : List Int)
    (hnd : ids.Nodup)
    (hnorm : ∀ i ∈ ids, IntKind.normalize .uint64 i = i) :
    CallSpecR (IDsPre ids) ⟨"quorum.JointConfig.IDs"⟩ [] recvV
      (fun σ' vs => ∃ ids', List.Perm ids' ids
        ∧ vs = [.map ⟨some (.base ⟨35⟩)⟩]
        ∧ Heap.lookup σ'.heap (.base ⟨35⟩)
            = some ⟨none, .mapData (toEntriesV (idKV ids'))⟩) := by
  intro σ hP plans envC kC ch
  obtain ⟨kL, done', tail', ch', hkL, hperm, hdead, hsuf, hloop⟩ :=
    ids_loop ids plans envC kC ch hnd hnorm
  have h1 := ids_w1_span (.mapData (toEntriesV (idKV ids)))
    plans envC kC ch
  have h2 := stepFnIter_chain h1
    (stepFnIter_one (ids_start ids plans envC kC ch))
  have h3 := stepFnIter_chain h2 hloop
  have h4 := stepFnIter_chain h3
    (ids_w2a ids done' tail' (42 + done'.length) plans envC kC ch')
  have h5 := stepFnIter_chain h4 (stepFnIter_one
    (ids_ccinit ids done' tail' (42 + done'.length) plans envC kC ch'
      (by omega) hdead))
  have h6 := stepFnIter_chain h5
    (ids_w2b ids done' tail' (42 + done'.length) plans envC kC ch')
  have h7 := stepFnIter_chain h6 (stepFnIter_one
    (ids_ccstore ids done' tail' (42 + done'.length) plans envC kC ch'
      (by omega) hdead))
  have h8 := stepFnIter_chain h7
    (ids_w2c ids done' tail' (42 + done'.length) plans envC kC ch')
  have h9 := stepFnIter_chain h8 (stepFnIter_one
    (ids_ccread ids done' tail' (42 + done'.length) _ ch'
      (by omega) hdead))
  have h10 := stepFnIter_chain h9
    (ids_w2d ids done' tail' (42 + done'.length) plans envC kC ch')
  refine ⟨117 + 1 + kL + 33 + 1 + 10 + 1 + 6 + 1 + 51,
    SLC ids done' tail' (42 + done'.length) 2 (.map ⟨some (.base ⟨35⟩)⟩),
    [.base ⟨33⟩], [.map ⟨some (.base ⟨35⟩)⟩], ch', ?_, ?_,
    ⟨done', hperm, rfl, rfl⟩, hsuf⟩
  · rw [hP]
    exact h10
  · exact loadMany_one (c := ⟨some tMapUS, .map ⟨some (.base ⟨35⟩)⟩⟩)
      rfl

/-- Non-vacuity: the family's ∃-discharge at the census's own
canonical instance (the T1 voter set `{1,2,3}` in ascending store
order — the harness `ApplySnapshot` route's realized value). -/
theorem idsPre_inhabited :
    IDsPre [1, 2, 3]
      { wBase with
          heap := preHeapV (.mapData (toEntriesV (idKV [1, 2, 3])))
          nextAddr := 32 } := rfl

/-! ## The order-insensitive READBACK consumers (the second
genuinely-different consumer class — the U3.2f Base-clause
vocabulary, transferred across the (M) family by the layer-1
quotient-crossing lemmas) -/

/-- **The population readback** (the `Pair.progress`-clause shape —
"tracker population = the voter set", here at the built IDs map):
ACROSS THE WHOLE FAMILY, membership in the built map's key column is
membership in `ids`, and lookup is DEFINED at exactly the voter ids —
order-insensitively (any family member gives the same answers). -/
theorem idsFam_population {ids ids' : List Int}
    (hperm : List.Perm ids' ids) (hnd : ids.Nodup) :
    ((idKV ids').map Prod.fst = ids'
      ∧ ∀ i, i ∈ ids' ↔ i ∈ ids)
    ∧ ∀ v ∈ ids, lookupP (idKV ids') v = some unitV := by
  refine ⟨⟨idKV_keys ids', fun i => hperm.mem_iff⟩, ?_⟩
  intro v hv
  have hnd' : NodupKeys (idKV ids') := by
    show ((idKV ids').map Prod.fst).Nodup
    rw [idKV_keys]
    exact (hperm.nodup_iff).mpr hnd
  exact lookupP_eq_some_of_mem hnd'
    (List.mem_map.mpr ⟨v, hperm.mem_iff.mpr hv, rfl⟩)

/-- **The lookup-agreement readback**: any two members of the same
(M) family answer every lookup identically — the quotient-crossing
lemma consumed at this member's decode (what makes every
`lookupI`-vocabulary invariant clause order-insensitive). -/
theorem idsFam_lookup_agree {ids l₁ l₂ : List Int}
    (h₁ : List.Perm l₁ ids) (h₂ : List.Perm l₂ ids) (hnd : ids.Nodup) :
    ∀ v, lookupP (idKV l₁) v = lookupP (idKV l₂) v := by
  intro v
  have hp : List.Perm (idKV l₁) (idKV l₂) :=
    (List.Perm.map _ (h₁.trans h₂.symm))
  have hnd₁ : NodupKeys (idKV l₁) := by
    show ((idKV l₁).map Prod.fst).Nodup
    rw [idKV_keys]
    exact h₁.nodup_iff.mpr hnd
  exact lookupP_perm hp hnd₁ v

/-- **The sorted-readback consumer** (the `VoterNodes`/`Slice`-class
converging read): sorting ANY family member's key column yields ONE
value — the whole permutation family collapses at a `slices.Sort`
boundary. -/
theorem idsFam_sorted_collapse {ids l₁ l₂ : List Int}
    (h₁ : List.Perm l₁ ids) (h₂ : List.Perm l₂ ids)
    (s₁ s₂ : List Int)
    (hs₁ : List.Perm s₁ l₁) (hs₂ : List.Perm s₂ l₂)
    (hsort₁ : s₁.Pairwise (· < ·)) (hsort₂ : s₂.Pairwise (· < ·)) :
    s₁ = s₂ :=
  sortedLT_eq_of_perm
    ((hs₁.trans h₁).trans (h₂.symm.trans hs₂.symm)) hsort₁ hsort₂

end GoLean.RaftSeam.MOrder
