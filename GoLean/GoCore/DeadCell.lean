import GoLean.GoCore.StepFn
import GoLean.GoCore.StepFnFacts
import GoLean.GoCore.ExecutionStatement

/-!
# The dead cell — refusal, frame and `NoDead` preservation (raft-proofs' rung-2 request)

[AGENT lane core/dead-cell-1124], 2026-11-24, on the [USER] approval of the same day (the
request is the raft-proofs session's: a cell a consumer can mark as holding nothing while it
keeps its address).

`HeapCell.dead` (`State.lean`) is a payload-free cell constructor. The machine never creates
one: `Store.markDead` (`Store.lean`) is its only producer and no machine operation calls it.
This module states the four properties the consumer relies on.

1. **Refusal.** Every reader and writer that reaches a dead root cell refuses with `.stuck` —
   never a Go panic, never a value: `loadLoc_dead`, `loadRoot_dead`, `storeLoc_dead`,
   `mapPayload?_dead`, `chanPayload?_dead`, `storeMapPayload_dead`, `storeChanPayload_dead`, and
   the `Mem.*` operations above them. `IsStuck` is the refusal shape.
2. **No machine step creates one.** `Store.NoDead` is preserved by `stepFn` (`stepFn_noDead`)
   and by the frame-entry operations a consumer's adapter calls directly (`enterFrame_noDead`,
   `bindParams_noDead`, `allocDecls_noDead`, `pinResultLocs_noDead`) and by the wide operations
   (`applyStmtOp_noDead`, `applySyncOp_noDead`, …). The empty store satisfies it
   (`Store.NoDead.empty`); `Store.markDead` at an allocated address is what breaks it
   (`Store.markDead_not_noDead`).
3. **Deadness is decidable** (`HeapCell.isDead`, `HeapCell.isDead_iff`, `State.lean`).
4. **A dead cell is an occupied address**: `Store.markDead_size`, `Store.markDead_nextAddr`.

The frame lemmas (`Store.markDead_lookup_ne`, `loadLoc_markDead_ne`, `storeLoc_markDead_ne`)
say that marking one root dead changes no load or store at a location rooted elsewhere.
-/

namespace GoLean.GoCore

open GoLean

/-! ## `Post`: a postcondition on the successful result of an `Except Stop` computation -/

/-- `P` holds of the value `x` returns, when it returns one. -/
def Post {α : Type} (x : Except Stop α) (P : α → Prop) : Prop := ∀ a, x = .ok a → P a

namespace Post
variable {α β : Type} {P : α → Prop}

theorem ok {a : α} (h : P a) : Post (.ok a : Except Stop α) P := by
  intro b hb; cases hb; exact h
theorem pure {a : α} (h : P a) : Post (Pure.pure a : Except Stop α) P := Post.ok h
theorem error {e : Stop} : Post (.error e : Except Stop α) P := by
  intro b hb; cases hb
theorem throw {e : Stop} : Post (MonadExcept.throw e : Except Stop α) P := Post.error
theorem stuck {m : String} : Post (GoCore.stuck m : Except Stop α) P := Post.error
theorem panic {m : String} : Post (GoCore.panic m : Except Stop α) P := Post.error
theorem unsupported {m : String} : Post (GoCore.unsupported m : Except Stop α) P := Post.error

theorem mono {x : Except Stop α} {Q : α → Prop} (hx : Post x Q) (h : ∀ a, Q a → P a) :
    Post x P := fun a ha => h a (hx a ha)

theorem bind {x : Except Stop α} {k : α → Except Stop β} {Q : α → Prop} {R : β → Prop}
    (hx : Post x Q) (hk : ∀ a, Q a → Post (k a) R) : Post (x >>= k) R := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a => exact hk a (hx a rfl) b hb

/-- A bind whose first computation tells us nothing we need. -/
theorem bind_any {x : Except Stop α} {k : α → Except Stop β} {R : β → Prop}
    (hk : ∀ a, Post (k a) R) : Post (x >>= k) R :=
  Post.bind (Q := fun _ => True) (fun _ _ => trivial) fun a _ => hk a

theorem map {x : Except Stop α} {g : α → β} {R : β → Prop}
    (hx : Post x fun a => R (g a)) : Post (g <$> x) R := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a => cases hb; exact hx a rfl

theorem exceptMap {x : Except Stop α} {g : α → β} {R : β → Prop}
    (hx : Post x fun a => R (g a)) : Post (x.map g) R := Post.map hx

/-- `toResult` turns a recoverable panic into a value; the `.ok` side keeps the postcondition. -/
theorem toResult {x : Except Stop α} {R : Result α → Prop}
    (hok : Post x fun a => R (.ok a)) (hpanic : ∀ msg, R (.panic msg)) :
    Post (GoLean.toResult x) R := by
  intro b hb
  cases x with
  | ok a => cases hb; exact hok a rfl
  | error e =>
    cases e with
    | terminal t =>
      cases t <;> first | (cases hb; exact hpanic _) | cases hb
    | _ => cases hb

/-- `toResult`, in the shape the delivery helpers consume: the `.ok` side keeps `Q`. -/
theorem toResult' {x : Except Stop α} {Q : α → Prop} (hx : Post x Q) :
    Post (GoLean.toResult x) fun r => ∀ a, r = .ok a → Q a :=
  Post.toResult (Post.mono hx fun a ha b hb => by cases hb; exact ha)
    (fun msg b hb => by cases hb)

theorem toResult_any {x : Except Stop α} :
    Post (GoLean.toResult x) fun r => ∀ a, r = .ok a → True := fun _ _ _ _ => trivial

end Post

theorem toResult_ok_inv {α : Type} {x : Except Stop α} {a : α}
    (h : GoLean.toResult x = .ok (.ok a)) : x = .ok a := by
  cases x with
  | ok b => cases h; rfl
  | error e =>
    cases e with
    | terminal t => cases t <;> cases h
    | _ => cases h

/-! ## The refusal shape -/

/-- `x` refuses with `.stuck`: a refusal — not a Go panic, not a value. -/
def IsStuck {α : Type} (x : Except Stop α) : Prop := ∃ msg, x = .error (.stuck msg)

theorem IsStuck.not_ok {α : Type} {x : Except Stop α} (h : IsStuck x) (a : α) : x ≠ .ok a := by
  obtain ⟨m, rfl⟩ := h; intro h; cases h

theorem IsStuck.not_panic {α : Type} {x : Except Stop α} (h : IsStuck x) (msg : String) :
    x ≠ .error (.panic msg) := by
  obtain ⟨m, rfl⟩ := h; intro h; cases h

theorem IsStuck.bind {α β : Type} {x : Except Stop α} (h : IsStuck x) (k : α → Except Stop β) :
    IsStuck (x >>= k) := by
  obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩

/-! ## A dead cell is an occupied address -/

theorem Heap.lookup_base (h : Heap) (a : Addr) : Heap.lookup h (.base a) = h[a.id]? := by
  cases a; rfl

@[simp] theorem Store.markDead_size (s : Store) (a : Addr) :
    (s.markDead a).heap.size = s.heap.size := by
  simp [Store.markDead]

@[simp] theorem Store.markDead_nextAddr (s : Store) (a : Addr) :
    (s.markDead a).nextAddr = s.nextAddr := by
  simp [Store.nextAddr]

theorem Store.markDead_lookup_self {s : Store} {a : Addr} (h : a.id < s.heap.size) :
    Heap.lookup (s.markDead a).heap (.base a) = some .dead := by
  obtain ⟨i⟩ := a
  simp [Store.markDead, Heap.lookup, h]

theorem Store.markDead_lookup_ne {s : Store} {a b : Addr} (h : b ≠ a) :
    Heap.lookup (s.markDead a).heap (.base b) = Heap.lookup s.heap (.base b) := by
  obtain ⟨i⟩ := a; obtain ⟨j⟩ := b
  have hij : i ≠ j := fun e => h (by rw [e])
  simp [Store.markDead, Heap.lookup, Array.getElem?_setIfInBounds_ne hij]

theorem Store.markDead_not_noDead {s : Store} {a : Addr} (h : a.id < s.heap.size) :
    ¬ (s.markDead a).NoDead := by
  intro hn
  refine hn .dead ?_ rfl
  have := Store.markDead_lookup_self h
  obtain ⟨i⟩ := a
  simp only [Heap.lookup] at this
  exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? this)

/-! ## Refusal: every reader and writer is stuck at a dead root -/

namespace Machine
section
variable {ctx : ProgramCtx}

theorem loadLoc_dead {s : Store} {l : Loc}
    (h : Heap.lookup s.heap (.base (Loc.rootPath l).1) = some .dead) : IsStuck (loadLoc ctx s l) := by
  rw [loadLoc_eq_readAt, h]; exact ⟨_, rfl⟩

theorem loadRoot_dead {s : Store} {a : Addr}
    (h : Heap.lookup s.heap (.base a) = some .dead) : IsStuck (loadRoot ctx s (.base a)) := by
  show IsStuck (loadLoc ctx s (.base a))
  exact loadLoc_dead (l := .base a) h

theorem storeLoc_dead {s : Store} {l : Loc} {v : GoValue}
    (h : Heap.lookup s.heap (.base (Loc.rootPath l).1) = some .dead) :
    IsStuck (storeLoc ctx s l v) := by
  have hlt := Heap.lookup_lt h
  have hcell : s.heap[(Loc.rootPath l).1.id] = .dead := by
    rw [Heap.lookup_base, Array.getElem?_eq_getElem hlt] at h
    exact Option.some.inj h
  unfold storeLoc Store.updateCell
  simp only [hlt, ↓reduceDIte, hcell]
  cases (Loc.rootPath l).2 <;> exact ⟨_, rfl⟩

theorem mapPayload?_dead {s : Store} {l : Loc} (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (mapPayload? s l) := by
  unfold mapPayload?; rw [h]; exact ⟨_, rfl⟩

theorem chanPayload?_dead {s : Store} {l : Loc} (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (chanPayload? s l) := by
  unfold chanPayload?; rw [h]; exact ⟨_, rfl⟩

theorem storeMapPayload_dead {s : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)}
    {n : Nat} (h : Heap.lookup s.heap l = some .dead) : IsStuck (storeMapPayload s l es n) := by
  cases l with
  | base a =>
    have hlt := Heap.lookup_lt h
    rw [Heap.lookup_base, Array.getElem?_eq_getElem hlt] at h
    unfold storeMapPayload Store.updateCell
    simp only [hlt, ↓reduceDIte, Option.some.inj h]
    exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

theorem storeChanPayload_dead {s : Store} {l : Loc} {buf : Array GoValue} {cap : Nat}
    {closed : Bool} (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (storeChanPayload s l buf cap closed) := by
  cases l with
  | base a =>
    have hlt := Heap.lookup_lt h
    rw [Heap.lookup_base, Array.getElem?_eq_getElem hlt] at h
    unfold storeChanPayload Store.updateCell
    simp only [hlt, ↓reduceDIte, Option.some.inj h]
    exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- The root cell of the location is dead. -/
def _root_.GoLean.GoCore.Store.DeadAt (s : Store) (l : Loc) : Prop :=
  Heap.lookup s.heap (.base (Loc.rootPath l).1) = some .dead

theorem Mem.load_dead {s : Store} {l : Loc} (h : s.DeadAt l) : IsStuck (Mem.load ctx s l) :=
  (loadLoc_dead h).bind _

theorem Mem.loadFor_dead {s : Store} {root leaf : Loc} (h : s.DeadAt root) :
    IsStuck (Mem.loadFor ctx s root leaf) := (loadLoc_dead h).bind _

theorem Mem.loadBinding_dead {s : Store} {a : Addr}
    (h : Heap.lookup s.heap (.base a) = some .dead) : IsStuck (Mem.loadBinding ctx s (.base a)) :=
  (loadRoot_dead h).bind _

theorem Mem.loadBindingFor_dead {s : Store} {a : Addr} {leaf : Loc}
    (h : Heap.lookup s.heap (.base a) = some .dead) :
    IsStuck (Mem.loadBindingFor ctx s (.base a) leaf) := (loadRoot_dead h).bind _

theorem Mem.store_dead {s : Store} {l : Loc} {v : GoValue} (h : s.DeadAt l) :
    IsStuck (Mem.store ctx s l v) := (storeLoc_dead h).bind _

theorem Mem.storeThrough_dead {s : Store} {l : Loc} {v : GoValue} (h : s.DeadAt l) :
    IsStuck (Mem.storeThrough ctx s l v) := by
  obtain ⟨m, hm⟩ := Mem.store_dead (ctx := ctx) (v := v) h
  unfold Mem.storeThrough
  rw [hm]
  dsimp only
  split
  · exact Mem.store_dead h
  · exact ⟨m, rfl⟩

theorem Mem.mapRead_dead {s : Store} {l : Loc} (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (Mem.mapRead s l) := (mapPayload?_dead h).bind _

theorem Mem.mapWrite_dead {s : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)} {n : Nat}
    (h : Heap.lookup s.heap l = some .dead) : IsStuck (Mem.mapWrite s l es n) :=
  (storeMapPayload_dead h).bind _

/-- A frame-exit result read whose FIRST cell is dead is stuck (the reads run in order). -/
theorem loadMany_dead_head {s : Store} {l : Loc} {ls : List Loc} (h : s.DeadAt l) :
    IsStuck (loadMany ctx s (l :: ls)) := by
  unfold loadMany
  exact (loadLoc_dead h).bind _

/-- No result read that includes a dead cell succeeds. -/
theorem loadMany_not_ok_of_dead {s : Store} : ∀ {ls : List Loc} {l : Loc}, l ∈ ls → s.DeadAt l →
    ∀ vs, loadMany ctx s ls ≠ .ok vs
  | l' :: ls, l, hm, hd, vs, hok => by
    unfold loadMany at hok
    cases hl : loadLoc ctx s l' with
    | error e => rw [hl] at hok; cases hok
    | ok v =>
      rw [hl] at hok
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact (loadLoc_dead hd).not_ok _ hl
      · cases hr : loadMany ctx s ls with
        | error e => rw [hr] at hok; cases hok
        | ok vs' => exact loadMany_not_ok_of_dead hm' hd _ hr

theorem loadResults_dead_head {s : Store} {a : Addr} {ls : List Loc}
    (h : Heap.lookup s.heap (.base a) = some .dead) :
    IsStuck (loadResults ctx s (.base a :: ls)) := by
  unfold loadResults
  exact (Mem.loadBinding_dead h).bind _

/-! ### The operations above the memory module -/

theorem applyStrictOp_deref_dead {s : Store} {leafOf : Loc → Loc} {ty : Ty} {l : Loc}
    (h : s.DeadAt l) : IsStuck (applyStrictOp ctx s leafOf (.deref ty) [.addr l]) := by
  obtain ⟨m, hm⟩ := Mem.loadFor_dead (ctx := ctx) (leaf := leafOf l) h
  exact ⟨m, by simp [applyStrictOp, valueAsLoc, hm, bind, Except.bind, pure, Except.pure]⟩

theorem applyStrictOp_indexGet_dead {s : Store} {leafOf : Loc → Loc} {l : Loc} {n : Int}
    {kind : IntKind} (h : s.DeadAt l) :
    IsStuck (applyStrictOp ctx s leafOf .indexGet [.addr l, .int n kind]) := by
  obtain ⟨m, hm⟩ := Mem.loadFor_dead (ctx := ctx) (leaf := .index l n) h
  exact ⟨m, by simp [applyStrictOp, valueAsInt, hm, bind, Except.bind, pure, Except.pure]⟩

theorem applySyncOpCore_lock_dead {s : Store} {l : Loc} {env : LocalEnv} {k : Cont}
    (h : s.DeadAt l) : IsStuck (applySyncOpCore ctx s .lock [.addr l] env k) := by
  obtain ⟨m, hm⟩ := loadLoc_dead (ctx := ctx) h
  exact ⟨m, by simp [applySyncOpCore, valueAsLoc, syncCell, hm, bind, Except.bind, pure, Except.pure]⟩

theorem applySyncOpCore_unlock_dead {s : Store} {l : Loc} {env : LocalEnv} {k : Cont}
    (h : s.DeadAt l) : IsStuck (applySyncOpCore ctx s .unlock [.addr l] env k) := by
  obtain ⟨m, hm⟩ := loadLoc_dead (ctx := ctx) h
  exact ⟨m, by simp [applySyncOpCore, valueAsLoc, syncCell, hm, bind, Except.bind, pure, Except.pure]⟩

theorem applySyncOp_lock_dead {s : Store} {ch : Choices} {l : Loc} {env : LocalEnv} {k : Cont}
    (h : s.DeadAt l) : IsStuck (applySyncOp ctx s ch .lock [.addr l] env k) := by
  obtain ⟨m, hm⟩ := applySyncOpCore_lock_dead (ctx := ctx) (env := env) (k := k) h
  exact ⟨m, by simp [applySyncOp, SyncOp.tryTargets?, hm, bind, Except.bind]⟩

theorem applySyncOp_unlock_dead {s : Store} {ch : Choices} {l : Loc} {env : LocalEnv} {k : Cont}
    (h : s.DeadAt l) : IsStuck (applySyncOp ctx s ch .unlock [.addr l] env k) := by
  obtain ⟨m, hm⟩ := applySyncOpCore_unlock_dead (ctx := ctx) (env := env) (k := k) h
  exact ⟨m, by simp [applySyncOp, SyncOp.tryTargets?, hm, bind, Except.bind]⟩

/-- `len` of a channel whose payload cell is dead is stuck (`typ` is the operand's static type
when it is a pointer to an array, the one form that reads no cell). -/
theorem applyStrictOp_lengthOf_chan_dead {s : Store} {leafOf : Loc → Loc} {typ : Option Ty}
    {l : Loc} (ht : ∀ n e, typ ≠ some (.pointer (.array n e)))
    (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (applyStrictOp ctx s leafOf (.lengthOf typ) [.chan { base := some l }]) := by
  obtain ⟨m, hm⟩ := chanPayload?_dead h
  refine ⟨m, ?_⟩
  simp only [applyStrictOp]
  simp [hm, bind, Except.bind]

theorem applyStrictOp_capacityOf_chan_dead {s : Store} {leafOf : Loc → Loc} {typ : Option Ty}
    {l : Loc} (ht : ∀ n e, typ ≠ some (.pointer (.array n e)))
    (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (applyStrictOp ctx s leafOf (.capacityOf typ) [.chan { base := some l }]) := by
  obtain ⟨m, hm⟩ := chanPayload?_dead h
  refine ⟨m, ?_⟩
  simp only [applyStrictOp]
  simp [hm, bind, Except.bind]

theorem applyStrictOp_lengthOf_map_dead {s : Store} {leafOf : Loc → Loc} {typ : Option Ty}
    {l : Loc} (ht : ∀ n e, typ ≠ some (.pointer (.array n e)))
    (h : Heap.lookup s.heap l = some .dead) :
    IsStuck (applyStrictOp ctx s leafOf (.lengthOf typ) [.map { base := some l }]) := by
  obtain ⟨m, hm⟩ := Mem.mapRead_dead h
  refine ⟨m, ?_⟩
  simp only [applyStrictOp]
  simp [hm, bind, Except.bind]

theorem applyStrictOp_lengthOf_addr_dead {s : Store} {leafOf : Loc → Loc} {typ : Option Ty}
    {l : Loc} (ht : ∀ n e, typ ≠ some (.pointer (.array n e))) (h : s.DeadAt l) :
    IsStuck (applyStrictOp ctx s leafOf (.lengthOf typ) [.addr l]) := by
  obtain ⟨m, hm⟩ := loadLoc_dead (ctx := ctx) h
  refine ⟨m, ?_⟩
  simp only [applyStrictOp]
  simp [hm, bind, Except.bind]

theorem applyStrictOp_capacityOf_addr_dead {s : Store} {leafOf : Loc → Loc} {typ : Option Ty}
    {l : Loc} (ht : ∀ n e, typ ≠ some (.pointer (.array n e))) (h : s.DeadAt l) :
    IsStuck (applyStrictOp ctx s leafOf (.capacityOf typ) [.addr l]) := by
  obtain ⟨m, hm⟩ := loadLoc_dead (ctx := ctx) h
  refine ⟨m, ?_⟩
  simp only [applyStrictOp]
  simp [hm, bind, Except.bind]

/-- The dynamic dispatch's receiver read (`dynamicDispatch?` reads the receiver through
`receiverAt`): a pointer-boxed receiver whose cell is dead is stuck. -/
theorem receiverAt_deref_dead {s : Store} {l : Loc} (h : s.DeadAt l) :
    IsStuck (receiverAt ctx s (.addr l) #[] .deref) := by
  obtain ⟨m, hm⟩ := Mem.load_dead (ctx := ctx) h
  exact ⟨m, by simp [receiverAt, promotionWalk, hm, bind, Except.bind, pure, Except.pure]⟩

/-! ## The frame: marking one root dead changes nothing rooted elsewhere -/

theorem loadLoc_markDead_ne {s : Store} {a : Addr} {l : Loc} (h : (Loc.rootPath l).1 ≠ a) :
    loadLoc ctx (s.markDead a) l = loadLoc ctx s l := by
  rw [loadLoc_eq_readAt, loadLoc_eq_readAt, Store.markDead_lookup_ne h]

theorem _root_.GoLean.GoCore.Store.updateCell_markDead_ne {s : Store} {a b : Addr}
    {f : HeapCell → Except Stop HeapCell} (h : b ≠ a) :
    (s.markDead a).updateCell b f = (s.updateCell b f).map (·.markDead a) := by
  have hne : a.id ≠ b.id := by
    intro e; apply h; cases a; cases b; simp_all
  unfold Store.updateCell
  by_cases hi : b.id < s.heap.size
  · have hi' : b.id < (s.markDead a).heap.size := by simpa using hi
    simp only [hi, hi', ↓reduceDIte]
    have hget : (s.markDead a).heap[b.id] = s.heap[b.id] :=
      Array.getElem_setIfInBounds_ne hi hne
    rw [hget]
    cases f s.heap[b.id] with
    | error e => rfl
    | ok c =>
      show Except.ok _ = Except.ok _
      congr 1
      simp only [Store.markDead]
      congr 1
      apply Array.ext_getElem?
      intro i
      simp only [Array.getElem?_set, Array.getElem?_setIfInBounds, Array.size_set]
      by_cases h3 : b.id = i
      · have h4 : a.id ≠ i := fun e => hne (e.trans h3.symm)
        simp [h3, h4]
      · simp [h3]
  · have hi' : ¬ b.id < (s.markDead a).heap.size := by simpa using hi
    simp only [hi, hi', ↓reduceDIte]
    rfl

theorem storeLoc_markDead_ne {s : Store} {a : Addr} {l : Loc} {v : GoValue}
    (h : (Loc.rootPath l).1 ≠ a) :
    storeLoc ctx (s.markDead a) l v = (storeLoc ctx s l v).map (·.markDead a) := by
  unfold storeLoc
  exact Store.updateCell_markDead_ne h

end
end Machine

/-! ## `NoDead`: the primitives -/

theorem Store.NoDead.empty : Store.NoDead {} := by
  intro c hc; simp at hc

theorem Store.noDead_iff_lookup {s : Store} :
    s.NoDead ↔ ∀ a : Addr, Heap.lookup s.heap (.base a) ≠ some .dead := by
  constructor
  · intro h a hl
    obtain ⟨i⟩ := a
    simp only [Heap.lookup] at hl
    exact h _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hl)) rfl
  · intro h c hc hd
    subst hd
    obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hc)
    exact h ⟨i⟩ (by simp [Heap.lookup, Array.getElem?_eq_getElem hi, hget])

theorem Store.NoDead.allocCell {s : Store} {c : HeapCell} (h : s.NoDead) (hc : c ≠ .dead) :
    (s.allocCell c).2.NoDead := by
  intro c' hc'
  simp only [Store.allocCell, Array.toList_push, List.mem_append, List.mem_singleton] at hc'
  rcases hc' with hc' | rfl
  · exact h c' hc'
  · exact hc

theorem Store.NoDead.updateCell {s : Store} {a : Addr} {f : HeapCell → Except Stop HeapCell}
    (h : s.NoDead) (hf : ∀ c, Post (f c) (· ≠ .dead)) : Post (s.updateCell a f) Store.NoDead := by
  intro s' hs'
  unfold Store.updateCell at hs'
  split at hs'
  · rename_i hi
    cases hfc : f s.heap[a.id] with
    | error e => rw [hfc] at hs'; cases hs'
    | ok cell =>
      rw [hfc] at hs'
      cases hs'
      intro c' hc'
      rcases List.mem_or_eq_of_mem_set (by simpa using hc') with hm | rfl
      · exact h c' hm
      · exact hf _ _ hfc
  · cases hs'

/-- A commit (a store-owning continuation of a validate phase) keeps `NoDead`: `proj` reads the
store out of its result. -/
def Commit.NoDead {α : Type} (c : Machine.Commit α) (proj : α → Store) : Prop :=
  ∀ s : Store, s.NoDead → Post (c s) fun r => (proj r).NoDead

theorem Commit.withStream_noDead {ch : Choices} {ps : List PickRecord}
    {c : Machine.Commit (Store × AccessTrace)} (hc : Commit.NoDead c fun r => r.1) :
    Commit.NoDead (Machine.Commit.withStream ch ps c) fun r => r.1 := by
  intro s h
  unfold Machine.Commit.withStream
  refine Post.bind (hc s h) fun a ha => ?_
  exact Post.pure ha

/-! ## The sweep tactic

`nd` walks an `Except Stop` program: a `pure` of a store known to be `NoDead` closes; an error
closes; a bind whose head is a store-returning operation with a registered lemma (`nd_db`) takes
that lemma's postcondition into the context; any other bind is stepped over; a `match`/`if` is
split. It is a proof-search convenience and nothing rests on it: every theorem it closes is
checked by the kernel as usual. -/

/-- The registered `NoDead` lemmas, one `macro_rules` alternative per lemma. -/
syntax "nd_db" : tactic

/-- `NoDead` of the store at hand: a hypothesis, or a fresh live cell pushed onto one. -/
macro "nd_h" : tactic => `(tactic| first
  | assumption
  | exact Store.NoDead.allocCell ‹_› (by intro hc; cases hc))

/-- The delivery helpers' steps (`deliverS`/`deliverV`), registered once those lemmas exist. -/
syntax "nd_deliver" : tactic

/-- One step of the sweep. -/
syntax "nd_step" : tactic
/-- The sweep: `nd_step` to exhaustion on every goal. -/
syntax "nd" : tactic
macro_rules
  | `(tactic| nd_step) => `(tactic| first
      | assumption
      | exact Post.pure (by nd_h)
      | exact Post.ok (by nd_h)
      | exact Post.error
      | exact Post.throw
      | exact Post.stuck
      | exact Post.panic
      | exact Post.unsupported
      | (refine Post.pure (Commit.withStream_noDead ?_); intro (_ : Store) (_ : Store.NoDead _))
      | (refine Post.pure ?_; intro (_ : Store) (_ : Store.NoDead _))
      | nd_db
      | (apply Post.bind; (case hx => nd_db); intro _ _)
      | (apply Post.bind; (case hx => (refine Post.toResult' (Q := ?Q') ?h'; (case h' => nd_db))); intro _ _)
      | (apply Post.bind; (case hx => exact Post.toResult_any); intro _ _)
      | nd_deliver
      | simp only [pure_bind]
      | (refine Post.bind_any ?_; intro _)
      | dsimp only
      | refine Post.map ?_
      | refine Post.exceptMap ?_
      | (apply Post.toResult; (case hpanic => intro _))
      | ((first | refine Post.ok ?_ | refine Post.pure ?_); intro _ hr; cases hr)
      | split)
macro_rules
  | `(tactic| nd) => `(tactic| repeat' nd_step)


macro_rules | `(tactic| nd_db) => `(tactic| exact (‹Commit.NoDead _ _›) _ (by nd_h))

variable {ctx : ProgramCtx}

theorem Store.alloc_noDead {s : Store} {v : GoValue} {ty : Ty} (h : s.NoDead) :
    Post (Store.alloc ctx s v ty) fun r => r.2.NoDead := by
  unfold Store.alloc
  refine Post.bind_any fun v' => Post.pure ?_
  exact h.allocCell (by intro hc; cases hc)
macro_rules | `(tactic| nd_db) => `(tactic| exact Store.alloc_noDead (by nd_h))

theorem storeLoc_noDead {s : Store} {l : Loc} {v : GoValue} (h : s.NoDead) :
    Post (storeLoc ctx s l v) Store.NoDead := by
  unfold storeLoc
  refine h.updateCell fun c => ?_
  cases c with
  | value ty root => exact Post.map fun a _ => by simp
  | _ => dsimp only; split <;> exact Post.stuck
macro_rules | `(tactic| nd_db) => `(tactic| exact storeLoc_noDead (by nd_h))

theorem storeMapPayload_noDead {s : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)}
    {n : Nat} (h : s.NoDead) : Post (storeMapPayload s l es n) Store.NoDead := by
  unfold storeMapPayload
  split
  · refine h.updateCell fun c => ?_
    cases c <;> first | exact Post.stuck | exact Post.pure (by simp)
  · exact Post.stuck
macro_rules | `(tactic| nd_db) => `(tactic| exact storeMapPayload_noDead (by nd_h))

theorem storeChanPayload_noDead {s : Store} {l : Loc} {buf : Array GoValue} {cap : Nat}
    {closed : Bool} (h : s.NoDead) : Post (storeChanPayload s l buf cap closed) Store.NoDead := by
  unfold storeChanPayload
  split
  · refine h.updateCell fun c => ?_
    cases c <;> first | exact Post.stuck | exact Post.pure (by simp)
  · exact Post.stuck
macro_rules | `(tactic| nd_db) => `(tactic| exact storeChanPayload_noDead (by nd_h))

theorem Mem.store_noDead {s : Store} {l : Loc} {v : GoValue} (h : s.NoDead) :
    Post (Mem.store ctx s l v) fun r => r.1.NoDead := by
  unfold Mem.store; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact Mem.store_noDead (by nd_h))

theorem Mem.storeThrough_noDead {s : Store} {l : Loc} {v : GoValue} (h : s.NoDead) :
    Post (Mem.storeThrough ctx s l v) fun r => r.1.NoDead := by
  unfold Mem.storeThrough
  split
  · rename_i r heq; exact Post.ok (Mem.store_noDead h _ heq)
  · nd
macro_rules | `(tactic| nd_db) => `(tactic| exact Mem.storeThrough_noDead (by nd_h))

theorem Mem.mapWrite_noDead {s : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)}
    {n : Nat} (h : s.NoDead) : Post (Mem.mapWrite s l es n) fun r => r.1.NoDead := by
  unfold Mem.mapWrite; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact Mem.mapWrite_noDead (by nd_h))

theorem Mem.storeElems_noDead {base : Loc} : ∀ {vs : List GoValue} {s : Store} {start : Nat},
    s.NoDead → Post (Mem.storeElems ctx s base start vs) fun r => r.1.NoDead
  | [], s, start, h => by unfold Mem.storeElems; nd
  | v :: vs, s, start, h => by
    unfold Mem.storeElems
    refine Post.bind (Mem.store_noDead h) fun a ha => ?_
    refine Post.bind (Mem.storeElems_noDead (vs := vs) ha) fun b hb => ?_
    exact Post.pure hb
macro_rules | `(tactic| nd_db) => `(tactic| exact Mem.storeElems_noDead (by nd_h))

theorem Mem.storeRun_noDead {s : Store} {sl : SliceValue} {start : Nat} {vs : List GoValue}
    (h : s.NoDead) : Post (Mem.storeRun ctx s sl start vs) fun r => r.1.NoDead := by
  unfold Mem.storeRun; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact Mem.storeRun_noDead (by nd_h))

namespace Machine

/-! ## `NoDead` through the machine's operations -/

theorem runCommit_noDead {α : Type} {c : Commit α} {proj : α → Store} {s : Store}
    (hc : Commit.NoDead c proj) (h : s.NoDead) :
    Post (runCommit c s) fun r => (proj r).NoDead := by
  unfold runCommit
  split
  · exact Post.throw
  · exact hc s h
macro_rules | `(tactic| nd_db) => `(tactic| exact runCommit_noDead ‹_› (by nd_h))

theorem mapAssignValue.plan_noDead {s : Store} {keyTy valueTy : Ty} {b k v : GoValue} :
    Post (mapAssignValue.plan ctx s keyTy valueTy b k v) fun c => Commit.NoDead c fun r => r.1 := by
  unfold mapAssignValue.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact mapAssignValue.plan_noDead)

theorem mapAssignValue_noDead {s : Store} {keyTy valueTy : Ty} {b k v : GoValue} (h : s.NoDead) :
    Post (mapAssignValue ctx s keyTy valueTy b k v) fun r => r.1.NoDead := by
  unfold mapAssignValue
  refine Post.bind mapAssignValue.plan_noDead fun c hc => hc s h
macro_rules | `(tactic| nd_db) => `(tactic| exact mapAssignValue_noDead (by nd_h))

theorem allocDecls_noDead : ∀ {ps : List Param} {env : LocalEnv} {s : Store},
    s.NoDead → Post (allocDecls ctx env s ps) fun r => r.2.NoDead
  | [], env, s, h => by unfold allocDecls; nd
  | p :: ps, env, s, h => by
    unfold allocDecls
    refine Post.bind_any fun v => ?_
    refine Post.bind (Store.alloc_noDead h) fun a ha => ?_
    exact allocDecls_noDead ha
macro_rules | `(tactic| nd_db) => `(tactic| exact allocDecls_noDead (by nd_h))

theorem bindParams_noDead : ∀ {ps : List Param} {vs : List GoValue} {env : LocalEnv} {s : Store},
    s.NoDead → Post (bindParams ctx env s ps vs) fun r => r.2.NoDead
  | [], [], env, s, h => by unfold bindParams; nd
  | p :: ps, v :: vs, env, s, h => by
    unfold bindParams
    refine Post.bind_any fun v => ?_
    refine Post.bind (Store.alloc_noDead h) fun a ha => ?_
    exact bindParams_noDead ha
  | [], _ :: _, env, s, h => by unfold bindParams; nd
  | _ :: _, [], env, s, h => by unfold bindParams; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact bindParams_noDead (by nd_h))

theorem applySlice_noDead {s : Store} {b : GoValue} {lo hi : Int} {mx : Option Int}
    (h : s.NoDead) : Post (applySlice ctx s b lo hi mx) fun r => r.2.NoDead := by
  unfold applySlice; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applySlice_noDead (by nd_h))

theorem applyStrictOp_noDead {s : Store} {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue}
    (h : s.NoDead) : Post (applyStrictOp ctx s leafOf op vs) fun r => r.2.1.NoDead := by
  unfold applyStrictOp; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStrictOp_noDead (by nd_h))

theorem convCapApplyAt_noDead {s : Store} {kind : ConvKind} {literal : Bool} {value : GoString}
    {pick : Nat} (h : s.NoDead) :
    Post (convCapApplyAt ctx s kind literal value pick) fun r => r.2.1.NoDead := by
  unfold convCapApplyAt; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact convCapApplyAt_noDead (by nd_h))

theorem convCapApply_noDead {s : Store} {kind : ConvKind} {literal : Bool} {vs : List GoValue}
    {ch : Choices} (h : s.NoDead) :
    Post (convCapApply ctx s kind literal vs ch) fun r => r.1.2.1.NoDead := by
  unfold convCapApply
  split
  · nd
  · obtain ⟨m, hm⟩ := convRefuse_eq_error kind vs
    rw [hm]; exact Post.error
macro_rules | `(tactic| nd_db) => `(tactic| exact convCapApply_noDead (by nd_h))

theorem applyStrictOpPick_noDead {s : Store} {leafOf : Loc → Loc} {op : StrictOp}
    {vs : List GoValue} {ch : Choices} (h : s.NoDead) :
    Post (applyStrictOpPick ctx s leafOf op vs ch) fun r => r.1.2.1.NoDead := by
  unfold applyStrictOpPick; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStrictOpPick_noDead (by nd_h))

theorem enterFrame.plan_noDead {s : Store} {fid : FuncId} {args : List GoValue} :
    Post (enterFrame.plan ctx s fid args) fun c => Commit.NoDead c fun r => r.2.1 := by
  unfold enterFrame.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact enterFrame.plan_noDead)

theorem enterFrame_noDead {s : Store} {fid : FuncId} {args : List GoValue} (h : s.NoDead) :
    Post (enterFrame ctx s fid args) fun r => r.2.1.NoDead := by
  unfold enterFrame; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact enterFrame_noDead (by nd_h))

theorem enterFramePick_noDead {s : Store} {fid : FuncId} {args : List GoValue} {ch : Choices}
    (h : s.NoDead) :
    Post (enterFramePick ctx s fid args ch) fun r =>
      ∀ a, r.1 = .ok a → a.2.1.NoDead := by
  unfold enterFramePick
  split
  · rename_i r heq
    refine Post.ok ?_
    intro a ha; cases ha
    exact enterFrame_noDead h _ (toResult_ok_inv heq)
  · exact Post.ok (by intro a ha; cases ha)
  · exact Post.error
macro_rules | `(tactic| nd_db) => `(tactic| exact enterFramePick_noDead (by nd_h))

theorem enterFramePickV_noDead {s : Store} {fid : FuncId} {args : List GoValue} {ch : Choices} :
    Post (enterFramePickV ctx s fid args ch) fun r =>
      ∀ c, r.1 = .ok c → Commit.NoDead c fun r => r.2.1 := by
  unfold enterFramePickV
  split
  · rename_i c heq
    refine Post.ok ?_
    intro a ha; cases ha
    exact enterFrame.plan_noDead _ (toResult_ok_inv heq)
  · exact Post.ok (by intro a ha; cases ha)
  · exact Post.error
macro_rules | `(tactic| nd_db) => `(tactic| exact enterFramePickV_noDead)

/-! `applyStmtOpCore.plan`, one operator at a time (each sweep within the default budget). -/

theorem applyStmtOpCore.plan_noDead_allocNew {s : Store} {vs : List GoValue} {typ : _} :
    Post (applyStmtOpCore.plan ctx s (.allocNew typ) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_makeSlice {s : Store} {vs : List GoValue} {elem : _} {hasCap : _} :
    Post (applyStmtOpCore.plan ctx s (.makeSlice elem hasCap) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_makeMap {s : Store} {vs : List GoValue} {hasSpace : _} :
    Post (applyStmtOpCore.plan ctx s (.makeMap hasSpace) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_makeChan {s : Store} {vs : List GoValue} {elem : _} {hasCap : _} :
    Post (applyStmtOpCore.plan ctx s (.makeChan elem hasCap) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_mapAssign {s : Store} {vs : List GoValue} {keyTy : _} {valueTy : _} :
    Post (applyStmtOpCore.plan ctx s (.mapAssign keyTy valueTy) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_appendSlice {s : Store} {vs : List GoValue} {elem : _} :
    Post (applyStmtOpCore.plan ctx s (.appendSlice elem) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_randIntn {s : Store} {vs : List GoValue}  :
    Post (applyStmtOpCore.plan ctx s .randIntn vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_copySlice {s : Store} {vs : List GoValue}  :
    Post (applyStmtOpCore.plan ctx s .copySlice vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_mapDelete {s : Store} {vs : List GoValue} {keyTy : _} :
    Post (applyStmtOpCore.plan ctx s (.mapDelete keyTy) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_clearMap {s : Store} {vs : List GoValue}  :
    Post (applyStmtOpCore.plan ctx s .clearMap vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_clearSlice {s : Store} {vs : List GoValue} {elem : _} :
    Post (applyStmtOpCore.plan ctx s (.clearSlice elem) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_sortSlice {s : Store} {vs : List GoValue} {elem : _} :
    Post (applyStmtOpCore.plan ctx s (.sortSlice elem) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead_print {s : Store} {vs : List GoValue} {newline : _} :
    Post (applyStmtOpCore.plan ctx s (.print newline) vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOpCore.plan; nd

theorem applyStmtOpCore.plan_noDead {s : Store} {op : StmtOp} {vs : List GoValue} :
    Post (applyStmtOpCore.plan ctx s op vs) fun c => Commit.NoDead c fun r => r.1 := by
  cases op with
  | allocNew => exact applyStmtOpCore.plan_noDead_allocNew
  | makeSlice => exact applyStmtOpCore.plan_noDead_makeSlice
  | makeMap => exact applyStmtOpCore.plan_noDead_makeMap
  | makeChan => exact applyStmtOpCore.plan_noDead_makeChan
  | mapAssign => exact applyStmtOpCore.plan_noDead_mapAssign
  | appendSlice => exact applyStmtOpCore.plan_noDead_appendSlice
  | randIntn => exact applyStmtOpCore.plan_noDead_randIntn
  | copySlice => exact applyStmtOpCore.plan_noDead_copySlice
  | mapDelete => exact applyStmtOpCore.plan_noDead_mapDelete
  | clearMap => exact applyStmtOpCore.plan_noDead_clearMap
  | clearSlice => exact applyStmtOpCore.plan_noDead_clearSlice
  | sortSlice => exact applyStmtOpCore.plan_noDead_sortSlice
  | print => exact applyStmtOpCore.plan_noDead_print
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStmtOpCore.plan_noDead)

theorem applyStmtOp.plan_noDead {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} :
    Post (applyStmtOp.plan ctx s ch op nt vs) fun c => Commit.NoDead c fun r => r.1 := by
  unfold applyStmtOp.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStmtOp.plan_noDead)

theorem bindIterVars_noDead {env : LocalEnv} {s : Store} {kv vv : Option VarId} {kt vt : Ty}
    {k v : GoValue} (h : s.NoDead) :
    Post (bindIterVars ctx env s kv vv kt vt k v) fun r => r.2.NoDead := by
  unfold bindIterVars; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact bindIterVars_noDead (by nd_h))

theorem storeTarget.plan_noDead {s : Store} {r : TargetRef} {v : GoValue} :
    Post (storeTarget.plan ctx s r v) fun c => Commit.NoDead c fun r => r.1 := by
  unfold storeTarget.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact storeTarget.plan_noDead)

theorem unseqLoad.plan_noDead {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)}
    {bind tgt : VarId} :
    Post (unseqLoad.plan ctx s env tg bind tgt) fun c => Commit.NoDead c fun r => r.1 := by
  unfold unseqLoad.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact unseqLoad.plan_noDead)

theorem unseqGuard_noDead {s : Store} {g : UnseqGraph} {env : LocalEnv} {st : List UnseqStatus}
    {i : Nat} {test : VarId} {w : Bool} {out : VarId} (h : s.NoDead) :
    Post (unseqGuard ctx s g env st i test w out) fun r => r.2.1.NoDead := by
  unfold unseqGuard; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact unseqGuard_noDead (by nd_h))

theorem enterRecvTargets_noDead {s : Store} {targets : List Assignee} {vals : List GoValue}
    {body : Stmt} {env : LocalEnv} {k : Cont} (h : s.NoDead) :
    Post (enterRecvTargets s targets vals body env k) fun r => r.2.NoDead := by
  unfold enterRecvTargets; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact enterRecvTargets_noDead (by nd_h))

theorem applyChanOp_noDead {s : Store} {op : ChanStOp} {vs : List GoValue} {env : LocalEnv}
    {k : Cont} (h : s.NoDead) : Post (applyChanOp ctx s op vs env k) fun r => r.2.1.NoDead := by
  unfold applyChanOp; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyChanOp_noDead (by nd_h))

theorem applySyncOpCore_noDead {s : Store} {op : SyncOp} {vs : List GoValue} {env : LocalEnv}
    {k : Cont} (h : s.NoDead) :
    Post (applySyncOpCore ctx s op vs env k) fun r => r.2.1.NoDead := by
  unfold applySyncOpCore; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applySyncOpCore_noDead (by nd_h))

theorem tryDeliver_noDead {b : Bool} {s : Store} {targets : List Assignee} {env : LocalEnv}
    {k : Cont} (h : s.NoDead) : Post (tryDeliver b s targets env k) fun r => r.2.NoDead := by
  unfold tryDeliver; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact tryDeliver_noDead (by nd_h))

theorem applyTryLock_noDead {s : Store} {op : SyncOp} {loc : Loc} {pre : SyncPrim}
    {spurious : Bool} {targets : List Assignee} {env : LocalEnv} {k : Cont} (h : s.NoDead) :
    Post (applyTryLock ctx s op loc pre spurious targets env k) fun r => r.2.1.NoDead := by
  unfold applyTryLock; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyTryLock_noDead (by nd_h))

theorem applySyncOp_noDead {s : Store} {ch : Choices} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : s.NoDead) :
    Post (applySyncOp ctx s ch op vs env k) fun r => r.2.1.NoDead := by
  unfold applySyncOp; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applySyncOp_noDead (by nd_h))

theorem atomicStore_noDead {s : Store} {loc : Loc} {kind : IntKind} {v : Option Int}
    (h : s.NoDead) : Post (atomicStore ctx s loc kind v) Store.NoDead := by
  unfold atomicStore; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact atomicStore_noDead (by nd_h))

theorem applyAtomicOp_noDead {s : Store} {op : AtomicOp} {vs : List GoValue} {env : LocalEnv}
    {k : Cont} (h : s.NoDead) : Post (applyAtomicOp ctx s op vs env k) fun r => r.2.1.NoDead := by
  unfold applyAtomicOp; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyAtomicOp_noDead (by nd_h))

theorem commitClause_noDead {s : Store} {env : LocalEnv} {k : Cont} {c : EvClause}
    (h : s.NoDead) : Post (commitClause ctx s env k c) fun r => r.2.1.NoDead := by
  unfold commitClause; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact commitClause_noDead (by nd_h))

/-- What a select's readiness step returns keeps `NoDead`: the committed store of a `.done`, and
the store of every pre-committed ready clause of a `.picks`. -/
def SelectOutcome.NoDead : SelectOutcome → Prop
  | .done _ σ _ _ => σ.NoDead
  | .picks _ commits => ∀ (i : Nat) (p : EvClause × Sum (Config × Store × AccessTrace) String),
      commits[i]? = some p → ∀ r, p.2 = .inl r → r.2.1.NoDead

theorem applySelectCore_noDead {s : Store} {clauses : List (SelectClauseHead × Stmt)}
    {d : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont} (h : s.NoDead) :
    Post (applySelectCore ctx s clauses d vs env k) SelectOutcome.NoDead := by
  unfold applySelectCore
  refine Post.bind_any fun evs => ?_
  dsimp only
  refine Post.bind_any fun ready => ?_
  split
  · split <;> exact Post.pure h
  · refine Post.bind (commitClause_noDead h) fun a ha => ?_
    exact Post.pure ha
  · refine Post.bind (Q := fun commits => SelectOutcome.NoDead (.picks (selectPoll evs) commits))
      ?_ fun cs hcs => Post.pure hcs
    intro cs hcs i p hp r hpr
    obtain ⟨cl, _, hf⟩ := mapM_getElem?_mem hcs hp
    split at hf
    · rename_i r' heq
      cases hf; cases hpr
      exact commitClause_noDead h _ heq
    · cases hf; cases hpr
    · cases hf

theorem applySelect_noDead {s : Store} {clauses : List (SelectClauseHead × Stmt)}
    {d : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : s.NoDead) : Post (applySelect ctx s clauses d vs env k ch) fun r => r.2.1.NoDead := by
  unfold applySelect
  refine Post.bind (applySelectCore_noDead h) fun o ho => ?_
  split
  · exact Post.pure ho
  · dsimp only
    split
    · rename_i heq
      exact Post.pure (ho _ _ heq _ rfl)
    · exact Post.pure h
    · exact Post.throw
macro_rules | `(tactic| nd_db) => `(tactic| exact applySelect_noDead (by nd_h))

theorem storeTarget_noDead {s : Store} {r : TargetRef} {v : GoValue} (h : s.NoDead) :
    Post (storeTarget ctx s r v) fun r => r.1.NoDead := by
  unfold storeTarget; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact storeTarget_noDead (by nd_h))

theorem unseqLoad_noDead {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)}
    {bind tgt : VarId} (h : s.NoDead) :
    Post (unseqLoad ctx s env tg bind tgt) fun r => r.1.NoDead := by
  unfold unseqLoad; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact unseqLoad_noDead (by nd_h))

theorem applyStmtOpCore_noDead {s : Store} {op : StmtOp} {vs : List GoValue} (h : s.NoDead) :
    Post (applyStmtOpCore ctx s op vs) fun r => r.1.NoDead := by
  unfold applyStmtOpCore; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStmtOpCore_noDead (by nd_h))

theorem applyStmtOp_noDead {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (h : s.NoDead) :
    Post (applyStmtOp ctx s ch op nt vs) fun r => r.1.NoDead := by
  unfold applyStmtOp; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStmtOp_noDead (by nd_h))

/-! ## The step function -/

theorem deliverS_noDead {α : Type} {s : Store} {k : Cont} {ch : Choices}
    {next : α → Config × Store × Choices × StepLabel} {r : Result α} {chain : List PanicEntry}
    {Q : α → Prop} (h : s.NoDead) (hr : ∀ a, r = .ok a → Q a)
    (hnext : ∀ a, Q a → (next a).2.1.NoDead) : (deliverS s k ch next r chain).2.1.NoDead := by
  cases r with
  | ok a => exact hnext a (hr a rfl)
  | panic msg => exact h

theorem deliverV_noDead {α : Type} {s : Store} {k : Cont} {ch : Choices}
    {next : α → Config × Store × Choices × StepLabel} {r : Result (Commit α)}
    {chain : List PanicEntry} {ps : List PickRecord} {proj : α → Store} (h : s.NoDead)
    (hr : ∀ c, r = .ok c → Commit.NoDead c proj)
    (hnext : ∀ a, (proj a).NoDead → (next a).2.1.NoDead) :
    Post (deliverV s k ch next r chain ps) fun x => x.2.1.NoDead := by
  cases r with
  | ok c => exact Post.map (Post.mono (runCommit_noDead (hr c rfl) h) hnext)
  | panic msg => exact Post.ok h

macro_rules
  | `(tactic| nd_deliver) => `(tactic| first
      | (refine Post.pure (deliverS_noDead (by nd_h) ‹_› ?_); intro _ _; assumption)
      | (refine Post.pure (deliverS_noDead (Q := fun _ => True) (by nd_h) ‹_› ?_); intro _ _;
          first | assumption | (dsimp only; nd_h))
      | (refine deliverV_noDead (by nd_h) ‹_› ?_; intro _ _; assumption))

theorem stepFrameExit_noDead {s : Store} {targets : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {ds : List (GoValue × List GoValue)} {k' : Cont}
    {fr : FuncId} {ch : Choices} (h : s.NoDead) :
    Post (stepFrameExit ctx s targets tenv results ds k' fr ch) fun r => r.2.1.NoDead := by
  unfold stepFrameExit; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepFrameExit_noDead (by nd_h))

theorem stepUnseqEnter_noDead {s : Store} {g : UnseqGraph} {thenB : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices} (h : s.NoDead) :
    Post (stepUnseqEnter ctx s g thenB env k ch) fun r => r.2.1.NoDead := by
  unfold stepUnseqEnter; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepUnseqEnter_noDead (by nd_h))

theorem stepUnseqNext_noDead {s : Store} {g : UnseqGraph} {thenB : Stmt} {st : List UnseqStatus}
    {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase} {k : Cont} {ch : Choices}
    (h : s.NoDead) :
    Post (stepUnseqNext ctx s g thenB st tg env ph k ch) fun r => r.2.1.NoDead := by
  unfold stepUnseqNext; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepUnseqNext_noDead (by nd_h))

theorem stepUnseqValue_noDead {s : Store} {v : GoValue} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {ch : Choices} (h : s.NoDead) :
    Post (stepUnseqValue ctx s v g thenB st tg env ph k ch) fun r => r.2.1.NoDead := by
  unfold stepUnseqValue; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepUnseqValue_noDead (by nd_h))

theorem stepPanicStop_noDead {s : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch : Choices} (h : s.NoDead) :
    Post (stepPanicStop ctx s first rest ch) fun r => r.2.1.NoDead := by
  unfold stepPanicStop; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepPanicStop_noDead (by nd_h))

theorem stepRetOther_noDead {s : Store} {v : GoValue} {k : Cont} {ch : Choices} (h : s.NoDead) :
    Post (stepRetOther s v k ch) fun r => r.2.1.NoDead := by
  unfold stepRetOther; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepRetOther_noDead (by nd_h))

theorem stepNextOther_noDead {s : Store} {k : Cont} {ch : Choices} (h : s.NoDead) :
    Post (stepNextOther ctx s k ch) fun r => r.2.1.NoDead := by
  unfold stepNextOther; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact stepNextOther_noDead (by nd_h))

/-! `stepFn`, one `Config` constructor at a time (each sweep within the default budget). -/

theorem stepFn_noDead_exec {s : Store} {ch : Choices} {stmt : _} {env : _} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.exec stmt env k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_evalE {s : Store} {ch : Choices} {e : _} {env : _} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.evalE e env k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_retV {s : Store} {ch : Choices} {v : _} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.retV v k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_next {s : Store} {ch : Choices} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.next k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_signal {s : Store} {ch : Choices} {sg : _} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.signal sg k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_panicking {s : Store} {ch : Choices} {chain : _} {k : _} (h : s.NoDead) :
    Post (stepFn ctx s (.panicking chain k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_blockedSend {s : Store} {ch : Choices} {c : _} {v : _} {k : _} :
    Post (stepFn ctx s (.blockedSend c v k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_blockedRecv {s : Store} {ch : Choices} {c : _} {targets : _} {elem : _} {env : _} {k : _} :
    Post (stepFn ctx s (.blockedRecv c targets elem env k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_blockedSelect {s : Store} {ch : Choices} {clauses : _} {env : _} {k : _} :
    Post (stepFn ctx s (.blockedSelect clauses env k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

theorem stepFn_noDead_blockedSync {s : Store} {ch : Choices} {op : _} {loc : _} {env : _} {k : _} :
    Post (stepFn ctx s (.blockedSync op loc env k) ch) fun r => r.2.1.NoDead := by
  unfold stepFn; nd

/-- **No machine step creates a dead cell.** -/
theorem stepFn_noDead {s : Store} {c : Config} {ch : Choices} (h : s.NoDead) :
    Post (stepFn ctx s c ch) fun r => r.2.1.NoDead := by
  cases c with
  | exec => exact stepFn_noDead_exec h
  | evalE => exact stepFn_noDead_evalE h
  | retV => exact stepFn_noDead_retV h
  | next => exact stepFn_noDead_next h
  | signal => exact stepFn_noDead_signal h
  | panicking => exact stepFn_noDead_panicking h
  | blockedSend => exact stepFn_noDead_blockedSend
  | blockedRecv => exact stepFn_noDead_blockedRecv
  | blockedSelect => exact stepFn_noDead_blockedSelect
  | blockedSync => exact stepFn_noDead_blockedSync

end Machine

/-- **No run creates a dead cell**: `NoDead` holds at the end of every labelled prefix that
starts in a `NoDead` store. -/
theorem ExecutionStatement.Prefix.noDead {ctx : ProgramCtx} {n : Nat} {s sf : Store}
    {c cf : Machine.Config} {ch chf : Choices} {ls : List StepLabel}
    (hp : ExecutionStatement.Prefix ctx n s c ch ls sf cf chf) : s.NoDead → sf.NoDead := by
  induction hp with
  | done => exact id
  | step hs _ ih => exact fun h => ih (Machine.stepFn_noDead h _ hs)

end GoLean.GoCore

