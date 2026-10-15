import RelationalCodeX.UnseqLifting
import RelationalCodeX.UnseqOperations
import GoLean.Relational
import Init.Data.List.Nat.Erase

namespace U1RD8
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational
open GoLean.Logic GoLean.IrisCustomer RelationalCodeX.Sweep

theorem path_plan {ctx rows c d finish post}
    (path : StorePathFor ctx (Facts rows) (Quiet ctx) c d)
    (next : Plan ctx finish post d rows) : Plan ctx finish post c rows := by
  induction path with
  | refl => exact next
  | step ht ha hq _ ih =>
    refine Plan.choose (ι := Unit) (next := fun _ => _) ha hq ?_ (fun _ => ih next)
    intro s hs ch
    obtain ⟨l, hl, hp⟩ := ht s hs
    exact ⟨(), l, ch, hl, by rw [hp]; rfl⟩

theorem focus {α : Type} {xs : List α} {i : Nat} {x : α}
    (get : xs[i]? = some x) : xs.Perm (x :: xs.eraseIdx i) := by
  induction xs generalizing i with
  | nil => simp at get
  | cons a xs ih =>
    cases i with
    | zero => simp at get; subst a; exact .refl _
    | succ i =>
      simp only [List.getElem?_cons_succ] at get
      exact (List.Perm.cons a (ih get)).trans (List.Perm.swap _ _ _)

theorem write_at {ctx finish post c d rows i slot old new}
    (get : rows[i]? = some (slot,old)) (quiet : Quiet ctx c)
    (shape : (Memory.flattenCell ctx (.base ⟨slot⟩) new).map Memory.skelOf =
      (Memory.flattenCell ctx (.base ⟨slot⟩) old).map Memory.skelOf)
    (effect : StoreEffect ctx (fun s t => ∃ h : s.heap[slot]? = some old,
      t = {s with heap := s.heap.set slot new (Array.getElem?_eq_some_iff.mp h).1}) c d)
    (next : Plan ctx finish post d (rows.set i (slot,new))) :
    Plan ctx finish post c rows := by
  apply Plan.reorder (focus get)
  apply Plan.write quiet shape effect
  have bound := (List.getElem?_eq_some_iff.mp get).1
  have perm := focus (List.getElem?_set_self (a := (slot,new)) bound)
  rw [List.eraseIdx_set_eq] at perm
  exact Plan.reorder perm.symm next

theorem int_shape (ctx : ProgramCtx) (slot : Nat) (a b : Int) :
    (Memory.flattenCell ctx (.base ⟨slot⟩) (cell a)).map Memory.skelOf =
      (Memory.flattenCell ctx (.base ⟨slot⟩) (cell b)).map Memory.skelOf := by
  exact (Memory.flattenCell_skel_flat (ctx := ctx) (ty := .int .int64) rfl _ _).trans
    (Memory.flattenCell_skel_flat (ctx := ctx) (ty := .int .int64) rfl _ _).symm

end U1RD8
