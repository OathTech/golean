import GoLeanProofs.Frame.HeapOps
import GoLeanProofs.Frame.Compare
import GoLeanProofs.Frame.Plans

/-!
# The executable frame theorem: shared relation vocabulary for the
machine-op layer

`CfgSim` is the payload relation for machine steps that return a
CONFIGURATION beside the state (`applyChanOp`, `applySyncOp`,
`commitClause`, `enterRecvTargets`, and ultimately `stepFn` itself):
the framed configuration is the renamed canonical one, and the states
stay `FrameSim`-related. `ListSim` is the pointwise list relation for
non-functional element relations (the multi-ready select's
pre-committed list).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- Configuration-and-state result relation. -/
def CfgSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    Config × ExecState → Config × ExecState → Prop :=
  fun r rF => rF.1 = renameConfig ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2

/-- Pointwise list relation (this toolchain has no `List.Forall₂`). -/
inductive ListSim {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListSim R [] []
  | cons {a b as bs} : R a b → ListSim R as bs → ListSim R (a :: as) (b :: bs)

namespace ListSim

theorem length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListSim R l l' → l.length = l'.length := by
  intro l l' h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, ListSim R l l' → ∀ i : Nat,
      (l[i]? = none ∧ l'[i]? = none)
        ∨ ∃ a b, l[i]? = some a ∧ l'[i]? = some b ∧ R a b := by
  intro l l' h
  induction h with
  | nil => intro i; left; simp
  | cons hab _ ih =>
      intro i
      cases i with
      | zero => right; exact ⟨_, _, rfl, rfl, hab⟩
      | succ j => simpa using ih j

theorem of_map {α β : Type} {t : α → β} {R : α → β → Prop}
    (ht : ∀ a, R a (t a)) : ∀ l : List α, ListSim R l (l.map t) := by
  intro l
  induction l with
  | nil => exact .nil
  | cons a as ih => exact .cons (ht a) ih

end ListSim

end GoLean.Frame
