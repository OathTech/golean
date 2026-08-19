import GoLean.GoCore.MachineSound

/-!
# Determinism of the machine (R3 restoration of `Inversions`)

The old file held per-expression-form `ExprR` determinism inversions
(`exprR_var_eq_lit_det` and family), consumed by the laws' `hred`
determinism obligations. Under the fine-grained machine they collapse into
ONE generic fact: away from the three nondeterministic step classes
(`mapIterK`'s pick-next, the `stmtOpK` apply position, whose
`applyStmtOp` may consume a capacity choice, and — channels arc slice
4 — the `selectOpsK` apply position, whose `applySelect` may consume
the L2 clause pick), the rules are syntactically
disjoint and their premises are function equations — so any two steps
from the same configuration agree. `step_det` is what every
`wp_det_step_keep`/`wp_store_step`-style `hred` cites for its determinism
half; no per-form inversion lemmas remain.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- Configurations whose outgoing step (if any) is unique. Everything
except the three choice classes — conservatively including the nullary
wide-statement entry (its `applyStmtOp` is in fact choice-independent,
but no law needs that) and every select apply position (single-ready
applies are in fact choice-independent, but no law steps through a
select). -/
def Config.choiceFree : Config → Prop
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ _) => False
  | .retV _ (.stmtOpK _ _ _ [] _ _) => False
  | .retV _ (.selectOpsK _ _ _ [] _ _) => False
  | .exec stmt _ _ =>
      match stmtPlan stmt with
      | some (_, _, []) => False
      | _ => True
  | _ => True

/-- **Generic determinism**: two steps from the same choice-free
configuration and state agree. Replaces the old per-form `*_det`
inversion family at strictly finer grain. -/
theorem step_det {c : Config} {σ : ExecState} {c₁ : Config} {σ₁ : ExecState}
    {c₂ : Config} {σ₂ : ExecState}
    (hcf : c.choiceFree)
    (h₁ : Step c σ c₁ σ₁) (h₂ : Step c σ c₂ σ₂) : c₁ = c₂ ∧ σ₁ = σ₂ := by
  cases h₁ <;> cases h₂ <;>
    first
      | (simp_all [Config.choiceFree, strictPlan, stmtPlan, panicPassthrough,
          chainNewestRecovered, chanPlan, selectOperands, syncPlan]; done)
      -- The cross-plan pairs simp cannot refute alone: a statement two
      -- plan classifiers claim (their domains are pairwise disjoint —
      -- `stmtPlan_of_chanPlan`, channels arc slice 1;
      -- `stmtPlan_of_syncPlan`/`chanPlan_of_syncPlan`, spec-parity
      -- slice 2).
      | (have := stmtPlan_of_chanPlan ‹_›; simp_all; done)
      | (have := stmtPlan_of_syncPlan ‹_›; simp_all; done)
      | (have := chanPlan_of_syncPlan ‹_›; simp_all; done)
      | omega

end GoLean.GoCore.Machine
