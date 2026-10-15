import Concurrency.Reuse
import Lean

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- The original root-only obligation, retained as a regression. D1's public
location/key order and shadow-history contracts cover arbitrary paths. -/
def RootComparatorContract : Prop :=
  ∀ a b : Addr, compare (Loc.base a) (Loc.base b) = compare a.id b.id

theorem root_comparator_contract : RootComparatorContract := by
  intro a b; rfl

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let name := ``instOrdLoc.ord
  let some (.defnInfo info) := env.find? name
    | throwError "D1 comparator must be a transparent definition"
  unless info.safety == .safe do throwError "D1 comparator must be total and safe"
  logInfo m!"D1 comparator: {name} is transparent, total and safe; other findings are audited separately"

#print axioms instOrdLoc.ord
#print axioms root_comparator_contract
end Concurrency
