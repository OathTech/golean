import Concurrency.Reuse
import Lean

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- Missing kernel-visible comparator contract. Named, never assumed. The
audited pin's recursive `deriving Ord` supplies an opaque partial definition
instead of equations with which this proposition could be proved. -/
def RootComparatorContract : Prop :=
  ∀ a b : Addr, compare (Loc.base a) (Loc.base b) = compare a.id b.id

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let name := ``instOrdLoc.ord
  let some (.opaqueInfo _) := env.find? name
    | throwError "expected opaque comparator missing; reassess this finding"
  let implementation := `GoLean.GoCore.instOrdLoc.ord._unsafe_rec
  let some (.defnInfo info) := env.find? implementation
    | throwError "expected generated partial implementation missing"
  unless info.safety == .partial do throwError "implementation classification changed"
  logInfo m!"FINDING: {name} is opaque; generated implementation {implementation} has DefinitionSafety.partial"

#print axioms instOrdLoc.ord
end Concurrency
