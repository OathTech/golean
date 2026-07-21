import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel

/-!
# GoCore ⇒ Iris `Language` wiring
The `Config`/`ExecState`/`Step` instantiation of iris-lean's bare `Language`.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

/-- Iris `Val` is unit; the terminal control configuration is `.next .stop`
(a GoCore statement run produces no value — results are written to caller heap
locations, so the content lives in the `State`). -/
instance : ToVal Config Unit where
  toVal c := match c with | .next .stop => some () | _ => none
  ofVal _ := .next .stop
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The Iris primitive step: GoCore's small-step `Step`, with no observations
and no forked threads (the sequential relation forks nothing). -/
inductive GoPrimStep :
    Config × ExecState → List Unit → Config × ExecState × List Config → Prop where
  | step {c s c' s'} : Step c s c' s' → GoPrimStep (c, s) [] (c', s', [])

instance : PrimStep Config ExecState (List Unit) where
  primStep := GoPrimStep

/-- The bare `Language` instance: a CK machine seats on iris-lean directly, with
no `EctxLanguage`. `val_stuck` holds because no `Step` rule has `.next .stop` as
its source — the terminal control is irreducible. -/
instance : Language Config ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st => cases st <;> rfl

instance : Inhabited ExecState := ⟨{}⟩

/-! ## Step 3b — gen_heap over GoCore's real heap

Wire iris-lean's gen_heap to GoCore's actual heap, keyed by the base address
`Nat` (heap cells live only at `.base ⟨n⟩` locs; `Nat` has the lawful compare
`ExtTreeMap`/gen_heap require, sidestepping a compare for the recursive `Loc`).
This gives the `↦` connective over GoCore's heap and the `StateInterp`/`IrisGS`
that WP laws — pure (`wp_seqn`) and heap-touching (`wp_assign`) — run against. -/

end GoLean.Iris
