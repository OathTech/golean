import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval

/-!
# Assignment laws (R3 rewrite over the fine-grained machine)

The old file's laws bundled target resolution, RHS evaluation, and the
store into one `ExprR`-conditioned step. Under the machine an assignment
is a WALK — entry, address, target receipt, RHS, store — and the
statement-level law here is that walk COMPOSED from `Laws/Eval`'s step
laws. `wp_assign_lit` is simultaneously the law and the non-vacuity
witness of the walk architecture (five steps chained through the
later/credit plumbing; the store side-condition closes to zero
hypotheses by `storeLoc_int_cell`, as before the reshape).

Old laws whose *shape* dissolved (`wp_assign` with an `ExprR` RHS
premise, `wp_deref_store`, `wp_store_via_ptr`, `wp_var_inc`, …) return as
composed walks when the golden/loop witnesses need them (same
restoration discipline as everything else in R3).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **`x = intLit n` — the composed assignment walk** (entry → `&x` →
target receipt → literal → store), and the walk architecture's discharge
witness: every premise of every step law is discharged here — the plan
fact by `rfl`, resolution by `hres`, and the store by
`storeLoc_int_cell` (zero residual hypotheses beyond the resolution). -/
theorem wp_assign_lit {x : String} {a : Addr} {w : GoValue} {n : Int}
    {kind : IntKind} {env k}
    (hres : LocalEnv.lookup env x = some (.base a)) :
    a.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var x) (.intLit n kind)) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply (wp_assign_start (te := .ref x) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred₁
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred₂
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred₃
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred₄
  iapply (wp_assign_store
    (oldcell := ⟨some (.int kind), w⟩)
    (newcell := ⟨some (.int kind), .int (kind.normalize n) kind⟩)
    (fun σ₁ hlook => storeLoc_int_cell hlook n))
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  iapply Hcont $$ Hpt

end

end GoLean.Iris
