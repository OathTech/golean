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
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions

/-!
# Expression-walk step laws (R3, new with the fine-grained machine)

The machine's answer to `wp_bind`: expression evaluation is a chain of
configurations (`evalE`/`retV` under operand frames), so instead of a
bind rule there is one small WP law per step class, composed
structurally. `wp_pure_det` is the generic engine for every pure
deterministic step (its determinism half is the generic `step_det` —
gone are the per-form inversion lemmas); the heap-touching steps
(`wp_eval_var` load, `wp_assign_store` store) instantiate the Lifting
cores. Statement-level laws (`Laws/Assign`, `Laws/Call`, `Laws/Loop`)
compose these walks.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **Generic pure deterministic step law.** A state-independent step from
a choice-free configuration lifts to WP with the standard later/credit
premise. Determinism comes from the generic `step_det`; each instance
supplies only its `Step` constructor. -/
theorem wp_pure_det {c₀ c₁ : Config}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hcf : c₀.choiceFree)
    (hstep : ∀ σ : ExecState, Step c₀ σ c₁ σ) :
    (|={E}[E]▷=> £ 1 -∗ WP c₁ @ s ; E {{ Φ }}) ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := c₁)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], c₁, σ, [], GoPrimStep.step (hstep σ)⟩
      · exact hnv)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        obtain ⟨he, hs⟩ := step_det hcf (hstep σ) st
        exact ⟨rfl, hs.symm, he.symm, rfl⟩))
  iexact H

/-! ### Pure expression steps -/

theorem wp_eval_intLit {n : Int} {kind : IntKind} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.retV (.int (kind.normalize n) kind) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.intLit n kind) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalIntLit)

theorem wp_eval_boolLit {b : Bool} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV (.bool b) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.boolLit b) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalBoolLit)

/-- `&x`: resolution is control-side (CEK), so taking an address is a pure
step. -/
theorem wp_eval_ref {id : String} {loc : Loc} {env k}
    (hres : LocalEnv.lookup env id = some loc) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV (.addr loc) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.ref id) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalRef hres)

/-- Enter a strict form: evaluate the first operand under the generic
frame. -/
theorem wp_eval_strict {e : Expr} {op : StrictOp} {e₁ : Expr}
    {rest : List Expr} {env k}
    (hplan : strictPlan e = some (op, e₁ :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e₁ env (.strictK op [] rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE e env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalStrict hplan)

/-- Shift to the next strict operand. -/
theorem wp_strict_shift {op : StrictOp} {done : List GoValue} {v : GoValue}
    {e : Expr} {rest : List Expr} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.strictK op (v :: done) rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.strictK op done (e :: rest) env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.strictShift)

/-- Apply a strict operator whose result is state-independent (every pure
operator: arithmetic, comparisons, logic — the premise quantifies the
state, discharged by `simp`/`decide` at concrete operands). ONE law for
the whole pure-op table. -/
theorem wp_strict_apply_pure {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {env k}
    (happly : ∀ σ : ExecState,
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV out k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.strictK op done [] env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun σ => Step.strictApply (happly σ))

/-! ### Statement-glue pure steps -/

/-- Begin an assignment: evaluate the target's address expression. -/
theorem wp_assign_start {lhs : Assignee} {te rhs : Expr} {env k}
    (hlhs : assigneeExpr lhs = some te) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE te env (.assignTargetK rhs env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.assign lhs rhs) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.assign hlhs)

/-- Receive the target address: evaluate the RHS toward the store. -/
theorem wp_assign_target {loc : Loc} {rhs : Expr} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE rhs env (.assignStoreK loc k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV (.addr loc) (.assignTargetK rhs env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.assignTargetLoc rfl)

/-- Receive an `if` condition. -/
theorem wp_if_bool {b : Bool} {t e : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.exec (if b then t else e) env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV (.bool b) (.ifK t e env k)) @ s ; E {{ Φ }} := by
  cases b
  · exact wp_pure_det rfl trivial (fun _ => Step.ifFalse)
  · exact wp_pure_det rfl trivial (fun _ => Step.ifTrue)

/-- Dispatch an `if`: evaluate the condition under its frame. -/
theorem wp_if_start {c : Expr} {t e : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE c env (.ifK t e env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.ifThenElse c t e) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.ifStmt)

/-- Dispatch a `while`: evaluate the condition under its frame. -/
theorem wp_while_start {c : Expr} {b : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE c env (.whileK c b env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.whileStmt)

/-- Receive a `while` condition: enter the body (`true`) or exit
(`false`). -/
theorem wp_while_bool {b : Bool} {c : Expr} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (if b then Config.exec body env (.loop c body env k)
          else Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV (.bool b) (.whileK c body env k)) @ s ; E {{ Φ }} := by
  cases b
  · exact wp_pure_det rfl trivial (fun _ => Step.whileFalse)
  · exact wp_pure_det rfl trivial (fun _ => Step.whileTrue)

/-! ### Heap-touching expression steps -/

/-- **The load step**: `x` reads its cell. Resolution is control-side; the
read is conditioned on the owned cell, which rides through unchanged. -/
theorem wp_eval_var {id : String} {a : Addr} {cell : HeapCell} {env k}
    (hres : LocalEnv.lookup env id = some (.base a)) :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (Config.retV cell.value k) @ s ; E {{ Φ }})
      ⊢ WP (Config.evalE (.var id) env k) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl)
  intro σ₁
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok cell.value := by
    simp [loadLoc, hlook]
  imodintro
  ipureintro
  refine ⟨Step.evalVar hres hload, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.evalVar hres hload) hst
  exact ⟨h1.symm, h2.symm⟩

/-- **The deref apply step**: the strict `deref` operator's application is
a load through the delivered address. The read cell rides through. -/
theorem wp_strict_apply_deref {ty : Ty} {a : Addr} {cell : HeapCell} {env k} :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (Config.retV cell.value k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr (.base a))
            (.strictK (.deref ty) [] [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl)
  intro σ₁
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have happly : applyStrictOp σ₁ (.deref ty) [.addr (.base a)]
      = .ok (cell.value, σ₁) := by
    simp [applyStrictOp, valueAsLoc, Bind.bind, Except.bind, loadLoc, hlook]
  imodintro
  ipureintro
  refine ⟨Step.strictApply (done := []) happly, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial)
    (Step.strictApply (done := []) happly) hst
  exact ⟨h1.symm, h2.symm⟩

/-- **The store step**: deliver the RHS value to a `.base`-located target
whose cell is owned. `hstore` is the cell-conditioned store fact (for
int-typed cells, `storeLoc_int_cell` discharges it). Instantiates the
`wp_store_step` core; determinism is `step_det`. -/
theorem wp_assign_store {a : Addr} {v : GoValue} {oldcell newcell : HeapCell} {k}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeLoc σ₁ (.base a) v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.assignStoreK (.base a) k)) @ s ; E {{ Φ }} := by
  iapply wp_store_step (hnv := rfl)
  intro σ₁ hfns hmeths htypes hlook
  refine ⟨Step.assignStore (hstore σ₁ htypes hlook), ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ :=
    step_det (by trivial) (Step.assignStore (hstore σ₁ htypes hlook)) hst
  exact ⟨h1.symm, h2.symm⟩

end

end GoLean.Iris
