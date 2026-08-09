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
import GoLeanProofs.Tactics.GoWalk

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

/-! ### The GoCore half of `go_walk`'s normalization set

`go_walk` runs `simp only [go_walk_simp]` between steps. Machine-side, the
one rewrite every hand walk needed there is the evaluation of
`IntKind.normalize` at a literal: `wp_eval_intLit` delivers
`.int (kind.normalize n) kind`, and the configuration only matches the next
law once that is the literal again (the hand walks wrote
`rw [show IntKind.int.normalize 0 = 0 from by decide]`). At a NON-literal
the walk carries the normalization as a hypothesis instead
(`go_walk with [hq]`). -/
open Lean Meta in
simproc [go_walk_simp] reduceIntKindNormalize (IntKind.normalize _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withDefault <| Meta.reduce e
  -- put the answer back in `OfNat`/`Neg` form — the shape a law statement's
  -- literal has — so that the next configuration match stays syntactic
  if let some n := (r.app1? ``Int.ofNat).bind (·.rawNatLit?) then
    return .done { expr := ← mkNumeral (mkConst ``Int) n }
  if let some n := (r.app1? ``Int.negSucc).bind (·.rawNatLit?) then
    return .done { expr := ← mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (n + 1)] }
  return .continue

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

@[go_walk_law]
theorem wp_eval_intLit {n : Int} {kind : IntKind} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.retV (.int (kind.normalize n) kind) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.intLit n kind) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalIntLit)

@[go_walk_law]
theorem wp_eval_boolLit {b : Bool} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV (.bool b) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.boolLit b) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalBoolLit)

/-- `&x`: resolution is control-side (CEK), so taking an address is a pure
step. -/
@[go_walk_law]
theorem wp_eval_ref {id : String} {loc : Loc} {env k}
    (hres : LocalEnv.lookup env id = some loc) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV (.addr loc) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.ref id) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalRef hres)

/-- Enter a strict form: evaluate the first operand under the generic
frame. -/
@[go_walk_law]
theorem wp_eval_strict {e : Expr} {op : StrictOp} {e₁ : Expr}
    {rest : List Expr} {env k}
    (hplan : strictPlan e = some (op, e₁ :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e₁ env (.strictK op [] rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE e env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.evalStrict hplan)

/-- Shift to the next strict operand. -/
@[go_walk_law]
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
@[go_walk_law]
theorem wp_strict_apply_pure {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {env k}
    (happly : ∀ σ : ExecState,
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV out k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.strictK op done [] env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun σ => Step.strictApply (happly σ))

/-- **Apply a strict operator that is state-independent GIVEN the type
environment.** Between `wp_strict_apply_pure` (no state at all) and
`wp_strict_apply_read` (one owned heap cell): a conversion at a NAMED Go
type resolves the target name through `TypeEnv.lookup σ.types`, so its
`∀σ` premise is false without the pin — but it reads no heap cell, so
demanding one would be a lie about what the step touches. Resource-free
on both sides. -/
@[go_walk_law]
theorem wp_strict_apply_pin {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {env k}
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    (WP (Config.retV out k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.strictK op done [] env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_det_step_keep (P := iprop(emp)) (c₁ := Config.retV out k)
    (hnv := rfl))
  · intro σ₁ _hfns _hmeths htypes
    iintro ⟨Hσ, -⟩
    imodintro
    ipureintro
    refine ⟨Step.strictApply (happly σ₁ htypes), ?_⟩
    intro c' s' hst
    obtain ⟨h1, h2⟩ :=
      step_det (by trivial) (Step.strictApply (happly σ₁ htypes)) hst
    exact ⟨h1.symm, h2.symm⟩
  · isplitl []
    · itrivial
    · iintro -
      iexact H

/-- **A NULLARY strict form whose value depends on the type environment.**
The pin-carrying sibling of `wp_eval_strict_nullary_pure`
(`Laws/Unwind`): `struct{}{}` and every other composite literal with no
operands is built by resolving its type through `σ.types`, so the
unpinned `∀σ` premise is false at a named type. Resource-free. -/
@[go_walk_law]
theorem wp_eval_strict_nullary_pin {e : Expr} {op : StrictOp}
    {v : GoValue} {env k}
    (hplan : strictPlan e = some (op, []))
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      applyStrictOp σ op [] = .ok (v, σ)) :
    (WP (Config.retV v k) @ s ; E {{ Φ }})
      ⊢ WP (Config.evalE e env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_det_step_keep (P := iprop(emp)) (c₁ := Config.retV v k)
    (hnv := rfl))
  · intro σ₁ _hfns _hmeths htypes
    iintro ⟨Hσ, -⟩
    imodintro
    ipureintro
    refine ⟨Step.evalStrictNullary hplan (happly σ₁ htypes), ?_⟩
    intro c' s' hst
    obtain ⟨h1, h2⟩ := step_det (by simp [Config.choiceFree])
      (Step.evalStrictNullary hplan (happly σ₁ htypes)) hst
    exact ⟨h1.symm, h2.symm⟩
  · isplitl []
    · itrivial
    · iintro -
      iexact H

/-- **Apply a strict operator whose result READS the heap but changes
nothing.** The general form of `wp_strict_apply_deref`: the operator's
answer is conditioned on ONE owned cell, which rides through unchanged
(the state is literally `σ` on both sides of `applyStrictOp`). One law
for the whole state-reading pure-op family — `len(m)` (loads the map's
data cell), `a[i]` on a slice (loads the backing array), `x[lo:hi]` on an
array address (loads the array to learn its size), `*p` — none of which
`wp_strict_apply_pure` can serve, because their `∀σ` premise is false
without the heap fact. -/
@[go_walk_law]
theorem wp_strict_apply_read {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {a : Addr} {cell : HeapCell} {env k}
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some cell →
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (Config.retV out k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.strictK op done [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV out k) (hnv := rfl)
  intro σ₁ _hfns _hmeths htypes
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  imodintro
  ipureintro
  refine ⟨Step.strictApply (happly σ₁ htypes hlook), ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ :=
    step_det (by trivial) (Step.strictApply (happly σ₁ htypes hlook)) hst
  exact ⟨h1.symm, h2.symm⟩

/-! ### Statement-glue pure steps

The assignment walk (spine restatement, spec-parity slice 1): a single
assignment rides the tgtOpK/rhsK/storeK spine as a one-target
multi-assign (BUG-037 — the machine's `assignFirst`), so the old
`assignTargetK`/`assignStoreK` two-frame walk (entry → address → RHS →
store) becomes entry → address → `wp_tgtop_rhs` → RHS →
`wp_rhs_stores_vals` → the `storeK` store (`wp_assign_store`) →
`wp_stores_done`. Same handover points for a human: the store law is
still the one non-mechanical step. The comma-ok forms (BUG-034) enter
the same spine via `wp_map_lookup_start`/`wp_type_assert_start` with the
source carried as an `RhsOp`, applied at the end of phase 1
(`Laws/StmtOps.wp_map_lookup`). -/

/-- Begin an assignment: the spine entry (`assignFirst`) — evaluate the
target's first operand under the one-target `tgtOpK` frame, the RHS
carried for `rhsK`. -/
@[go_walk_law]
theorem wp_assign_start {lhs : Assignee} {rhs e : Expr} {sh : TargetShape}
    {ops : List Expr} {env k}
    (hplan : targetPlan lhs = some (sh, e :: ops)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] []
        (.seqn #[]) env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.assign lhs rhs) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.assignFirst hplan)

/-- Shift to the current target's next phase-1 operand. -/
@[go_walk_law]
theorem wp_tgtop_shift {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {e : Expr} {pending : List Expr} {refs : List TargetRef}
    {targets : List (TargetShape × List Expr)} {rop : RhsOp} {rhs : List Expr}
    {vals : List GoValue} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.tgtOpK sh (v :: ops) pending refs targets
        rop rhs vals body env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.tgtOpK sh ops (e :: pending) refs targets
        rop rhs vals body env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.tgtOpShift)

/-- Complete the current target and start the next one's operands. -/
@[go_walk_law]
theorem wp_tgtop_next {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {r : TargetRef} {sh' : TargetShape} {e : Expr} {ops' : List Expr}
    {targets : List (TargetShape × List Expr)} {refs : List TargetRef}
    {rop : RhsOp} {rhs : List Expr} {vals : List GoValue} {body : Stmt} {env k}
    (hcomp : completeTargetRef sh (v :: ops).reverse = some r) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) targets
        rop rhs vals body env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: targets)
        rop rhs vals body env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.tgtOpNext hcomp)

/-- Complete the LAST target: phase 1 turns to the right-hand side
(`rhsK`), the value source riding along. -/
@[go_walk_law]
theorem wp_tgtop_rhs {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {r : TargetRef} {refs : List TargetRef} {rop : RhsOp} {e : Expr}
    {rest : List Expr} {vals : List GoValue} {body : Stmt} {env k}
    (hcomp : completeTargetRef sh (v :: ops).reverse = some r) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals
        body env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.tgtOpRhs hcomp)

/-- Shift to the next right-hand expression. -/
@[go_walk_law]
theorem wp_rhs_shift {rop : RhsOp} {refs : List TargetRef}
    {done : List GoValue} {v : GoValue} {e : Expr} {rest : List Expr}
    {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.rhsK rop refs (v :: done) rest body env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.rhsK rop refs done (e :: rest) body env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.rhsShift)

/-- The last RHS value under the IDENTITY source (`.vals` — plain
single/multi assigns): phase 2 begins. The comma-ok sources' apply step
reads the heap and lives in `Laws/StmtOps` (`wp_rhs_map_lookup`). -/
@[go_walk_law]
theorem wp_rhs_stores_vals {refs : List TargetRef} {done : List GoValue}
    {v : GoValue} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.next (.storeK refs (v :: done).reverse body env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.rhsK .vals refs done [] body env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.rhsStores rfl)

/-- Phase 2 complete: enter the body (`.seqn #[]` for the statement
forms — the next walk steps drain it). -/
@[go_walk_law]
theorem wp_stores_done {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.exec body env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.storeK [] [] body env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.storeDone)

/-- Receive an `if` condition. -/
@[go_walk_law]
theorem wp_if_bool {b : Bool} {t e : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.exec (if b then t else e) env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV (.bool b) (.ifK t e env k)) @ s ; E {{ Φ }} := by
  cases b
  · exact wp_pure_det rfl trivial (fun _ => Step.ifFalse)
  · exact wp_pure_det rfl trivial (fun _ => Step.ifTrue)

/-- Dispatch an `if`: evaluate the condition under its frame. -/
@[go_walk_law]
theorem wp_if_start {c : Expr} {t e : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE c env (.ifK t e env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.ifThenElse c t e) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.ifStmt)

/-- Dispatch a `while`: evaluate the condition under its frame. -/
@[go_walk_law]
theorem wp_while_start {c : Expr} {b : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE c env (.whileK c b env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl
    (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.whileStmt)

/-- Receive a `while` condition: enter the body (`true`) or exit
(`false`). -/
@[go_walk_law]
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
@[go_walk_law]
theorem wp_eval_var {id : String} {a : Addr} {cell : HeapCell} {env k}
    (hres : LocalEnv.lookup env id = some (.base a)) :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (Config.retV cell.value k) @ s ; E {{ Φ }})
      ⊢ WP (Config.evalE (.var id) env k) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl)
  intro σ₁ _hfns _hmeths _htypes
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
@[go_walk_law]
theorem wp_strict_apply_deref {ty : Ty} {a : Addr} {cell : HeapCell} {env k} :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (Config.retV cell.value k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr (.base a))
            (.strictK (.deref ty) [] [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl)
  intro σ₁ _hfns _hmeths _htypes
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

/-- **The store step** (spine restatement): one `storeK` phase-2 store
through a completed bare-chain target (`.chain (.addr tgt) [] []` — the
shape every `x`/`$res` target completes to), the target's cell owned.
`hstore` is the SAME cell-conditioned `storeLoc` fact as before the
restatement (for int-typed cells, `storeLoc_int_cell` discharges it);
the chain replay (`storeTarget` → `resolveChain` → `valueAsLoc`) is
folded here once. Instantiates the `wp_store_step` core; determinism is
`step_det`. -/
theorem wp_store_target {a : Addr} {r : TargetRef} {v : GoValue}
    {oldcell newcell : HeapCell} {rs : List TargetRef} {vals : List GoValue}
    {body : Stmt} {env : LocalEnv} {k}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeTarget σ₁ r v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗
          WP (Config.next (.storeK rs vals body env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.storeK (r :: rs) (v :: vals)
            body env k)) @ s ; E {{ Φ }} := by
  iapply wp_store_step (hnv := rfl)
  intro σ₁ hfns hmeths htypes hlook
  refine ⟨Step.storeStep (hstore σ₁ htypes hlook), ?_⟩
  intro c' s' hst'
  obtain ⟨h1, h2⟩ :=
    step_det (by trivial) (Step.storeStep (hstore σ₁ htypes hlook)) hst'
  exact ⟨h1.symm, h2.symm⟩

/-- The bare-chain instance of `wp_store_target`: a completed
`.chain (.addr tgt) [] []` reference (the shape every `x`/`$res` target
completes to), whose replay is exactly one `storeLoc` — so the `hstore`
premise keeps the pre-restatement `storeLoc` shape every walk
discharges with `storeLoc_int_cell`/`storeLoc_int_any`/a `simp`. -/
theorem wp_assign_store_loc {a : Addr} {tgt : Loc} {v : GoValue}
    {oldcell newcell : HeapCell} {rs : List TargetRef} {vals : List GoValue}
    {body : Stmt} {env : LocalEnv} {k}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeLoc σ₁ tgt v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗
          WP (Config.next (.storeK rs vals body env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.storeK (.chain (.addr tgt) [] [] :: rs) (v :: vals)
            body env k)) @ s ; E {{ Φ }} :=
  wp_store_target (fun σ₁ htypes hlook => by
    simp [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
      hstore σ₁ htypes hlook])

/-- The base-location instance of `wp_assign_store_loc` — the shape every
`x = e` takes. The general form exists because `a[i] = e` stores at a
`Loc.index` whose write lands in the BASE cell (a slice's elements live
in one backing cell): the owned resource and the store target are then
different `Loc`s for the same address, which the base-only statement
could not express. -/
@[go_walk_law]
theorem wp_assign_store {a : Addr} {v : GoValue} {oldcell newcell : HeapCell}
    {rs : List TargetRef} {vals : List GoValue} {body : Stmt}
    {env : LocalEnv} {k}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeLoc σ₁ (.base a) v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗
          WP (Config.next (.storeK rs vals body env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.storeK (.chain (.addr (.base a)) [] [] :: rs)
            (v :: vals) body env k)) @ s ; E {{ Φ }} :=
  wp_assign_store_loc hstore

end

end GoLean.Iris
