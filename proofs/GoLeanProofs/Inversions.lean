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
import GoLeanProofs.HeapBridge

/-!
# Deterministic-evaluation inversion lemmas
`ExprR` determinism facts (conditioned on env/cells) and `IntKind` reflexivity —
pure lemmas shared by the law files' determinism proofs.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

/-- **Deref-load as an `ExprR` fact.** If `aexpr` resolves to `.addr (.base a)`
(state unchanged) and the cell at `a` holds `cell`, then `*aexpr` evaluates to
`cell.value`. This is the expression-level building block for a non-literal
right-hand side such as `*p` (and, composed with `ExprR.addInt`, `*p + 1`). Pure
relational fact — no separation logic here; heap *ownership* enters only where
this feeds a WP premise, via `pointsTo_loadLoc` turning `↦` into the `hcell`
hypothesis. -/
theorem exprR_deref_load {env : LocalEnv} {σ : ExecState} {aexpr : Expr} {ty : Ty}
    {a : Addr} {cell : HeapCell}
    (haddr : ExprR env σ aexpr (.value (.addr (.base a)) σ))
    (hcell : Heap.lookup σ.heap (.base a) = some cell) :
    ExprR env σ (.deref aexpr ty) (.value cell.value σ) :=
  ExprR.deref haddr (loadLoc_base_of_lookup hcell)

/-- Inversion of `ExprR` on an integer literal: it evaluates only to its
normalized value, leaving the state unchanged. The `binPanic*` rules carry a
function-valued `mk` index, so plain `cases` punts (higher-order unification) —
`generalize` the literal to a variable first, then each spurious case is refuted
by `Expr.noConfusion` (after fixing `mk` from its disjunction). -/
theorem exprR_intLit_det {env : LocalEnv} {σ : ExecState} {n : Int}
    {kind : IntKind} {out : ExprOut}
    (h : ExprR env σ (.intLit n kind) out) :
    out = ExprOut.value (.int (kind.normalize n) kind) σ := by
  generalize he : Expr.intLit n kind = e at h
  cases h with
  | intLit => injection he with e1 e2; subst e1; subst e2; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `.ref id` (address-of a variable): it evaluates only
to the address of `id`'s location (state unchanged). Same `generalize`-past-the
function-valued `binPanic*` indices shape as `exprR_intLit_det`. -/
theorem exprR_ref_det {env : LocalEnv} {σ : ExecState} {id : String}
    {loc : Loc} {out : ExprOut} (hlk : LocalEnv.lookup env id = some loc)
    (h : ExprR env σ (.ref id) out) :
    out = ExprOut.value (.addr loc) σ := by
  generalize he : Expr.ref id = e at h
  cases h with
  | ref hl =>
      injection he with hid; subst hid
      rw [hlk] at hl; injection hl with hl'; subst hl'; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `.var p`, conditioned on the resolution and load
facts: it evaluates only to the loaded value, state unchanged. -/
theorem exprR_var_det {env : LocalEnv} {σ : ExecState} {p : String}
    {loc : Loc} {val : GoValue} {out : ExprOut}
    (hl : LocalEnv.lookup env p = some loc)
    (hv : loadLoc σ loc = .ok val)
    (h : ExprR env σ (.var p) out) : out = .value val σ := by
  generalize he : Expr.var p = e at h
  cases h with
  | var hl' hv' =>
      injection he with hp; subst hp
      rw [hl] at hl'; injection hl' with hloc; subst hloc
      rw [hv] at hv'; injection hv' with hval; subst hval; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `*p` (deref of a variable), conditioned on `p`'s
resolution and both cells: it evaluates only to the target cell's value. -/
theorem exprR_deref_var_det {env : LocalEnv} {σ : ExecState} {p : String}
    {ty : Ty} {pa a : Addr} {pcell acell : HeapCell} {out : ExprOut}
    (hl : LocalEnv.lookup env p = some (.base pa))
    (hp : Heap.lookup σ.heap (.base pa) = some pcell)
    (hpv : pcell.value = .addr (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some acell)
    (h : ExprR env σ (.deref (.var p) ty) out) : out = .value acell.value σ := by
  have hloadp : loadLoc σ (.base pa) = .ok (.addr (.base a)) := by
    rw [loadLoc_base_of_lookup hp, hpv]
  generalize he : Expr.deref (.var p) ty = e at h
  cases h with
  | deref haddr hload =>
      injection he with h1 h2; subst h1; subst h2
      have hd := exprR_var_det hl hloadp haddr
      injection hd with hav hs1
      injection hav with hloc
      subst hs1; subst hloc
      rw [loadLoc_base_of_lookup ha] at hload
      injection hload with hval; subst hval
      rfl
  | derefNil haddr =>
      injection he with h1 h2; subst h1
      have hd := exprR_var_det hl hloadp haddr
      injection hd with hav _
      exact GoValue.noConfusion hav
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | derefPanic hpanic =>
      injection he with h1 h2
      subst h1
      have hd := exprR_var_det hl hloadp hpanic
      exact ExprOut.noConfusion hd
  | _ => exact Expr.noConfusion he

/-- `k == k` for the derived `BEq IntKind` (constant constructors by `decide`;
`unbounded` reduces to `String` beq-reflexivity). -/
theorem intKind_beq_self (k : IntKind) : (k == k) = true := by
  cases k
  case unbounded name => exact beq_self_eq_true (a := name)
  all_goals decide

/-- `compatibleResult` on equal kinds is that kind. -/
theorem intKind_compatibleResult_self (k : IntKind) :
    IntKind.compatibleResult k k = some k := by
  simp [IntKind.compatibleResult, intKind_beq_self]

/-- Inversion of `ExprR` on `*p + lit`, conditioned on the cells: it evaluates
only to the normalized sum. The composite determinism fact behind the
`*p = *p + 1` witness. -/
theorem exprR_inc_det {env : LocalEnv} {σ : ExecState} {p : String}
    {ty : Ty} {pa a : Addr} {pcell : HeapCell} {kind : IntKind} {m lit : Int}
    {out : ExprOut}
    (hl : LocalEnv.lookup env p = some (.base pa))
    (hp : Heap.lookup σ.heap (.base pa) = some pcell)
    (hpv : pcell.value = .addr (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), .int m kind⟩)
    (h : ExprR env σ (.add (.deref (.var p) ty) (.intLit lit kind)) out) :
    out = .value (.int (kind.normalize (m + kind.normalize lit)) kind) σ := by
  generalize he : Expr.add (.deref (.var p) ty) (.intLit lit kind) = e at h
  cases h with
  | addInt hle hre hk =>
      injection he with h1 h2; subst h1; subst h2
      have hld := exprR_deref_var_det hl hp hpv ha hle
      injection hld with hlv hs1
      injection hlv with hm hkl
      have hrd := exprR_intLit_det (hs1 ▸ hre)
      injection hrd with hrv hs2
      injection hrv with hn hkr
      subst hkl; subst hkr
      rw [intKind_compatibleResult_self] at hk
      injection hk with hkk
      subst hkk; subst hm; subst hn; subst hs2
      rfl
  | binPanicLeft mk hmk hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1
      exact ExprOut.noConfusion (exprR_deref_var_det hl hp hpv ha hpanic)
  | binPanicRight mk hmk hval hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1; subst h2
      have hd := exprR_deref_var_det hl hp hpv ha hval
      injection hd with _ hs1
      exact ExprOut.noConfusion (exprR_intLit_det (hs1 ▸ hpanic))
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `x + lit` (variable plus int literal),
conditioned on `x`'s int cell: it evaluates only to the normalized sum.
The var twin of `exprR_inc_det` (arc E rung B1: the loop witness body
`x = x + 1`). -/
theorem exprR_var_add_lit_det {env : LocalEnv} {σ : ExecState} {x : String}
    {a : Addr} {kind : IntKind} {m lit : Int} {out : ExprOut}
    (hl : LocalEnv.lookup env x = some (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), .int m kind⟩)
    (h : ExprR env σ (.add (.var x) (.intLit lit kind)) out) :
    out = .value (.int (kind.normalize (m + kind.normalize lit)) kind) σ := by
  generalize he : Expr.add (.var x) (.intLit lit kind) = e at h
  cases h with
  | addInt hle hre hk =>
      injection he with h1 h2; subst h1; subst h2
      have hld := exprR_var_det hl (loadLoc_base_of_lookup ha) hle
      injection hld with hlv hs1
      injection hlv with hm hkl
      have hrd := exprR_intLit_det (hs1 ▸ hre)
      injection hrd with hrv hs2
      injection hrv with hn hkr
      subst hkl; subst hkr
      rw [intKind_compatibleResult_self] at hk
      injection hk with hkk
      subst hkk; subst hm; subst hn; subst hs2
      rfl
  | binPanicLeft mk hmk hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1
      exact ExprOut.noConfusion
        (exprR_var_det hl (loadLoc_base_of_lookup ha) hpanic)
  | binPanicRight mk hmk hval hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1; subst h2
      have hd := exprR_var_det hl (loadLoc_base_of_lookup ha) hval
      injection hd with _ hs1
      exact ExprOut.noConfusion (exprR_intLit_det (hs1 ▸ hpanic))
  | _ => exact Expr.noConfusion he

/-- `x == z` (int-typed equality of a variable against an int literal)
evaluates to the boolean `m == kind.normalize z`, state unchanged —
forward direction, conditioned on `x`'s int cell. The `valueEq` premise
reduces definitionally on the int/int case (fuel- and state-blind). -/
theorem exprR_var_eq_lit {env : LocalEnv} {σ : ExecState} {x : String}
    {a : Addr} {kind : IntKind} {m z : Int}
    (hl : LocalEnv.lookup env x = some (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), .int m kind⟩) :
    ExprR env σ (.eqCmp (.int kind) (.var x) (.intLit z kind))
      (.value (.bool (m == kind.normalize z)) σ) :=
  ExprR.eqCmp (ExprR.var hl (loadLoc_base_of_lookup ha)) ExprR.intLit
    (by simp only [valueEq, valueEqFuel]; rfl)

/-- Inversion of `ExprR` on `x == z`, conditioned on `x`'s int cell: it
evaluates only to the boolean `m == kind.normalize z`, state unchanged. -/
theorem exprR_var_eq_lit_det {env : LocalEnv} {σ : ExecState} {x : String}
    {a : Addr} {kind : IntKind} {m z : Int} {out : ExprOut}
    (hl : LocalEnv.lookup env x = some (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), .int m kind⟩)
    (h : ExprR env σ (.eqCmp (.int kind) (.var x) (.intLit z kind)) out) :
    out = .value (.bool (m == kind.normalize z)) σ := by
  generalize he : Expr.eqCmp (.int kind) (.var x) (.intLit z kind) = e at h
  cases h with
  | eqCmp hle hre hveq =>
      injection he with h0 h1 h2; subst h0; subst h1; subst h2
      have hld := exprR_var_det hl (loadLoc_base_of_lookup ha) hle
      injection hld with hlv hs1
      subst hlv
      have hrd := exprR_intLit_det (hs1 ▸ hre)
      injection hrd with hrv hs2
      subst hrv
      rw [show valueEq _ (.int kind) (GoValue.int m kind)
          (.int (kind.normalize z) kind) = .ok (m == kind.normalize z)
        from by simp only [valueEq, valueEqFuel]; rfl] at hveq
      injection hveq with hb
      subst hb; subst hs2; rfl
  | eqPanicLeft hpanic =>
      injection he with h0 h1 h2; subst h1
      exact ExprOut.noConfusion
        (exprR_var_det hl (loadLoc_base_of_lookup ha) hpanic)
  | eqPanicRight hval hpanic =>
      injection he with h0 h1 h2; subst h1; subst h2
      have hd := exprR_var_det hl (loadLoc_base_of_lookup ha) hval
      injection hd with _ hs1
      exact ExprOut.noConfusion (exprR_intLit_det (hs1 ▸ hpanic))
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

end GoLean.Iris
