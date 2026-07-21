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
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions

/-!
# Call/frame laws + witnesses
Frame entry (unary arg; nullary-arg/unary-result) with fresh-cell handover;
value-returning frame exit.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The unary void call law.** General over the function, argument
expression, and continuation; arity-specialized to the slice's shape (one
parameter, no results — `inc`). Premises: the function is in the pinned
program; the argument evaluates (state-independently, e.g. `&x`) to `v`, which
normalizes at the parameter type to `v'`. The continuation runs the body in
the fresh one-binding frame env, owning the freshly allocated parameter cell,
under the `.frame` continuation. Arity-generality (parameter *lists*) is a
tracked widening, not a semantic limitation. -/
theorem wp_call_unary {funcId : FuncId} {func : Func} {pid : String} {pty : Ty}
    {body : Stmt} {argExpr : Expr} {v v' : GoValue} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) funcId = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hbody : func.body = body)
    (harg : ∀ σ₁ : ExecState, ExprR env σ₁ argExpr (.value v σ₁))
    (harg_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ argExpr out → out = .value v σ₁)
    (hnorm : ∀ σ₁ : ExecState, normalizeValueForTy σ₁ pty v = .ok v') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v'⟩ : HeapCell) -∗
        WP (Config.exec body [[(pid, Loc.base pa)]]
              (.frame [] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[] funcId #[argExpr]) env k) @ s ; E {{ Φ }} := by
  obtain ⟨fid, fargs, fres, fbody⟩ := func
  simp only at hargs hres hbody
  subst hargs; subst hres; subst hbody
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  have hstep : Step (.exec (.call #[] funcId #[argExpr]) env k) σ₁
      (.exec fbody [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] (.frame [] [] k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.call AssigneesR.nil (ArgsR.cons (harg σ₁) ArgsR.nil)
      (by rw [hfns]; exact hfind)
      (BindParamsR.cons (hnorm σ₁) (ExecState.alloc_eq σ₁ v' (some pty))
        BindParamsR.nil)
      DeclsR.nil LookupsR.nil
  have hdet : ∀ c' s',
      Step (.exec (.call #[] funcId #[argExpr]) env k) σ₁ c' s' →
      c' = Config.exec fbody [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] (.frame [] [] k) ∧
      s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩,
                     nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    cases hst with
    | call hass hargsR hfindR hbind hdecls hlk =>
      cases hass
      cases hargsR with
      | cons hE hrest =>
        have hd := harg_det σ₁ _ hE
        injection hd with hv hs0
        rw [hs0] at hrest
        cases hrest
        rw [hfns, hfind] at hfindR
        injection hfindR with hfunc
        subst hfunc
        rw [hv] at hbind
        cases hbind with
        | cons hn' ha' hrest' =>
          rw [hnorm σ₁] at hn'
          injection hn' with hv'
          rw [← hv', ExecState.alloc_eq] at ha'
          injection ha' with hloc hst'
          rw [← hloc, ← hst'] at hrest'
          cases hrest'
          cases hdecls
          cases hlk
          exact ⟨rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hstep⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some pty, v'⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- **The nullary-arg, unary-result call law** (`main`'s entry shape): zero
arguments, one named result — the result cell is allocated at its default
value by the `DeclsR` leg of `Step.call` (the results-allocation fix) and
handed fresh to the continuation. The caller's target resolves in the caller
env; its cell is stored only at frame RETURN, so no target ownership is needed
at entry. -/
theorem wp_call_nullary_ret {funcId : FuncId} {func : Func} {rname : String}
    {rty : Ty} {body : Stmt} {v : GoValue} {tgt : String} {ta : Addr} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) funcId = some func)
    (hargs : func.args = #[])
    (hres : func.results = #[⟨rname, rty⟩])
    (hbody : func.body = body)
    (hres_t : LocalEnv.lookup env tgt = some (.base ta))
    (hdef : ∀ σ₁ : ExecState, defaultValue σ₁ rty = .ok v) :
    iprop(∀ ra : Addr, ra.id ↦ (⟨some rty, v⟩ : HeapCell) -∗
        WP (Config.exec body [[(rname, Loc.base ra)]]
              (.frame [Loc.base ta] [Loc.base ra] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var tgt] funcId #[]) env k) @ s ; E {{ Φ }} := by
  obtain ⟨fid, fargs, fres, fbody⟩ := func
  simp only at hargs hres hbody
  subst hargs; subst hres; subst hbody
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  have hlkp : LocalEnv.lookup
      (LocalEnv.declare [] rname (Loc.base ⟨σ₁.nextAddr⟩)) rname
      = some (Loc.base ⟨σ₁.nextAddr⟩) := by
    simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
  have hstep : Step (.exec (.call #[.var tgt] funcId #[]) env k) σ₁
      (.exec fbody [[(rname, Loc.base ⟨σ₁.nextAddr⟩)]]
        (.frame [Loc.base ta] [Loc.base ⟨σ₁.nextAddr⟩] k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, v⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.call (AssigneesR.cons (AssigneeR.var hres_t) AssigneesR.nil) ArgsR.nil
      (by rw [hfns]; exact hfind)
      BindParamsR.nil
      (DeclsR.cons (hdef σ₁) (ExecState.alloc_eq σ₁ v (some rty)) DeclsR.nil)
      (LookupsR.cons hlkp LookupsR.nil)
  have hdet : ∀ c' s',
      Step (.exec (.call #[.var tgt] funcId #[]) env k) σ₁ c' s' →
      c' = Config.exec fbody [[(rname, Loc.base ⟨σ₁.nextAddr⟩)]]
             (.frame [Loc.base ta] [Loc.base ⟨σ₁.nextAddr⟩] k) ∧
      s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, v⟩,
                     nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    cases hst with
    | call hass hargsR hfindR hbind hdecls hlk =>
      cases hass with
      | cons hA hrestA =>
        cases hA with
        | var hl =>
          rw [hres_t] at hl
          injection hl with hloc
          cases hrestA
          cases hargsR
          rw [hfns, hfind] at hfindR
          injection hfindR with hfunc
          subst hfunc
          cases hbind
          cases hdecls with
          | cons hd ha hrest =>
            rw [hdef σ₁] at hd
            injection hd with hv
            rw [← hv, ExecState.alloc_eq] at ha
            injection ha with hloc2 hst'
            rw [← hloc2, ← hst'] at hrest
            cases hrest
            cases hlk with
            | cons hlk1 hlkrest =>
              cases hlkrest
              have hlkloc := hlk1
              rw [show LocalEnv.declare [] rname (Loc.base ⟨σ₁.nextAddr⟩)
                  = [[(rname, Loc.base ⟨σ₁.nextAddr⟩)]] from rfl] at hlkloc ⊢
              simp [LocalEnv.lookup, Scope.lookup] at hlkloc
              rw [← hloc, ← hlkloc]
              exact ⟨rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hstep⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some rty, v⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- **The value-returning frame exit.** `return` reaches the frame; the
result cell — whose *location* was pinned at call time (D2-proper) — is read
from its owned cell and stored to the caller's target cell. Premises
conditioned on the two owned cells, via the two-cell core (result cell read,
target written). No environment resolution: the env-free `.returning` and
the location-carrying frame make the read unambiguous under any shadowing.
Arity-specialized to one result/one target, like `wp_call_unary`. Witness:
`wp_frame_return_int`. -/
theorem wp_frame_return {ra ta : Addr} {rcell tcell newtcell : HeapCell} {k}
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base ta) = some tcell →
        storeLoc σ₁ (.base ta) rcell.value
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) :
    ra.id ↦ rcell ∗ ta.id ↦ tcell
      ∗ (ra.id ↦ rcell ∗ ta.id ↦ newtcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [.base ta] [.base ra] k))
          @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base ra) = some rcell →
      Heap.lookup σ₁.heap (.base ta) = some tcell →
      Step (Config.returning (.frame [.base ta] [.base ra] k)) σ₁
        (.next k) { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell } ∧
      (∀ c' s',
        Step (Config.returning (.frame [.base ta] [.base ra] k)) σ₁ c' s' →
        c' = Config.next k ∧
        s' = { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) := by
    intro σ₁ hlr hlt
    refine ⟨Step.frameReturn
      (LoadsR.cons (loadLoc_base_of_lookup hlr) LoadsR.nil)
      (StoreManyR.cons (hstore σ₁ hlt) StoreManyR.nil), ?_⟩
    intro c' s' hst
    cases hst with
    | frameReturn hresR hstoreR =>
      cases hresR with
      | cons hload hrest =>
        rw [loadLoc_base_of_lookup hlr] at hload
        injection hload with hval
        cases hrest
        rw [← hval] at hstoreR
        cases hstoreR with
        | cons hst1 hrest2 =>
          rw [hstore σ₁ hlt] at hst1
          injection hst1 with hs1
          rw [← hs1] at hrest2
          cases hrest2
          exact ⟨rfl, rfl⟩
  exact wp_store_step₂ rfl hred

/-- Witness for `wp_frame_return`: an int result local (holding a normalized
`n`, ∀-general) returned into an int target cell (any prior value `w`).
Zero premises beyond the owned cells (D2-proper erased the env-resolution
premise). -/
theorem wp_frame_return_int {ra ta : Addr} {kind : IntKind} {n : Int}
    {w : GoValue} {k} :
    ra.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [.base ta] [.base ra] k))
          @ s ; E {{ Φ }} :=
  wp_frame_return (fun σ₁ hlt => storeLoc_int_cell hlt n)

end

end GoLean.Iris
