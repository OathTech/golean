import GoLeanIris.Lifting

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

theorem loadLoc_cell {state : ExecState} {a : Nat} {ty : Ty} {v : GoValue}
    (h : state.heap[a]? = some (.value ty v)) :
    loadLoc state (.base ⟨a⟩) = .ok v := by
  simp [loadLoc, Heap.lookup, h]

theorem storeLoc_cell {state : ExecState} {a : Nat} {ty : Ty} {old v v' : GoValue}
    (h : state.heap[a]? = some (.value ty old))
    (hv : normalizeValueForTy state ty v = .ok v') :
    storeLoc state (.base ⟨a⟩) v = .ok
      {state with heap := state.heap.set a (.value ty v') (Array.getElem?_eq_some_iff.mp h).1} := by
  obtain ⟨ha, hcell⟩ := Array.getElem?_eq_some_iff.mp h
  simp [storeLoc, ExecState.updateCell, ha, hcell, hv, Bind.bind, Except.bind]

section
variable {GF : BundledGFunctors} [GoGS GF]
variable {E : CoPset} {Φ : Unit → IProp GF}

/-- Direct recovery across an assignment and its statement sequence. The
non-wrapper deferred frame and suspended panic are explicit premises of the
configuration, and the conclusion marks that very panic as recovered. -/
theorem wp_recover_assignment {rop : RhsOp} {refs : List TargetRef}
    {done : List GoValue} {pending : List Expr} {body : Stmt} {env eenv : LocalEnv}
    {rest : List Stmt} {kenv : LocalEnv} {targets : List (TargetShape × List Expr)}
    {targetEnv : LocalEnv} {results : List Loc} {defers : List (GoValue × List GoValue)}
    {v : GoValue} {k : Cont} :
    (▷ WP (Config.retV v (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results defers (.panicResumeK [⟨v, true⟩] k) false))))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results defers (.panicResumeK [⟨v, false⟩] k) false))))
        @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  rw [GateA1.recover_stepFn]
  unfold recoverResult
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_act (by rfl)]
  dsimp only
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  rfl

theorem wp_initialize {p : Param} {env : LocalEnv} {rest : List Stmt} {k : Cont}
    {v : GoValue} (hv : ∀ state, ContextEq state (GoGS.context GF) →
      defaultValue state p.typ = .ok v) :
    (▷ ∀ a : Nat, a ↦ (.value p.typ v) -∗
      WP (Config.next (.seq rest (env.declare p.id (.base ⟨a⟩)) k))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.exec (.initialization p) env (.seq rest env k))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_alloc_step _ rfl
  intro state hc choices
  simp [stepFn, hv state hc, ExecState.alloc, ExecState.allocCell, Bind.bind, Except.bind]

theorem wp_neq_interface_nil {id : TypeId} {dynTy : Ty} {v : GoValue}
    {env : LocalEnv} {k : Cont} :
    (▷ WP (Config.retV (.bool true) k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.retV .nil (.strictK (.neqCmp (.interface id)) [.interface dynTy v] [] env k))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  have he : valueEq state (.interface id) (.interface dynTy v) .nil = .ok false := by
    rw [valueEq.eq_def]
    simp [TypeEnv.resolve, Pure.pure, Except.pure]
  simp [stepFn, applyStrictOp, he, toResult, deliverS, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem wp_load_var {name : String} {env : LocalEnv} {k : Cont}
    {a : Nat} {ty : Ty} {v : GoValue} {dq : DFrac}
    (hvar : env.lookup name = some (.base ⟨a⟩)) :
    (a ↦{dq} (.value ty v) ∗
      ▷ (a ↦{dq} (.value ty v) -∗ WP (Config.retV v k) @ Stuckness.NotStuck; E {{ Φ }})) ⊢
      WP (Config.evalE (.var name) env k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_read_step rfl
  intro state _ hlook choices
  simp [stepFn, hvar, loadLoc_cell hlook, Bind.bind, Except.bind]

theorem wp_store_cell {a : Nat} {ty : Ty} {old v v' : GoValue}
    {refs : List TargetRef} {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hv : ∀ state, ContextEq state (GoGS.context GF) →
      normalizeValueForTy state ty v = .ok v') :
    (a ↦ (.value ty old) ∗
      ▷ (a ↦ (.value ty v') -∗ WP (Config.next (.storeK refs vals body env k))
        @ Stuckness.NotStuck; E {{ Φ }})) ⊢
      WP (Config.next (.storeK (.chain (.addr (.base ⟨a⟩)) [] [] :: refs)
        (v :: vals) body env k)) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_write_step rfl
  intro state hc hlook choices
  simp [stepFn, storeTarget, resolveChain, valueAsLoc, storeLoc_cell hlook (hv state hc),
    toResult, deliverS, Bind.bind, Except.bind]

/-- Consequence and frame are the ordinary Iris laws at the actual machine
configuration; they do not assert that adding a Go continuation is inert. -/
theorem wp_consequence {c : Config} {Ψ : Unit → IProp GF} :
    (WP c @ Stuckness.NotStuck; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v)) ⊢
      WP c @ Stuckness.NotStuck; E {{ Ψ }} := by
  iintro ⟨Hwp, Hwand⟩
  iapply wp_wand $$ Hwp Hwand

theorem wp_frame {c : Config} (R : IProp GF) :
    (WP c @ Stuckness.NotStuck; E {{ Φ }} ∗ R) ⊢
      WP c @ Stuckness.NotStuck; E {{ v, Φ v ∗ R }} := by
  iintro ⟨Hwp, HR⟩
  iapply wp_wand $$ Hwp
  iintro %v HΦ
  iframe

end
end GoLean.IrisCustomer
