import GoLeanIris.Allocation
import GoLean.Interface

/-! The adapter inventories all seven actual frame-entry shapes. The one
allocation rule is shared by ordinary calls, known closures and both defer
drain paths; callee proofs receive explicit continuations. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryTyping GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

inductive CallSite (fid : FuncId) :
    List GoValue → Config → (List Loc → Bool → Cont) → Prop where
  | direct {targets plans env k} (hplans : targetsPlan targets.toList = some plans) :
      CallSite fid [] (.exec (.call targets fid #[]) env k)
        (fun roots w => .frame plans env roots [] k w)
  | arguments {done v plans env k} :
      CallSite fid (done ++ [v]) (.retV v (.callArgsK fid plans done [] env k))
        (fun roots w => .frame plans env roots [] k w)
  | closure {caps plans env k} :
      CallSite fid caps (.retV (.funcVal fid caps) (.callValCalleeK plans [] env k))
        (fun roots w => .frame plans env roots [] k w)
  | closureArguments {caps done v plans env k} :
      CallSite fid (caps ++ done ++ [v])
        (.retV v (.callValArgsK (.funcVal fid caps) plans done [] env k))
        (fun roots w => .frame plans env roots [] k w)
  | deferFall {caps args plans env roots ds k w} :
      CallSite fid (caps ++ args)
        (.next (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ innerW => .frame [] [] [] [] (.frame plans env roots ds k w) innerW)
  | deferReturn {caps args plans env roots ds k w} :
      CallSite fid (caps ++ args)
        (.signal .ret (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ innerW => .frame [] [] [] [] (.frame plans env roots ds k w) innerW)
  | deferPanic {caps args plans env roots ds k w chain} :
      CallSite fid (caps ++ args)
        (.panicking chain (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ innerW => .frame [] [] [] []
          (.panicResumeK chain (.frame plans env roots ds k w)) innerW)

theorem CallSite.not_value {fid args c frame} (site : CallSite fid args c frame) :
    ToVal.toVal c = (none : Option Unit) := by cases site <;> rfl

theorem CallSite.step {fid args c frame} (site : CallSite fid args c frame)
    {s f env roots t ch}
    (entry : enterFramePick s fid args ch = .ok (.ok (f, env, roots, t), ch)) :
    stepFn s c ch = .ok (.exec f.body env (frame roots f.wrapper), t, ch) := by
  cases site <;>
    simp_all only [stepFn, stepFrameExit, signalStep,
      deliverS, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ContextEq.sameContext {s context : ExecState} (hc : ContextEq s context) :
    BooleanRuntime.SameContext context s := by
  unfold ContextEq at hc
  rw [hc]
  rfl

section
variable {GF : BundledGFunctors} [GoGS GF]
variable {E : CoPset} {Φ : Unit → IProp GF}

/-- The callee receives ownership of fresh parameter/result slots. Existing
pointee ownership can be framed through this rule, and is never manufactured
by the pure argument schema or by capture-address copying. -/
theorem wp_call {p : Program} {world fid f args zeros c frame}
    (hp : ProgramTyped p)
    (hctx : BooleanRuntime.SameContext (BooleanRuntime.programState p) (GoGS.context GF))
    (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args)
    (zeroValues : ZeroValues f.results.toList zeros)
    (site : CallSite fid args c frame) :
    (▷ ∀ base : Nat, ownsCells base (callCells f args zeros) -∗
      WP (Config.exec f.body (callEnv f base) (frame (callResults f base) f.wrapper))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_alloc_cells_step _ site.not_value
  intro state hc choices
  exact site.step (enterFramePick_layout hp (hctx.trans hc.sameContext) hf values zeroValues choices)

end
end GoLean.IrisCustomer
