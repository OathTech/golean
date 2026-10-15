import PhaseAcceptance

/-! Original actual-caller theorem headers, with only the three proved law
parameters discharged. Assembly remains outside the caller proof. -/
namespace PhaseAcceptance
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational
open GoLean.Logic GoLean.Logic.ProgramExecution GoLean.IrisCustomer
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open RelationalCodeX.ObservedCaller
noncomputable section
variable {ctx : ProgramCtx}
  (calleeLookup : findFunctionIn? ctx.functions identityFunction.id = some identityFunction)
  (calleeMethod : methodInfoByFuncId? ctx identityFunction.id = none)
  (callerLookup : findFunctionIn? ctx.functions callerFunction.id = some callerFunction)
  (callerMethod : methodInfoByFuncId? ctx callerFunction.id = none)

include calleeLookup calleeMethod callerLookup callerMethod

theorem hist_code {GF : BundledGFunctors} [GoGSO GF observer] :
    let M := model ctx GF
    M.Entails (M.persistently (M.emp : M.Assertion 0 0))
      (HistContract M (.funcVal callerFunction.id []) [.boolean] [.boolean]
        (fun v : Bool => [GoValue.bool v]) result (fun _ _ _ _ => False)) := by
  exact RelationalCodeX.ObservedCaller.hist_code assignment entry delivery calleeLookup calleeMethod callerLookup callerMethod

theorem adequate (v : Bool) :
    let D := definition ctx callerFunction callerLookup callerMethod rfl rfl rfl
    Safe.HistAdequate
      (Safe.ExprAt.run (ctx := ctx) (O := observer) (m := .main) (initialConfig D))
      (initialState D [GoValue.bool v], [])
      (EntryOutcomeState D {} (result v)
        (fun p vs hist => StringPanicH (fun _ _ _ => False) p vs hist)) := by
  exact RelationalCodeX.ObservedCaller.adequate assignment entry delivery calleeLookup calleeMethod callerLookup callerMethod v

theorem caller_prefix (plain : Safe.StringPlain ctx) (v : Bool) (n : Nat) (choices : Choices)
    {ls : List StepLabel} {cf : Config} {sf : Store} {chf : Choices}
    (hp : let D := definition ctx callerFunction callerLookup callerMethod rfl rfl rfl
      ExecutionStatement.Prefix ctx n (initialState D [GoValue.bool v]) (initialConfig D) choices ls sf cf chf) :
    let D := definition ctx callerFunction callerLookup callerMethod rfl rfl rfl
    observer.Inv (Safe.Obs ctx observer.obs (initialState D [GoValue.bool v]) (initialConfig D) choices ls) := by
  exact RelationalCodeX.ObservedCaller.caller_prefix assignment entry delivery calleeLookup calleeMethod callerLookup callerMethod plain v n choices hp

theorem outcomes (plain : Safe.StringPlain ctx)
    (globals : ctx.program.globals = #[])
    (initializer : findFunctionIn? ctx.functions pkgInitFuncId = none)
    (reserved : ctx.program.typeDefs.hasReservedPrefix = true)
    (v : Bool) (fuel : Nat) (choices : Choices) :
    let D := definition ctx callerFunction callerLookup callerMethod rfl rfl rfl
    runProgramM fuel ctx.program D.fid.key (D.captures.val ++ [GoValue.bool v]).toArray choices = .error .fuelOut ∨
      (∃ out, runProgramM fuel ctx.program D.fid.key (D.captures.val ++ [GoValue.bool v]).toArray choices = .ok out ∧
        Procedure.ValuesTyped [Source.ScalarTy.boolean] out.values.toList ∧ out.output = .empty ∧
        ∃ ls sf chf, Safe.NormalRun ctx fuel (initialState D [GoValue.bool v]) (initialConfig D) choices ls sf chf ∧
          loadMany ctx sf (Frame.roots D.arguments.length D.results.length) = .ok out.values.toList ∧
          result v out.values.toList (Safe.Obs ctx observer.obs (initialState D [GoValue.bool v]) (initialConfig D) choices ls)) ∨
      (∃ first rest text, runProgramM fuel ctx.program D.fid.key (D.captures.val ++ [GoValue.bool v]).toArray choices =
          .error (.panic text) ∧
        ∃ ls sf, Safe.AbortRun ctx fuel (initialState D [GoValue.bool v]) (initialConfig D) choices first rest text ls sf ∧
          PanicStateH D (fun _ _ (_ : List Event) => False) first rest text sf
            (Safe.Obs ctx observer.obs (initialState D [GoValue.bool v]) (initialConfig D) choices ls)) := by
  exact RelationalCodeX.ObservedCaller.outcomes assignment entry delivery calleeLookup calleeMethod callerLookup callerMethod plain globals initializer reserved v fuel choices

end
end PhaseAcceptance
