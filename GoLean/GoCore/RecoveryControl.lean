import GoLean.GoCore.RecoveryControlData

/-! Structural control invariant. Source admission is defined in the
committed static modules. No constructor contains future safety or evaluation
success. The live state connects to this control through `HeapTyped`. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

mutual
inductive ReturnCont (world : World) (fs : Array Func) : Cont → Prop
  | seq {Γ env ss k} : EnvTyped world Γ env → ControlStmts fs Γ ss →
      ReturnCont world fs k → ReturnCont world fs (.seq ss env k)
  | frame {Γ plans ps tenv results ds k} : EnvTyped world Γ tenv →
      PlansTyped Γ plans ps → ResultRoots world ps results → DefersTyped world fs ds →
      ExitCont world fs k → (plans ≠ [] → ReturnCont world fs k) →
      ReturnCont world fs (.frame plans tenv results ds k false)
inductive ExitCont (world : World) (fs : Array Func) : Cont → Prop
  | stop : ExitCont world fs .stop
  | stmt {k} : ReturnCont world fs k → ExitCont world fs k
  | resume {chain k} : ChainTyped chain → ReturnCont world fs k →
      ExitCont world fs (.panicResumeK chain k)
end

inductive ValueCont (world : World) (fs : Array Func) : ValueKind → Cont → Prop
  | coerce {left right k} : KindLe left right → ValueCont world fs right k →
      ValueCont world fs left k
  | strict {Γ env op doneKinds kind pendingKinds out done pending k} :
      EnvTyped world Γ env → Operator op (doneKinds ++ kind :: pendingKinds) out →
      DeliveryList world doneKinds done.reverse → Expressions Γ pending pendingKinds →
      ValueCont world fs out k →
      ValueCont world fs kind (.strictK op done pending env k)
  | and {Γ env e k} : EnvTyped world Γ env → ExprTyped Γ e .boolean →
      ValueCont world fs (.value .boolean) k →
      ValueCont world fs (.value .boolean) (.andK e env k)
  | or {Γ env e k} : EnvTyped world Γ env → ExprTyped Γ e .boolean →
      ValueCont world fs (.value .boolean) k →
      ValueCont world fs (.value .boolean) (.orK e env k)
  | bool {k} : ValueCont world fs (.value .boolean) k →
      ValueCont world fs (.value .boolean) (.boolK k)
  | branch {Γ env t f k} : EnvTyped world Γ env →
      ControlStmt fs false Γ t → ControlStmt fs false Γ f →
      declarationCount t = 0 → declarationCount f = 0 → ReturnCont world fs k →
      ValueCont world fs (.value .boolean) (.ifK t f env k)
  | target {Γ env p sort before after refs plans rhs vals k} :
      EnvTyped world Γ env → TypeClass p.typ sort → RefsTyped world before refs →
      PlansTyped Γ plans after → AssignmentSource world Γ (before ++ p :: after) rhs vals →
      ReturnCont world fs k →
      ValueCont world fs (.address sort)
        (.tgtOpK (.chain []) [] [] refs plans .vals rhs vals (.seqn #[]) env k)
  | rhs {Γ env p before after refs done pending k} : EnvTyped world Γ env →
      RefsTyped world (before ++ p :: after) refs → ParamsValues world before done.reverse →
      Arguments Γ pending after → ReturnCont world fs k →
      ValueCont world fs (.typed p.typ)
        (.rhsK .vals refs done pending (.seqn #[]) env k)
  | callArgs {Γ env f fid plans before p after done pending k} :
      EnvTyped world Γ env → findFunctionIn? fs fid = some f →
      f.args.toList = before ++ p :: after →
      ParamsValues world before done → Arguments Γ pending after →
      PlansTyped Γ plans f.results.toList → ReturnCont world fs k →
      ValueCont world fs (.typed p.typ) (.callArgsK fid plans done pending env k)
  | callCallee {Γ env f fid caps ps args plans k} :
      EnvTyped world Γ env → findFunctionIn? fs fid = some f →
      f.args.toList = caps ++ ps → Arguments Γ args ps →
      PlansTyped Γ plans f.results.toList → ReturnCont world fs k →
      ValueCont world fs (.closure fid caps) (.callValCalleeK plans args env k)
  | callValueArgs {Γ env f fid caps capValues before p after plans done pending k} :
      EnvTyped world Γ env → findFunctionIn? fs fid = some f →
      f.args.toList = caps ++ (before ++ p :: after) →
      ParamsValues world caps capValues → ParamsValues world before done →
      Arguments Γ pending after → PlansTyped Γ plans f.results.toList →
      ReturnCont world fs k → ValueCont world fs (.typed p.typ)
        (.callValArgsK (.funcVal fid capValues) plans done pending env k)
  | deferCallee {Γ env f fid caps ps args k} :
      EnvTyped world Γ env → findFunctionIn? fs fid = some f →
      f.args.toList = caps ++ ps → Arguments Γ args ps → ReturnCont world fs k →
      ValueCont world fs (.closure fid caps) (.deferCalleeK args env k)
  | deferArgs {Γ env f fid caps capValues before p after done pending k} :
      EnvTyped world Γ env → findFunctionIn? fs fid = some f →
      f.args.toList = caps ++ (before ++ p :: after) →
      ParamsValues world caps capValues → ParamsValues world before done →
      Arguments Γ pending after → ReturnCont world fs k →
      ValueCont world fs (.typed p.typ)
        (.deferArgsK (.funcVal fid capValues) done pending env k)
  | panic {k} : ReturnCont world fs k → ValueCont world fs .boxed (.panicArgK k)

inductive UnwindCont (world : World) (fs : Array Func) : Cont → Prop
  | exit {k} : ExitCont world fs k → UnwindCont world fs k
  | value {kind k} : ValueCont world fs kind k → UnwindCont world fs k

inductive Control (world : World) (fs : Array Func) : Config → Prop
  | next {k} : ExitCont world fs k → Control world fs (.next k)
  /-- Neutral statements may run under an independently typed saved sequence.
  Declaration-exporting statements use the joint `execSeq` constructor. -/
  | execNeutral {Γ env stmt k} : EnvTyped world Γ env →
      ControlStmt fs false Γ stmt → declarationCount stmt = 0 → ReturnCont world fs k →
      Control world fs (.exec stmt env k)
  | execFrame {Γ env stmt plans tenv results ds k} : EnvTyped world Γ env →
      ControlStmt fs false Γ stmt →
      ReturnCont world fs (.frame plans tenv results ds k false) →
      Control world fs (.exec stmt env (.frame plans tenv results ds k false))
  | execSeq {Γ env stmt rest k} : EnvTyped world Γ env → ControlStmt fs true Γ stmt →
      ControlStmts fs (afterStmt Γ stmt) rest → ReturnCont world fs k →
      Control world fs (.exec stmt env (.seq rest env k))
  | eval {Γ env e kind k} : EnvTyped world Γ env → Expression Γ e kind →
      ValueCont world fs kind k → Control world fs (.evalE e env k)
  | ret {kind v k} : Delivered world kind v → ValueCont world fs kind k →
      Control world fs (.retV v k)
  | store {env ps refs vs k} : BindingsTyped world env → RefsTyped world ps refs →
      ParamsValues world ps vs → ReturnCont world fs k →
      Control world fs (.next (.storeK refs vs (.seqn #[]) env k))
  | returning {k} : ReturnCont world fs k → Control world fs (.signal .ret k)
  | panicking {chain k} : ChainTyped chain → UnwindCont world fs k →
      Control world fs (.panicking chain k)

theorem ReturnCont.not_stop {world fs} : ¬ ReturnCont world fs .stop := by
  intro h
  cases h

theorem Control.not_return_stop {world fs} : ¬ Control world fs (.signal .ret .stop) := by
  intro h
  cases h with
  | returning h => exact h.not_stop

theorem Control.initialization_environment {world fs p env rest env' k}
    (h : Control world fs (.exec (.initialization p) env (.seq rest env' k))) : env = env' := by
  cases h with
  | execNeutral _ hs _ _ => cases hs
  | execSeq => rfl

theorem Control.initialization_not_frame {world fs p env plans tenv results ds k} :
    ¬ Control world fs (.exec (.initialization p) env (.frame plans tenv results ds k false)) := by
  intro h
  cases h with
  | execNeutral _ hs _ _ => cases hs
  | execFrame _ hs _ => cases hs

end GoLean.GoCore.RecoveryRuntime
