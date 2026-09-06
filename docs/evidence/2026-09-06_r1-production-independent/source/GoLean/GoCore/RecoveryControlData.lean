import GoLean.GoCore.RecoveryDelivery
import GoLean.GoCore.RecoveryResultRoots
import GoLean.GoCore.RecoveryControlTyping

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

inductive Expression (Γ : Context) : Expr → ValueKind → Prop
  | value {e sort} : ExprTyped Γ e sort → Expression Γ e (.value sort)
  | typed {e ty} : ExprAt Γ e ty → Expression Γ e (.typed ty)
  | addressRef {name sort} : Has Γ name sort →
      Expression Γ (.ref name) (.address sort)
  | addressExpr {e} : ExprTyped Γ e .root → Expression Γ e (.address .boolean)
  | boxed {e} : PanicArgument Γ e → Expression Γ e .boxed
  | closure {fid caps ps} : Arguments Γ caps.toList ps →
      Expression Γ (.funcVal fid caps) (.closure fid ps)

inductive Expressions (Γ : Context) : List Expr → List ValueKind → Prop
  | nil : Expressions Γ [] []
  | cons {e es kind kinds} : Expression Γ e kind → Expressions Γ es kinds →
      Expressions Γ (e :: es) (kind :: kinds)

theorem Expressions.arguments {Γ es ps} (h : Arguments Γ es ps) :
    Expressions Γ es (ps.map (fun p => .typed p.typ)) := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (.typed he) ih

inductive PlanTyped (Γ : Context) : (TargetShape × List Expr) → Ty → Prop
  | root {e sort ty} : TypeClass ty sort → Expression Γ e (.address sort) →
      PlanTyped Γ (.chain [], [e]) ty

inductive PlansTyped (Γ : Context) : List (TargetShape × List Expr) → List Param → Prop
  | nil : PlansTyped Γ [] []
  | cons {plan plans p ps} : PlanTyped Γ plan p.typ → PlansTyped Γ plans ps →
      PlansTyped Γ (plan :: plans) (p :: ps)

inductive RefTyped (world : World) : TargetRef → Ty → Prop
  | root {loc ty} : AddressAt world ty loc → RefTyped world (.chain (.addr loc) [] []) ty

inductive RefsTyped (world : World) : List Param → List TargetRef → Prop
  | nil : RefsTyped world [] []
  | cons {p ps ref refs} : RefTyped world ref p.typ → RefsTyped world ps refs →
      RefsTyped world (p :: ps) (ref :: refs)

theorem RefTyped.mono {world next ref ty} (h : RefTyped world ref ty)
    (ext : Extends world next) : RefTyped next ref ty := by
  cases h with
  | root h => exact .root (h.mono ext)

theorem RefsTyped.mono {world next ps refs} (h : RefsTyped world ps refs)
    (ext : Extends world next) : RefsTyped next ps refs := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (hr.mono ext) ih

theorem RefsTyped.append {world ps ps' refs refs'} (h : RefsTyped world ps refs)
    (h' : RefsTyped world ps' refs') : RefsTyped world (ps ++ ps') (refs ++ refs') := by
  induction h with
  | nil => exact h'
  | cons hr _ ih => exact .cons hr ih

/-- A registered invocation holds actual typed captured and explicit values
for the complete function signature. Its eventual execution is not assumed. -/
def PendingCall (world : World) (fs : Array Func) (callee : GoValue)
    (args : List GoValue) : Prop :=
  ∃ fid caps f, callee = .funcVal fid caps ∧ findFunctionIn? fs fid = some f ∧
    ParamsValues world f.args.toList (caps ++ args)

def DefersTyped (world : World) (fs : Array Func) (ds : List (GoValue × List GoValue)) : Prop :=
  ∀ d ∈ ds, PendingCall world fs d.1 d.2

theorem PendingCall.mono {world next fs callee args} (h : PendingCall world fs callee args)
    (ext : Extends world next) : PendingCall next fs callee args := by
  obtain ⟨fid, caps, f, hc, hf, hv⟩ := h
  exact ⟨fid, caps, f, hc, hf, hv.mono ext⟩

theorem DefersTyped.mono {world next fs ds} (h : DefersTyped world fs ds)
    (ext : Extends world next) : DefersTyped next fs ds :=
  fun d hd => (h d hd).mono ext

/-- Every chain entry is an explicit boxed string; the recovered flag may
change independently. Equal payloads and arbitrary bytes remain admitted. -/
def ChainTyped (chain : List PanicEntry) : Prop :=
  chain ≠ [] ∧ ∀ entry ∈ chain, ∃ bytes, entry.value = .interface .string (.string bytes)

inductive AssignmentSource (world : World) (Γ : Context) :
    List Param → List Expr → List GoValue → Prop
  | expressions {ps es} : Arguments Γ es ps → AssignmentSource world Γ ps es []
  | values {ps vs} : ParamsValues world ps vs → AssignmentSource world Γ ps [] vs

theorem AssignmentSource.mono {world next Γ ps es vs} (h : AssignmentSource world Γ ps es vs)
    (ext : Extends world next) : AssignmentSource next Γ ps es vs := by
  cases h with
  | expressions h => exact .expressions h
  | values h => exact .values (h.mono ext)

end GoLean.GoCore.RecoveryRuntime
