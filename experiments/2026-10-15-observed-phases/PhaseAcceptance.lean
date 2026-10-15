import GoLean.Relational
import RelationalCodeX.ObservedCallerAdequacy

/-! Private adapters to the unchanged 3c9be98 requests. No downstream type
appears in the permanent semantic exports. -/
namespace PhaseAcceptance
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

theorem path {ctx fact c d} (h : Observed.StorePath ctx fact c d) :
    RelationalCodeX.Observed.QuietPath ctx fact c d := by
  induction h with
  | refl => exact .refl
  | step ht ha hq _ ih => exact .step ht hq ha ih

theorem effect {ctx op c d} (h : Observed.StoreEffect ctx op c d) :
    RelationalCodeX.Observed.QuietEffect ctx op c d := ⟨h.effect, h.source_policy⟩

theorem writes {ctx ls vs c d} (h : Observed.OrderedWrites ctx ls vs c d) :
    RelationalCodeX.Observed.QuietWrites ctx ls vs c d := by
  induction h with
  | nil p => exact .nil (path p)
  | cons p e _ ih => exact .cons (path p) (effect e) ih

theorem assignment : RelationalCodeX.Observed.AssignmentQuiet := by
  intro ctx env k dst src target source value hd hs
  obtain ⟨before, after, p, e, q⟩ :=
    Observed.variable_assignment_phases ctx env k dst src target source value hd hs
  exact ⟨before, after, path p, effect e, path q⟩

theorem entry : RelationalCodeX.Observed.VariableEntryObserved := by
  intro ctx caller fid id source v bound
  obtain ⟨before, p, admitted, activate⟩ :=
    Observed.SavedCaller.entry_phases caller ctx fid [.var id] [v] _
      (.cons (Observed.ReadOnlyExpr.variable ctx caller.locals id source v bound) .nil)
  exact ⟨before, path p, admitted, activate⟩

theorem delivery : RelationalCodeX.Observed.DeliveryObserved := by
  intro ctx b mode ls vs count values valid bound
  obtain ⟨after, before, admitted, ret, p, ws⟩ :=
    Observed.CallBoundary.delivery_phases b mode ctx ls vs count values valid bound
  exact ⟨after, before, admitted, ret, path p, writes ws⟩

theorem callee : RelationalCodeX.ObservedCaller.CalleeTarget :=
  RelationalCodeX.ObservedCaller.callee_acceptance assignment

theorem caller : RelationalCodeX.ObservedCaller.CallerTarget :=
  RelationalCodeX.ObservedCaller.caller_acceptance entry delivery

end PhaseAcceptance
