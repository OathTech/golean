import GoLean.GoCore.RecoveryControlHelpers
import GoLean.GoCore.RecoveryCallEntry

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem call_entry_control {p : Program} {world s fid f args Γ env plans k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args)
    (he : EnvTyped world Γ env) (ht : PlansTyped Γ plans f.results.toList)
    (hk : ReturnCont world p.funcs k) (ch : Choices) :
    ∃ next env' roots t,
      enterFramePick s fid args ch = .ok (.ok (f, env', roots, t), ch) ∧
      StoreExtension world next s t ∧ f.wrapper = false ∧
      Control next p.funcs (.exec f.body env' (.frame plans env roots [] k false)) := by
  obtain ⟨next, env', roots, t, run, ex, hh, he', hr, ctx, _, hft, hw⟩ :=
    enterFramePick_typed hp hc heap hf values ch
  exact ⟨next, env', roots, t, run, ⟨ex, hh, ctx⟩, hw,
    .execFrame he' (.of_static hft.2.2.2.2.1)
      (.frame (he.mono ex) ht hr (by simp [DefersTyped]) (.stmt (hk.mono ex))
        (fun _ => hk.mono ex))⟩

theorem deferred_entry_control {p : Program} {world s callee args k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (pending : PendingCall world p.funcs callee args)
    (hk : ExitCont world p.funcs k) (ch : Choices) :
    ∃ fid caps f next env roots t,
      callee = .funcVal fid caps ∧
      enterFramePick s fid (caps ++ args) ch = .ok (.ok (f, env, roots, t), ch) ∧
      StoreExtension world next s t ∧ f.wrapper = false ∧
      Control next p.funcs (.exec f.body env (.frame [] [] [] [] k false)) := by
  obtain ⟨fid, caps, f, hcallee, hf, hv⟩ := pending
  obtain ⟨next, env, roots, t, run, ex, hh, he, _, ctx, _, hft, hw⟩ :=
    enterFramePick_typed hp hc heap hf hv ch
  exact ⟨fid, caps, f, next, env, roots, t, hcallee, run, ⟨ex, hh, ctx⟩, hw,
    .execFrame he (.of_static hft.2.2.2.2.1)
      (.frame (EnvTyped.empty next) .nil .nil (by simp [DefersTyped]) (hk.mono ex)
        (by simp))⟩

end GoLean.GoCore.RecoveryRuntime
