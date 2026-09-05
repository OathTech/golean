import GateA1.Trace

namespace GoLean.GateA1
open GoCore GoCore.Machine

def bareFrame : Cont := .frame [] [] [] [] .stop false
def panicFrame : Cont := .frame [] [] [] [] (.panicResumeK [panicEntry "audit"] .stop) false

theorem recover_bare : recoverResult bareFrame = (.nil, bareFrame) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  change (match recoverThroughWrappers .stop with
    | some (v, k) => (v, Cont.frame [] [] [] [] k false)
    | none => (.nil, bareFrame)) = _
  unfold recoverThroughWrappers
  rw [Cont.rebuild_stop]
def recoveredFrame : Cont := .frame [] [] [] []
  (.panicResumeK [{ panicEntry "audit" with recovered := true }] .stop) false
theorem recover_handler : recoverResult panicFrame = ((panicEntry "audit").value, recoveredFrame) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  change (match recoverThroughWrappers (.panicResumeK [panicEntry "audit"] .stop) with
    | some (v, k) => (v, Cont.frame [] [] [] [] k false)
    | none => (.nil, panicFrame)) = _
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  rfl
theorem recover_changes_value : (recoverResult bareFrame).1 ≠ (recoverResult panicFrame).1 := by
  intro h
  rw [recover_bare, recover_handler] at h
  cases h

theorem recover_changes_handler : (recoverResult panicFrame).2 ≠ panicFrame := by
  intro h
  rw [recover_handler] at h
  have hb := congrArg (fun k => match k with
    | .frame _ _ _ _ (.panicResumeK (e :: _) _) _ => e.recovered
    | _ => false) h
  cases hb

theorem recover_stepFn (s : ExecState) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn s (.evalE .recoverCall env k) ch =
      .ok (.retV (recoverResult k).1 (recoverResult k).2, s, ch) := rfl

/-- Transporting the bare-frame recover successor under the added handler
is not a step. This refutes the concrete instance of the proposed fill law. -/
theorem recover_step_does_not_transport (s : ExecState) :
    Step (.evalE .recoverCall [] bareFrame) s (.retV .nil bareFrame) s ∧
    ¬ Step (.evalE .recoverCall [] panicFrame) s (.retV .nil panicFrame) s := by
  refine ⟨.evalRecover recover_bare, ?_⟩
  intro h
  obtain ⟨ch, ch', he⟩ := step_complete h
  rw [recover_stepFn, recover_handler] at he
  have hc := (Prod.mk.inj (Except.ok.inj he)).1
  cases hc

def illTyped : ExecState := { heap := #[.value .bool (.int 7)] }
theorem address_bound_admits_ill_typed : StateWf illTyped := by decide

/-- An actual choice site of the current machine, not a toy transition system. -/
def forkPoint : Config := .panicking [panicEntry "audit"] (.probeK .stop)
def raised : Config := .panicking [panicEntry "audit"] .stop

theorem choose_defer (s : ExecState) (tail : Choices) :
    stepFn s forkPoint (0 :: tail) = .ok (.next .stop, s, tail) := rfl
theorem choose_raise (s : ExecState) (tail : Choices) :
    stepFn s forkPoint (1 :: tail) = .ok (raised, s, tail) := rfl

theorem both_relational_successors (s : ExecState) :
    Step forkPoint s (.next .stop) s ∧ Step forkPoint s raised s :=
  ⟨.probeDefer, .probeRaise⟩

/-- The old fixed-stream ⇐ existential-path claim already fails at one step. -/
theorem fixed_stream_not_existential_path (s : ExecState) :
    Steps forkPoint s raised s ∧
      ¬ ∃ chf, stepFnIter 1 s forkPoint [0] = .ok (raised, s, chf) := by
  refine ⟨Steps.single (both_relational_successors s).2, ?_⟩
  rintro ⟨chf, h⟩
  have hc : Config.next .stop = raised := congrArg (fun x => x.toOption.map Prod.fst) h
    |> Option.some.inj
  cases hc

theorem defer_trace (s : ExecState) (tail : Choices) :
    Trace 1 s forkPoint (0 :: tail) s (.next .stop) tail :=
  .step (choose_defer s tail) .done
theorem raise_trace (s : ExecState) (tail : Choices) :
    Trace 1 s forkPoint (1 :: tail) s raised tail :=
  .step (choose_raise s tail) .done

end GoLean.GateA1
