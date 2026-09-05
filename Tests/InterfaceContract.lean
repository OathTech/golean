import GoLean.Interface

namespace GoLean.GateA1
open GoCore GoCore.Machine Semantics

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

namespace GoLean.GateA1
open GoCore GoCore.Machine Semantics

def exampleState : ExecState := { types := TypeEnv.reserved }
def choicePool : MultiConfig := ⟨#[Thread.running forkPoint none], exampleState, 0⟩

/-- Hand-authored GoCore; no claim of a certified Go frontend translation. -/
def printPanicProgram : Program := { funcs := #[{
  id := ⟨"main.audit"⟩, args := #[], results := #[],
  body := .seqn #[.print true #[.stringLit (GoString.fromLeanString "before")],
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string
      (.stringLit (GoString.fromLeanString "boom")))] }] }

def recoverBranch (k : Cont) : Cont :=
  .ifK (.seqn #[]) (.unsupported "recovery did not happen") [] k
def recoverCompare (k : Cont) : Cont :=
  .strictK (.neqCmp (.interface ⟨"empty_interface"⟩)) [.nil] [] [] (recoverBranch k)
def recoverCheck : Config := .evalE .recoverCall [] (recoverCompare panicFrame)

/-- An injective readout for panic results, to make kernel computation
avoid equality instances for unrelated successful result values. -/
def panicObservation : RunResult → Option (String × Array UInt8)
  | .error (.terminal (.panic msg), out) => some (msg, out.bytes)
  | _ => none

theorem panicObservation_sound {r : RunResult} {msg : String} {bytes : Array UInt8}
    (h : panicObservation r = some (msg, bytes)) :
    r = .error (.panic msg, ⟨bytes⟩) := by
  cases r with
  | ok v => cases h
  | error e =>
    obtain ⟨stop, ⟨out⟩⟩ := e
    cases stop with
    | refusal e => cases h
    | fuelOut => cases h
    | terminal t => cases t with
      | panic m =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rfl
      | fatal m => cases h
      | deadlock => cases h
      | raceDetected => cases h

set_option maxRecDepth 4096 in
/-- Full entry, actual print event, abort, and the retained byte prefix. -/
theorem print_before_panic :
    runProgramPoolOutM 20 printPanicProgram "main.audit" #[] [] =
      .error (.panic "boom", GoString.fromLeanString "before\n") := by
  apply panicObservation_sound
  decide +kernel

theorem print_before_panic_trace :
    Pool.ProgramRun 20 printPanicProgram "main.audit" #[] []
      (.error (.panic "boom", GoString.fromLeanString "before\n")) :=
  Pool.program_run_iff.mp print_before_panic

/-- Terminal checking precedes exhaustion. One step suffices for DEFER. -/
theorem defer_completes (s : ExecState) (tail : Choices) :
    execStmtLoop 1 s forkPoint (0 :: tail) = .ok (s, tail) :=
  run_ok_iff.mpr ⟨1, Nat.le_refl _, defer_trace s tail⟩

theorem raise_needs_abort_fuel (s : ExecState) (tail : Choices) :
    execStmtLoop 1 s forkPoint (1 :: tail) = .error .fuelOut := by
  rw [execStmtLoop_step (choose_raise s tail)]
  rfl

theorem raise_aborts :
    execStmtLoop 2 exampleState forkPoint [1] = .error (.panic "audit") := by
  rw [execStmtLoop_step (choose_raise exampleState [])]
  with_unfolding_all rfl

/-- Both directions of the corrected bridge at the actual choice site. -/
theorem defer_run_iff :
    execStmtLoop 1 exampleState forkPoint [0] = .ok (exampleState, []) ↔
      ∃ n, n ≤ 1 ∧ Trace n exampleState forkPoint [0] exampleState (.next .stop) [] :=
  run_ok_iff

theorem pool_defer (acc : GoString) :
    execProgLoopOut 2 choicePool {} [0] acc = (acc, .ok (exampleState, [])) := by
  with_unfolding_all rfl

theorem pool_raise (acc : GoString) :
    execProgLoopOut 2 choicePool {} [1] acc = (acc, .error (.panic "audit")) := by
  with_unfolding_all rfl

theorem both_pool_traces (acc : GoString) :
    Pool.Run 2 choicePool {} [0] acc (acc, .ok (exampleState, [])) ∧
    Pool.Run 2 choicePool {} [1] acc (acc, .error (.panic "audit")) :=
  ⟨Pool.run_iff.mp (pool_defer acc), Pool.run_iff.mp (pool_raise acc)⟩

theorem two_choice_pool_bridge (acc : GoString) :
    (∃ ch, execProgLoopOut 2 choicePool {} ch acc = (acc, .error (.panic "audit"))) ∧
    execProgLoopOut 2 choicePool {} [0] acc ≠ (acc, .error (.panic "audit")) := by
  refine ⟨⟨[1], pool_raise acc⟩, ?_⟩
  rw [pool_defer]
  intro h
  cases (Prod.mk.inj h).2


end GoLean.GateA1
