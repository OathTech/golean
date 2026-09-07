import GoLean.GoCore.RecoverySetup

/-! Address well-formedness follows from the mixed schema and source typing.
It is not an additional assumption of successful entry or future execution. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem ValueTyped.locSup_le {world sort v} (h : ValueTyped world sort v) :
    GoValue.locSup v ≤ world.size := by
  cases h with
  | root ha =>
    have hb := (Array.getElem?_eq_some_iff.mp ha).1
    simpa [GoValue.locSup, Loc.locSup, Loc.rootBase] using Nat.succ_le_of_lt hb
  | _ => simp [GoValue.locSup]

theorem HeapTyped.heapLocSup_le {world s} (h : HeapTyped world s) :
    Heap.locSup s.heap ≤ s.heap.size := by
  rw [Heap.locSup_le_iff]
  intro cell hc
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hc
  have hw : i < world.size := by simpa only [h.size] using hi
  obtain ⟨ty, v, hv, _, htype⟩ := h.cells i world[i] (by simp)
  have hh : s.heap[i] = .value ty v := (Array.getElem?_eq_some_iff.mp hv).2
  rw [← he, hh]
  simpa only [HeapCell.locSup, h.size] using htype.locSup_le

theorem BindingsTyped.locSup_le {world env s} (h : BindingsTyped world env)
    (heap : HeapTyped world s) : LocalEnv.locSup env ≤ s.nextAddr := by
  rw [localEnvLocSup_eq, supBy_le_iff]
  intro scope hs
  rw [scopeLocSup_eq, supBy_le_iff]
  intro binding hb
  obtain ⟨sort, hl⟩ := h scope hs binding hb
  obtain ⟨a, ha, hbound⟩ := heap.address_bound hl
  simp only [ha, Loc.locSup, Loc.rootBase, ExecState.nextAddr]
  omega

theorem typedState_wf {p world s} (hp : ProgramTyped p) (hh : HeapTyped world s)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s) : StateWf s := by
  have hf : s.functions = p.funcs := (congrArg ExecState.functions hc).symm
  simpa [StateWf, ExecState.locSup, hf, program_funcListSup hp,
    ExecState.nextAddr] using hh.heapLocSup_le

theorem typedEntry_wf {p world s f Γ env} (hp : ProgramTyped p)
    (hf : f ∈ p.funcs.toList) (hh : HeapTyped world s) (he : EnvTyped world Γ env)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s) :
    MachineWf s (.exec f.body env (.frame [] [] [] [] .stop)) := by
  refine ⟨typedState_wf hp hh hc, ?_, Config.itersNormalized_true _ _⟩
  have hb := statement_locSup (hp.2.2.1 f hf).2.2.2.2.1
  simpa [ConfigWf, Config.locSup, Cont.locSup, locListSup, LocalEnv.locSup,
    targetPlansSup, deferListSup, hb] using he.bindings.locSup_le hh

/-- Admission establishes actual entry, all typed storage facts, and the
structural machine invariant for any supplied setup fuel/choice stream.
The recovery control invariant will compose with this entry contract. -/
theorem setup_typed_wf {p : Program} {name : String} {args : Array GoValue}
    (h : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (zeros : List GoValue) (world : World),
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped p.funcs f ∧
      ZeroValues f.results.toList zeros ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f args.toList zeros, BooleanRuntime.initialResults f, ch) ∧
      MachineWf (initialState p f args.toList zeros)
        (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop)) ∧
      HeapTyped world (initialState p f args.toList zeros) ∧
      EnvTyped world (initialContext f) (BooleanRuntime.initialEnv f) ∧
      ResultRoots world f.results.toList (BooleanRuntime.initialResults f) ∧
      BooleanRuntime.SameContext (BooleanRuntime.programState p)
        (initialState p f args.toList zeros) ∧
      (initialState p f args.toList zeros).heap.size = args.size + f.results.size ∧
      f.args.size = args.size := by
  obtain ⟨f, zeros, world, hf, ht, hz, hs, hh, he, hr, hc, hsize, hargs⟩ :=
    setup_typed h fuel ch
  exact ⟨f, zeros, world, hf, ht, hz, hs,
    typedEntry_wf h.2.2 (BooleanRuntime.findFunction_mem hf) hh he hc,
    hh, he, hr, hc, hsize, hargs⟩

end GoLean.GoCore.RecoveryRuntime
