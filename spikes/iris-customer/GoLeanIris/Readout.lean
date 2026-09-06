import GoLeanIris.Examples
import GoLean.Interface

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap Iris.BI

/-- Allocate a concrete Iris model, supply initial ownership, and extract an
actual final heap lookup. No abstract ghost-state assumption escapes. -/
theorem cell_adequacy (c : Config) (heap : Heap) (a : Nat) (old new : HeapCell)
    (hlook : heap[a]? = some old)
    (hwp : ∀ [GoGS GoResources], GoGS.context GoResources = programState heap →
      (a ↦ old) ⊢ WP c @ Stuckness.NotStuck; ⊤ {{ _v, a ↦ new }}) :
    adequate .NotStuck c (programState heap) (fun _ final => final.heap[a]? = some new) := by
  apply heap_adequacy (GF := GoResources) c (programState heap)
    (fun _ => iprop(a ↦ new))
  · intro _ hc
    iintro Hpts
    iapply hwp hc
    iapply BigSepM.bigSepM_lookup (by rw [get?_heapToMap]; exact hlook) $$ Hpts
  · intro _ _ final _
    iintro ⟨Hheap, Hpt⟩
    icases genHeap_valid $$ [$Hheap $Hpt] with >%h
    imodintro
    ipureintro
    simpa only [get?_heapToMap] using h

theorem recovered_adequate (heap : Heap) (a : Nat) (old : GoValue)
    (hlook : heap[a]? = some (.value .bool old)) :
    adequate .NotStuck (recoveredConfig a) (programState heap)
      (fun _ final => final.heap[a]? = some (.value .bool (.bool true))) :=
  cell_adequacy _ _ _ _ _ hlook (fun hc => wp_recovered hc a old)

theorem normal_adequate (heap : Heap) (a : Nat) (old : GoValue)
    (hlook : heap[a]? = some (.value .bool old)) :
    adequate .NotStuck (normalConfig a) (programState heap)
      (fun _ final => final.heap[a]? = some (.value .bool (.bool true))) :=
  cell_adequacy _ _ _ _ _ hlook (fun hc => wp_normal hc a old)

theorem wp_recovered_framed {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hc : GoGS.context GF = programState heap) (a : Nat) (old : GoValue) (R : IProp GF) :
    (a ↦ (.value .bool old) ∗ R) ⊢ WP (recoveredConfig a) @ Stuckness.NotStuck; ⊤
      {{ _v, a ↦ (.value .bool (.bool true)) ∗ R }} := by
  iintro ⟨Ha, HR⟩
  iapply wp_frame R
  isplitl [Ha]
  · iapply wp_recovered hc a old $$ Ha
  · iexact HR

/-- A concrete framed adequacy exercise: the normal-return program owns cell
0; an arbitrary cell at 1 is framed through the proof and read back unchanged. -/
theorem framed_normal_adequate (cell : HeapCell) :
    adequate .NotStuck (normalConfig 0)
      (programState #[.value .bool (.bool false), cell])
      (fun _ final => final.heap[0]? = some (.value .bool (.bool true)) ∧
        final.heap[1]? = some cell) := by
  apply heap_adequacy (GF := GoResources) _ _
    (fun _ => iprop(0 ↦ (.value .bool (.bool true)) ∗ 1 ↦ cell))
  · intro _ hc
    iintro Hpts
    icases BigSepM.bigSepM_delete (i := 0) (x := .value .bool (.bool false))
      (by rw [get?_heapToMap]; rfl) $$ Hpts with ⟨Ha, Hrest⟩
    iapply wp_frame (iprop(1 ↦ cell))
    isplitl [Ha]
    · iapply wp_normal hc 0 (.bool false) $$ Ha
    · iapply BigSepM.bigSepM_lookup (i := 1) (x := cell) ?_ $$ Hrest
      rw [get?_delete_ne (by decide), get?_heapToMap]
      rfl
  · intro _ _ final _
    iintro ⟨Hheap, Ha, Hb⟩
    ihave %ha : ⌜get? (heapToMap final.heap) 0 = some (.value .bool (.bool true))⌝
      $$ [Hheap Ha]
    · icases genHeap_valid $$ [$Hheap $Ha] with >%h
      itrivial
    icases genHeap_valid $$ [$Hheap $Hb] with >%hb
    imodintro
    ipureintro
    simpa only [get?_heapToMap] using And.intro ha hb

/-- Transfer a successful sequential witness through the existing singleton
pool conservation theorem and the actual output-folding driver. Registry
boundary steps must be absent at this same fuel. Output is retained verbatim,
not silently equated to an empty trace. -/
theorem adequate_program_result {program : Program} {name : String} {args : Array GoValue}
    {fuel : Nat} {choices initial residual : Choices} {c : Config}
    {state final : ExecState} {locs : List Loc} {values : List GoValue}
    (hsetup : runProgramSetupM fuel program name args choices = .ok (c, state, locs, initial))
    (ha : adequate .NotStuck c state (fun _ final => loadMany final locs = .ok values))
    (hr : execStmtLoop fuel state c initial = .ok (final, residual))
    (hop : seqOpCount fuel state c initial = 0) :
    ∃ out, runProgramPoolOutM fuel program name args choices =
      .ok {values := values.toArray, output := out} := by
  have hread := adequate_execStmtLoop ha hr
  have hp := execProgLoop_single (rs := {}) hr (by trivial)
  rw [hop, Nat.add_zero] at hp
  generalize hout : execProgLoopOut fuel ⟨#[.running c none], state, 0⟩ {} initial .empty = result
  obtain ⟨out, result⟩ := result
  have he := execProgLoopOut_snd fuel ⟨#[.running c none], state, 0⟩ {} initial .empty
  rw [hout, hp] at he
  dsimp only at he
  subst result
  exact ⟨out, by simp only [runProgramPoolOutM, hsetup, hout, hread]⟩

/-- Shared functional-customer bridge. Admission supplies actual setup and
pool invariants internally; Iris adequacy supplies the result. A separate
successful sequential witness supplies termination. The same fuel and
original choices reach the shipped driver, with proved empty output. -/
theorem adequate_typed_program_result {program : Program} {name : String} {args : Array GoValue}
    {fuel : Nat} {choices initial residual : Choices} {c : Config}
    {state final : ExecState} {locs : List Loc} {values : List GoValue}
    (admitted : RecoveryTyping.RecoveryAdmission program name args)
    (hsetup : runProgramSetupM fuel program name args choices = .ok (c, state, locs, initial))
    (ha : adequate .NotStuck c state (fun _ final => loadMany final locs = .ok values))
    (hr : execStmtLoop fuel state c initial = .ok (final, residual)) :
    runProgramPoolOutM fuel program name args choices =
      .ok {values := values.toArray, output := GoString.empty} := by
  have hread := adequate_execStmtLoop ha hr
  rw [RecoveryRuntime.runProgramPool_eq_sequential admitted]
  simp [runProgramM, hsetup, BooleanRuntime.runConfig_eq_loop, hr, hread,
    Bind.bind, Except.bind, Except.mapError]

/-- One separate bounded termination witness suffices for every supplied
choice stream. The semantic invariant proves this profile never consults
the stream; no existentially reselected choices enter the customer result. -/
theorem adequate_typed_program_all_choices {program : Program} {name : String}
    {args : Array GoValue} {fuel : Nat} {residual : Choices} {c : Config}
    {state final : ExecState} {locs : List Loc} {values : List GoValue}
    (admitted : RecoveryTyping.RecoveryAdmission program name args)
    (setup : ∀ ch, runProgramSetupM fuel program name args ch = .ok (c, state, locs, ch))
    (ha : adequate .NotStuck c state (fun _ final => loadMany final locs = .ok values))
    (run : execStmtLoop fuel state c [] = .ok (final, residual)) (ch : Choices) :
    runProgramPoolOutM fuel program name args ch =
      .ok {values := values.toArray, output := GoString.empty} := by
  obtain ⟨_, f, _, inv⟩ := RecoveryRuntime.setup_result_inv admitted (setup [])
  exact adequate_typed_program_result admitted (setup ch) ha (inv.loop_all_choices run ch)

end GoLean.IrisCustomer
