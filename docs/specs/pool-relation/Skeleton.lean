import GoLean.GoCore.PoolStatement

/-!
# The pool/registry half — the SKELETON (sorry'd; OUTSIDE every build target and gate scan)

[AGENT design worker, lane `design/pool-relation-spec-1004`] 2026-10-04. This file is NOT a module
of the `GoLean` library: it lives under `docs/specs/`, which no `lakefile.toml` glob, no
`GoLean.lean` import and no `scripts/ci` escape-hatch scan (`find GoLean GoLean.lean Main.lean`)
reaches. It is built AD HOC against the tree —

    scripts/capped lake build GoLean.GoCore.PoolStatement
    scripts/capped lake env lean docs/specs/pool-relation/Skeleton.lean

— and its only purpose is to show that every target statement ELABORATES and to list, in the
suggested proof order, the theorems the grind discharges. Each `theorem <name> : <name>_stmt :=
by sorry` here becomes `theorem <name> : <name>_stmt := <proof>` in `GoLean/GoCore/PoolSound.lean`
(the grind's module, in the build, no `sorry`). The statements are FROZEN in
`GoLean/GoCore/PoolStatement.lean`; this file must never be imported by anything.

The `sorry` warnings this file emits are the point; a build of the GoLean library emits none.
-/

namespace GoLean.GoCore.PoolSkeleton

open GoLean.GoCore.PoolStatement

/-! ## Milestone 1 — the step correspondence (A) and the error classes (D) -/

theorem stepMulti_error_cases : stepMulti_error_cases_stmt := by sorry
theorem raceUpdate_error : raceUpdate_error_stmt := by sorry
theorem schedSlot_iff : schedSlot_iff_stmt := by sorry
theorem stepML_erase : stepML_erase_stmt := by sorry
theorem stepML_sound : stepML_sound_stmt := by sorry
theorem stepML_complete : stepML_complete_stmt := by sorry
theorem stepM_lift : stepM_lift_stmt := by sorry
theorem stepsML_erase : stepsML_erase_stmt := by sorry
theorem stepMulti_replay : stepMulti_replay_stmt := by sorry

/-! ## Milestone 2 — attribution, registry boundaries (B) and the deadlock (C) -/

theorem stepML_who_runnable : stepML_who_runnable_stmt := by sorry
theorem stepML_sched : stepML_sched_stmt := by sorry
theorem stepML_switch_boundary : stepML_switch_boundary_stmt := by sorry
theorem stepML_sched_record : stepML_sched_record_stmt := by sorry
theorem stepML_frame : stepML_frame_stmt := by sorry
theorem stepML_paired_trace : stepML_paired_trace_stmt := by sorry
theorem stepML_spawn : stepML_spawn_stmt := by sorry
theorem asleep_silent : asleep_silent_stmt := by sorry
theorem singleton_deadlock : singleton_deadlock_stmt := by sorry
theorem mainOutcome_not_deadlock : mainOutcome_not_deadlock_stmt := by sorry
theorem stepMulti_deadlock_elim : stepMulti_deadlock_elim_stmt := by sorry

/-! ## Milestone 3 — the driver carriers vs `front`; terminal priority (E) -/

theorem front_continue : front_continue_stmt := by sorry
theorem front_finish : front_finish_stmt := by sorry
theorem front_refusal : front_refusal_stmt := by sorry
theorem poolFinish_functional : poolFinish_functional_stmt := by sorry
theorem poolFinish_zero_not_continue : poolFinish_zero_not_continue_stmt := by sorry

/-! ## Milestone 4 — the run lifts (F) and the program seam (G) -/

theorem poolPrefix_comp : poolPrefix_comp_stmt := by sorry
theorem poolPrefix_split : poolPrefix_split_stmt := by sorry
theorem poolPrefix_labelled : poolPrefix_labelled_stmt := by sorry
theorem poolPrefix_erase : poolPrefix_erase_stmt := by sorry
theorem poolPrefix_run : poolPrefix_run_stmt := by sorry
theorem pool_run_ok_iff : pool_run_ok_iff_stmt := by sorry
theorem pool_run_terminal_iff : pool_run_terminal_iff_stmt := by sorry
theorem pool_run_fuelOut_iff : pool_run_fuelOut_iff_stmt := by sorry
theorem pool_run_refusal_iff : pool_run_refusal_iff_stmt := by sorry
theorem pool_classification : pool_classification_stmt := by sorry
theorem run_ok_prefix : run_ok_prefix_stmt := by sorry
theorem continue_replay : continue_replay_stmt := by sorry
theorem poolPrefix_replay : poolPrefix_replay_stmt := by sorry
theorem program_prefix : program_prefix_stmt := by sorry

/-! ## Milestone 5 — the single-goroutine reduction (H) -/

theorem stepML_single_sound : stepML_single_sound_stmt := by sorry
theorem stepML_single_complete : stepML_single_complete_stmt := by sorry
theorem singleton_finish_normal : singleton_finish_normal_stmt := by sorry
theorem singleton_finish_aborted : singleton_finish_aborted_stmt := by sorry
theorem singleton_finish_refused : singleton_finish_refused_stmt := by sorry
theorem singleton_finish_fatal : singleton_finish_fatal_stmt := by sorry
theorem singleton_finish_deadlock : singleton_finish_deadlock_stmt := by sorry
theorem singleton_prefix_embedding : singleton_prefix_embedding_stmt := by sorry
theorem singleton_run : singleton_run_stmt := by sorry

end GoLean.GoCore.PoolSkeleton
