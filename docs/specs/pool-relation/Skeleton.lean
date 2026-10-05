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


/-! ## Milestone 2 — attribution, registry boundaries (B) and the deadlock (C) -/


/-! ## Milestone 3 — the driver carriers vs `front`; terminal priority (E) -/


/-! ## Milestone 4 — the run lifts (F) and the program seam (G) -/


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
