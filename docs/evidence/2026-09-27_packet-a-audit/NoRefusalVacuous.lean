import GoLean.GoCore.ExecutionStatement
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

#eval match stepFn (ProgramCtx.ofTables #[] #[]) {} (.next .stop) [] with
  | .ok _ => "ok" | .error e => s!"{repr e}"

/-- `stepFn` refuses at the normal terminal, so `NoRefusal` FAILS at every configuration
from which `.next .stop` is Prefix-reachable: the corollary's premise excludes every run
that completes normally. -/
theorem not_noRefusal_stop (ctx : ProgramCtx) (s : Store) : ¬ NoRefusal ctx s (.next .stop) := by
  intro h
  exact (h 0 [] [] s (.next .stop) [] .done).1 (.internal "step on terminal configuration") rfl

/-- GENERAL: any configuration with a Prefix to the normal terminal fails `NoRefusal` —
so `classification_wf_stmt`'s premise holds of NO run that completes normally. -/
theorem not_noRefusal_of_completes {ctx : ProgramCtx} {n s c ch ls sf chf}
    (hp : Prefix ctx n s c ch ls sf (.next .stop) chf) : ¬ NoRefusal ctx s c := by
  intro h
  exact (h n ch ls sf (.next .stop) chf hp).1 (.internal "step on terminal configuration") rfl

/-- `program_bridge_stmt` is the definition of `runProgramPoolOutM` unfolded: it carries no
content beyond the driver's own equation. -/
theorem program_bridge_trivial : program_bridge_stmt := by
  intro fuel p name args ch pctx c₀ s₀ locs ch₁ h
  simp only [runProgramPoolOutM, h]; rfl

theorem silent_projection : silent_projection_stmt := by
  intro ls₁ ls₂; simp

theorem single_embedding : single_embedding_stmt :=
  fun _ _ _ _ _ _ _ => execProgLoop_single
