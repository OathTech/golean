import GoLeanProofs.Frame.PlugRule
import GoLeanProofs.Frame.PlugProbe

/-!
# The plug family's discharge witnesses (triage landing, 2026-08-27)

Named, pinnable witness theorems that APPLY the landed plug lemmas —
`stepFn_plug` (the per-step fill/step commutation) and
`callSpan_plug` (the span-level bind rule) — on a small concrete
program (the probe module's `p.f`: a callee with a defer and a
nested call). Judgment-free: the plug lemmas' statements never
mention any spec judgment, and neither do these.

Role (the witness ruling, triage plan §1.4 + amendment A4): the plug
family's previous in-tree instantiation (`W2Gate.lean`) died with the
CallSpec calculus; `PlugProbe` is a parallel concrete PROBE of the
commutation (verified, but its examples restate the commutation
shape rather than applying the theorems). These witnesses are the
family's non-vacuity demonstration until the G-BIND unit's own gate
instance lands (the named retirement condition — retire these, or
re-point them at the G-BIND instance, when it does).

Both witnesses hold at OPEN caller context `(env', k')` under the
rule's own two premises — exactly the plug rule's consumption shape.
The ∃-side facts (the canonical run of `p.f`, the `enterFrame`
non-wrapper fact) are discharged by kernel evaluation, per the
charter's concrete-evaluation carve-out for ∃-shaped discharge.

Audit pins: `proofs/Audit/Landing.lean`.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

namespace GoLean.Frame

open PlugProbe (gFunc hFunc fFunc pFunc σ0)

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- The `.next .stop` readout of a run result (shape extractor for the
kernel-discharged canonical run below). -/
private def doneStopOut :
    Except GoError (Config × ExecState × Choices)
      → Option (ExecState × Choices)
  | .ok (.next .stop, σ, ch) => some (σ, ch)
  | _ => none

/-- The canonical (anchor-context) run of the probe's `p.f` span:
caller env `[]`, below-barrier tail `.stop` — `callSpan_plug`'s
canonical shape, at `vals = []`, `v = .int 5 .int`. -/
private def canonRun : Except GoError (Config × ExecState × Choices) :=
  stepFnIter 54 σ0
    (.retV (.int 5 .int) (.callArgsK ⟨"p.f"⟩ [] [] [] [] .stop)) []

private def canonOut : Option (ExecState × Choices) := doneStopOut canonRun

private theorem canonOut_isSome : canonOut.isSome = true := by kernel_rfl

/-- The canonical run's final state (kernel-computed, never spelled). -/
private def canonσ : ExecState := (canonOut.get canonOut_isSome).1
private def canonCh : Choices := (canonOut.get canonOut_isSome).2

private theorem canonRun_eq :
    canonRun = .ok (.next .stop, canonσ, canonCh) := by kernel_rfl

/-- Non-wrapper check → the `callSpan_plug` premise shape. -/
private theorem wrapper_false_of_check
    {r : Except GoError (Func × LocalEnv × List Loc × ExecState)}
    (h : (match r with
          | .ok (f, _, _, _) => f.wrapper == false
          | .error _ => true) = true) :
    ∀ {f : Func} {e : LocalEnv} {ls : List Loc} {σe : ExecState},
      r = .ok (f, e, ls, σe) → f.wrapper = false := by
  intro f e ls σe hr
  subst hr
  simpa using h

private theorem enterF_not_wrapper :
    (match enterFrame σ0 ⟨"p.f"⟩ ([] ++ [GoValue.int 5 .int]) with
      | .ok (f, _, _, _) => f.wrapper == false
      | .error _ => true) = true := by kernel_rfl

/-- **THE CALL-SPAN WITNESS** (`callSpan_plug` applied): the probe
program's `p.f` call span — defer registration, a nested `p.g` call,
the defer drain — proved at the canonical anchor by kernel
evaluation, holds at ANY caller context `(env', k')` satisfying the
plug rule's two premises, at the same fuel, final state, and stream.
The caller context is OPEN: this is one application of the rule
covering every plug context, not a per-context replay. -/
theorem callSpan_plug_witness (env' : LocalEnv) (k' : Cont)
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none) :
    stepFnIter 54 σ0
      (.retV (.int 5 .int) (.callArgsK ⟨"p.f"⟩ [] [] [] env' k')) []
      = .ok (.next k', canonσ, canonCh) :=
  callSpan_plug hmf hrc
    (fun _ _ _ _ henter => wrapper_false_of_check enterF_not_wrapper henter)
    canonRun_eq

/-- **THE PER-STEP WITNESS** (`stepFn_plug` applied): the per-step
commutation at a concrete barrier-carrying configuration of the probe
program (entry into `p.f`'s body over the barrier frame), at open
`(env', k')` under the rule's premises. -/
theorem stepFn_plug_witness (env' : LocalEnv) (k' : Cont)
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none) :
    PS env' k'
      (stepFn σ0 (.exec fFunc.body [] (.frame [] [] [] [] .stop false)) [])
      (stepFn σ0 (plugC env' k'
        (.exec fFunc.body [] (.frame [] [] [] [] .stop false))) []) :=
  stepFn_plug hmf hrc (by rfl)

end GoLean.Frame
