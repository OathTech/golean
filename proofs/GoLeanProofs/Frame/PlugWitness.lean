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
shape rather than applying the theorems). Witness status after
G-BIND (corrected at the audit fix round, F2): the retirement
condition fired **for the PER-STEP rule only** — the C-05 `callchain`
quartet (`Specs/Callchain.lean`) reaches `stepFn_plug` (and the new
inversion walk) through `wp_plug_bind`'s chain, so
`stepFn_plug_witness` is re-pointed at that live consumer. The
SPAN-level rules (`callSpan_plug` / `stepFnIter_plug`) are NOT on the
bind chain; **`callSpan_plug_witness` below remains their live
application and stays load-bearing** (retiring it would zero their
applications and reopen the A4 vacuity gap — the auditor's explicit
recommendation is to keep both `Audit/Landing` pins).

Both witnesses hold at OPEN caller context `(env', k')` under the
rule's own two premises — exactly the plug rule's consumption shape.

**Which carve-out applies (corrected 2026-08-27, pre-merge audit,
claim-dimension F7).** The kernel evaluations here — the canonical
run of `p.f` (`canonRun_eq`), the `enterFrame` non-wrapper fact
(`enterF_not_wrapper`), and the step-success anchor
(`stepFn_plug_witness_step_ok`) — are NOT the charter's "∃-shaped
discharge, exhibiting a run is how existentials are proved" clause.
Both witnesses' statements are ∀-shaped EQUATIONS over the open
caller context; what the kernel discharges is their PREMISES —
concrete facts about a concrete probe program that the plug rule
consumes as hypotheses. That falls under the carve-out for declared
reflection/evaluation certificates, not the ∃ clause. The
distinction matters because the ∃ clause licenses exhibiting a
witness as the proof itself, and nothing here does that: the proof
is one application of a ∀-quantified rule.

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

/-! ### The per-step witness's non-vacuity anchor (audit finding F6)

`PS env' k' x y` is an IMPLICATION: it says "if `x = .ok (d, σ₁,
ch₁)` then `y = .ok (plugC env' k' d, σ₁, ch₁)` and `d` classifies".
It is therefore VACUOUSLY TRUE whenever the canonical step `x`
errors — `PS.err` is one line. So `stepFn_plug_witness` on its own
does not demonstrate that the plug rule says anything here; it
demonstrates that at most. The lemma below closes that hole by
pinning the antecedent: the canonical step at the witness's
configuration genuinely succeeds. -/

/-- The canonical per-step run at the witness's configuration. -/
private def plugStepRun : Except GoError (Config × ExecState × Choices) :=
  stepFn σ0 (.exec fFunc.body [] (.frame [] [] [] [] .stop false)) []

private def plugStepOut : Option (Config × ExecState × Choices) :=
  match plugStepRun with
  | .ok r => some r
  | .error _ => none

private theorem plugStepOut_isSome : plugStepOut.isSome = true := by
  kernel_rfl

/-- The step's result triple (kernel-computed, never spelled). -/
private def plugStepRes : Config × ExecState × Choices :=
  plugStepOut.get plugStepOut_isSome

/-- **THE NON-VACUITY ANCHOR** for `stepFn_plug_witness` (pre-merge
audit, claim-dimension F6): the canonical step at the witness's
configuration reduces to an `.ok`, so the `PS` implication the
witness proves has a satisfied antecedent and its conclusion is
actually asserted. Without this, `PS.err` would prove the witness
for free at any configuration whose step errors.

Discharged by kernel evaluation — a concrete step on a concrete
probe configuration, inside the charter's carve-out for declared
reflection/evaluation certificates. -/
theorem stepFn_plug_witness_step_ok :
    stepFn σ0 (.exec fFunc.body [] (.frame [] [] [] [] .stop false)) []
      = .ok plugStepRes := by
  kernel_rfl

/-- **THE PER-STEP WITNESS** (`stepFn_plug` applied): the per-step
commutation at a concrete barrier-carrying configuration of the probe
program, at open `(env', k')` under the rule's premises.

**Non-vacuity:** `PS` is an implication and would hold vacuously on
an erroring step — `stepFn_plug_witness_step_ok` (above) pins that
the canonical step here reduces to `.ok`, so the commutation is
genuinely asserted rather than dodged.

**The configuration is SYNTHETIC — read this before citing the
witness** (pre-merge audit, claim-dimension F6): `.frame [] [] [] []
.stop false` is a hand-built barrier frame chosen to carry a barrier
at the right place, NOT the frame `enterFrame σ0 ⟨"p.f"⟩ …` actually
produces for this call (that one carries the callee's allocated
result locations and its bound parameter environment; all four
columns here are empty). What the witness therefore demonstrates is
that `stepFn_plug` APPLIES and commutes at a barrier-carrying
configuration of a real program's body — which is the rule's
consumption shape — and NOT that it commutes at this call's exact
entry product. The span-level `callSpan_plug_witness` above is the
one that runs the real entry, through `enterFrame` itself. -/
theorem stepFn_plug_witness (env' : LocalEnv) (k' : Cont)
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none) :
    PS env' k'
      (stepFn σ0 (.exec fFunc.body [] (.frame [] [] [] [] .stop false)) [])
      (stepFn σ0 (plugC env' k'
        (.exec fFunc.body [] (.frame [] [] [] [] .stop false))) []) :=
  stepFn_plug hmf hrc (by rfl)

end GoLean.Frame
