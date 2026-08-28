import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProofMode
import GoLean.GoCore.MachineSound
import GoLeanProofs.Ghost
import GoLeanProofs.Lifting
import GoLeanProofs.Frame.PlugInv

/-!
# G-BIND: the bind/fill rule (`wp_bind` for the plug geometry)

The plan of record's §4.1 deliverable, route (b): the direct bind
lemma at the WP level. From
`WP c {{ _, WP (.next k') {{ Φ }} }}` conclude
`WP (plugC env' k' c) {{ Φ }}` — the callee's WP at its CANONICAL
configuration composes into any caller context `(env', k')`
satisfying the plug premises. `plugC (.next .stop) = .next k'` is the
`fill k v` of the classic rule; our continuations are configuration
data, so the fill is the below-barrier replacement.

LINEAGE: the ectx-language bind rule (Iris `EctxLanguage`/`wp_bind`;
the proof mirrors the pin's `wp_bind_iff` forward branch,
`Iris/ProgramLogic/WeakestPre.lean:401`). Divergences, both forced by
the machine's geometry (unit log `docs/g-bind-log.md`):
1. the fill/decomposition laws are barrier-premised (`step_plug` /
   `step_plug_inv`, `Frame/PlugInv.lean`) — the unconditional
   `Language.Context` shape is FALSE here (log D-2), so this is a
   standalone lemma, not a typeclass instantiation;
2. the machine's two-step panic abort (`.panicking → .panicked →`
   stuck) forces the THIRD context premise `hdrain` — without it the
   entailment is semantically false at step-indexed granularity for
   contexts whose panic-drain sticks before the canonical render
   (log F-3). `hdrain` asks only that the drain's HEAD steps, and is
   discharged at concrete call sites by one constructor
   (`step_panicking_of_passthrough` / `step_panicking_frame_empty`).

Stated at `s = .NotStuck` (the crossed-case refutation consumes the
reducibility conjunct; every Surface-exit WP is NotStuck, so no
consumer narrows).

Non-vacuity witness: the C-05 `callchain` gate instance
(`Specs/Callchain.lean`) closes through this rule three times.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {E : CoPset}

/-! ## Pure step-transfer facts (the relation-level plug family lifted
to the language instance's `PrimStep`) -/

/-- Our `toVal` is `none` away from the terminal. -/
theorem toVal_none_of_ne_next_stop {c : Config}
    (h : c ≠ .next .stop) : (ToVal.toVal c : Option Unit) = none := by
  cases c <;> first
    | rfl
    | (rename_i k; cases k <;> first | rfl | exact absurd rfl h)

/-- `.panicked` is irreducible: the abort is terminal. -/
theorem not_reducible_panicked {msg : String} {σ : ExecState} :
    ¬ PrimStep.Reducible ((Config.panicked msg : Config), σ) := by
  rintro ⟨obs, e', σ', eₜ, h⟩
  cases h with
  | step st => exact not_step_panicked st

/-- Reducibility transports through the fill (the forward half). -/
theorem reducible_plugC {env' : LocalEnv} {k' : Cont} {c : Config}
    {σ : ExecState}
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    (hbar : hasBarrierC c = true)
    (h : PrimStep.Reducible ((c : Config), σ)) :
    PrimStep.Reducible ((plugC env' k' c : Config), σ) := by
  obtain ⟨obs, e', σ', eₜ, hstep⟩ := h
  cases hstep with
  | step st =>
      obtain ⟨hstep', _⟩ := step_plug hmf hrc hbar st
      exact ⟨[], _, _, _, GoPrimStep.step hstep'⟩

/-- A `PrimStep` of the filled configuration decomposes (the inversion
at the language instance). -/
theorem primStep_plugC_inv {env' : LocalEnv} {k' : Cont} {c : Config}
    {σ : ExecState} {obs : List Unit} {e₂ : Config} {σ₂ : ExecState}
    {eₜ : List Config}
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    (hbar : hasBarrierC c = true)
    (h : GoPrimStep (plugC env' k' c, σ) obs (e₂, σ₂, eₜ)) :
    obs = [] ∧ eₜ = [] ∧ ∃ d, e₂ = plugC env' k' d ∧ Step c σ d σ₂
      ∧ (hasBarrierC d = true ∨ d = .next .stop
          ∨ ∃ chain, d = .panicking chain .stop) := by
  cases h with
  | step st => exact ⟨rfl, rfl, step_plug_inv hmf hrc hbar st⟩

/-! ## The crossed-panic transport -/

/-- **The panic-arrival transport**: a NotStuck WP of the CROSSED shape
(`.panicking chain .stop` — the canonical run after the panic passed
the barrier) proves any WP of the context-filled drain, because the
crossed WP is refutable in two interrogations: its own reducibility
pins the render step, and the rendered `.panicked` is irreducible. The
`hdrain` premise supplies the filled drain's reducibility conjunct so
the refutation has a round to run in. -/
theorem wp_crossed_of_canonical {k' : Cont} {chain : List PanicEntry}
    {Φ Ψ : Unit → IProp GF}
    (hdr : ∀ (chain : List PanicEntry) (σ : ExecState),
      PrimStep.Reducible ((Config.panicking chain k' : Config), σ)) :
    WP (Config.panicking chain .stop) @ Stuckness.NotStuck ; E {{ Ψ }}
      ⊢ WP (Config.panicking chain k') @ Stuckness.NotStuck ; E {{ Φ }} := by
  rewrite [wp_unfold.to_eq, wp_unfold.to_eq]
  simp only [wp.pre,
    show (ToVal.toVal (Config.panicking chain .stop) : Option Unit)
      = none from rfl,
    show (ToVal.toVal (Config.panicking chain k') : Option Unit)
      = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ [$] with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact hdr chain σ₁
  · -- receive an arbitrary step of the filled drain, then refute from
    -- the canonical side: render step → `.panicked` → irreducible.
    iintro %e₂ %σ₂ %eₜ %Hstep2 Hcred
    -- the canonical crossed configuration's own reducibility pins the
    -- render step
    obtain ⟨obsc, ec, σc, eₜc, hstepc⟩ := Hred
    have hobs : obs = [] := by
      cases Hstep2; rfl
    obtain ⟨msg, hec, hσc⟩ : ∃ msg, ec = .panicked msg ∧ σc = σ₁ := by
      cases hstepc with
      | step st => exact step_panicking_stop_inv st
    rw [hec, hσc] at hstepc
    have hcanstep : (((Config.panicking chain .stop : Config), σ₁)
        -<obs>-> ((.panicked msg : Config), σ₁, eₜc)) := by
      subst hobs
      cases hstepc with
      | step st => exact GoPrimStep.step st
    icases H $$ %(Config.panicked msg) %σ₁ %eₜc %hcanstep Hcred with H
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨Hσ, Hp, Hforks⟩
    -- interrogate the rendered abort: irreducible at NotStuck → False
    rewrite [(wp_unfold (e := (Config.panicked msg : Config))).to_eq]
    simp only [wp.pre,
      show (ToVal.toVal (Config.panicked msg) : Option Unit)
        = none from rfl]
    icases Hp $$ %σ₁ %(ns + 1) %(List.nil (α := Unit)) %obs'
        %(nt + eₜc.length) Hσ with >⟨%Hred2, Hp2⟩
    exact absurd Hred2 not_reducible_panicked

/-! ## The bind rule -/

/-- **THE BIND RULE** (`wp_bind` for the plug geometry — G-BIND §4.1
route (b)): a WP of the callee's CANONICAL configuration whose
postcondition continues as a WP of the context resumption `.next k'`
proves the WP of the FILLED configuration. One application composes a
function's spec into any call site whose context satisfies the three
premises; the per-arity enter laws' "widening owed" surface reduces to
entry steps only (G-CALLS absorbs them).

Quantifier-audit line: this is the rule discharging the **∀ caller
contexts** quantifier — never by per-context instances. -/
theorem wp_plug_bind {env' : LocalEnv} {k' : Cont}
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    (hdr : ∀ (chain : List PanicEntry) (σ : ExecState),
      PrimStep.Reducible ((Config.panicking chain k' : Config), σ)) :
    ⊢ iprop(∀ (E : CoPset) (c : Config) (Φ : Unit → IProp GF),
        ⌜hasBarrierC c = true⌝ →
        (WP c @ Stuckness.NotStuck ; E
          {{_v, WP (Config.next k') @ Stuckness.NotStuck ; E {{ Φ }} }}) -∗
        WP (plugC env' k' c) @ Stuckness.NotStuck ; E {{ Φ }}) := by
  iloeb as IH
  iintro %E %c %Φ %hbar H
  have htv : (ToVal.toVal c : Option Unit) = none :=
    toVal_none_of_ne_next_stop (ne_next_stop_of_hasBarrierC hbar)
  have htv' : (ToVal.toVal (plugC env' k' c) : Option Unit) = none :=
    toVal_none_of_ne_next_stop (plugC_ne_next_stop hbar)
  rewrite [(wp_unfold (e := c)).to_eq,
    (wp_unfold (e := plugC env' k' c)).to_eq]
  simp only [wp.pre, htv, htv', Nat.repeat]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ [$] with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact reducible_plugC hmf hrc hbar Hred
  · iintro %e₂ %σ₂ %eₜ %Hstep2 Hcred
    obtain ⟨hobs, hetl, d, rfl, hstep, hcls⟩ :=
      primStep_plugC_inv hmf hrc hbar Hstep2
    have hcanstep : (((c : Config), σ₁) -<obs>-> ((d : Config), σ₂, eₜ)) := by
      subst hobs; subst hetl
      exact GoPrimStep.step hstep
    icases H $$ %d %σ₂ %eₜ %hcanstep Hcred with >H
    imodintro; imodintro
    imod H; imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨$, H, $⟩
    imodintro
    rcases hcls with hbd | rfl | ⟨chain, rfl⟩
    · -- the barrier survives: Löb
      iapply IH $$ %E %d %Φ %hbd H
    · -- the callee exited: the value case — `plugC (.next .stop)` is
      -- the context resumption, and the postcondition IS its WP
      rw [show plugC env' k' (Config.next Cont.stop) = Config.next k'
        from rfl]
      ihave H2 : iprop(|={E}=>
          WP (Config.next k') @ Stuckness.NotStuck ; E {{ Φ }}) $$ [H]
      · iapply (wp_value_fupd' (v := ())).1 $$ H
      iapply fupd_wp $$ H2
    · -- the panic crossed: refute from the canonical side
      rw [show plugC env' k' (Config.panicking chain Cont.stop)
        = Config.panicking chain k' from rfl]
      iapply (wp_crossed_of_canonical hdr) $$ H

/-- The bind rule in the entailment shape call-site walks apply. -/
theorem wp_bind_plug {env' : LocalEnv} {k' : Cont} {c : Config}
    {Φ : Unit → IProp GF}
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    (hdr : ∀ (chain : List PanicEntry) (σ : ExecState),
      PrimStep.Reducible ((Config.panicking chain k' : Config), σ))
    (hbar : hasBarrierC c = true) :
    (WP c @ Stuckness.NotStuck ; E
      {{_v, WP (Config.next k') @ Stuckness.NotStuck ; E {{ Φ }} }})
      ⊢ WP (plugC env' k' c) @ Stuckness.NotStuck ; E {{ Φ }} := by
  iintro H
  iapply (wp_plug_bind hmf hrc hdr) $$ %E %c %Φ %hbar H

/-! ## `hdrain` dischargers (one constructor each, for the concrete
contexts call sites exhibit) -/

/-- Pop-headed contexts drain: the passthrough arm steps. -/
theorem drain_reducible_of_passthrough {k' k₂ : Cont}
    (h : panicPassthrough k' = some k₂) :
    ∀ (chain : List PanicEntry) (σ : ExecState),
      PrimStep.Reducible ((Config.panicking chain k' : Config), σ) :=
  fun _ _ => ⟨[], _, _, _,
    GoPrimStep.step (step_panicking_of_passthrough h)⟩

/-- Defer-free frame-headed contexts drain: the frame pops. -/
theorem drain_reducible_frame {t : List (TargetShape × List Expr)}
    {te : LocalEnv} {r : List Loc} {k : Cont} {w : Bool} :
    ∀ (chain : List PanicEntry) (σ : ExecState),
      PrimStep.Reducible
        ((Config.panicking chain (.frame t te r [] k w) : Config), σ) :=
  fun _ _ => ⟨[], _, _, _, GoPrimStep.step step_panicking_frame_empty⟩

end

end GoLean.Iris
