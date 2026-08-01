import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.Ghost
import GoLeanProofs.Tactics.GoWalk

/-!
# Pure control-step laws
Deterministic, state-preserving control transitions: sequencing, return
unwinding, frame fall-through.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

-- The uniform Hpuredet closer names every function a rule-premise might
-- need; the unused-arg linter misfires per-law (an argument unused in one
-- law's rule set is load-bearing in another's).
set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The D1 splice** (same-env governing sequence): entering a `seqn`
under a `.seq` at the SAME environment splices the two statement lists.
Lives here (rather than restated per walk file) because it is `seqCont`'s
own algebra and because `go_walk`'s between-step normalization needs it —
it is the rewrite every hand walk ran after `wp_seqn`. -/
@[go_walk_simp]
theorem seqCont_splice {ss rest : List Stmt} {env : LocalEnv} {k : Cont} :
    seqCont ss env (.seq rest env k) = .seq (ss ++ rest) env k := by
  simp [seqCont]

/-- `seqn` is a pure, deterministic control step: `.exec (.seqn ss) env k`
reduces only to `.next (seqCont ss.toList env k)` with the state unchanged
(D1: under a same-env governing seq this splices; at a concrete non-seq
continuation `seqCont` reduces definitionally to the old wrap, so existing
applications are unchanged). A genuine weakest-precondition law over
GoCore's actual `Step` relation. -/
@[go_walk_law]
theorem wp_seqn {ss env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (seqCont ss.toList env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (seqCont ss.toList env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (seqCont ss.toList env k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic frame pop for VOID frames: normal completion of a
body with no results and no targets resumes the caller (`Step.frameFall`
with empty read/store legs — D2-proper: value-returning frame exits are
state-reading and get their own law in `Laws/Call`). -/
@[go_walk_law]
theorem wp_frame_fall {k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.frame [] [] [] k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step (Step.frameFall (targets := []) (results := []) rfl rfl)⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic step: enter a declaration-free block
(`Step.block` with the empty `DeclsR` leg) — the shape the frontend wraps
every function body and control-flow branch in. The block's sequence runs
under a pushed (empty) scope; declaration-carrying blocks get their own law
when a proof first needs one. -/
@[go_walk_law]
theorem wp_block_nil {ss : Array Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.next (.seq ss.toList env.pushScope k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.block #[] ss) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (.seq ss.toList env.pushScope k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step (Step.block rfl)⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic step: advance a sequence to its next statement
(`Step.seqNext`). -/
@[go_walk_law]
theorem wp_seq_next {t : Stmt} {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec t env (.seq rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq (t :: rest) env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.exec t env (.seq rest env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.seqNext⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic step: `return` starts unwinding (env-free after
D2-proper: the frame reads results from call-time-pinned locations). -/
@[go_walk_law]
theorem wp_return {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning k) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec .returnStmt env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.returnStmt⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic step: `return` unwinds past a sequence continuation,
discarding that scope (`Step.seqReturn`). -/
@[go_walk_law]
theorem wp_seq_return {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning k) @ s ; E {{ Φ }}) ⊢
      WP (Config.returning (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.seqReturn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

/-- Pure, deterministic control step: an exhausted sequence pops to its
continuation (discarding that scope's env — CEK scope exit). Mirror of
`wp_seqn` for `Step.seqDone`. -/
@[go_walk_law]
theorem wp_seq_done {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq [] env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step Step.seqDone⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st <;> simp_all [stmtPlan, loadMany, storeMany, allocDecls]))
  iexact H

end

/-! ## The `go_walk` normalization set (Lean-core half)

`go_walk` runs `simp only [go_walk_simp]` between steps; these are the
rewrites the hand walks ran there. Configuration-shaped and confluent:
list-append normal forms (a spliced `seqCont` produces `(ss ++ rest)`),
array-to-list, the `if` a delivered `Bool` condition leaves behind, and
`String` literal comparison (name resolution through `LocalEnv.declare`
layers). The GoCore-specific half is tagged at each lemma's definition. -/
attribute [go_walk_simp]
  List.toList_toArray List.cons_append List.nil_append List.append_nil
  List.singleton_append List.append_eq Option.isSome_none Option.toList_none
  Option.toList_some List.length_cons List.length_nil
  List.reverse_cons List.reverse_nil
  reduceIte String.reduceBEq Bool.false_eq_true

/-! `reduceGroundDecide` reduces a GROUND `decide p` to `true`/`false`.

A machine comparison delivers `.bool (decide …)`: `wp_strict_apply_pure`
computes the operator's answer, and until that `decide` is a literal the
`if` it feeds cannot reduce and no law matches the next configuration.
(The hand walks avoided this by SUPPLYING the answer — `(out := .bool
true)` — which is exactly the guess the walk must not have to make.)
Ground only: an OPEN `decide` is left alone. -/
open Lean Meta in
simproc [go_walk_simp] reduceGroundDecide (Decidable.decide _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withDefault <| whnf e
  if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then
    return .done { expr := r }
  return .continue

end GoLean.Iris
