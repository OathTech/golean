import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Init
import GoLeanProofs.Specs.GoldenSliceWP
import GoLeanProofs.Tactics.GoWalk

/-!
# The recover composition over the PINNED ACTUAL LOWERING
(proof-corpus catch-up arc, slice B)

`wp_recover_catch_seven` walked the hand-authored core shape; this module
pays the frontend-lowering twin the manifest recorded as owed: the same
defer/panic/recover composition, but over `GoldenRecover.recoverLowered` —
the frontend's actual lowering of
`Corpus/coverage/exec/panic-recover/recover-direct/main.go`, pinned by
`scripts/check-golden`. The lowering's deltas from the core shape are
exactly what the walk exercises beyond it: block wrappers (pushed scopes),
recover's value routed through the `$c0` temporary (an interface-typed
`initialization` + assignment, with the recover continuation walk crossing
the assign frames), the `if` condition reading `$c0` back from its cell,
and the FALL-path value frame exit (no explicit `return` — Go's "the
surrounding function returns normally", `wp_frame_fall_int`'s witness).

Top: `recoverFuncSpec` — the `GoFuncSpec` form ("`recoverDirect()` needs
no heap and returns 7"), through the same exit pipe as `goldenFuncSpec`.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris.GoldenRecover

set_option linter.unusedSimpArgs false

/-- The panic payload after the lowering's `any`-conversion. -/
abbrev payload : GoValue :=
  .interface .string (.string ⟨#[98, 111, 111, 109, 45, 100, 105, 114, 101, 99, 116]⟩)

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The composition walk over the actual lowering**: from
`recoverDirect`'s lowered body under its own call frame (result cell `ra`
holding 0, pinned as the frame's result location), through defer
registration, the panic, the panic-path drain of the lambda-lifted
closure, `$c0 := recover()`, the guarded write of 7 through the captured
pointer, the recovered marker cancelling the unwind — ending at the
frame's FALL exit still pending (`Config.next` at the frame), with the
result cell holding 7. The `$c0` cell and the capture-parameter cell are
dropped (affine). -/
theorem wp_recoverDirect_body {ra : Addr} {tl : Loc} {k}
    (hprog : GoCoreGS.prog GF = recoverLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    ra.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .int), .int 7 .int⟩ : HeapCell)
          -∗ WP (Config.next (.frame [tl] [.base ra] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec recoverDirectFunc.body [[("result", Loc.base ra)]]
              (.frame [tl] [.base ra] [] k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [recoverDirectFunc]
  -- the body block, the defer registration, `panic("boom-direct")`
  go_walk
  -- the payload's conversion to `any`
  go_walk_step (wp_strict_apply_pure (out := payload) (happly := fun σ => by
    simp [applyStrictOp, canonicalDynamicTy, canonicalTy, canonicalTyFuel,
      Ty.mentionsUnsupported, payload, Bind.bind, Except.bind]))
  -- the unwind of the statement spine
  go_walk
  -- the deferred closure's frame, on the PANIC path
  go_walk_step (wp_panic_frame_defer_cap1
    (func := litFunc)
    (cv' := .addr (.base ra))
    (hfind := by rw [hprog, recoverLowered_funcs_eq]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel])) as [pa, Hp]
  -- the closure body: block, then `var $c0 any` (interface default: nil)
  simp only [litFunc]
  go_walk
  go_walk_step (wp_init (v := .nil) (hdef := fun _ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [ca, Hc]
  -- `$c0 = recover()`: the walk crosses the assign frames, lands on the
  -- marker under the drain frame and marks the chain
  go_walk with [recoverResult, markNewestRecovered]
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.interface ⟨"any"⟩), .nil⟩)
    (newcell := ⟨some (.interface ⟨"any"⟩), payload⟩)
    (fun σ₁ _ht hlook => by
      unfold storeLoc
      rw [hlook]
      simp [normalizeValueForTy, normalizeValueForTyFuel, panicPayload,
        Bind.bind, Except.bind]))
  -- `if $c0 != nil { *result$cap = 7 }`
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, panicPayload, valueEq, valueEqFuel,
        Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 7 .int⟩)
    (fun σ₁ _ht hlook => by
      have h := storeLoc_int_cell hlook 7
      rw [show IntKind.normalize .int 7 = 7 from by decide] at h
      exact h))
  -- the closure falls off its end; the recovered marker cancels the unwind
  go_walk_finish Hcont

/-- **The generic recover call walk**: `x = recoverDirect()` into any
target cell (any prior value), any environment binding, any continuation.
The frame exit is the FALL path (`wp_frame_fall_int`'s witness): the
function ends by recovered-panic fall-through, never by `return`. -/
theorem wp_recoverCall {ta : Addr} {w : GoValue} {x : String} {env k}
    (hres : LocalEnv.lookup env x = some (.base ta))
    (hprog : GoCoreGS.prog GF = recoverLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .int), .int 7 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var x] ⟨"recoverDirect"⟩ #[]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Ht, Hcont⟩
  iapply (wp_call_first_target (te := .ref x) (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc₁
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc₂
  iapply (wp_call_enter_ret1
    (func := recoverDirectFunc) (tl := .base ta) (dv := .int 0 .int)
    (hfind := by rw [hprog, recoverLowered_funcs_eq]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra Hres
  iapply (wp_recoverDirect_body hprog hmeths)
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iapply (wp_frame_fall_int (m := 7) (kind := .int) (tkind := .int) (w := w))
  isplitl [Hres]
  · iexact Hres
  isplitl [Ht]
  · iexact Ht
  iintro ⟨Hres, Ht⟩
  rw [show IntKind.normalize .int 7 = 7 from by decide] at *
  iapply Hcont $$ Ht

end

end GoLean.Iris.GoldenRecover

namespace GoLean.Surface

open Iris Iris.ProgramLogic
open GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenRecover

/-- **The recover function spec, as a statement** (the arc's slice-B
target): "`recoverDirect()` takes no arguments, needs no heap, and
returns 7" — over the PINNED ACTUAL LOWERING, ∀-quantified over the
caller's target cell, its prior value, and the frame. -/
def recoverFuncSpec_statement : Prop :=
  GoFuncSpec recoverLowered.typeDefs.toList recoverLowered.funcs
    recoverLowered.methods ⟨"recoverDirect"⟩ .int #[] .emp
    (fun n => .pure (n = 7))

/-- **The recover function spec, proven** — the composition walk applied
at the quantified target through the generic exit pipe (`goSpec_of_wp`),
exactly the `goldenFuncSpec` shape. -/
theorem recoverFuncSpec : recoverFuncSpec_statement := by
  unfold recoverFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (wp_recoverCall (w := w) (x := "$callres") rfl hprog hmeths)
  isplitl [H0]
  · iexact H0
  iintro H2
  iapply (wp_value' (v := ()))
  iexists (7 : Int)
  isplitl [H2]
  · iexact H2
  · ipureintro
    rfl

end GoLean.Surface
