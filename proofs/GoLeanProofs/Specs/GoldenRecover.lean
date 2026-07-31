import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Init
import GoLeanProofs.Specs.GoldenSliceWP

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
open GoLean.Iris.GoldenSlice (seqCont_splice)

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
  -- the body block: pushed scope over [defer, panic]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  -- defer recoverDirect$lit0(&result): evaluate the closure, register
  iapply wp_defer_stmt
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_eval_ref (loc := Loc.base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_strict_apply_pure
    (out := .funcVal ⟨"recoverDirect$lit0"⟩ [.addr (.base ra)])
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_defer_register_noargs (hcallee := rfl) (hpush := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  -- panic("boom-direct"): payload converts to any, unwinding starts
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply wp_panic_stmt
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply wp_eval_stringLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply (wp_strict_apply_pure (out := payload) (happly := fun σ => by
    simp [applyStrictOp, canonicalDynamicTy, canonicalTy, canonicalTyFuel,
      Ty.mentionsUnsupported, payload, Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply wp_panic_value
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  -- unwind the statement spine, drain the deferred closure on the panic path
  iapply (wp_panic_unwind (hpass := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_panic_frame_defer_cap1
    (func := litFunc)
    (cv' := .addr (.base ra))
    (hfind := by rw [hprog, recoverLowered_funcs_eq]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel]))
  iintro %pa Hp
  -- the closure body: block, then $c0 := recover()
  simp only [litFunc]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc17
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc18
  -- var $c0 any (interface default: nil)
  iapply (wp_init (v := .nil) (hdef := fun _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ca Hc
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc19
  -- $c0 = recover(): the continuation walk crosses the assign frames,
  -- lands on the marker under the drain frame, marks the chain
  iapply (wp_assign_start (te := .ref "$c0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc20
  iapply (wp_eval_ref (loc := Loc.base ca) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc21
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc22
  iapply (wp_recover (hrec := rfl))
  simp only [recoverResult, markNewestRecovered, Bool.false_eq_true, reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc23
  -- store the recovered payload into $c0's interface-typed cell
  iapply (wp_assign_store
    (oldcell := ⟨some (.interface ⟨"any"⟩), .nil⟩)
    (newcell := ⟨some (.interface ⟨"any"⟩), payload⟩)
    (fun σ₁ _ht hlook => by
      unfold storeLoc
      rw [hlook]
      simp [normalizeValueForTy, normalizeValueForTyFuel, panicPayload,
        Bind.bind, Except.bind]))
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  -- if $c0 != nil: read the cell back, compare against nil
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc24
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc25
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc26
  iapply (wp_eval_var
    (cell := ⟨some (.interface ⟨"any"⟩), payload⟩) rfl)
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc27
  iapply (wp_eval_strict_nullary_pure (hplan := rfl)
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc28
  iapply (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, panicPayload, valueEq, valueEqFuel,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc29
  iapply wp_if_bool
  simp only [reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc30
  -- the guarded branch block: *result$cap = 7 through the captured pointer
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc31
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc32
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc33
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc34
  iapply (wp_assign_start (te := .var "result$cap") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc35
  iapply (wp_eval_var
    (cell := ⟨some (.pointer (.int .int)), .addr (.base ra)⟩) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc36
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc37
  iapply (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.normalize .int 7) .int⟩)
    (fun σ₁ _ht hlook => storeLoc_int_cell hlook 7))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  -- the closure falls off its end; the recovered marker cancels the unwind
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc38
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc39
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc40
  iapply (wp_panic_resume_recovered (hrec := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc41
  rw [show IntKind.normalize .int 7 = 7 from by decide]
  iapply Hcont $$ Hr

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
    ⟨"recoverDirect"⟩ .int #[] .emp
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
