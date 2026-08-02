import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.Statements
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

/- `recoverFuncSpec_statement` moved to `Specs/Statements.lean` — the
Iris-free statement layer (comparator-judge sprint, 2026-08-02). -/

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

/-! ### The first-order readout (audit response 2026-08-01)

The TCB/layering doctrine (`docs/2026-08-01_tcb-and-layering-doctrine.md`
§1, ladder rung 2) makes the first-order readout mandatory beside any
`GoFuncSpec*` headline; `recoverFuncSpec` predates the doctrine and
shipped without one (pre-merge audit finding). This is `goldenReturnsTwo`'s
shape over the recover pin: read the triple out at a pinned address. -/

/- `recoverOut`/`recoverOutEnv` (the readout's seeded state) moved to
`Specs/Statements.lean`. -/

/-- **The first-order readout**: every terminating run of
`$callres = recoverDirect()` from the seeded one-cell state leaves
`int(7)` at base address 0 — the recover-caught write, observed by
`execStmt`/`loadLoc` with no separation logic in the statement. -/
theorem recoverReturnsSeven
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel recoverOutEnv
        { types := recoverLowered.typeDefs.toList,
          functions := recoverLowered.funcs, methods := recoverLowered.methods,
          heap := recoverOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) := by
  have htriple := (recoverFuncSpec 0 (.int 0 .int)).1
  have hres := htriple recoverOut 1 (heapletOf recoverOut) (∅ : Heaplet)
    { bounded := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rfl
      disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := ⟨heapletOf recoverOut, ∅, rfl, rfl,
        fun k => .inr (by
          rw [heaplet_get?_eq]
          exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)),
        fun k c => ⟨fun h => .inl h, fun h => h.elim id (fun h0 => by
          rw [heaplet_get?_eq,
            LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h0
          cases h0)⟩⟩ }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn7, rfl⟩ := hp2
  subst hn7
  have hget : h.get? 0 = some ⟨some (.int .int), .int 7 .int⟩ := by
    rw [hcov]
    exact Or.inl (by
      rw [hp1, heaplet_get?_eq, heaplet_insert_eq]
      exact LawfulPartialMap.get?_insert_eq rfl)
  have := hsub 0 ⟨some (.int .int), .int 7 .int⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at this
  exact loadLoc_base_of_lookup this

end GoLean.Surface
