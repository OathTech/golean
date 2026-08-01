import Iris.ProgramLogic.WeakestPre
import Iris.ProofMode
import GoLean.GoCore.MachineSound
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Init
import GoLeanProofs.SurfaceBridge

/-!
# The golden WP walk (R3 rewrite over the fine-grained machine)

The full walk for the frontend's pinned lowering, composed from the new
per-step laws: `wp_inc_body` (the `*p = *p + 1` body — var read, deref
apply, add apply, store), `wp_call_inc_stmt` (the `inc(&x)` call
statement end to end), `wp_incViaCall_body` (init, seeded assign, two
`inc` calls, result write-back, return), and `wp_goldenDriver` — the
exit-form WP for the seeded driver `r = incViaCall()`: `{r ↦ 0} … {r ↦ 2}`
over any bundle with the golden program/method pins. The old `*_computes`
existential-address readouts are RETIRED (superseded by the Surface
pinned forms), as are the fragment-shape lemmas (the machine's soundness
is total).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface (outCell0 outCell2 goldenDriver outEnv)

namespace GoLean.Iris.GoldenSlice

set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- The `inc` body walk: `*p = *p + 1` under the frame environment. -/
theorem wp_inc_body {pa xa : Addr} {m : Int} {k} :
    pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base xa)⟩ : HeapCell)
      ∗ xa.id ↦ (⟨some (.int .int), .int m .int⟩ : HeapCell)
      ∗ (pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base xa)⟩ : HeapCell)
          ∗ xa.id ↦ (⟨some (.int .int), .int (IntKind.normalize .int (m + 1)) .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec incFunc.body [[("p", Loc.base pa)]] k) @ s ; E {{ Φ }} := by
  iintro ⟨Hp, Hx, Hcont⟩
  simp only [incFunc]
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
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_assign_start (te := .var "p") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_eval_var
    (cell := ⟨some (.pointer (.int .int)), .addr (.base xa)⟩) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_eval_strict (op := .add)
    (e₁ := .deref (.var "p") (.int .int)) (rest := [.intLit 1 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_strict (op := .deref (.int .int)) (e₁ := .var "p")
    (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply (wp_eval_var
    (cell := ⟨some (.pointer (.int .int)), .addr (.base xa)⟩) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_strict_apply_deref (cell := ⟨some (.int .int), .int m .int⟩))
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  rw [show IntKind.normalize .int 1 = 1 from by decide]
  iapply (wp_strict_apply_pure
    (out := .int (IntKind.normalize .int (m + 1)) .int) (happly := by
      intro σ
      have h1 : IntKind.compatibleResult .int .int = some .int := rfl
      simp [applyStrictOp, intBinaryResult, valueAsIntValue, h1,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply (wp_assign_store (oldcell := ⟨some (.int .int), .int m .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.normalize .int (m + 1)) .int⟩)
    (fun σ₁ _ht hlook => storeLoc_int_cell hlook (m + 1)))
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply Hcont $$ [$Hp $Hx]

/-- The `inc(&x)` call statement, end to end: dispatch → argument → frame
entry (the `wp_call_enter_inc` witness) → body → frame fall. The dead
parameter cell is dropped (affine). -/
theorem wp_call_inc_stmt {env : LocalEnv} {xa : Addr} {m : Int} {k}
    (hx : LocalEnv.lookup env "x" = some (.base xa))
    (hprog : GoCoreGS.prog GF = sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    xa.id ↦ (⟨some (.int .int), .int m .int⟩ : HeapCell)
      ∗ (xa.id ↦ (⟨some (.int .int), .int (IntKind.normalize .int (m + 1)) .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[] ⟨"inc"⟩ #[.ref "x"]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hx, Hcont⟩
  iapply (wp_call_first_arg (a := .ref "x") (rest := []) rfl rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply (wp_eval_ref hx)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply (wp_call_enter_inc (locs := []) hprog hmeths)
  iintro %pa Hp
  iapply wp_inc_body
  isplitl [Hp]
  · iexact Hp
  isplitl [Hx]
  · iexact Hx
  iintro ⟨Hp, Hx⟩
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply Hcont $$ Hx

/-- The `incViaCall` body walk: declare `x`, seed 0, two `inc(&x)` calls,
write `x` to the pinned result cell, return. The dead `x` cell is
dropped. -/
theorem wp_incViaCall_body {ra : Addr} {k}
    (hprog : GoCoreGS.prog GF = sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    ra.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .int), .int 2 .int⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec incViaCallFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [incViaCallFunc]
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
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply wp_init_int
  iintro %xa Hx
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_assign_lit (n := 0) (kind := .int)
    (w := .int 0 .int) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  rw [show IntKind.normalize .int 0 = 0 from by decide] at *
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_call_inc_stmt (m := 0) rfl hprog hmeths)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  rw [show IntKind.normalize .int (0 + 1) = 1 from by decide] at *
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_call_inc_stmt (m := 1) rfl hprog hmeths)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  rw [show IntKind.normalize .int (1 + 1) = 2 from by decide] at *
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply (wp_assign_start (te := .ref "$res0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply (wp_eval_ref (loc := .base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  iapply (wp_eval_var (cell := ⟨some (.int .int), .int 2 .int⟩) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 2 .int⟩)
    (fun σ₁ _ht hlook => by
      have h := storeLoc_int_any (mkind := .int) hlook 2
      rw [show IntKind.normalize .int 2 = 2 from by decide] at h
      exact h))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply Hcont $$ Hr

/-- **The generic golden call walk**: `x = incViaCall()` into any target
cell (any prior value), any environment binding, any continuation —
dispatch → target address → frame entry → body → value frame exit. -/
theorem wp_goldenCall {ta : Addr} {w : GoValue} {x : String} {env k}
    (hres : LocalEnv.lookup env x = some (.base ta))
    (hprog : GoCoreGS.prog GF = sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .int), .int 2 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var x] ⟨"incViaCall"⟩ #[]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
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
  iapply (wp_call_enter_incViaCall (tl := .base ta) hprog hmeths)
  iintro %ra Hres
  iapply (wp_incViaCall_body hprog hmeths)
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iapply (wp_frame_return_int (m := 2) (kind := .int) (tkind := .int)
    (w := w))
  isplitl [Hres]
  · iexact Hres
  isplitl [Hr]
  · iexact Hr
  iintro ⟨Hres, Hr⟩
  rw [show IntKind.normalize .int 2 = 2 from by decide] at *
  iapply Hcont $$ Hr

/-- **The invariant-form golden call walk**: the target register lives in
an Iris invariant (never owned by the walk — the call only computes its
ADDRESS before the single frame-exit write, which opens and re-closes the
invariant via `wp_frame_return_int_inv`). The rest of the walk is
identical to `wp_goldenCall`. -/
theorem wp_goldenCall_inv {ta : Addr} {x : String} {env k} {N : Namespace}
    {S : HeapCell → Prop} {Icnt : IProp GF}
    (hres : LocalEnv.lookup env x = some (.base ta))
    (hprog : GoCoreGS.prog GF = sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[])
    (hN : ↑N ⊆ E)
    (hint : ∀ cell, S cell → ∃ w', cell = ⟨some (.int .int), w'⟩)
    (hopen : Icnt ⊢ iprop(∃ cell, ⌜S cell⌝ ∗ ta.id ↦ cell))
    (hclose : (iprop(ta.id ↦ (⟨some (.int .int), .int (IntKind.normalize .int 2) .int⟩ : HeapCell)) : IProp GF) ⊢ Icnt) :
    Iris.inv N Icnt ∗ WP (Config.next k) @ s ; E {{ Φ }}
      ⊢ WP (Config.exec (.call #[.var x] ⟨"incViaCall"⟩ #[]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨HinvT, Hnext⟩
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
  iapply (wp_call_enter_incViaCall (tl := .base ta) hprog hmeths)
  iintro %ra Hres
  iapply (wp_incViaCall_body hprog hmeths)
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iapply (wp_frame_return_int_inv (m := 2) (kind := .int) (tkind := .int)
    hN hint hopen hclose)
  isplitl [HinvT]
  · iexact HinvT
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iexact Hnext

/-- **The golden driver, exit form**: `{r ↦ 0} r = incViaCall() {r ↦ 2}`
as the WP entailment the Surface exit theorems consume. -/
theorem wp_goldenDriver
    (hprog : GoCoreGS.prog GF = sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) outCell0
      ⊢ WP (Config.exec goldenDriver outEnv .stop) {{ _v, embed outCell2 }} := by
  simp only [outCell0, outCell2, embed]
  iintro Hr
  iapply (wp_goldenCall (w := .int 0 .int) rfl hprog hmeths)
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

end GoLean.Iris.GoldenSlice
