import Iris.ProgramLogic.WeakestPre
import Iris.ProofMode
import GoLean.GoCore.MachineSound
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Laws.Bind
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenTargets
import GoLeanProofs.Specs.CallchainProgram

/-!
# C-05 `callchain` — the G-BIND gate instance (iris-corpus-plan §5.2)

The first corpus-plan case: nested static calls with a defer, composed
THROUGH THE BIND RULE. Every callee's spec is proved ONCE at its
canonical configuration (the plug barrier `.frame [] [] [] [] .stop
false` below the body) and applied at its call sites via
`wp_bind_plug` (`Laws/Bind.lean`) — three applications:

1. `ccDouble`'s spec at the call site inside `ccWork`;
2. `ccBump`'s spec at the DEFER-DRAIN site inside `ccWork` (the drain
   entry frame is also a plug image — `env' = []`);
3. `ccWork`'s spec at the call site inside `ccCaller`.

No callee body is inlined at any call site — that is the gate
criterion (§4.1: "proved once through `wp_bind` at an open caller
context"), and these walks are the bind rule's and the new
entry/defer laws' non-vacuity witnesses.

Subject identity: `callchainLowered` enters only through the golden
pin (`Specs/CallchainProgram.lean`, `scripts/check-golden`);
`callchainLowered_funcs_eq` is the kernel bridge to the named
literals the walks mention.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Frame
open GoLean.Surface (outCell0 outEnv HProp GoSpec GoTriple ProgressExec
  Heaplet heapletOf sat InitialSplit)

namespace GoLean.Iris.Callchain

open GoLean.Iris

set_option linter.unusedSimpArgs false

/-- `ccDouble` as a named literal (`callchainLowered_funcs_eq` is the
kernel bridge to the pin). -/
def ccDoubleFunc : Func :=
  { id := ⟨"ccDouble"⟩,
    args := #[⟨"dst", .pointer (.int .int)⟩, ⟨"x", .int .int⟩],
    results := #[],
    body := .block #[] #[.seqn #[.assign (.addr (.var "dst"))
      (.add (.var "x") (.var "x"))]] }

/-- `ccBump` as a named literal. -/
def ccBumpFunc : Func :=
  { id := ⟨"ccBump"⟩,
    args := #[⟨"dst", .pointer (.int .int)⟩],
    results := #[],
    body := .block #[] #[.seqn #[.assign (.addr (.var "dst"))
      (.add (.deref (.var "dst") (.int .int)) (.intLit 1 .int))]] }

/-- `ccWork` as a named literal. -/
def ccWorkFunc : Func :=
  { id := ⟨"ccWork"⟩,
    args := #[⟨"dst", .pointer (.int .int)⟩, ⟨"x", .int .int⟩],
    results := #[],
    body := .block #[] #[
      .deferCall (.funcVal ⟨"ccBump"⟩ #[]) #[.var "dst"],
      .call #[] ⟨"ccDouble"⟩ #[.var "dst", .var "x"]] }

/-- `ccCaller` as a named literal. -/
def ccCallerFunc : Func :=
  { id := ⟨"ccCaller"⟩,
    args := #[⟨"x", .int .int⟩],
    results := #[⟨"$res0", .int .int⟩],
    body := .block #[] #[
      .seqn #[.initialization ⟨"y", .int .int⟩,
              .assign (.var "y") (.intLit 0 .int)],
      .call #[] ⟨"ccWork"⟩ #[.ref "y", .var "x"],
      .seqn #[.assign (.var "$res0") (.add (.var "y") (.intLit 3 .int)),
              .returnStmt]] }

/-- Kernel bridge: the named literals ARE the pinned lowering's
functions. -/
theorem callchainLowered_funcs_eq :
    callchainLowered.funcs = #[ccDoubleFunc, ccBumpFunc, ccWorkFunc,
      ccCallerFunc] := rfl

/-- The canonical below-body context: the plug barrier. -/
abbrev KB : Cont := .frame [] [] [] [] .stop false

/-- Pointer-to-int cell shorthand. -/
abbrev ptrCell (ya : Addr) : HeapCell :=
  ⟨some (.pointer (.int .int)), .addr (.base ya)⟩

/-- Int cell shorthand. -/
abbrev intCell (n : Int) : HeapCell := ⟨some (.int .int), .int n .int⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **`ccDouble`'s canonical spec**: at the canonical configuration
(body over the plug barrier), `*dst = x + x` writes the doubled input
through the pointer and the run terminates at the value. Proved once;
applied at call sites only through `wp_bind_plug`. -/
theorem wp_ccDouble_canonical {pa xa ya : Addr} {xv yv : Int} :
    pa.id ↦ ptrCell ya ∗ xa.id ↦ intCell xv ∗ ya.id ↦ intCell yv
      ∗ (pa.id ↦ ptrCell ya ∗ xa.id ↦ intCell xv
          ∗ ya.id ↦ intCell (IntKind.normalize .int (xv + xv)) -∗ Φ ())
      ⊢ WP (Config.exec ccDoubleFunc.body
            [[("x", Loc.base xa), ("dst", Loc.base pa)]] KB)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hp, Hx, Hy, Hcont⟩
  simp only [ccDoubleFunc]
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
  iapply (wp_assign_start (e := .var "dst") (sh := .chain [])
    (ops := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_eval_var (cell := ptrCell ya) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_tgtop_rhs rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_eval_strict (op := .add) (e₁ := .var "x")
    (rest := [.var "x"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_var (cell := intCell xv) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply (wp_eval_var (cell := intCell xv) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply (wp_strict_apply_pure
    (out := .int (IntKind.normalize .int (xv + xv)) .int) (happly := by
      intro σ
      have h1 : IntKind.compatibleResult .int .int = some .int := rfl
      simp [applyStrictOp, intBinaryResult, valueAsIntValue, h1,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (oldcell := intCell yv)
    (newcell := intCell (IntKind.normalize .int (xv + xv)))
    (fun σ₁ _ht hlook => storeLoc_int_cell hlook (xv + xv)))
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  iapply wp_stores_done_nil
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  iapply (wp_value' (v := ()))
  iapply Hcont $$ [$Hp $Hx $Hy]

/-- **`ccBump`'s canonical spec**: `*dst = *dst + 1` through the
pointer, at the canonical configuration. -/
theorem wp_ccBump_canonical {pa ya : Addr} {yv : Int} :
    pa.id ↦ ptrCell ya ∗ ya.id ↦ intCell yv
      ∗ (pa.id ↦ ptrCell ya
          ∗ ya.id ↦ intCell (IntKind.normalize .int (yv + 1)) -∗ Φ ())
      ⊢ WP (Config.exec ccBumpFunc.body [[("dst", Loc.base pa)]] KB)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hp, Hy, Hcont⟩
  simp only [ccBumpFunc]
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
  iapply (wp_assign_start (e := .var "dst") (sh := .chain [])
    (ops := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_eval_var (cell := ptrCell ya) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_tgtop_rhs rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_eval_strict (op := .add)
    (e₁ := .deref (.var "dst") (.int .int)) (rest := [.intLit 1 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_strict (op := .deref (.int .int)) (e₁ := .var "dst")
    (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply (wp_eval_var (cell := ptrCell ya) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_strict_apply_deref (cell := intCell yv))
  isplitl [Hy]
  · iexact Hy
  iintro Hy
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
    (out := .int (IntKind.normalize .int (yv + 1)) .int) (happly := by
      intro σ
      have h1 : IntKind.compatibleResult .int .int = some .int := rfl
      simp [applyStrictOp, intBinaryResult, valueAsIntValue, h1,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11b
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (oldcell := intCell yv)
    (newcell := intCell (IntKind.normalize .int (yv + 1)))
    (fun σ₁ _ht hlook => storeLoc_int_cell hlook (yv + 1)))
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  iapply wp_stores_done_nil
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_value' (v := ()))
  iapply Hcont $$ [$Hp $Hy]

/-- Every targetless, resultless, defer-free non-wrapper frame is the
plug image of the canonical barrier — the rewrite that turns an
entry-law continuation into the bind rule's conclusion shape. -/
theorem exec_frame_as_plug {b : Stmt} {fe te : LocalEnv} {kk : Cont} :
    (Config.exec b fe (.frame [] te [] [] kk false))
      = plugC te kk (Config.exec b fe KB) := rfl

/-- **`ccWork`'s canonical spec — the bind showcase**: register the
deferred `ccBump`, call `ccDouble` (its spec applied at the call site
THROUGH `wp_bind_plug`), then drain the defer (`ccBump`'s spec applied
at the drain site through `wp_bind_plug` again). The callee bodies are
never inlined here — both compose through the bind rule. `hxnorm` pins
the input as an in-range `int` (its cell came from a normalized
store). -/
theorem wp_ccWork_canonical {paW xaW ya : Addr} {xv yv : Int}
    {Φ : Unit → IProp GF}
    (hprog : GoCoreGS.prog GF = callchainLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[])
    (hxnorm : IntKind.normalize .int xv = xv) :
    paW.id ↦ ptrCell ya ∗ xaW.id ↦ intCell xv ∗ ya.id ↦ intCell yv
      ∗ (ya.id ↦ intCell
            (IntKind.normalize .int (IntKind.normalize .int (xv + xv) + 1))
          -∗ Φ ())
      ⊢ WP (Config.exec ccWorkFunc.body
            [[("x", Loc.base xaW), ("dst", Loc.base paW)]] KB)
          @ Stuckness.NotStuck ; E {{ Φ }} := by
  iintro ⟨Hp, Hx, Hy, Hcont⟩
  simp only [ccWorkFunc]
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
  iapply wp_defer_stmt
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply (wp_eval_strict_nullary_pure
    (op := .funcValOf ⟨"ccBump"⟩) (v := .funcVal ⟨"ccBump"⟩ [])
    (hplan := rfl)
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_defer_callee_arg (hcallee := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_eval_var (cell := ptrCell ya) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_defer_register_args (vals := []) (hpush := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_call_start (plans := []) (a := .var "dst")
    (rest := [.var "x"]) rfl rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply (wp_eval_var (cell := ptrCell ya) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply (wp_eval_var (cell := intCell xv) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  simp only [List.nil_append]
  iapply (wp_call_enter_arg2 (func := ccDoubleFunc)
    (v₀ := (ptrCell ya).value)
    (v₁ := (intCell xv).value)
    (w₀ := .addr (.base ya)) (w₁ := .int xv .int)
    (hfind := by rw [hprog, callchainLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ _ hm _ => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, hxnorm]))
  iintro %a₀ %a₁ ⟨Ha0, Ha1⟩
  -- BIND APPLICATION 1: `ccDouble`'s spec at the open caller context.
  rw [show ccDoubleFunc.wrapper = false from rfl, exec_frame_as_plug]
  iapply (wp_bind_plug (hmf := rfl) (hrc := rfl)
    (hdr := drain_reducible_of_passthrough rfl) (hbar := rfl))
  iapply wp_ccDouble_canonical
  isplitl [Ha0]
  · iexact Ha0
  isplitl [Ha1]
  · iexact Ha1
  isplitl [Hy]
  · iexact Hy
  iintro ⟨Ha0, Ha1, Hy⟩
  -- the context resumes: pop the empty sequence, then drain the defer
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply (wp_frame_defer_fall_arg1 (func := ccBumpFunc)
    (cv' := .addr (.base ya))
    (hfind := by rw [hprog, callchainLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ hm => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        Bind.bind, Except.bind])
    (hnorm := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]))
  iintro %pa₂ Hp2
  -- BIND APPLICATION 2: `ccBump`'s spec at the defer-drain site.
  rw [show ccBumpFunc.wrapper = false from rfl, exec_frame_as_plug]
  iapply (wp_bind_plug (hmf := rfl) (hrc := rfl)
    (hdr := drain_reducible_frame) (hbar := rfl))
  iapply wp_ccBump_canonical
  isplitl [Hp2]
  · iexact Hp2
  isplitl [Hy]
  · iexact Hy
  iintro ⟨Hp2, Hy⟩
  -- the canonical barrier remains: fall through to the value
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply (wp_value' (v := ()))
  iapply Hcont $$ Hy

/-- What `ccCaller(x)` computes, op by op — the machine's
wrap-per-op normalize discipline (`docs/ARCHIVE.md` harvest fact 3)
made explicit: double, bump, add three. -/
def ccSpec (x : Int) : Int :=
  IntKind.normalize .int
    (IntKind.normalize .int (IntKind.normalize .int (x + x) + 1) + 3)

/-- **`ccCaller`'s body walk**: declare and seed `y`, call `ccWork`
(its spec applied at the call site THROUGH `wp_bind_plug` — the third
bind application), then write `y + 3` to the pinned result cell and
return. Generic in the below-frame continuation `k` under the two
computable context premises (discharged by `rfl` at the harness, where
`k = .stop`). -/
theorem wp_ccCaller_body {ra xaC : Addr} {xv : Int} {k : Cont}
    {Φ : Unit → IProp GF}
    (hprog : GoCoreGS.prog GF = callchainLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[])
    (hxnorm : IntKind.normalize .int xv = xv)
    (hmfk : mapIterFree k = true)
    (hrck : recoverThroughWrappers k = none) :
    ra.id ↦ intCell 0 ∗ xaC.id ↦ intCell xv
      ∗ (ra.id ↦ intCell (ccSpec xv)
          -∗ WP (Config.returning k) @ Stuckness.NotStuck ; E {{ Φ }})
      ⊢ WP (Config.exec ccCallerFunc.body
            [[("$res0", Loc.base ra), ("x", Loc.base xaC)]] k)
          @ Stuckness.NotStuck ; E {{ Φ }} := by
  iintro ⟨Hr, Hx, Hcont⟩
  simp only [ccCallerFunc]
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
  iintro %ya Hy
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_assign_lit (n := 0) (kind := .int) (w := .int 0 .int) rfl)
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  rw [show IntKind.normalize .int 0 = 0 from by decide] at *
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_call_start (plans := []) (a := .ref "y")
    (rest := [.var "x"]) rfl rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_ref (loc := .base ya) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply (wp_eval_var (cell := intCell xv) rfl)
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  simp only [List.nil_append]
  iapply (wp_call_enter_arg2 (func := ccWorkFunc)
    (v₀ := GoValue.addr (Loc.base ya))
    (v₁ := (intCell xv).value)
    (w₀ := .addr (.base ya)) (w₁ := .int xv .int)
    (hfind := by rw [hprog, callchainLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ _ hm _ => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, hxnorm]))
  iintro %b₀ %b₁ ⟨Hb0, Hb1⟩
  -- BIND APPLICATION 3: `ccWork`'s spec at the open caller context.
  rw [show ccWorkFunc.wrapper = false from rfl, exec_frame_as_plug]
  iapply (wp_bind_plug (hmf := by simp [mapIterFree, hmfk])
    (hrc := by simp [recoverThroughWrappers, hrck])
    (hdr := drain_reducible_of_passthrough rfl) (hbar := rfl))
  iapply (wp_ccWork_canonical hprog hmeths hxnorm)
  isplitl [Hb0]
  · iexact Hb0
  isplitl [Hb1]
  · iexact Hb1
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  -- the caller resumes: write `y + 3` into the result cell and return
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply (wp_assign_start (e := .ref "$res0") (sh := .chain [])
    (ops := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  iapply (wp_eval_ref (loc := .base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_tgtop_rhs rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply (wp_eval_strict (op := .add) (e₁ := .var "y")
    (rest := [.intLit 3 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply (wp_eval_var (cell := intCell
    (IntKind.normalize .int (IntKind.normalize .int (xv + xv) + 1))) rfl)
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc17
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc18
  rw [show IntKind.normalize .int 3 = 3 from by decide]
  iapply (wp_strict_apply_pure
    (out := .int (ccSpec xv) .int) (happly := by
      intro σ
      have h1 : IntKind.compatibleResult .int .int = some .int := rfl
      simp [applyStrictOp, intBinaryResult, valueAsIntValue, h1, ccSpec,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc19
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc20
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (oldcell := intCell 0)
    (newcell := intCell (ccSpec xv))
    (fun σ₁ _ht hlook => by
      have h := storeLoc_int_any (mkind := .int) hlook (ccSpec xv)
      rw [show IntKind.normalize .int (ccSpec xv) = ccSpec xv from by
        simp [ccSpec, GoLean.SliceMem.intKind_normalize_idem]] at h
      exact h))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_stores_done_nil
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc21
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc22
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc23
  iapply Hcont $$ Hr

/-- **The harness call walk**: `t = ccCaller(n)` into any target cell,
environment, and continuation — argument, frame entry
(`wp_call_enter₁₁`), the body (three bind applications inside), and
the targeted write-back. -/
theorem wp_callchainCall {ta : Addr} {w : GoValue} {t : String} {n : Int}
    {env : LocalEnv} {k : Cont} {Φ : Unit → IProp GF}
    (hres : LocalEnv.lookup env t = some (.base ta))
    (hprog : GoCoreGS.prog GF = callchainLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[])
    (hn : IntKind.normalize .int n = n)
    (hmfk : mapIterFree k = true) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ intCell (ccSpec n)
          -∗ WP (Config.next k) @ Stuckness.NotStuck ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var t] ⟨"ccCaller"⟩ #[.intLit n .int])
            env k)
          @ Stuckness.NotStuck ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  iapply (wp_call_start (plans := [(.chain [], [.ref t])])
    (a := .intLit n .int) (rest := []) rfl rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  rw [hn]
  iapply (wp_call_enter₁₁ (func := ccCallerFunc)
    (w₀ := .int n .int) (dv₀ := .int 0 .int)
    (hfind := by rw [hprog, callchainLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ _ hm _ => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, hn])
    (hdef₀ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a₀ %a₁ ⟨Hx, Hres⟩
  rw [show ccCallerFunc.wrapper = false from rfl]
  iapply (wp_ccCaller_body hprog hmeths hn
    (hmfk := by simpa [mapIterFree] using hmfk)
    (hrck := rfl))
  isplitl [Hres]
  · iexact Hres
  isplitl [Hx]
  · iexact Hx
  iintro Hres
  iapply (wp_frame_return_int (x := t) (kind := .int) (tkind := .int)
    (m := ccSpec n) (w := w) hres)
  isplitl [Hres]
  · iexact Hres
  isplitl [Hr]
  · iexact Hr
  iintro ⟨-, Hr⟩
  rw [show IntKind.normalize .int (ccSpec n) = ccSpec n from by
    simp [ccSpec, GoLean.SliceMem.intKind_normalize_idem]] at *
  iapply Hcont $$ Hr

end

end GoLean.Iris.Callchain
