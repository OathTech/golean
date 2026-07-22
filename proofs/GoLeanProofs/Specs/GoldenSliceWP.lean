import GoLeanProofs.Specs.Slice
import GoLeanProofs.Specs.GoldenSlice

/-!
# The golden WP walk (arc `exit-infra`)

The Iris side of the golden slice: weakest-precondition walks over the
frontend's ACTUAL lowering (`GoldenSlice.sliceLowered`, pinned by
`scripts/check-golden`), composed with the correspondence witness
(`golden_interp_run_in_relation`) into `golden_interp_computes_two` — the
lowering-target theorem with the "hand model ≈ lowering" footnote fully
retired: every terminating interpreter run of the driver over the frontend's
own output ends with a heap cell holding `int 2`, and the proof subject IS
the executed artifact.

The lowered shape differs from the hand-modeled slice (`Specs/Slice.lean`)
in exactly the ways Arc C/D built machinery for: `.block`-wrapped bodies
(`wp_block_nil` + a pushed scope every lookup must see through), nested
`.seqn` declaration groups spliced by D1's `seqCont` (`seqCont_splice`),
the explicit `x = 0` assignment the frontend emits after the declaration,
and the synthesized `$res0` result local.

The walks are ∀-general over `kind`/`lit`/`m` where the lowered term is
(the golden instance `kind = .int`, `lit = 1` appears only in the final
specialized theorems — same anti-specialization discipline as `Slice.lean`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence

namespace GoLean.Iris.GoldenSlice

/-- D1's `seqCont` splices under a same-env governing sequence — the
equation the walks use to step through the frontend's nested `.seqn`
groups (the hand-modeled slice only ever hit `seqCont`'s non-`.seq`
wrap branch). -/
theorem seqCont_splice (ss rest : List Stmt) (env : LocalEnv) (k : Cont) :
    seqCont ss env (.seq rest env k) = .seq (ss ++ rest) env k := by
  simp [seqCont]

/-! ## The lowered shapes, parametrized

`abbrev`s so `iapply` sees through them; `sliceLowered_funcs` below is the
machine-checked bridge to the golden term. -/

/-- The frontend's lowering of `inc`'s body: block-wrapped, `.seqn`-grouped
`*p = *p + lit` (golden instance: `kind = .int`, `ty = .int .int`,
`lit = 1`). -/
abbrev incLoweredBody (kind : IntKind) (ty : Ty) (lit : Int) : Stmt :=
  .block #[] #[.seqn #[.assign (.addr (.var "p"))
    (.add (.deref (.var "p") ty) (.intLit lit kind))]]

abbrev incLoweredFunc (fid : FuncId) (kind : IntKind) (ty : Ty)
    (lit : Int) : Func :=
  ⟨fid, #[⟨"p", .pointer (.int kind)⟩], #[], incLoweredBody kind ty lit⟩

/-- The frontend's lowering of `incViaCall`'s body: block-wrapped; the
`x := 0` short declaration lowers to a `.seqn`-grouped init + explicit
zero assignment; `return x` lowers to a `.seqn`-grouped `$res0`-assign +
bare return. -/
abbrev incViaCallLoweredBody (incId : FuncId) (kind : IntKind) : Stmt :=
  .block #[] #[
    .seqn #[.initialization ⟨"x", .int kind⟩,
            .assign (.var "x") (.intLit 0 kind)],
    .call #[] incId #[.ref "x"],
    .call #[] incId #[.ref "x"],
    .seqn #[.assign (.var "$res0") (.var "x"), .returnStmt]]

abbrev incViaCallLoweredFunc (mid incId : FuncId) (kind : IntKind) : Func :=
  ⟨mid, #[], #[⟨"$res0", .int kind⟩], incViaCallLoweredBody incId kind⟩

/-- **The bridge: the parametrized shapes ARE the golden term** — the walks
below are about `sliceLowered`, kernel-checked, not by analogy. -/
theorem sliceLowered_funcs :
    sliceLowered.funcs
      = #[incLoweredFunc ⟨"inc"⟩ .int (.int .int) 1,
          incViaCallLoweredFunc ⟨"incViaCall"⟩ ⟨"inc"⟩ .int] := rfl

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The lowered `inc(&x)` call spec**: `{x ↦ m} inc(&x) {x ↦ norm(m+lit)}`
for the FRONTEND's lowered `inc` — the golden counterpart of `wp_inc_call`.
The block wrapper costs a `wp_block_nil` step and a pushed scope (hence
`wp_inc_via_ptr_env` with the lookup discharged through it); the `.seqn`
group costs a `seqCont_splice`. Premises: program membership (`hfind`) and
argument resolution (`hx`), both genuinely external — same status as
`wp_inc_call`'s. -/
theorem wp_incLowered_call {a : Addr} {kind : IntKind} {m lit : Int} {ty : Ty}
    {fid incId : FuncId} {xname : String} {env : LocalEnv} {k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) incId
      = some (incLoweredFunc fid kind ty lit))
    (hx : LocalEnv.lookup env xname = some (.base a)) :
    a.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize (m + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[] incId #[.ref xname]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Ha, Hcont⟩
  iapply (wp_call_unary (pid := "p") (pty := .pointer (.int kind))
    (v := .addr (.base a)) (v' := .addr (.base a)) hfind rfl rfl rfl
    (fun _ => ExprR.ref hx)
    (fun _ _ h => exprR_ref_det hx h)
    (fun _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
      rfl))
  iintro %pa Hp
  iapply wp_block_nil
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred1
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred2
  iapply wp_seqn
  rw [seqCont_splice]
  simp only [List.cons_append, List.nil_append]
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred3
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred4
  iapply (wp_inc_via_ptr_env (pa := pa) (a := a)
    (pdecl := some ((Ty.int kind).pointer)) (ty := ty) (kind := kind)
    (m := m) (lit := lit)
    (hres := by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.pushScope]))
  isplitl [Hp]
  · iexact Hp
  isplitl [Ha]
  · iexact Ha
  iintro ⟨Hp', Ha'⟩
  iapply wp_seq_done
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred5
  iapply wp_frame_fall
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred6
  iapply Hcont $$ Ha'

/-- **The lowered `incViaCall()` composition, ∀-general**: calling the
frontend's lowered `incViaCall` stores `norm(norm(norm 0 + norm lit) +
norm lit)` — explicit zero assignment, then two lowered `inc`s — into the
caller's target cell. The golden counterpart of `wp_main_call`; the extra
`norm 0` in the chain is the frontend's explicit `x = 0` assignment (the
hand model relied on the declaration default). -/
theorem wp_incViaCallLowered_call {kind : IntKind} {lit : Int} {ty : Ty}
    {mid incId fid : FuncId} {tgt : String} {ta : Addr} {w : GoValue} {env k}
    (hmain : findFunctionIn? (GoCoreGS.prog GF) mid
      = some (incViaCallLoweredFunc mid incId kind))
    (hinc : findFunctionIn? (GoCoreGS.prog GF) incId
      = some (incLoweredFunc fid kind ty lit))
    (htgt : LocalEnv.lookup env tgt = some (.base ta)) :
    ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int kind),
            .int (kind.normalize (kind.normalize (kind.normalize 0 + kind.normalize lit)
              + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var tgt] mid #[]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hta, Hcont⟩
  iapply (wp_call_nullary_ret (rname := "$res0") (rty := .int kind)
    (v := .int 0 kind) (body := incViaCallLoweredBody incId kind)
    hmain rfl rfl rfl htgt
    (fun _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]
      rfl))
  iintro %ra Hra
  iapply wp_block_nil
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred1
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred2
  iapply wp_seqn
  rw [seqCont_splice]
  simp only [List.cons_append, List.nil_append]
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred3
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred4
  iapply wp_init_int
  iintro %xa Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred5
  iapply (wp_assign (id := "x") (a := xa)
    (oldcell := ⟨some (.int kind), .int 0 kind⟩)
    (newcell := ⟨some (.int kind), .int (kind.normalize 0) kind⟩)
    (v := .int (kind.normalize 0) kind)
    (hres := by
      simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare, LocalEnv.pushScope])
    (hrhs := fun _ => ExprR.intLit)
    (hrhs_det := fun _ _ h => exprR_intLit_det h)
    (hstore := fun _ hlook => storeLoc_int_cell hlook 0))
  isplitl [Hxa]
  · iexact Hxa
  iintro Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred6
  iapply (wp_incLowered_call (a := xa) (kind := kind) (lit := lit)
    (m := kind.normalize 0) hinc
    (by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare, LocalEnv.pushScope]))
  isplitl [Hxa]
  · iexact Hxa
  iintro Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred7
  iapply (wp_incLowered_call (a := xa) (kind := kind) (lit := lit)
    (m := kind.normalize (kind.normalize 0 + kind.normalize lit)) hinc
    (by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare, LocalEnv.pushScope]))
  isplitl [Hxa]
  · iexact Hxa
  iintro Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred8
  iapply wp_seqn
  rw [seqCont_splice]
  simp only [List.cons_append, List.nil_append]
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred9
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred10
  iapply (wp_assign_var_int (sa := xa) (ta := ra) (kind := kind)
    (n := kind.normalize (kind.normalize 0 + kind.normalize lit) + kind.normalize lit)
    (w := .int 0 kind) (tgt := "$res0") (src := "x")
    (hres_t := by
      simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare, LocalEnv.pushScope])
    (hres_s := by
      simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare, LocalEnv.pushScope]))
  isplitl [Hxa]
  · iexact Hxa
  isplitl [Hra]
  · iexact Hra
  iintro ⟨Hxa, Hra⟩
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred11
  iapply wp_return
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred12
  iapply wp_seq_return
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred13
  iapply (wp_frame_return_int (ra := ra) (ta := ta) (kind := kind)
    (n := kind.normalize (kind.normalize 0 + kind.normalize lit) + kind.normalize lit)
    (w := w))
  isplitl [Hra]
  · iexact Hra
  isplitl [Hta]
  · iexact Hta
  iintro ⟨Hra, Hta⟩
  iapply Hcont $$ Hta

/-- **The golden L6 finish line: lowered `incViaCall` returns 2** — the
`kind = .int`, `lit = 1` instance. The literal `2` appears only in the
specialized instances, never in the general walks. -/
theorem wp_incViaCallLowered_ret2 {ty : Ty} {mid incId fid : FuncId}
    {tgt : String} {ta : Addr} {w : GoValue} {env k}
    (hmain : findFunctionIn? (GoCoreGS.prog GF) mid
      = some (incViaCallLoweredFunc mid incId .int))
    (hinc : findFunctionIn? (GoCoreGS.prog GF) incId
      = some (incLoweredFunc fid .int ty 1))
    (htgt : LocalEnv.lookup env tgt = some (.base ta)) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .int), .int 2 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var tgt] mid #[]) env k) @ s ; E {{ Φ }} := by
  have h2 : IntKind.normalize .int
      (IntKind.normalize .int (IntKind.normalize .int 0 + IntKind.normalize .int 1)
        + IntKind.normalize .int 1) = 2 := by decide
  have := wp_incViaCallLowered_call (kind := .int) (lit := 1) (ty := ty)
    hmain hinc htgt (w := w) (k := k) (s := s) (E := E) (Φ := Φ)
  rw [h2] at this
  exact this

/-- **The golden operational readout.** The driver over the lowered
program, with the result surfaced into `adequate`'s φ: every terminating
run's final heap contains a cell holding exactly `int 2`. Mirror of
`slice_adequate_computes`, subject swapped for the frontend's lowering. -/
theorem golden_adequate_computes {ty : Ty} (σ : ExecState) (fid : FuncId)
    (hwf : HeapWf σ)
    (hmain : findFunctionIn? σ.functions ⟨"incViaCall"⟩
      = some (incViaCallLoweredFunc ⟨"incViaCall"⟩ ⟨"inc"⟩ .int))
    (hinc : findFunctionIn? σ.functions ⟨"inc"⟩
      = some (incLoweredFunc fid .int ty 1)) :
    adequate .NotStuck (Config.exec goldenProg [] .stop) σ
      (fun _ σf => ∃ a : Addr, loadLoc σf (.base a) = .ok (.int 2 .int)) := by
  refine go_heap_adequacy (GF := GoCoreS) _ _
    (Ψ := fun _ => iprop(∃ a : Addr,
      a.id ↦ (⟨some (.int .int), .int 2 .int⟩ : HeapCell))) _ hwf ?_ ?_
  · intro _ hprog
    iapply wp_seqn
    simp only [seqCont]
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred1
    iapply wp_seq_next
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred2
    iapply wp_init_int
    iintro %ra Hra
    iapply wp_seq_next
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred3
    iapply (wp_incViaCallLowered_ret2 (ta := ra) (ty := ty)
      (hmain := by rw [hprog]; exact hmain)
      (hinc := by rw [hprog]; exact hinc)
      (htgt := by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare]))
    isplitl [Hra]
    · iexact Hra
    iintro Hra
    iapply wp_seq_done
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred4
    iapply (wp_value' (v := ()))
    iexists ra
    iexact Hra
  · intro _ hprog σ2 v
    iintro ⟨Hgh, ⟨%a, Hpt⟩⟩
    imod (pointsTo_loadLoc (σ := σ2) (a := a)) $$ [$Hgh $Hpt] with %Hload
    imodintro
    ipureintro
    exact ⟨a, Hload⟩

end

/-- **The golden computed-somewhere readout.** Every terminating
interpreter run of the driver over THE FRONTEND'S ACTUAL LOWERING
(`sliceLowered`, pinned to the frontend's output by `scripts/check-golden`)
ends with SOME heap cell holding exactly `int 2`. Statement mentions only
the interpreter and the golden state — no Iris, no relation; the chain
(correspondence witness → trace erasure → strong adequacy → heap readout)
is inside the proof. **Scope: the address is EXISTENTIAL — this is NOT the
lowering target** ("the result cell holds 2"), per
`docs/2026-07-21_native-spec-surface.md` D8; the pinned-observable form is
the spec-surface arc's step-0 target. -/
theorem golden_interp_computes_two (fuel : Nat) (σf : ExecState)
    (ch' : Choices)
    (hrun : execStmt fuel σg [] goldenProg = .ok (.normal σf, ch')) :
    ∃ a : Addr, loadLoc σf (.base a) = .ok (.int 2 .int) := by
  have hsteps := golden_interp_run_in_relation fuel σf ch' hrun
  have htp := steps_erased hsteps
  have hwf : HeapWf σg := by intro n hn; rfl
  have hadeq := golden_adequate_computes (ty := .int .int) σg ⟨"inc"⟩ hwf
    (by rfl) (by rfl)
  have := hadeq.adequate_result [] (σf.withLocals []) () htp
  obtain ⟨a, hload⟩ := this
  exact ⟨a, by rw [← loadLoc_withLocals σf [] (.base a)]; exact hload⟩

end GoLean.Iris.GoldenSlice
