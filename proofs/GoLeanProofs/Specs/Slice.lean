import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Control
import GoLeanProofs.Adequacy

/-!
# The vertical-slice specs
Hand-modeled slice programs (`inc`, `main`, the closed driver), the cross-frame
`inc` spec, the `main` composition, and the closed end-to-end `slice_adequate`.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **Zero-hypothesis-modulo-program witness: the full `inc(&x)` call.**
`{x ↦ m} inc(&x) {x ↦ norm(m + lit)}` where `inc` is the one-pointer-param,
no-results function with body `*p = *p + lit` — the slice's `inc`, ∀-general
over `m` and `lit`. Composes `wp_call_unary` (frame entry, fresh param cell)
→ `wp_inc_via_ptr` (the body's multi-`↦` store) → `wp_frame_fall` (frame
exit); the parameter cell is dropped at return (affine). Premises: program
membership (`hfind`, genuinely external — *which* program we run) and the
argument-variable resolution (`hx`, a fixed-env side-condition discharged by
`simp` at every use). (Premise count corrected per the 2026-07-21 pre-merge
audit, finding F1.) -/
theorem wp_inc_call {a : Addr} {kind : IntKind} {m lit : Int} {ty : Ty}
    {fid incId : FuncId} {xname : String} {env : LocalEnv} {k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) incId = some
      ⟨fid, #[⟨"p", .pointer (.int kind)⟩], #[],
        .assign (.addr (.var "p"))
          (.add (.deref (.var "p") ty) (.intLit lit kind))⟩)
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
  iapply (wp_inc_via_ptr (pa := pa) (a := a)
    (pdecl := some ((Ty.int kind).pointer)) (ty := ty) (kind := kind)
    (m := m) (lit := lit) (rest := []) (k := .frame [] [] k))
  isplitl [Hp]
  · iexact Hp
  isplitl [Ha]
  · iexact Ha
  iintro ⟨Hp', Ha'⟩
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred
  iapply Hcont $$ Ha'

/-! ## Item 5 — the slice composition: `main` returns 2

The slice programs as GoCore terms (`abbrev` so `iapply` sees through them).
These are **hand-modeled** GoCore-level `inc`/`main`: semantically equivalent
to the native frontend's lowering of the corpus case
(`Corpus/coverage/exec/pointers/inc-via-call`) but not byte-identical — the
frontend synthesizes the result-local name (`$res0`, not `ret`) and nests
`return`'s assign+return in its own `seqn` inside a `block`. That equivalence
is a manual claim, not machine-checked: the corpus differential validates the
*interpreter* against Go, and the interpreter⇄relation link is punch-list
item 6 (stated, not proven). (Precision added per the 2026-07-21 pre-merge
audit, auditors 1+2.) -/

/-- `func inc(p *int) { *p = *p + lit }` (slice: `lit = 1`). -/
abbrev incFunc (fid : FuncId) (kind : IntKind) (ty : Ty) (lit : Int) : Func :=
  ⟨fid, #[⟨"p", .pointer (.int kind)⟩], #[],
    .assign (.addr (.var "p"))
      (.add (.deref (.var "p") ty) (.intLit lit kind))⟩

/-- `func main() int { x := 0; inc(&x); inc(&x); ret = x; return }` — `return
x` in result-local lowered form. -/
abbrev mainBody (incId : FuncId) (kind : IntKind) : Stmt :=
  .seqn #[
    .initialization ⟨"x", .int kind⟩,
    .call #[] incId #[.ref "x"],
    .call #[] incId #[.ref "x"],
    .assign (.var "ret") (.var "x"),
    .returnStmt]

abbrev mainFunc (mid incId : FuncId) (kind : IntKind) : Func :=
  ⟨mid, #[], #[⟨"ret", .int kind⟩], mainBody incId kind⟩

/-- **The slice composition, ∀-general:** calling `main` stores
`norm(norm(0 + norm lit) + norm lit)` — two `inc`s from zero — into the
caller's target cell. Every law in the chain fires: nullary-ret call entry
(fresh result cell) → seqn → init (fresh `x` cell) → two cross-frame `inc`
calls → result-local copy → return unwinding → value-returning frame exit.
Premises: the two functions are in the pinned program and the target resolves
— all genuinely external. -/
theorem wp_main_call {kind : IntKind} {lit : Int} {ty : Ty}
    {mid incId fid : FuncId} {tgt : String} {ta : Addr} {w : GoValue} {env k}
    (hmain : findFunctionIn? (GoCoreGS.prog GF) mid
      = some (mainFunc mid incId kind))
    (hinc : findFunctionIn? (GoCoreGS.prog GF) incId
      = some (incFunc fid kind ty lit))
    (htgt : LocalEnv.lookup env tgt = some (.base ta)) :
    ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int kind),
            .int (kind.normalize (kind.normalize (0 + kind.normalize lit)
              + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var tgt] mid #[]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hta, Hcont⟩
  iapply (wp_call_nullary_ret (rname := "ret") (rty := .int kind)
    (v := .int 0 kind) (body := mainBody incId kind) hmain rfl rfl rfl htgt
    (fun _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]
      rfl))
  iintro %ra Hra
  iapply wp_seqn
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred1
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred2
  iapply wp_init_int
  iintro %xa Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred3
  iapply (wp_inc_call (a := xa) (kind := kind) (lit := lit) (m := 0) hinc
    (by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare]))
  isplitl [Hxa]
  · iexact Hxa
  iintro Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred4
  iapply (wp_inc_call (a := xa) (kind := kind) (lit := lit)
    (m := kind.normalize (0 + kind.normalize lit)) hinc
    (by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare]))
  isplitl [Hxa]
  · iexact Hxa
  iintro Hxa
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred5
  iapply (wp_assign_var_int (sa := xa) (ta := ra) (kind := kind)
    (n := kind.normalize (0 + kind.normalize lit) + kind.normalize lit)
    (w := .int 0 kind) (tgt := "ret") (src := "x")
    (hres_t := by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare])
    (hres_s := by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare]))
  isplitl [Hxa]
  · iexact Hxa
  isplitl [Hra]
  · iexact Hra
  iintro ⟨Hxa, Hra⟩
  iapply wp_seq_next
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred6
  iapply wp_return
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred7
  iapply wp_seq_return
  iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred8
  iapply (wp_frame_return_int (ra := ra) (ta := ta) (kind := kind)
    (n := kind.normalize (0 + kind.normalize lit) + kind.normalize lit)
    (w := w))
  isplitl [Hra]
  · iexact Hra
  isplitl [Hta]
  · iexact Hta
  iintro ⟨Hra, Hta⟩
  iapply Hcont $$ Hta

/-- **The slice's L6 finish line: `main` returns 2** — the `kind = .int`,
`lit = 1` instance of the general composition. The literal `2` appears only
here, in the final specialized instance (the composition and every law are
∀-general — the anti-specialization check). -/
theorem wp_main_returns_two {ty : Ty} {mid incId fid : FuncId} {tgt : String}
    {ta : Addr} {w : GoValue} {env k}
    (hmain : findFunctionIn? (GoCoreGS.prog GF) mid
      = some (mainFunc mid incId .int))
    (hinc : findFunctionIn? (GoCoreGS.prog GF) incId
      = some (incFunc fid .int ty 1))
    (htgt : LocalEnv.lookup env tgt = some (.base ta)) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .int), .int 2 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var tgt] mid #[]) env k) @ s ; E {{ Φ }} := by
  have h2 : IntKind.normalize .int
      (IntKind.normalize .int (0 + IntKind.normalize .int 1)
        + IntKind.normalize .int 1) = 2 := by decide
  have := wp_main_call (kind := .int) (lit := 1) (ty := ty) hmain hinc htgt
    (w := w) (k := k) (s := s) (E := E) (Φ := Φ)
  rw [h2] at this
  exact this

/-- The closed slice program: allocate the result target, call `main` into it.
Runs from ANY well-formed state — it owns nothing initially (the target cell
is its own allocation), which is what lets adequacy discharge with zero
ownership hypotheses. -/
abbrev sliceProg (mid : FuncId) (kind : IntKind) : Stmt :=
  .seqn #[.initialization ⟨"r", .int kind⟩, .call #[.var "r"] mid #[]]

/-- **The slice's closed end-to-end theorem.** For any well-formed initial
state whose function table contains the slice's `inc` and `main`, the full
program `r := 0; r = main()` — two pointer-writing `inc` calls deep — provably
runs to termination and never gets stuck: a closed `adequate .NotStuck` whose
statement contains no Iris. The result value (`r ↦ 2`) is machine-checked
Iris-side inside this very proof (`wp_main_returns_two`); surfacing it
*operationally* in `adequate`'s φ needs the strong-adequacy final-state
readout — tracked as the 2b remainder in the punch list. -/
theorem slice_adequate {ty : Ty} (σ : ExecState) (mid incId fid : FuncId)
    (hwf : HeapWf σ)
    (hmain : findFunctionIn? σ.functions mid = some (mainFunc mid incId .int))
    (hinc : findFunctionIn? σ.functions incId = some (incFunc fid .int ty 1)) :
    adequate .NotStuck (Config.exec (sliceProg mid .int) [] .stop) σ
      (fun _ _ => True) :=
  go_adequacy (GF := GoCoreS) _ _ _ hwf (by
    intro _ hprog
    iapply wp_seqn
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred1
    iapply wp_seq_next
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred2
    iapply wp_init_int
    iintro %ra Hra
    iapply wp_seq_next
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred3
    iapply (wp_main_returns_two (ta := ra) (ty := ty)
      (hmain := by rw [hprog]; exact hmain)
      (hinc := by rw [hprog]; exact hinc)
      (htgt := by simp [LocalEnv.lookup, Scope.lookup, LocalEnv.declare]))
    isplitl [Hra]
    · iexact Hra
    iintro Hra
    iapply wp_seq_done
    iapply fupd_intro; inext; iapply fupd_intro; iintro Hcred4
    iapply (wp_value' (v := ()))
    ipureintro
    trivial)

end

end GoLean.Iris
