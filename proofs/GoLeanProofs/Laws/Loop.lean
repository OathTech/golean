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
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Tactics.GoWalk

/-!
# Loop laws (R3 rewrite; arc E rung B1 restored over the machine)

`wp_while_inv` keeps the Goose/Perennial `wp_forBreak_cond` shape
(`I : Bool → IProp`, exit receives `I false`, Löb induction), and the
reshape RETIRES the recorded arc-E divergence: the condition is no longer
an operational `ExprR` premise (`Hcond` as a determinism fact) but a
resource-conditioned WP entailment — the condition WALKS through the
machine's configurations, which is exactly the bind-form condition
handling HeapLang/Goose have and our old CK machine could not express.
Body scope is unchanged from B1 (normal completion only; `break`/
`continue` laws arrive with a witness needing them). Partial correctness,
as before.

Witness: `wp_while_eq_once` — the corpus-pinned
`control-flow/while-eq-single-iteration` loop, re-proved over the
machine with the full walk (condition: var-load / shift / literal /
eqCmp apply; body: the composed assignment walk with an add apply). The
multi-iteration witness still arrives with the `ltCmp`-widening rung
(deferred past the reshape, as recorded).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- The loop back edge: normal body completion re-enters the `while`
(`Step.loopNext`). The `▷` slot is where the Löb hypothesis strips. -/
@[go_walk_law]
theorem wp_loop_next {c : Expr} {b : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.loop c b env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.loopNext)

/-- **The while-invariant law** (Hoare while-rule, partial correctness;
Goose `wp_forBreak_cond` shape). `I : Bool → IProp` is the loop invariant
indexed by the condition's value.

- `Hcond`: from `I d`, the condition's evaluation WALK delivers `.bool d`
  to the `while` frame, handing `I d` back — the bind-form condition
  premise (a WP entailment, not an operational fact; the arc-E recorded
  divergence is retired).
- `Hbody`: one body iteration from `I true`, re-establishing `I` at some
  condition value at the loop continuation. Lean-level, hence freely
  reusable across iterations (Goose's □, for free).

Conclusion: from `I` at any condition value, the loop runs and the exit
continuation receives `I false`. Proven by Löb induction; the back edge
(`wp_loop_next`) strips the `▷` on the induction hypothesis. -/
theorem wp_while_inv {c : Expr} {b : Stmt} {env k} {I : Bool → IProp GF}
    (Hcond : ∀ d : Bool,
      iprop(I d ∗ (I d -∗
          WP (Config.retV (.bool d) (.whileK c b env k)) @ s ; E {{ Φ }}))
        ⊢ WP (Config.evalE c env (.whileK c b env k)) @ s ; E {{ Φ }})
    (Hbody : iprop(I true
        ∗ ((∃ d, I d) -∗ WP (Config.next (.loop c b env k)) @ s ; E {{ Φ }}))
        ⊢ WP (Config.exec b env (.loop c b env k)) @ s ; E {{ Φ }}) :
    iprop((∃ d, I d)
      ∗ (I false -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }} := by
  apply BI.wand_entails
  iloeb as IH
  iintro ⟨⟨%d, HId⟩, Hexit⟩
  iapply wp_while_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred
  iapply (Hcond d)
  isplitl [HId]
  · iexact HId
  iintro HId
  cases d with
  | false =>
    iapply wp_while_bool (b := false)
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred₂
    rw [if_neg Bool.false_ne_true]
    iapply Hexit $$ HId
  | true =>
    iapply wp_while_bool (b := true)
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred₂
    rw [if_pos rfl]
    iapply Hbody
    isplitl [HId]
    · iexact HId
    iintro HId'
    iapply wp_loop_next
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred₃
    iapply IH
    isplitl [HId']
    · iexact HId'
    · iexact Hexit

/-- **The discharge witness: `while (x == 0) { x = x + 1 }`** — the
corpus-pinned single-iteration loop (`control-flow/while-eq-single-
iteration`, differential PASS), re-proved over the machine: the condition
premise is discharged by the actual condition WALK (strict enter →
var load → shift → literal → eqCmp apply), the body by the composed
assignment walk (with an add apply), all from `Laws/Eval`. From
`{x ↦ 0}` the loop delivers `{x ↦ 1}`. -/
theorem wp_while_eq_once {xa : Addr} {x : String} {env k}
    (hres : LocalEnv.lookup env x = some (.base xa)) :
    xa.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (xa.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.while (.eqCmp (.int .int) (.var x) (.intLit 0 .int))
              (.assign (.var x) (.add (.var x) (.intLit 1 .int)))) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply (wp_while_inv
    (I := fun d => iprop(∃ n : Int,
      ⌜(n = 0 ∨ n = 1) ∧ (n == 0) = d⌝
        ∗ xa.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell)))
    (Hcond := by
      intro d
      iintro ⟨⟨%n, %hn, Hpt⟩, Hk⟩
      obtain ⟨h01, hnd⟩ := hn
      iapply (wp_eval_strict (op := .eqCmp (.int .int)) (e₁ := .var x)
        (rest := [.intLit 0 .int]) rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₁
      iapply (wp_eval_var (cell := ⟨some (.int .int), .int n .int⟩) hres)
      isplitl [Hpt]
      · iexact Hpt
      iintro Hpt
      iapply wp_strict_shift
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₂
      iapply wp_eval_intLit
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₃
      rw [show IntKind.normalize .int 0 = 0 from by decide]
      iapply (wp_strict_apply_pure (out := .bool (n == 0)) (happly := by
        intro σ
        simp [applyStrictOp, valueEq, valueEqFuel, Bind.bind, Except.bind]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₄
      rw [hnd]
      iapply Hk
      iexists n
      isplitl []
      · ipureintro
        exact ⟨h01, hnd⟩
      · iexact Hpt)
    (Hbody := by
      iintro ⟨⟨%n, %hn, Hpt⟩, Hk⟩
      obtain ⟨h01, hnd⟩ := hn
      have hn0 : n = 0 := by
        rcases h01 with rfl | rfl
        · rfl
        · simp at hnd
      subst hn0
      iapply (wp_assign_start (te := .ref x) rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₁
      iapply (wp_eval_ref hres)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₂
      iapply wp_assign_target
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₃
      iapply (wp_eval_strict (op := .add) (e₁ := .var x)
        (rest := [.intLit 1 .int]) rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₄
      iapply (wp_eval_var (cell := ⟨some (.int .int), .int 0 .int⟩) hres)
      isplitl [Hpt]
      · iexact Hpt
      iintro Hpt
      iapply wp_strict_shift
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₅
      iapply wp_eval_intLit
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₆
      rw [show IntKind.normalize .int 1 = 1 from by decide]
      iapply (wp_strict_apply_pure (out := .int 1 .int) (happly := by
        intro σ
        have h1 : IntKind.compatibleResult .int .int = some .int := rfl
        have h2 : IntKind.normalize .int 1 = 1 := by decide
        simp [applyStrictOp, intBinaryResult, valueAsIntValue, h1, h2,
          Bind.bind, Except.bind]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hb₇
      iapply (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
        (newcell := ⟨some (.int .int), .int 1 .int⟩)
        (hstore := fun σ₁ _ht hlook => by
          have h := storeLoc_int_cell (kind := .int) hlook 1
          rw [show IntKind.normalize .int 1 = 1 from by decide] at h
          exact h))
      isplitl [Hpt]
      · iexact Hpt
      iintro Hpt
      iapply Hk
      iexists false
      iexists (1 : Int)
      isplitl []
      · ipureintro
        exact ⟨Or.inr rfl, by decide⟩
      · iexact Hpt))
  isplitl [Hpt]
  · iexists true
    iexists (0 : Int)
    isplitl []
    · ipureintro
      exact ⟨Or.inl rfl, by decide⟩
    · iexact Hpt
  · iintro ⟨%n, %hn, Hpt₂⟩
    obtain ⟨h01, hnd⟩ := hn
    have hn1 : n = 1 := by
      rcases h01 with rfl | rfl
      · simp at hnd
      · rfl
    subst hn1
    iapply Hcont $$ Hpt₂


end

end GoLean.Iris
