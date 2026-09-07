import GoLean.GoCore.BooleanTyping

/-! Structural typing used at the runtime boundary. Source admission checks
distinct declaration keys and branch-local scope effects. Those checks are
erased here: Boolean memory safety needs actual bound names and Boolean
cells, and allows weakening to additional saved bindings. No definition
refers to an execution, reachability, or future safety. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission

def Included (Γ Δ : Context) : Prop := ∀ x, Bound Γ x → Bound Δ x

theorem Included.refl (Γ : Context) : Included Γ Γ := fun _ h => h
theorem Included.trans {Γ Δ Ξ} (h : Included Γ Δ) (h' : Included Δ Ξ) :
    Included Γ Ξ := fun x hx => h' x (h x hx)

theorem Included.declare {Γ Δ} (h : Included Γ Δ) (x : String) :
    Included (declare Γ x) (declare Δ x) := by
  intro y hy
  rw [bound_declare] at hy ⊢
  exact hy.imp id (h y)

theorem Included.push {Γ Δ} (h : Included Γ Δ) (ps : Array Param) :
    Included (push Γ ps) (push Δ ps) := by
  intro x hx
  rw [bound_push] at hx ⊢
  exact hx.imp id (h x)

theorem Included.append_left (Γ Δ : Context) : Included Γ (Γ ++ Δ) := by
  rintro x ⟨scope, hs, hx⟩
  exact ⟨scope, List.mem_append_left Δ hs, hx⟩

theorem Included.append_right (Γ Δ : Context) : Included Δ (Γ ++ Δ) := by
  rintro x ⟨scope, hs, hx⟩
  exact ⟨scope, List.mem_append_right Γ hs, hx⟩

mutual
theorem afterStmt_included (Γ Δ : Context) (s : Stmt) (h : Included Γ Δ) :
    Included (afterStmt Γ s) (afterStmt Δ s) := by
  cases s <;> try exact h
  case seqn ss => exact afterStmts_included Γ Δ ss.toList h
  case initialization p => exact h.declare p.id
termination_by structural s
theorem afterStmts_included (Γ Δ : Context) (ss : List Stmt) (h : Included Γ Δ) :
    Included (afterStmts Γ ss) (afterStmts Δ ss) := by
  cases ss with
  | nil => exact h
  | cons s ss =>
    exact afterStmts_included (afterStmt Γ s) (afterStmt Δ s) ss
      (afterStmt_included Γ Δ s h)
termination_by structural ss
end

mutual
theorem afterStmt_extends (Γ : Context) (s : Stmt) : Included Γ (afterStmt Γ s) := by
  cases s <;> try exact Included.refl Γ
  case seqn ss => exact afterStmts_extends Γ ss.toList
  case initialization p =>
    intro x hx
    exact (bound_declare Γ p.id x).mpr (.inr hx)
termination_by structural s
theorem afterStmts_extends (Γ : Context) (ss : List Stmt) : Included Γ (afterStmts Γ ss) := by
  cases ss with
  | nil => exact Included.refl Γ
  | cons s ss => exact (afterStmt_extends Γ s).trans (afterStmts_extends (afterStmt Γ s) ss)
termination_by structural ss
end

theorem expr_weaken {Γ Δ e} (h : ExprTyped Γ e) (inc : Included Γ Δ) : ExprTyped Δ e := by
  induction h with
  | var hx => exact .var (inc _ hx)
  | literal b => exact .literal b
  | not _ ih => exact .not ih
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂

mutual
inductive ControlStmt : Bool → Context → Stmt → Prop
  | seqn {inSequence Γ ss} : ControlStmts Γ ss.toList →
      ControlStmt inSequence Γ (.seqn ss)
  | block {inSequence Γ ps ss} : BoolParams ps →
      ControlStmts (push Γ ps) ss.toList → ControlStmt inSequence Γ (.block ps ss)
  | initialization {Γ p} : p.typ = .bool → ControlStmt true Γ (.initialization p)
  | assign {inSequence Γ x e} : Bound Γ x → ExprTyped Γ e →
      ControlStmt inSequence Γ (.assign (.var x) e)
  | branch {inSequence Γ e t f} : ExprTyped Γ e →
      ControlStmt false Γ t → ControlStmt false Γ f →
      ControlStmt inSequence Γ (.ifThenElse e t f)
  | ret {inSequence Γ} : ControlStmt inSequence Γ .returnStmt
inductive ControlStmts : Context → List Stmt → Prop
  | nil {Γ} : ControlStmts Γ []
  | cons {Γ s ss} : ControlStmt true Γ s → ControlStmts (afterStmt Γ s) ss →
      ControlStmts Γ (s :: ss)
end

theorem ControlStmt.of_static {inSequence Γ s} (h : Statement inSequence Γ s) :
    ControlStmt inSequence Γ s := by
  induction h using Statement.rec
    (motive_2 := fun Γ ss _ => ControlStmts Γ ss) with
  | seqn _ ih => exact .seqn ih
  | block ht _ _ ih => exact .block ht ih
  | initialization ht _ => exact .initialization ht
  | assign hx he => exact .assign hx he
  | branch he _ _ _ _ it iff => exact .branch he it iff
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih it => exact .cons ih it

theorem ControlStmts.of_static {Γ ss} (h : StmtsTyped Γ ss) : ControlStmts Γ ss := by
  induction h using StmtsTyped.rec
    (motive_1 := fun inSequence Γ s _ => ControlStmt inSequence Γ s) with
  | seqn _ ih => exact .seqn ih
  | block ht _ _ ih => exact .block ht ih
  | initialization ht _ => exact .initialization ht
  | assign hx he => exact .assign hx he
  | branch he _ _ _ _ it iff => exact .branch he it iff
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih it => exact .cons ih it

theorem ControlStmt.weaken {inSequence Γ s} (h : ControlStmt inSequence Γ s)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmt inSequence Δ s := by
  revert Δ
  induction h using ControlStmt.rec
    (motive_2 := fun Γ ss _ => ∀ Δ, Included Γ Δ → ControlStmts Δ ss) with
  | seqn _ ih => intro Δ inc; exact .seqn (ih Δ inc)
  | block ht _ ih => intro Δ inc; exact .block ht (ih (push Δ _) (inc.push _))
  | initialization ht => intro Δ _; exact .initialization ht
  | assign hx he => intro Δ inc; exact .assign (inc _ hx) (expr_weaken he inc)
  | branch he _ _ it iff =>
      intro Δ inc; exact .branch (expr_weaken he inc) (it Δ inc) (iff Δ inc)
  | ret => intro Δ _; exact .ret
  | nil => exact .nil
  | @cons Γ s ss _ _ ih it =>
      rename_i Δ inc
      exact .cons (ih Δ inc) (it (afterStmt Δ s) (afterStmt_included Γ Δ s inc))
  -- The recursor returns the generalized statement before applying Δ/inc.

theorem ControlStmts.weaken {Γ ss} (h : ControlStmts Γ ss)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmts Δ ss := by
  revert Δ
  induction h using ControlStmts.rec
    (motive_1 := fun inSequence Γ s _ =>
      ∀ Δ, Included Γ Δ → ControlStmt inSequence Δ s) with
  | seqn _ ih => rename_i Δ inc; exact .seqn (ih Δ inc)
  | block ht _ ih => rename_i Δ inc; exact .block ht (ih (push Δ _) (inc.push _))
  | initialization ht => exact .initialization ht
  | assign hx he => rename_i Δ inc; exact .assign (inc _ hx) (expr_weaken he inc)
  | branch he _ _ it iff =>
      rename_i Δ inc; exact .branch (expr_weaken he inc) (it Δ inc) (iff Δ inc)
  | ret => exact .ret
  | nil => intro Δ _; exact .nil
  | @cons Γ s ss _ _ ih it =>
      intro Δ inc
      exact .cons (ih Δ inc) (it (afterStmt Δ s) (afterStmt_included Γ Δ s inc))

@[simp] theorem controlStmts_nil (Γ : Context) : ControlStmts Γ [] := .nil

theorem controlStmts_cons_iff {Γ s ss} :
    ControlStmts Γ (s :: ss) ↔
      ControlStmt true Γ s ∧ ControlStmts (afterStmt Γ s) ss := by
  constructor
  · intro h; cases h; exact ⟨‹_›, ‹_›⟩
  · rintro ⟨h, ht⟩; exact .cons h ht

theorem controlStmts_append_iff (Γ : Context) (ss ts : List Stmt) :
    ControlStmts Γ (ss ++ ts) ↔
      ControlStmts Γ ss ∧ ControlStmts (afterStmts Γ ss) ts := by
  induction ss generalizing Γ with
  | nil => simp [afterStmts]
  | cons s ss ih => simp [controlStmts_cons_iff, ih, afterStmts, and_assoc]

theorem ControlStmt.inSequence {Γ s} (h : ControlStmt false Γ s) : ControlStmt true Γ s := by
  cases h with
  | seqn h => exact .seqn h
  | block ht hs => exact .block ht hs
  | assign hx he => exact .assign hx he
  | branch he ht hf => exact .branch he ht hf
  | ret => exact .ret

end GoLean.GoCore.BooleanRuntime
