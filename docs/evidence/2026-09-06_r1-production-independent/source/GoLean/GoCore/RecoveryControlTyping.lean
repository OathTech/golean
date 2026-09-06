import GoLean.GoCore.RecoveryContext

/-! Runtime source typing erases duplicate-key rejection, retaining actual
first-match types and declaration effects. General weakening preserves sorts;
it does not assert that old sorts survive new declarations. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping

mutual
inductive ControlStmt (fs : Array Func) : Bool → Context → Stmt → Prop
  | seqn {inSequence Γ ss} : ControlStmts fs Γ ss.toList →
      ControlStmt fs inSequence Γ (.seqn ss)
  | block {inSequence Γ ps ss} : StorageParams ps → DistinctParams ps →
      ControlStmts fs (push Γ ps) ss.toList → ControlStmt fs inSequence Γ (.block ps ss)
  | initialization {Γ p} : StorageType p.typ → ControlStmt fs true Γ (.initialization p)
  | assign {inSequence Γ a e} : Assignment Γ a e → ControlStmt fs inSequence Γ (.assign a e)
  | branch {inSequence Γ e t f} : ExprTyped Γ e .boolean →
      ControlStmt fs false Γ t → ControlStmt fs false Γ f →
      declarationCount t = 0 → declarationCount f = 0 →
      ControlStmt fs inSequence Γ (.ifThenElse e t f)
  | call {inSequence Γ targets fid args} : DirectCall fs Γ targets fid args →
      ControlStmt fs inSequence Γ (.call targets fid args)
  | closureCall {inSequence Γ targets callee args} : ClosureCall fs Γ targets args callee →
      ControlStmt fs inSequence Γ (.callValue targets callee args)
  | deferCall {inSequence Γ callee args} : DeferredCall fs Γ args callee →
      ControlStmt fs inSequence Γ (.deferCall callee args)
  | panic {inSequence Γ e} : PanicArgument Γ e → ControlStmt fs inSequence Γ (.panicStmt e)
  | ret {inSequence Γ} : ControlStmt fs inSequence Γ .returnStmt
inductive ControlStmts (fs : Array Func) : Context → List Stmt → Prop
  | nil {Γ} : ControlStmts fs Γ []
  | cons {Γ s ss} : ControlStmt fs true Γ s → ControlStmts fs (afterStmt Γ s) ss →
      ControlStmts fs Γ (s :: ss)
end

theorem ControlStmt.of_static {fs inSequence Γ s} (h : Statement fs inSequence Γ s) :
    ControlStmt fs inSequence Γ s := by
  induction h using Statement.rec (motive_2 := fun Γ ss _ => ControlStmts fs Γ ss) with
  | seqn _ ih => exact .seqn ih
  | block ht hd _ ih => exact .block ht hd ih
  | initialization ht _ => exact .initialization ht
  | assign ht => exact .assign ht
  | branch he _ _ nt nf ih ih' => exact .branch he ih ih' nt nf
  | call ht => exact .call ht
  | closureCall ht => exact .closureCall ht
  | deferCall ht => exact .deferCall ht
  | panic ht => exact .panic ht
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

theorem ControlStmts.of_static {fs Γ ss} (h : Statements fs Γ ss) :
    ControlStmts fs Γ ss := by
  induction h using Statements.rec
    (motive_1 := fun inSequence Γ s _ => ControlStmt fs inSequence Γ s) with
  | seqn _ ih => exact .seqn ih
  | block ht hd _ ih => exact .block ht hd ih
  | initialization ht _ => exact .initialization ht
  | assign ht => exact .assign ht
  | branch he _ _ nt nf ih ih' => exact .branch he ih ih' nt nf
  | call ht => exact .call ht
  | closureCall ht => exact .closureCall ht
  | deferCall ht => exact .deferCall ht
  | panic ht => exact .panic ht
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

mutual
theorem afterStmt_included (Γ Δ : Context) (s : Stmt) (h : Included Γ Δ) :
    Included (afterStmt Γ s) (afterStmt Δ s) := by
  cases s <;> try exact h
  case seqn ss => exact afterStmts_included Γ Δ ss.toList h
  case initialization p => exact h.declare p
termination_by structural s
theorem afterStmts_included (Γ Δ : Context) (ss : List Stmt) (h : Included Γ Δ) :
    Included (afterStmts Γ ss) (afterStmts Δ ss) := by
  cases ss with
  | nil => exact h
  | cons s ss => exact afterStmts_included _ _ ss (afterStmt_included Γ Δ s h)
termination_by structural ss
end

theorem assignment_weaken {Γ Δ a e} (h : Assignment Γ a e) (inc : Included Γ Δ) :
    Assignment Δ a e := by
  cases h with
  | typed ha he => exact .typed (target_weaken ha inc) (expr_weaken he inc)

theorem directCall_weaken {fs Γ Δ targets fid args} (h : DirectCall fs Γ targets fid args)
    (inc : Included Γ Δ) : DirectCall fs Δ targets fid args := by
  obtain ⟨f, hf, ha, ht⟩ := h
  exact ⟨f, hf, arguments_weaken ha inc, targets_weaken ht inc⟩

theorem closureCall_weaken {fs Γ Δ targets args callee}
    (h : ClosureCall fs Γ targets args callee) (inc : Included Γ Δ) :
    ClosureCall fs Δ targets args callee := by
  cases h with
  | known hf hc ha ht =>
    exact .known hf (captures_weaken hc inc) (arguments_weaken ha inc) (targets_weaken ht inc)

theorem deferredCall_weaken {fs Γ Δ args callee}
    (h : DeferredCall fs Γ args callee) (inc : Included Γ Δ) :
    DeferredCall fs Δ args callee := by
  cases h with
  | known hf hc ha => exact .known hf (captures_weaken hc inc) (arguments_weaken ha inc)

theorem panicArgument_weaken {Γ Δ e} (h : PanicArgument Γ e) (inc : Included Γ Δ) :
    PanicArgument Δ e := by
  cases h with
  | stringBox ht he => exact .stringBox ht (expr_weaken he inc)

theorem ControlStmt.weaken {fs inSequence Γ s} (h : ControlStmt fs inSequence Γ s)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmt fs inSequence Δ s := by
  revert Δ
  induction h using ControlStmt.rec
    (motive_2 := fun Γ ss _ => ∀ Δ, Included Γ Δ → ControlStmts fs Δ ss) with
  | seqn _ ih => intro Δ inc; exact .seqn (ih Δ inc)
  | block ht hd _ ih => intro Δ inc; exact .block ht hd (ih (push Δ _) (inc.push _))
  | initialization ht => intro Δ _; exact .initialization ht
  | assign ht => intro Δ inc; exact .assign (assignment_weaken ht inc)
  | branch he _ _ nt nf ih ih' =>
    intro Δ inc
    exact .branch (expr_weaken he inc) (ih Δ inc) (ih' Δ inc) nt nf
  | call ht => intro Δ inc; exact .call (directCall_weaken ht inc)
  | closureCall ht => intro Δ inc; exact .closureCall (closureCall_weaken ht inc)
  | deferCall ht => intro Δ inc; exact .deferCall (deferredCall_weaken ht inc)
  | panic ht => intro Δ inc; exact .panic (panicArgument_weaken ht inc)
  | ret => intro Δ _; exact .ret
  | nil => exact .nil
  | @cons Γ s ss _ _ ih ih' =>
    rename_i Δ inc
    exact .cons (ih Δ inc) (ih' (afterStmt Δ s) (afterStmt_included Γ Δ s inc))

theorem ControlStmts.weaken {fs Γ ss} (h : ControlStmts fs Γ ss)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmts fs Δ ss := by
  induction ss generalizing Γ Δ with
  | nil => exact .nil
  | cons s ss ih =>
    cases h with
    | cons h h' => exact .cons (h.weaken Δ inc) (ih h' _ (afterStmt_included Γ Δ s inc))

theorem afterStmts_append (Γ : Context) (ss ts : List Stmt) :
    afterStmts Γ (ss ++ ts) = afterStmts (afterStmts Γ ss) ts := by
  induction ss generalizing Γ with
  | nil => rfl
  | cons s ss ih => exact ih (afterStmt Γ s)

theorem ControlStmts.append {fs Γ ss ts} (h : ControlStmts fs Γ ss)
    (h' : ControlStmts fs (afterStmts Γ ss) ts) : ControlStmts fs Γ (ss ++ ts) := by
  induction ss generalizing Γ with
  | nil => exact h'
  | cons s ss ih =>
    cases h with
    | cons hs hss => exact .cons hs (ih hss h')

end GoLean.GoCore.RecoveryRuntime
