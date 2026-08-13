import GoLeanProofs.Frame.Rename

/-!
# The executable frame theorem: rename-identity below the seed bound

The `locSup` family's mirror on the rename side (build handoff §4): a
renaming that is the identity below `n` fixes every syntactic carrier
whose `locSup` is at most `n`. Consumers: the seed `FrameSim`'s
`bodies_inv` (function bodies of a lowered program are `ρ`-invariant —
`funcListSup` bounds them below `na₀` and the shift is the identity
there, `uniformShift_low`) and the seed configuration's invariance
(`renameStmt`/`renameEnv` on the driver call).

The bound is ≤-shaped so a `locSup = 0` program (no address literal
anywhere — every frontend-lowered program) is covered at ANY `n`,
including `n = 0` with the identity hypothesis vacuous.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {ρ : Nat → Nat} {n : Nat}

theorem renameLoc_id (hid : ∀ x < n, ρ x = x) :
    ∀ l : Loc, Loc.locSup l ≤ n → renameLoc ρ l = l := by
  intro l
  induction l with
  | base a =>
      intro h
      simp only [Loc.locSup, Loc.rootBase] at h
      simp [renameLoc, hid a.id (by omega)]
  | field b tid f ih =>
      intro h
      simp only [Loc.locSup, Loc.rootBase] at h ih
      simp [renameLoc, ih h]
  | index b i ih =>
      intro h
      simp only [Loc.locSup, Loc.rootBase] at h ih
      simp [renameLoc, ih h]

theorem renameExpr_id (hid : ∀ x < n, ρ x = x) (e : Expr) :
    Expr.locSup e ≤ n → renameExpr ρ e = e := by
  apply renameExpr.induct
    (motive_1 := fun e => Expr.locSup e ≤ n → renameExpr ρ e = e)
    (motive_2 := fun o => optExprSup o ≤ n → renameOptExpr ρ o = o)
    (motive_3 := fun l =>
      keyedExprListSup l ≤ n → renameKeyedExprList ρ l = l)
    (motive_4 := fun l => exprListSup l ≤ n → renameExprList ρ l = l) <;>
    intros <;>
    first
      | rfl
      | simp_all [Expr.locSup, optExprSup, exprListSup, keyedExprListSup,
          renameExpr, renameOptExpr, renameExprList, renameKeyedExprList,
          Nat.max_le, renameLoc_id hid]

theorem renameOptExpr_id (hid : ∀ x < n, ρ x = x) (o : Option Expr)
    (h : optExprSup o ≤ n) : renameOptExpr ρ o = o := by
  cases o with
  | none => rfl
  | some e =>
      simp only [optExprSup] at h
      simp [renameOptExpr, renameExpr_id hid e h]

theorem renameExprList_id (hid : ∀ x < n, ρ x = x) :
    ∀ l : List Expr, exprListSup l ≤ n → renameExprList ρ l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e es ih =>
      intro h
      simp only [exprListSup, Nat.max_le] at h
      simp [renameExprList, renameExpr_id hid e h.1, ih h.2]

theorem renameAssignee_id (hid : ∀ x < n, ρ x = x) (a : Assignee)
    (h : Assignee.locSup a ≤ n) : renameAssignee ρ a = a := by
  cases a with
  | var id => rfl
  | unsupported f => rfl
  | addr e =>
      simp only [Assignee.locSup] at h
      simp [renameAssignee, renameExpr_id hid e h]
  | mapElem b k kt vt =>
      simp only [Assignee.locSup, Nat.max_le] at h
      simp [renameAssignee, renameExpr_id hid b h.1, renameExpr_id hid k h.2]

theorem renameAssigneeList_map_id (hid : ∀ x < n, ρ x = x) :
    ∀ l : List Assignee, assigneeListSup l ≤ n →
      l.map (renameAssignee ρ) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      simp only [assigneeListSup, Nat.max_le] at h
      simp [renameAssignee_id hid a h.1, ih h.2]

theorem renameSelectHead_id (hid : ∀ x < n, ρ x = x)
    (hd : SelectClauseHead) (h : selectClauseHeadSup hd ≤ n) :
    renameSelectHead ρ hd = hd := by
  cases hd with
  | send ch v elem =>
      simp only [selectClauseHeadSup, Nat.max_le] at h
      simp [renameSelectHead, renameExpr_id hid ch h.1,
        renameExpr_id hid v h.2]
  | recv targets ch elem =>
      simp only [selectClauseHeadSup, Nat.max_le] at h
      simp [renameSelectHead, renameAssigneeList,
        renameAssigneeList_map_id hid targets.toList h.1,
        renameExpr_id hid ch h.2]

theorem renameStmt_id (hid : ∀ x < n, ρ x = x) (s : Stmt) :
    Stmt.locSup s ≤ n → renameStmt ρ s = s := by
  apply renameStmt.induct
    (motive_1 := fun s => Stmt.locSup s ≤ n → renameStmt ρ s = s)
    (motive_2 := fun o => optStmtSup o ≤ n → renameOptStmt ρ o = o)
    (motive_3 := fun l =>
      selectClausesSup l ≤ n → renameSelectClauses ρ l = l)
    (motive_4 := fun l => stmtListSup l ≤ n → renameStmtList ρ l = l) <;>
    intros <;>
    first
      | rfl
      | simp_all [Stmt.locSup, stmtListSup, selectClausesSup, optStmtSup,
          selectClauseHeadSup, renameStmt, renameStmtList,
          renameSelectClauses, renameOptStmt, Nat.max_le,
          renameExpr_id hid, renameExprList_id hid, renameOptExpr_id hid,
          renameAssignee_id hid, renameAssigneeList_map_id hid,
          renameSelectHead_id hid]

/-! ## Environment and function-table corollaries -/

theorem renameScope_id (hid : ∀ x < n, ρ x = x) :
    ∀ sc : Scope, Scope.locSup sc ≤ n → renameScope ρ sc = sc := by
  intro sc
  induction sc with
  | nil => intro _; rfl
  | cons p rest ih =>
      obtain ⟨name, l⟩ := p
      intro h
      simp only [Scope.locSup, Nat.max_le] at h
      simp only [renameScope, List.map_cons]
      rw [renameLoc_id hid l h.1]
      have := ih h.2
      simpa [renameScope] using this

theorem renameEnv_id (hid : ∀ x < n, ρ x = x) :
    ∀ env : LocalEnv, LocalEnv.locSup env ≤ n → renameEnv ρ env = env := by
  intro env
  induction env with
  | nil => intro _; rfl
  | cons sc rest ih =>
      intro h
      simp only [LocalEnv.locSup, Nat.max_le] at h
      simp only [renameEnv, List.map_cons]
      rw [renameScope_id hid sc h.1]
      have := ih h.2
      simpa [renameEnv] using this

/-- A member's bound from the list bound. -/
theorem funcListSup_mem {fs : List Func} {f : Func} (hf : f ∈ fs) :
    Func.locSup f ≤ funcListSup fs := by
  induction fs with
  | nil => cases hf
  | cons g gs ih =>
      simp only [funcListSup]
      rcases hf with _ | hf
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih ‹_›) (Nat.le_max_right _ _)

/-- The `bodies_inv` discharger: every body of a function table whose
`funcListSup` sits below the identity region renames to itself. -/
theorem renameBodies_id (hid : ∀ x < n, ρ x = x) {fs : Array Func}
    (hsup : funcListSup fs.toList ≤ n) :
    ∀ f ∈ fs.toList, renameStmt ρ f.body = f.body := by
  intro f hf
  exact renameStmt_id hid f.body
    (Nat.le_trans (funcListSup_mem hf) hsup)

end GoLean.Frame
