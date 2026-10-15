import U1RD8.Base

namespace U1RD8
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational
open GoLean.GoCore.Relational.Unseq
open GoLean.Logic GoLean.IrisCustomer RelationalCodeX.Sweep

def head : Nat → Expr
  | 0 => .var 0
  | 1 => .var 1
  | _ => .add (.var 3) (.var 4)
def result (x y : Input) : Nat → Int
  | 0 => x.val
  | 1 => y.val
  | _ => IntKind.int64.normalize (x.val + y.val)
def content (x y : Input) (st : List UnseqStatus) (i : Nat) : Int :=
  if st[i]? = some .done then result x y i else 0
def rows (p q base : Nat) (x y : Input) (st : List UnseqStatus) : List Row :=
  [(p,cell x.val), (q,cell y.val),
   (base,cell (content x y st 0)), (base+1,cell (content x y st 1)),
   (base+2,cell (content x y st 2))]
abbrev scope (env : LocalEnv) (base : Nat) := declareRoots env.pushScope base [3,4,5]

theorem ranked : Ranked graph := by
  constructor
  · intro o ho
    simp [graph] at ho
    rcases ho with rfl | rfl | rfl <;> rfl
  · intro i o get d hd
    have hi := (List.getElem?_eq_some_iff.mp get).1
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
    rcases cases_i with rfl | rfl | rfl <;> simp [graph] at get <;> subst o
    · simp [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names,
        UnseqGraph.isCell, UnseqGraph.cellNames, graph] at hd
    · simp [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names,
        UnseqGraph.isCell, UnseqGraph.cellNames, graph] at hd
    · have dep : d = 3 ∨ d = 4 := by
        simpa [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names,
          UnseqGraph.isCell, UnseqGraph.cellNames, graph] using hd
      rcases dep with rfl | rfl
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
  · intro i o get name hn
    have hi := (List.getElem?_eq_some_iff.mp get).1
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
    rcases cases_i with rfl | rfl | rfl <;> simp [graph] at get <;> subst o <;> simp at hn
  · intro d hd
    have cases_d : d = 3 ∨ d = 4 ∨ d = 5 := by simpa [UnseqGraph.cellNames, graph] using hd
    rcases cases_d with rfl | rfl | rfl
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩

theorem quiet_var (ctx : ProgramCtx) (env : LocalEnv) (id : VarId) (k : Cont) :
    Quiet ctx (.evalE (.var id) env k) := by intro Ev O s ch; rfl
theorem quiet_add (ctx : ProgramCtx) (env : LocalEnv) (a b : Expr) (k : Cont) :
    Quiet ctx (.evalE (.add a b) env k) := by intro Ev O s ch; rfl
theorem quiet_strict (ctx : ProgramCtx) (env : LocalEnv) (v : GoValue)
    (vs : List GoValue) (es : List Expr) (k : Cont) :
    Quiet ctx (.retV v (.strictK .add vs es env k)) := by intro Ev O s ch; rfl
theorem quiet_next (ctx : ProgramCtx) (g : UnseqGraph) (body : Stmt)
    (st : List UnseqStatus) (env : LocalEnv) (phase : UnseqPhase) (k : Cont) :
    Quiet ctx (.next (.unseqK g body st [] env phase k)) := by intro Ev O s ch; rfl
theorem quiet_wait (ctx : ProgramCtx) (g : UnseqGraph) (body : Stmt)
    (st : List UnseqStatus) (env : LocalEnv) (i : Nat) (v : GoValue) (k : Cont) :
    Quiet ctx (.retV v (.unseqK g body st [] env (.wait i) k)) := by intro Ev O s ch; rfl

theorem paths (ctx : ProgramCtx) (env : LocalEnv) (p q base : Nat) (x y : Input)
    (h0 : env.lookup 0 = some (.base ⟨p⟩)) (h1 : env.lookup 1 = some (.base ⟨q⟩))
    (st : List UnseqStatus) (i : Nat) (ready : i ∈ graph.ready st) :
    ReadOnlyExprFor ctx (Facts (rows p q base x y st)) (Quiet ctx)
      (scope env base) (head i) (val (result x y i)) := by
  have hi : i < 3 := by
    have := List.mem_range.mp (List.mem_filter.mp ready).1
    simpa [graph] using this
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl
  · apply (ReadOnlyExprFor.variable ctx _ 0 (.base ⟨p⟩) (val x.val) ?_
      (Quiet ctx) (quiet_var ctx _ 0)).weaken
    · intro s hs; exact read_root (hs (p,cell x.val) (by simp [rows]))
    · rw [Frame.lookup_untouched _ _ _ _ (by decide)]; exact h0
  · apply (ReadOnlyExprFor.variable ctx _ 1 (.base ⟨q⟩) (val y.val) ?_
      (Quiet ctx) (quiet_var ctx _ 1)).weaken
    · intro s hs; exact read_root (hs (q,cell y.val) (by simp [rows]))
    · rw [Frame.lookup_untouched _ _ _ _ (by decide)]; exact h1
  · have hd0 : st[0]? = some .done := by
      have h := ready_produced (g := graph) (st := st) (i := 2)
        (by rfl) ready (d := 3) (by decide)
      change (st[0]? == some UnseqStatus.done) = true at h
      simpa using h
    have hd1 : st[1]? = some .done := by
      have h := ready_produced (g := graph) (st := st) (i := 2)
        (by rfl) ready (d := 4) (by decide)
      change (st[1]? == some UnseqStatus.done) = true at h
      simpa using h
    apply ReadOnlyExprFor.add_int .int64
    · apply (ReadOnlyExprFor.variable ctx _ 3 (.base ⟨base⟩) (val x.val) ?_
        (Quiet ctx) (quiet_var ctx _ 3)).weaken
      · intro s hs; apply read_root; exact hs (base,cell x.val) (by simp [rows, content, hd0, result])
      · exact Frame.lookup_declared env.pushScope base [3,4,5] (by decide) ⟨0,by decide⟩
    · apply (ReadOnlyExprFor.variable ctx _ 4 (.base ⟨base+1⟩) (val y.val) ?_
        (Quiet ctx) (quiet_var ctx _ 4)).weaken
      · intro s hs; apply read_root; exact hs (base+1,cell y.val) (by simp [rows, content, hd1, result])
      · exact Frame.lookup_declared env.pushScope base [3,4,5] (by decide) ⟨1,by decide⟩
    · exact quiet_add ctx _ _ _
    · exact quiet_strict ctx _ _ _ _
    · exact quiet_strict ctx _ _ _ _

theorem traversal (ctx : ProgramCtx) (env : LocalEnv) (p q base : Nat) (x y : Input)
    (h0 : env.lookup 0 = some (.base ⟨p⟩)) (h1 : env.lookup 1 = some (.base ⟨q⟩)) :
    Traversal ctx graph (scope env base) (fun st => Facts (rows p q base x y st))
      (Quiet ctx) head (fun i => val (result x y i)) graph.initStatus :=
  ranked.traversal (fun st _ i hr => paths ctx env p q base x y h0 h1 st i hr)
    _ (binary_initial graph)

end U1RD8
