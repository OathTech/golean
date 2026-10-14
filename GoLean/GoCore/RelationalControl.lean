import GoLean.GoCore.RelationalSound

/-!
# Source-construct views and laws

Continuations are opaque parameters in client laws. Source views below are
the entry/exit points of a construct; clients need not case-split on frames.
The first contracts cover literal evaluation, conditional control and
declaration blocks. They quantify over stores, environments and tails.

`Pure` explicitly includes store preservation and silence of `StepLabel`.
An empty race trace, or even an entirely silent label, does not establish
store preservation. Client observations of control may still emit events;
`PureFor` additionally requires silence under a supplied observation.
-/

namespace GoLean.GoCore.Relational

open Machine

/-- A saved continuation. Its machine projection belongs to correspondence
proofs; construct laws take it abstractly. -/
structure Continuation where
  ofMachine ::
  toMachine : Cont

def Continuation.halt : Continuation := ⟨.stop⟩

def statement (body : Stmt) (env : LocalEnv) (k : Continuation) (s : Store) : State :=
  ⟨.exec body env k.toMachine, s⟩

def expression (e : Expr) (env : LocalEnv) (k : Continuation) (s : Store) : State :=
  ⟨.evalE e env k.toMachine, s⟩

def returned (v : GoValue) (k : Continuation) (s : Store) : State :=
  ⟨.retV v k.toMachine, s⟩

def resumed (k : Continuation) (s : Store) : State := ⟨.next k.toMachine, s⟩

/-- Purity of the store and base label. This does not assert silence under
client observations of control: a normal return can satisfy this contract
and still emit a return event. Use `PureFor` for that additional claim. -/
def Pure (ctx : ProgramCtx) (a b : State) : Prop :=
  Transition ctx a ⟨[], [], []⟩ b ∧ b.store = a.store

/-- Purity including the client's chosen observation projection. No Iris
judgment or ownership is involved in this semantic contract. -/
def PureFor {Event : Type} (observe : State → StepLabel → State → List Event)
    (ctx : ProgramCtx) (a b : State) : Prop :=
  Pure ctx a b ∧ observe a ⟨[], [], []⟩ b = []

theorem Pure.unique {ctx : ProgramCtx} {a b c : State} {l : StepLabel}
    (h : Pure ctx a b) (hs : Transition ctx a l c) : b = c ∧ l = ⟨[], [], []⟩ := by
  obtain ⟨hb, hl⟩ := h.1.unique_of_no_picks rfl hs
  exact ⟨hb, hl.symm⟩

theorem PureFor.all_successors {Event : Type}
    {observe : State → StepLabel → State → List Event}
    {ctx : ProgramCtx} {a b c : State} {l : StepLabel}
    (h : PureFor observe ctx a b) (hs : Transition ctx a l c) :
    b = c ∧ c.store = a.store ∧ l = ⟨[], [], []⟩ ∧ observe a l c = [] := by
  obtain ⟨rfl, rfl⟩ := h.1.unique hs
  exact ⟨rfl, h.1.2, rfl, h.2⟩

theorem bool_literal (ctx : ProgramCtx) (v : Bool) (env : LocalEnv)
    (k : Continuation) (s : Store) :
    Pure ctx (expression (.boolLit v) env k s) (returned (.bool v) k s) :=
  ⟨Step.evalBoolLit, rfl⟩

theorem int_literal (ctx : ProgramCtx) (v : Int) (kind : IntKind)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (expression (.intLit v kind) env k s)
      (returned (.int (kind.normalize v) kind) k s) := ⟨Step.evalIntLit, rfl⟩

theorem string_literal (ctx : ProgramCtx) (v : GoString) (env : LocalEnv)
    (k : Continuation) (s : Store) :
    Pure ctx (expression (.stringLit v) env k s) (returned (.string v) k s) :=
  ⟨Step.evalStringLit, rfl⟩

/-- A successful variable read preserves the store and records its actual
access. The continuation may narrow that access to a projected leaf, so the
trace is not asserted to be silent or fixed to the whole binding cell. -/
theorem read_variable (ctx : ProgramCtx) (s : Store) (env : LocalEnv)
    (k : Continuation) (id : VarId) (loc : Loc) (value : GoValue)
    (lookup : LocalEnv.lookup env id = some loc)
    (read : loadRoot ctx s loc = .ok value) :
    ∃ tr, Transition ctx (expression (.var id) env k s)
      ⟨tr, [], []⟩ (returned value k s) := by
  refine ⟨[.access .read (.data (projChainTarget ctx s k.toMachine loc).canon)],
    Step.evalVar lookup ?_⟩
  simp [expression, Mem.loadBindingFor, read, Bind.bind, Except.bind, pure, Except.pure]

/-- The observation-free branch selection, after a Boolean guard is read. -/
def branch (yes no : Stmt) (env : LocalEnv) (k : Continuation) : Continuation :=
  ⟨.ifK yes no env k.toMachine⟩

theorem conditional_enter (ctx : ProgramCtx) (guard : Expr) (yes no : Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (statement (.ifThenElse guard yes no) env k s)
      (expression guard env (branch yes no env k) s) := ⟨Step.ifStmt, rfl⟩

theorem conditional_select (ctx : ProgramCtx) (b : Bool) (yes no : Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (returned (.bool b) (branch yes no env k) s)
      (statement (if b then yes else no) env k s) := by
  cases b
  · exact ⟨Step.ifFalse, rfl⟩
  · exact ⟨Step.ifTrue, rfl⟩

/-- A complete construct law: any guard execution producing a Boolean
continues in precisely the selected branch, with its labels preserved.
This packages the continuation bookkeeping in one semantic citation. -/
theorem conditional {ctx : ProgramCtx} {guard : Expr} {yes no : Stmt}
    {env : LocalEnv} {k : Continuation} {s t : Store} {b : Bool} {ls : List StepLabel}
    (h : Run ctx (expression guard env (branch yes no env k) s) ls
      (returned (.bool b) (branch yes no env k) t)) :
    Run ctx (statement (.ifThenElse guard yes no) env k s)
      (⟨[], [], []⟩ :: ls ++ [⟨[], [], []⟩])
      (statement (if b then yes else no) env k t) :=
  .cons (conditional_enter ctx guard yes no env k s).1
    (h.append (.single (conditional_select ctx b yes no env k t).1))

/-- The continuation of a list of statements in one lexical environment. -/
def sequence (ss : List Stmt) (env : LocalEnv) (k : Continuation) : Continuation :=
  ⟨.seq ss env k.toMachine⟩

/-- Enter a statement sequence under a governing sequence in the same
environment. The statements splice into the existing tail without adding a
scope or an extra continuation frame. -/
theorem sequence_splice (ctx : ProgramCtx) (ss : Array Stmt) (rest : List Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (statement (.seqn ss) env (sequence rest env k) s)
      (resumed (sequence (ss.toList ++ rest) env k) s) := by
  refine ⟨?_, rfl⟩
  simpa [Transition, statement, resumed, sequence, seqCont_seq] using
    (Step.seqn (ctx := ctx) (ss := ss) (env := env) (k := .seq rest env k.toMachine) (s := s))

theorem sequence_next (ctx : ProgramCtx) (body : Stmt) (rest : List Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (resumed (sequence (body :: rest) env k) s)
      (statement body env (sequence rest env k) s) := ⟨Step.seqNext, rfl⟩

theorem sequence_done (ctx : ProgramCtx) (env : LocalEnv) (k : Continuation) (s : Store) :
    Pure ctx (resumed (sequence [] env k) s) (resumed k s) := ⟨Step.seqDone, rfl⟩

/-- A declaration block allocates, even though its label is silent. The
post-entry environment is explicit; old bindings are preserved by scope. -/
theorem block_enter {ctx : ProgramCtx} {decls : Array Param} {ss : Array Stmt}
    {env env' : LocalEnv} {k : Continuation} {s t : Store}
    (h : allocDecls ctx env.pushScope s decls.toList = .ok (env', t)) :
    Transition ctx (statement (.block decls ss) env k s) ⟨[], [], []⟩
      (resumed (sequence ss.toList env' k) t) ∧
    t.heap.size = s.heap.size + decls.size ∧
    (∀ i, i < s.heap.size → t.heap[i]? = s.heap[i]?) ∧
    (∀ id, id ∉ decls.toList.map (·.id) → LocalEnv.lookup env' id = LocalEnv.lookup env id) := by
  refine ⟨Step.block h, ?_, ?_, ?_⟩
  · simpa using allocDecls_heap_size _ _ _ h
  · intro i hi
    exact allocDecls_heap_get_lt _ _ _ h hi
  · intro id hi
    exact blockEntry_lookup_outer h hi

/-- Empty sequence execution preserves its governing continuation and store. -/
theorem empty_sequence_run (ctx : ProgramCtx) (env : LocalEnv)
    (k : Continuation) (s : Store) :
    ∃ ls, Run ctx (statement (.seqn #[]) env k s) ls (resumed k s) ∧
      (∀ l ∈ ls, l.picks = []) ∧ (∀ l ∈ ls, l.out = []) := by
  have shape : seqCont [] env k.toMachine = k.toMachine ∨
      seqCont [] env k.toMachine = .seq [] env k.toMachine := by
    unfold seqCont
    split
    · split <;> simp_all
    · exact .inr rfl
  rcases shape with splice | wrap
  · refine ⟨[⟨[], [], []⟩], .single ?_, by simp, by simp⟩
    simpa [Transition, statement, resumed, splice] using
      (Step.seqn (ctx := ctx) (ss := #[]) (env := env) (k := k.toMachine) (s := s))
  · refine ⟨[⟨[], [], []⟩, ⟨[], [], []⟩],
      .cons ?_ (.single (sequence_done ctx env k s).1), by simp, by simp⟩
    simpa [Transition, statement, resumed, sequence, wrap] using
      (Step.seqn (ctx := ctx) (ss := #[]) (env := env) (k := k.toMachine) (s := s))

end GoLean.GoCore.Relational
