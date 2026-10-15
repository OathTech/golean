import GoLean.Relational

/-! Actual source graph: two independent occurrences share input x;
the third consumes both results. Stores, addresses and values are symbolic.
No schedule list or status table is used. -/
namespace U1.Symbolic
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational
open GoLean.GoCore.Relational.Unseq

def u64 : Ty := .int .uint64
def norm (x : Int) : Int := IntKind.uint64.normalize x
def val (x : Int) : GoValue := .int (norm x) .uint64

def graph : UnseqGraph := {
  cells := [{id := 2, typ := u64}, {id := 3, typ := u64}, {id := 4, typ := .bool}]
  occs := [
    {name := "sum", body := .eval 2 (.add (.var 0) (.var 1))},
    {name := "copy", body := .eval 3 (.var 0)},
    {name := "less", body := .eval 4 (.lessCmp (.var 2) (.var 3))}]
  stores := [] }

def inputEnv (a b : Nat) : LocalEnv := [[(0, .base ⟨a⟩), (1, .base ⟨b⟩)]]
def sweepEnv (s : Store) (a b : Nat) : LocalEnv :=
  (((inputEnv a b).pushScope.declare 2 (.base ⟨s.heap.size⟩)).declare 3
    (.base ⟨s.heap.size + 1⟩)).declare 4 (.base ⟨s.heap.size + 2⟩)
def sweepStore (s : Store) : Store :=
  ⟨((s.heap.push (.value u64 (val 0))).push (.value u64 (val 0))).push (.value .bool (.bool false))⟩

def zero : Nat → GoValue
  | 0 | 1 => val 0
  | _ => .bool false
def result (x y : Int) : Nat → GoValue
  | 0 => val (norm x + norm y)
  | 1 => val x
  | _ => .bool (decide (norm (norm x + norm y) < norm x))
def head : Nat → Expr
  | 0 => .add (.var 0) (.var 1)
  | 1 => .var 0
  | _ => .lessCmp (.var 2) (.var 3)

theorem wf : graph.wellFormed? = none := by decide
theorem ranked : Ranked graph := by
  constructor
  · intro o ho
    simp [graph] at ho
    rcases ho with rfl | rfl | rfl <;> rfl
  · intro i o get d hd
    have hi := (List.getElem?_eq_some_iff.mp get).1
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
    rcases cases_i with rfl | rfl | rfl <;>
      simp [graph] at get <;> subst o
    · simp [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names, UnseqGraph.isCell,
        UnseqGraph.cellNames, graph] at hd
    · simp [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names, UnseqGraph.isCell,
        UnseqGraph.cellNames, graph] at hd
    · have dep : d = 2 ∨ d = 3 := by
        simpa [UnseqGraph.deps, UnseqBody.mentions, UnseqBody.targetMentions, Expr.names, UnseqGraph.isCell,
          UnseqGraph.cellNames, graph] using hd
      rcases dep with rfl | rfl
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
  · intro i o get name hn
    have hi := (List.getElem?_eq_some_iff.mp get).1
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
    rcases cases_i with rfl | rfl | rfl <;> simp [graph] at get <;> subst o <;> simp at hn
  · intro d hd
    have cases_d : d = 2 ∨ d = 3 ∨ d = 4 := by simpa [UnseqGraph.cellNames, graph] using hd
    rcases cases_d with rfl | rfl | rfl
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩

theorem allocation (ctx : ProgramCtx) (s : Store) (a b : Nat) :
    allocDecls ctx (inputEnv a b).pushScope s graph.cells = .ok (sweepEnv s a b, sweepStore s) := by
  simp [allocDecls, graph, defaultValue, defaultValueTy, Store.alloc, Store.allocCell,
    normalizeValueForTy, normalizeValueForTyTy, sweepEnv, sweepStore, u64, val, norm,
    IntKind.normalize, IntKind.bitsAt, IntKind.bits?, IntKind.signed,
    Bind.bind, Except.bind, pure, Except.pure, Nat.add_assoc]

theorem entry (a b : Nat) : unseqEntryCheck? graph (inputEnv a b) = none := by
  rfl

def heap (ctx : ProgramCtx) (s : Store) (a b : Nat) (x y : Int) : HeapDomain :=
  HeapDomain.ofAllocation s (inputEnv a b).pushScope (sweepEnv s a b) (sweepStore s)
    graph.cells zero (result x y) (allocation ctx s a b)
    (by intro i hi; have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
        rcases cases_i with rfl | rfl | rfl <;> rfl)
    (by intro i hi; have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
        rcases cases_i with rfl | rfl | rfl <;> rfl)

theorem normalize_val (ctx : ProgramCtx) (x : Int) :
    normalizeValueForTy ctx u64 (val x) = .ok (val x) := by
  simp [u64, val, norm, normalizeValueForTy, normalizeValueForTyTy,
    IntKind.normalize, IntKind.bits?, IntKind.bitsAt, IntKind.signed]

def domain (ctx : ProgramCtx) (s : Store) (a b : Nat) (x y : Int)
    (ha : s.heap[a]? = some (.value u64 (val x)))
    (hb : s.heap[b]? = some (.value u64 (val y))) : Domain ctx graph (sweepEnv s a b) where
  heap := heap ctx s a b x y
  cells := rfl
  count := rfl
  ranked := ranked
  stores := rfl
  head := head
  bodies := by
    intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
    rcases cases_i with rfl | rfl | rfl <;> rfl
  bindings := by
    intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases_i with rfl | rfl | rfl <;> rfl
  normal := by
    intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases_i with rfl | rfl | rfl
    · exact normalize_val ctx _
    · exact normalize_val ctx _
    · rfl
  evaluates := by
    intro st binary i ready
    have hi : i < 3 := by exact List.mem_range.mp (List.mem_filter.mp ready).1
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have ba : a < s.heap.size := (Array.getElem?_eq_some_iff.mp ha).1
    have bb : b < s.heap.size := (Array.getElem?_eq_some_iff.mp hb).1
    have ca : (heap ctx s a b x y).initial.heap[a]? = some (.value u64 (val x)) :=
      (allocDecls_heap_get_lt (ctx := ctx) _ _ _ (allocation ctx s a b) ba).trans ha
    have cb : (heap ctx s a b x y).initial.heap[b]? = some (.value u64 (val y)) :=
      (allocDecls_heap_get_lt (ctx := ctx) _ _ _ (allocation ctx s a b) bb).trans hb
    have left : ReadOnlyExpr ctx ((heap ctx s a b x y).At st) (sweepEnv s a b) (.var 0) (val x) :=
      (ReadOnlyExpr.variable ctx _ 0 (.base ⟨a⟩) _ rfl).weaken
        (fun _ hs => hs.read_old ba ca)
    have right : ReadOnlyExpr ctx ((heap ctx s a b x y).At st) (sweepEnv s a b) (.var 1) (val y) :=
      (ReadOnlyExpr.variable ctx _ 1 (.base ⟨b⟩) _ rfl).weaken
        (fun _ hs => hs.read_old bb cb)
    rcases cases_i with rfl | rfl | rfl
    · exact ReadOnlyExpr.add_int .uint64 left right
    · exact left
    · have p0 := ready_produced (g := graph) (o := graph.occs[2]) rfl ready (d := 2) (by change 2 ∈ graph.deps graph.occs[2]; decide +revert)
      have p1 := ready_produced (g := graph) (o := graph.occs[2]) rfl ready (d := 3) (by change 3 ∈ graph.deps graph.occs[2]; decide +revert)
      have d0 : st[0]? = some .done := by
        change (st[0]? == some .done) = true at p0
        exact eq_of_beq p0
      have d1 : st[1]? = some .done := by
        change (st[1]? == some .done) = true at p1
        exact eq_of_beq p1
      apply ReadOnlyExpr.less_int .uint64
      · exact (ReadOnlyExpr.variable ctx _ 2 (.base ⟨s.heap.size⟩) _ rfl).weaken
          (fun _ hs => hs.read 0 (by change 0 < 3; omega) d0)
      · exact (ReadOnlyExpr.variable ctx _ 3 (.base ⟨s.heap.size + 1⟩) _ rfl).weaken
          (fun _ hs => hs.read 1 (by change 1 < 3; omega) d1)

theorem all_schedules (ctx : ProgramCtx) (s : Store) (a b : Nat) (x y : Int)
    (ha : s.heap[a]? = some (.value u64 (val x)))
    (hb : s.heap[b]? = some (.value u64 (val y))) (body : Stmt) (tail : Continuation) :
    SafeUntil ctx (domain ctx s a b x y ha hb).FrameStep
      (Completed (domain ctx s a b x y ha hb) body tail)
      (atPick graph body graph.initStatus (sweepEnv s a b) tail (sweepStore s)) :=
  (domain ctx s a b x y ha hb).all_schedules body tail _ (binary_initial graph) _
    ((heap ctx s a b x y).at_initial)

theorem from_entry (ctx : ProgramCtx) (s : Store) (a b : Nat) (x y : Int)
    (ha : s.heap[a]? = some (.value u64 (val x)))
    (hb : s.heap[b]? = some (.value u64 (val y)))
    (body : Stmt) (rest : List Stmt) (k : Continuation) :
    let d := domain ctx s a b x y ha hb
    let source : State := ⟨.exec (.unseq graph body) (inputEnv a b)
      (.seq rest (inputEnv a b) k.toMachine), s⟩
    SafeUntil ctx (d.EntryFrame source)
      (Completed d body ⟨.seq rest (inputEnv a b) k.toMachine⟩) source :=
  (domain ctx s a b x y ha hb).enter wf (entry a b) (allocation ctx s a b)
    (heap ctx s a b x y).at_initial body rest k

theorem canonical (ctx : ProgramCtx) (s : Store) (a b : Nat) (x y : Int)
    (ha : s.heap[a]? = some (.value u64 (val x)))
    (hb : s.heap[b]? = some (.value u64 (val y)))
    (body : Stmt) (rest : List Stmt) (k : Continuation) :
    ∃ order labels final,
      CanonicalExecution (domain ctx s a b x y ha hb) body
        ⟨.seq rest (inputEnv a b) k.toMachine⟩ graph.initStatus (sweepStore s) order labels final ∧
      Run ctx ⟨.exec (.unseq graph body) (inputEnv a b)
        (.seq rest (inputEnv a b) k.toMachine), s⟩ (⟨[], [], []⟩ :: labels) final :=
  (domain ctx s a b x y ha hb).canonical_entry wf (entry a b) (allocation ctx s a b)
    (heap ctx s a b x y).at_initial body rest k

end U1.Symbolic
