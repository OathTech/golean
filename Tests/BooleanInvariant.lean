import GoLean.GoCore.BooleanSafety

namespace GoLean.GoCore.BooleanRuntime.Tests
open BooleanTyping Admission Machine

def barrier : Cont := .frame [] [] [] [] .stop
def fresh : ExecState := {}

/-- A sequence tail can refer to a cell not allocated when its head starts.
The required future binding is carried by the head's declaration effect. -/
theorem staged_initialization (name : String) :
    TypedControl fresh (.exec (.initialization ⟨name, .bool⟩) []
      (.seq [.assign (.var name) (.not (.var name)), .returnStmt] [] barrier)) := by
  have hb : Bound (declare [] name) name := (bound_declare [] name name).mpr (.inl rfl)
  exact .execSeq (Covers.empty _) (.nil _) (.initialization rfl)
    (.cons (.assign hb (.not (.var hb))) (.cons .ret .nil)) .barrier

theorem staged_initialization_inv (name : String) :
    Inv fresh [] fresh (.exec (.initialization ⟨name, .bool⟩) []
      (.seq [.assign (.var name) (.not (.var name)), .returnStmt] [] barrier)) := by
  refine ⟨rfl, BoolHeap.empty rfl, by simp, staged_initialization name, ?_⟩
  simp [MachineWf, StateWf, ConfigWf, fresh, barrier, Config.locSup, Cont.locSup,
    Stmt.locSup, Expr.locSup, Assignee.locSup, LocalEnv.locSup, stmtListSup,
    targetPlansSup, deferListSup, locListSup, ExecState.nextAddr,
    Config.itersNormalized, Cont.itersNormalized]
  rfl

/-- Every successor is covered, not just the executable's chosen one. -/
theorem staged_successor (name : String) {c s}
    (hs : Step (.exec (.initialization ⟨name, .bool⟩) []
      (.seq [.assign (.var name) (.not (.var name)), .returnStmt] [] barrier)) fresh c s) :
    Inv fresh [] s c := (staged_initialization_inv name).step hs

theorem staged_no_refusal (name : String) (fuel : Nat) (ch : Choices) (r : Refusal) :
    runConfig fuel fresh (.exec (.initialization ⟨name, .bool⟩) []
      (.seq [.assign (.var name) (.not (.var name)), .returnStmt] [] barrier)) ch ≠
      .error (.refusal r) := (staged_initialization_inv name).run_no_refusal fuel ch r

theorem foreign_initialization_rejected (p : Param) (env env' : LocalEnv) (rest : List Stmt)
    (k : Cont) (s : ExecState) (hne : env ≠ env') :
    ¬ TypedControl s (.exec (.initialization p) env (.seq rest env' k)) :=
  fun h => hne h.initialization_environment

theorem root_initialization_rejected (p : Param) (env : LocalEnv) (s : ExecState) :
    ¬ TypedControl s (.exec (.initialization p) env barrier) :=
  Control.initialization_not_barrier

theorem return_stop_rejected (s : ExecState) : ¬ TypedControl s (.signal .ret .stop) :=
  Control.not_return_stop

theorem wrong_return_sort_rejected (s : ExecState) (k : Cont) :
    ¬ TypedControl s (.retV (.int 0) k) := by intro h; cases h

theorem dangling_root_rejected : ¬ BoolRoot fresh (.base ⟨0⟩) := by
  rintro ⟨a, b, heq, hcell⟩
  cases heq
  contradiction

/-- Checking only successful visible lookups would miss this hidden root. -/
theorem hidden_dangling_binding_rejected :
    ¬ EnvRoots {fresh with heap := #[.value .bool (.bool true)]}
      [[("x", .base ⟨0⟩)], [("x", .base ⟨7⟩)]] := by
  intro h
  have hb := h [("x", .base ⟨7⟩)] (by simp) ("x", .base ⟨7⟩) (by simp)
  obtain ⟨a, b, heq, hcell⟩ := hb
  cases heq
  contradiction

def scopeEnv : LocalEnv := [[("result", .base ⟨0⟩), ("x", .base ⟨1⟩)]]
def scopeState (b : Bool) : ExecState :=
  {fresh with heap := #[.value .bool (.bool false), .value .bool (.bool b)]}
def scopeBody : Stmt := .seqn #[
  .block #[⟨"x", .bool⟩] #[.assign (.var "x") (.not (.var "x"))],
  .assign (.var "result") (.var "x"), .returnStmt]

/-- The inner zero-initialized shadow is changed to true; after its block,
the read resolves the outer input. Both inputs distinguish different errors. -/
theorem actual_scope_restoration (b : Bool) :
    (do let (s, _) ← runConfig 40 (scopeState b) (.exec scopeBody scopeEnv barrier) []
        loadMany s [.base ⟨0⟩]) = .ok [.bool b] := by
  cases b <;> with_unfolding_all rfl

def zeroBody : Stmt := .seqn #[.initialization ⟨"zero", .bool⟩,
  .assign (.var "result") (.var "zero"), .returnStmt]

theorem actual_new_local_zero (b : Bool) :
    (do let (s, _) ← runConfig 30 (scopeState b) (.exec zeroBody scopeEnv barrier) []
        loadMany s [.base ⟨0⟩]) = .ok [.bool false] := by
  cases b <;> with_unfolding_all rfl

end GoLean.GoCore.BooleanRuntime.Tests
