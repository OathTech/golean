import GoLean.Interface
import Tests.BooleanRuntime

namespace BooleanInitializationAdversarial
open GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.BooleanRuntime
set_option maxRecDepth 4096

-- Generic consumers connect actual lookup with the value at that exact root.
-- No generated-name convention or particular fixture occurs in these claims.
theorem generic_named_argument (p : Program) (f : Func) (bs : List Bool)
    (hd : (initialNames f).Nodup) (hlen : bs.length = f.args.size)
    (i : Nat) (hi : i < bs.length) :
    ∃ loc, (initialEnv f).lookup (f.args[i]'(by omega)).id = some loc ∧
      loadLoc (initialState p f bs) loc = .ok (.bool bs[i]) := by
  exact ⟨.base ⟨i⟩, initialEnv_argument hd i (by omega),
    initialState_argument p f bs i hi⟩

theorem generic_named_result (p : Program) (f : Func) (bs : List Bool)
    (hd : (initialNames f).Nodup) (hlen : bs.length = f.args.size)
    (i : Nat) (hi : i < f.results.size) :
    ∃ loc, (initialEnv f).lookup f.results[i].id = some loc ∧
      loadLoc (initialState p f bs) loc = .ok (.bool false) := by
  exact ⟨.base ⟨f.args.size + i⟩, initialEnv_result hd i hi,
    initialState_result p f bs hlen i hi⟩

-- Canonical-list distinctness cannot be substituted for actual result pins
-- when strong admission/signature distinctness is absent.
def duplicate : Func := {
  id := ⟨"F"⟩, args := #[], results := #[⟨"x", .bool⟩, ⟨"x", .bool⟩],
  body := .returnStmt }

theorem duplicate_canonical_distinct : (initialResults duplicate).Nodup :=
  initialResults_distinct duplicate

theorem duplicate_actual_pins_alias :
    pinResultLocs (initialEnv duplicate) duplicate.results.toList =
      .ok [.base ⟨1⟩, .base ⟨1⟩] := by with_unfolding_all rfl

theorem duplicate_strongly_rejected :
    BooleanTyping.checkTypedBoolean {funcs := #[duplicate]} "F" #[] =
      .error (.duplicateSignatureBinding ⟨"F"⟩) := by with_unfolding_all rfl

-- The argument-count premise in initialState_result is essential. Without
-- it a canonical result offset can point into an argument containing true.
def oneResult : Func := {
  id := ⟨"F"⟩, args := #[], results := #[⟨"r", .bool⟩], body := .returnStmt }

theorem mismatched_argument_count_is_not_zero :
    loadMany (initialState {funcs := #[oneResult]} oneResult [true])
      (initialResults oneResult) = .ok [.bool true] := by with_unfolding_all rfl

-- Exact helpers allow arbitrary prior storage/environment: they append the
-- right cells but cannot be read as repairing malformed old storage.
def oldState : ExecState := { heap := #[.value .bool .nil] }
def oldEnv : LocalEnv := [[("a", .base ⟨999⟩)]]

theorem binder_retains_hidden_bad_state :
    bindParams oldEnv oldState [⟨"a", .bool⟩, ⟨"b", .bool⟩]
      [.bool false, .bool true] =
      .ok ([[ ("b", .base ⟨2⟩), ("a", .base ⟨1⟩), ("a", .base ⟨999⟩) ]],
        { heap := #[.value .bool .nil, .value .bool (.bool false),
          .value .bool (.bool true)] }) := by with_unfolding_all rfl

theorem old_cell_not_repaired :
    ¬ BoolHeap {heap := #[.value .bool .nil, .value .bool (.bool false),
      .value .bool (.bool true)]} := by
  intro h
  obtain ⟨b, hb⟩ := h 0 (by decide +kernel)
  simp at hb

#print axioms generic_named_argument
#print axioms generic_named_result
#print axioms duplicate_canonical_distinct
#print axioms duplicate_actual_pins_alias
#print axioms duplicate_strongly_rejected
#print axioms mismatched_argument_count_is_not_zero
#print axioms binder_retains_hidden_bad_state
#print axioms old_cell_not_repaired
#print axioms setup_typed_exact
end BooleanInitializationAdversarial
