import GoLean.GoCore.BooleanTyping

namespace GoLean.GoCore.BooleanTyping.Tests

/-- Complete native artifact for boolean-typing-fixture/main.go, compared
with fresh emission/lowering by scripts/check-boolean-typing. -/
def nativeFixture : Program := {
  funcs := #[
    { id := ⟨"Argument"⟩, args := #[⟨"b", .bool⟩], results := #[⟨"result", .bool⟩]
      body := .block #[] #[
        .seqn #[.assign (.var "result") (.and (.var "b") (.boolLit true))],
        .returnStmt] },
    { id := ⟨"Shadow"⟩, args := #[], results := #[⟨"result", .bool⟩]
      body := .block #[] #[
        .seqn #[.initialization ⟨"x", .bool⟩, .assign (.var "x") (.boolLit true)],
        .block #[] #[
          .seqn #[.initialization ⟨"$c0", .bool⟩, .assign (.var "$c0") (.not (.var "x"))],
          .seqn #[.initialization ⟨"x", .bool⟩, .assign (.var "x") (.var "$c0")],
          .seqn #[.assign (.var "result") (.var "x")]],
        .seqn #[.assign (.var "result") (.and (.var "result") (.var "x"))],
        .returnStmt] },
    { id := ⟨"Branches"⟩, args := #[], results := #[⟨"result", .bool⟩]
      body := .block #[] #[
        .seqn #[.initialization ⟨"b", .bool⟩],
        .ifThenElse (.var "b")
          (.block #[] #[.seqn #[.assign (.var "result") (.boolLit true)], .returnStmt])
          (.block #[] #[.seqn #[.assign (.var "result") (.boolLit false)], .returnStmt])] },
    { id := ⟨"Zero"⟩, args := #[], results := #[⟨"result", .bool⟩]
      body := .block #[] #[
        .seqn #[.initialization ⟨"zero", .bool⟩],
        .seqn #[.assign (.var "result") (.or (.var "result") (.var "zero"))],
        .returnStmt] }]
  methodSets := #[{ key := "struct{}", coverage := .full }]
}

set_option maxRecDepth 4096

theorem native_argument_true :
    checkTypedBoolean nativeFixture "Argument" #[.bool true] = .ok () := by
  with_unfolding_all rfl
theorem native_argument_false :
    checkTypedBoolean nativeFixture "Argument" #[.bool false] = .ok () := by
  with_unfolding_all rfl
theorem native_shadow : checkTypedBoolean nativeFixture "Shadow" #[] = .ok () := by
  with_unfolding_all rfl
theorem native_branches : checkTypedBoolean nativeFixture "Branches" #[] = .ok () := by
  with_unfolding_all rfl
theorem native_zero : checkTypedBoolean nativeFixture "Zero" #[] = .ok () := by
  with_unfolding_all rfl

end GoLean.GoCore.BooleanTyping.Tests
