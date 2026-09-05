import GoLean.GoCore.Admission

namespace GoLean.GoCore.Admission.Tests

/-- Complete GoCore artifact for `Tests/admission-fixture/main.go`, checked
against a fresh native emission/lowering by `scripts/check-admission`.
This executable comparison is not a compiler-correctness theorem. -/
def fixture : Program := {
  funcs := #[
    { id := ⟨"Negate"⟩, args := #[⟨"b", .bool⟩], results := #[⟨"result", .bool⟩]
      body := .block #[] #[.seqn #[.assign (.var "result") (.not (.var "b"))], .returnStmt] },
    { id := ⟨"Constant"⟩, args := #[], results := #[⟨"result", .bool⟩]
      body := .block #[] #[.seqn #[.assign (.var "result") (.boolLit true)], .returnStmt] }]
  methods := #[], globals := #[]
  methodSets := #[{ key := "struct{}", coverage := .full }]
}

end GoLean.GoCore.Admission.Tests
