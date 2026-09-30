import GoLean.GoCore.Admission

namespace GoLean.GoCore.Admission.Tests
/-- B6 (2026-09-30): a spelling interned injectively into a `VarId` (test-local). -/
def vid (s : String) : GoLean.GoCore.VarId := s.toUTF8.foldl (fun n b => n * 256 + b.toNat) 0

/-- Complete GoCore artifact for `Tests/admission-fixture/main.go`, checked
against a fresh native emission/lowering by `scripts/check-admission`.
This executable comparison is not a compiler-correctness theorem. -/
def fixture : Program := {
  funcs := #[
    { id := ⟨"Negate"⟩, args := #[⟨vid "b", .bool⟩], results := #[⟨vid "result", .bool⟩]
      body := .block #[] #[.seqn #[.assign (.var (vid "result")) (.not (.var (vid "b")))], .returnStmt] },
    { id := ⟨"Constant"⟩, args := #[], results := #[⟨vid "result", .bool⟩]
      body := .block #[] #[.seqn #[.assign (.var (vid "result")) (.boolLit true)], .returnStmt] }]
  methods := #[], globals := #[]
  methodSets := #[{ key := "struct{}", coverage := .full }]
}

end GoLean.GoCore.Admission.Tests
