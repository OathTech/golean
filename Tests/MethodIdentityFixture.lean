import Tests.MethodIdentity

/-! The method-identity check that CANNOT run at build time (lane `gate/contract-pins-1025`,
2026-10-25; release-readiness row 42's follow-up): the FRESH executable member wire that the
frontend's own Go tests write (`tools/nativefrontend/memberidentity_test.go`,
`GOLEAN_METHOD_IDENTITY_FIXTURE`) is read by the strict decoder and its checked identities, the
promoted records and the exact member schema are checked, with the named malformed controls. It
needs a subprocess (the Go tests), the filesystem (the fixture) and a process argument (its path),
and a build-time read of a fixed path would be cached by Lake's trace — a changed fixture would not
rebuild the module — so this stays a `lean --run` module driven by `scripts/check-method-identity`:
library `MethodIdentityFixtureTests`, built by name, NOT a default target (its `main` would stop
`lake check`), carrying no theorem. The twelve theorems and the two in-memory controls are in
`Tests/MethodIdentity.lean` (a default target, under `lake check`), whose wire-building helpers this
module reuses. -/

open Lean GoLean GoLean.GoCore

namespace GoLean.MethodIdentityTests

def fixtureMain (args : List String) : IO Unit := do
  let [fixture] := args | throw (IO.userError "expected fresh executable member fixture")
  let p ← IO.ofExcept (NativeToIR.decodeProgram (← IO.ofExcept
    (StrictJson.parseBytes (← IO.FS.readBinFile fixture))))
  for recv in ["main.T", "main.I"] do
    for (name, pkg) in [("m", "main"), ("M", ""), ("é", "main"), ("É", ""),
        ("ǅ", "main"), ("𐐀", "")] do
      check (p.methods.any fun m => m.funcId == methodFuncId recv ⟨name, pkg⟩ &&
        m.id == Declaration.MemberId.mk name pkg) s!"lost checked identity {recv}.{pkg}:{name}"
  -- main.S's entries are PROMOTED (G-P S2): promotion records on the same
  -- checked identity, each resolving to main.T's declared method.
  for (name, pkg) in [("m", "main"), ("M", ""), ("é", "main"), ("É", ""),
      ("ǅ", "main"), ("𐐀", "")] do
    check (p.promotions.any fun r => r.type == ⟨"main.S"⟩ &&
      r.member == Declaration.MemberId.mk name pkg &&
      r.target == .method (methodFuncId "main.T" ⟨name, pkg⟩))
      s!"lost checked promoted identity main.S.{pkg}:{name}"
  for (name, pkg) in [("M", ""), ("É", ""), ("Σ", ""), ("𐐀", ""),
      ("m", "red/inner"), ("é", "blue/inner"), ("ǅ", "main")] do
    let id := member name pkg
    check (NativeToIR.decodeProgram (program #[requirement id] #[method id])).isOk
      s!"valid executable identity refused: {id.compress}"
  for (id, reason) in [
      (member "m" "", "unexported member has no package identity"),
      (member "ǅ" "", "unexported member has no package identity"),
      (member "M" "p", "exported member carries a package identity"),
      (member "𐐀" "p", "exported member carries a package identity"),
      (member "" "p", "empty member name"),
      (Json.mkObj [("name", .str "m")], "package"),
      (Json.mkObj [("name", .str "m"), ("package", .num 4)], "String expected"),
      (Json.mkObj [("name", .num 4), ("package", .str "p")], "String expected"),
      (Json.mkObj [("name", .str "m"), ("package", .str "p"), ("pkg", .str "q")], "pkg")] do
    reject (program #[requirement id] #[]) "program.types[1].def.methods[0].id" reason
    reject (program #[] #[method id]) "program.methods[0].id" reason
  let id := member "m" "p"
  let oldReq := Json.mkObj [("name", .str "m"), ("params", .arr #[]),
    ("results", .arr #[]), ("variadic", .bool false)]
  reject (program #[oldReq] #[]) "program.types[1].def.methods[0]" "name"
  let withoutId := Json.mkObj [("params", .arr #[]), ("results", .arr #[]), ("variadic", .bool false)]
  reject (program #[withoutId] #[]) "program.types[1].def.methods[0]" "missing field 'id'"
  let methodObj ← IO.ofExcept ((method id).getObj?)
  let legacyMethod := Json.mkObj ((methodObj.toList.filter fun x => x.1 != "id") ++ [("name", .str "m")])
  reject (program #[] #[legacyMethod]) "program.methods[0]" "name"
  let missingMethod := Json.mkObj (methodObj.toList.filter fun x => x.1 != "id")
  reject (program #[] #[missingMethod]) "program.methods[0]" "missing field 'id'"
  let conflicting := Json.mkObj (methodObj.toList ++ [("name", .str "other")])
  reject (program #[] #[conflicting]) "program.methods[0]" "name"
  reject (program #[requirement id, requirement id] #[]) "program.types[1]" "duplicate interface member"
  check (NativeToIR.decodeProgram (program #[requirement id, requirement (member "m" "q")] #[])).isOk
    "distinct package requirements collapsed"
  IO.println "Method identity: PASS; fresh checked-object fixture, exact member schema, named malformed controls"

end GoLean.MethodIdentityTests

def main := GoLean.MethodIdentityTests.fixtureMain
