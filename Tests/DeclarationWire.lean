import GoLean.NativeDeclaration

open Lean GoLean GoLean.StrictJson GoLean.NativeDeclaration

namespace GoLean.DeclarationWireTests

private def failCheck (msg : String) : IO α := throw (IO.userError msg)

private def check (condition : Bool) (msg : String) : IO Unit :=
  unless condition do failCheck msg

private def parsed (text : String) : IO Json := IO.ofExcept (GoLean.StrictJson.parse text)

private def refused (value : Except String α) : Bool :=
  match value with
  | .error _ => true
  | .ok _ => false

private def reject (name text : String) (ns : Nominals := []) : IO Unit := do
  match decode ns (← parsed text) with
  | .error _ => pure ()
  | .ok value => failCheck s!"{name}: malformed declaration accepted as {repr value}"

private def reviewControls : IO Unit := do
  let basic := Json.mkObj [("kind", .str "basic"), ("basic", .str "bool")]
  let signature := Json.mkObj [("kind", .str "func"), ("params", .arr #[]),
    ("results", .arr #[]), ("variadic", .bool false)]
  let member := fun name pkg => Json.mkObj [("name", .str name), ("package", .str pkg)]
  let field := fun name pkg => Json.mkObj [("id", member name pkg), ("type", basic),
    ("embedded", .bool false), ("tagBytes", .arr #[])]
  let structWire := fun fields => Json.mkObj [("kind", .str "struct"), ("fields", .arr fields)]
  let iface := fun name pkg => Json.mkObj [("kind", .str "interface"), ("methods", .arr #[
    Json.mkObj [("id", member name pkg), ("signature", signature)]])]
  let rejectNamed := fun value reason => do
    match decodeBytes [] value.compress.toUTF8 with
    | .ok _ => failCheck s!"review control accepted: {value.compress}"
    | .error message =>
        check ((message.splitOn reason).length > 1) s!"wrong review refusal: {message}"
  for (name, pkg, reason) in [
      ("x", "", "unexported member has no package identity"),
      ("X", "p", "exported member carries a package identity"),
      ("é", "", "unexported member has no package identity"),
      ("ǅ", "", "unexported member has no package identity"),
      ("É", "p", "exported member carries a package identity"),
      ("𐐀", "p", "exported member carries a package identity") ] do
    rejectNamed (structWire #[field name pkg]) reason
    rejectNamed (iface name pkg) reason
  for (name, pkg) in [("X", ""), ("É", ""), ("Σ", ""), ("𐐀", ""),
      ("x", "p"), ("é", "p"), ("ǅ", "p"), ("_", "p")] do
    check (decode [] (structWire #[field name pkg])).toOption.isSome
      s!"valid field identity refused: {name}"
    if name != "_" then
      check (decode [] (iface name pkg)).toOption.isSome
        s!"valid method identity refused: {name}"
  rejectNamed (structWire #[field "X" "", field "X" ""]) "duplicate struct field"
  rejectNamed (structWire #[field "x" "p", field "x" "p"]) "duplicate struct field"
  check (decode [] (structWire #[field "_" "p", field "_" "p"])).toOption.isSome
    "Go permits repeated blank fields"
  check (decode [] (structWire #[field "x" "p", field "x" "q"])).toOption.isSome
    "different private field identities collapsed"
  let forward ← IO.ofExcept (decode [] (structWire #[field "A" "", field "B" ""]))
  let backward ← IO.ofExcept (decode [] (structWire #[field "B" "", field "A" ""]))
  check (forward != backward) "struct fields reordered during duplicate check"
  IO.println "Declaration review controls: PASS; member export/package agreement and ordered unique nonblank fields"

def main (args : List String) : IO UInt32 := do
  reviewControls
  let [path] := args | failCheck "expected the fresh Go declaration fixture path"
  let json ← IO.ofExcept (GoLean.StrictJson.parseBytes (← IO.FS.readBinFile path))
  let o ← IO.ofExcept (obj "fixture" json)
  IO.ofExcept (requireExactKeys "fixture" o ["schema", "nominals", "types", "pairs"])
  check ((← IO.ofExcept do string "schema" (← field "fixture" o "schema")) ==
    "i1-declaration-test-v1") "wrong fixture schema"
  let nominals ← IO.ofExcept do
    let values ← array "nominals" (← field "fixture" o "nominals")
    mapArrayIdx values fun i value => do
      let p := s!"nominals[{i}]"
      let no ← obj p value
      requireExactKeys p no ["id", "arity"]
      let id ← string p (← field p no "id")
      let arity ← nat p (← field p no "arity")
      return (TypeId.mk id, arity)
  let types ← IO.ofExcept do
    let values ← array "types" (← field "fixture" o "types")
    mapArrayIdx values fun i value => do
      let p := s!"types[{i}]"
      let row ← obj p value
      requireExactKeys p row ["name", "type"]
      let name ← string p (← field p row "name")
      let ty ← decode nominals.toList (← field p row "type")
      return (name, ty)
  let pairs ← IO.ofExcept do array "pairs" (← field "fixture" o "pairs")
  check (types.size == 24 && pairs.size == 576) "fixture inventory is incomplete"
  for i in [:pairs.size] do
    let p := s!"pairs[{i}]"
    let row ← IO.ofExcept (obj p pairs[i]!)
    let (left, right, want) ← IO.ofExcept do
      requireExactKeys p row ["left", "right", "equal"]
      return (← nat p (← field p row "left"), ← nat p (← field p row "right"),
        ← bool p (← field p row "equal"))
    let some a := types[left]? | failCheck s!"{p}: invalid left index"
    let some b := types[right]? | failCheck s!"{p}: invalid right index"
    check (left == i / types.size && right == i % types.size)
      s!"{p}: duplicate, missing or reordered identity pair"
    check ((a.2 == b.2) == want) s!"Go/Lean declaration identity differs: {a.1} / {b.1}"

  for (name, text) in [
      ("old unsupported marker", "{\"kind\":\"unsupported\",\"reason\":\"complex\"}"),
      ("unknown basic", "{\"kind\":\"basic\",\"basic\":\"untyped int\"}"),
      ("missing basic", "{\"kind\":\"basic\"}"),
      ("extra body", "{\"kind\":\"basic\",\"basic\":\"bool\",\"body\":null}"),
      ("unknown nominal", "{\"kind\":\"named\",\"id\":\"missing\",\"args\":[]}"),
      ("negative length", "{\"kind\":\"array\",\"len\":-1,\"elem\":{\"kind\":\"basic\",\"basic\":\"bool\"}}"),
      ("invalid direction", "{\"kind\":\"chan\",\"direction\":\"guess\",\"elem\":{\"kind\":\"basic\",\"basic\":\"bool\"}}"),
      ("variadic empty", "{\"kind\":\"func\",\"params\":[],\"results\":[],\"variadic\":true}"),
      ("variadic scalar", "{\"kind\":\"func\",\"params\":[{\"kind\":\"basic\",\"basic\":\"bool\"}],\"results\":[],\"variadic\":true}")
    ] do reject name text
  let named := "{\"kind\":\"named\",\"id\":\"N\",\"args\":[]}"
  reject "wrong nominal arity" named [(⟨"N"⟩, 1)]
  reject "duplicate nominal declaration" named [(⟨"N"⟩, 0), (⟨"N"⟩, 0)]
  reject "empty nominal declaration" named [(⟨""⟩, 0)]

  let basicBool := Json.mkObj [("kind", .str "basic"), ("basic", .str "bool")]
  let member := fun name => Json.mkObj [("name", .str name), ("package", .str "")]
  let fieldWithTag := fun tag => Json.mkObj [("id", member "X"), ("type", basicBool),
    ("embedded", .bool false), ("tagBytes", tag)]
  for bad in [Json.num 256, Json.num (-1), Json.str "ff"] do
    let ty := Json.mkObj [("kind", .str "struct"), ("fields", .arr #[fieldWithTag (.arr #[bad])])]
    check (refused (decode [] ty)) "malformed struct tag byte accepted"
  let signature := Json.mkObj [("kind", .str "func"), ("params", .arr #[]),
    ("results", .arr #[]), ("variadic", .bool false)]
  let method := fun name sig => Json.mkObj [("id", member name), ("signature", sig)]
  let iface := fun methods => Json.mkObj [("kind", .str "interface"), ("methods", .arr methods)]
  check (refused (decode [] (iface #[method "A" signature, method "A" signature])))
    "duplicate interface method accepted"
  check (refused (decode [] (iface #[method "A" basicBool]))) "non-function method accepted"
  let ordered ← IO.ofExcept (decode [] (iface #[method "A" signature, method "Z" signature]))
  let reversed ← IO.ofExcept (decode [] (iface #[method "Z" signature, method "A" signature]))
  check (ordered == reversed) "interface declaration equality depends on wire method order"
  IO.println "Declaration wire: PASS; 24 fresh Go types, 576 go/types identity pairs, 17 malformed-input controls, method-order normalization"
  return 0

end GoLean.DeclarationWireTests
