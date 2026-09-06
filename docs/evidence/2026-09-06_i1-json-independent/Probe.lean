import GoLean.NativeDeclaration

open Lean

private def observed (result : Except String Json) : Json :=
  match result with
  | .ok value => Json.mkObj [("ok", .bool true), ("value", value)]
  | .error message => Json.mkObj [("ok", .bool false), ("error", .str message)]

def main (args : List String) : IO Unit := do
  let [manifest] := args | throw (IO.userError "expected probe manifest")
  let output ← IO.getStdout
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    if line.isEmpty then continue
    let [name, path] := line.splitOn "\t" |
      throw (IO.userError "malformed probe manifest")
    let bytes ← IO.FS.readBinFile path
    -- The companion file deliberately replaces malformed UTF-8 outside the
    -- candidate, showing why checking an already-created String is too late.
    let text ← IO.FS.readFile (path ++ ".replacement")
    let old := Json.parse text
    let nominal : GoLean.NativeDeclaration.Nominals := [(⟨"�"⟩, 0)]
    let oldDecl := old.bind (GoLean.NativeDeclaration.decode [])
    let oldNominal := old.bind (GoLean.NativeDeclaration.decode nominal)
    output.putStrLn (Json.mkObj [
      ("name", .str name),
      ("bytes", observed (GoLean.StrictJson.parseBytes bytes)),
      ("text", observed (GoLean.StrictJson.parse text)),
      ("declarationBytes", .bool (GoLean.NativeDeclaration.decodeBytes [] bytes).toOption.isSome),
      ("oldParsedDeclaration", .bool oldDecl.toOption.isSome),
      ("nominalBytes", .bool (GoLean.NativeDeclaration.decodeBytes nominal bytes).toOption.isSome),
      ("oldParsedNominal", .bool oldNominal.toOption.isSome)]).compress
