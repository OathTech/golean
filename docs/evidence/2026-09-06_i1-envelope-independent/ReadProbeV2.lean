import GoLean.NativeDeclarationPackage
open GoLean
 def main (args : List String) : IO Unit := do
  for path in args do
    let bytes ← IO.FS.readBinFile path
    match NativeDeclarationPackage.decodeBytes bytes with
    | .error err => IO.println (path ++ "|REJECTED|" ++ err)
    | .ok p =>
      let rows := p.interfaces.toList.flatMap fun iface => iface.methods.map fun (.mk id ps rs v) =>
        s!"{id.package}.{id.name}:{ps.length}/{rs.length}/{v}"
      IO.println (path ++ "|ACCEPTED|" ++ String.intercalate "," rows)
