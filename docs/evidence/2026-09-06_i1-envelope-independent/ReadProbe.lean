import GoLean.NativeDeclarationPackage
open GoLean
 def main (args : List String) : IO Unit := do
  for path in args do
    let bytes ← IO.FS.readBinFile path
    match NativeDeclarationPackage.decodeBytes bytes with
    | .error err => IO.println ("REJECTED: " ++ err)
    | .ok p => IO.println ("ACCEPTED; interfaces=" ++ toString p.interfaces.size)
