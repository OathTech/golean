import Tests.DeclarationWire
import Tests.DeclarationUnicode

def main (args : List String) : IO UInt32 := do
  match args with
  | "--unicode" :: rest => GoLean.DeclarationUnicodeTests.main rest; return 0
  | _ => GoLean.DeclarationWireTests.main args
