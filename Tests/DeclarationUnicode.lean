import GoLean.DeclarationUnicode

namespace GoLean.DeclarationUnicodeTests

/-- Compare every code point, including holes between table ranges and strides,
against a fresh Go unicode.IsUpper bitmap, independently of the generated table. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected Go uppercase bitmap path")
  let bytes ← IO.FS.readBinFile path
  unless bytes.size == 0x110000 / 8 do
    throw (IO.userError "incomplete Go uppercase bitmap")
  for code in [:0x110000] do
    let want := ((bytes[code / 8]!).toNat >>> (code % 8)) &&& 1 == 1
    unless GoLean.DeclarationUnicode.isUpperCode code == want do
      throw (IO.userError s!"Go/Lean Unicode uppercase mismatch at {code}")
  IO.println "Declaration Unicode: PASS; all 1114112 code points match Go unicode.IsUpper"

end GoLean.DeclarationUnicodeTests
