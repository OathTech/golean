import GoLean.NativeDeclaration
open Lean GoLean GoLean.GoCore.Declaration GoLean.NativeDeclaration

def b (name : String) := Json.mkObj [("kind", .str "basic"), ("basic", .str name)]
def named (id : String) (as : Array Json) := Json.mkObj [("kind", .str "named"), ("id", .str id), ("args", .arr as)]
def mem (name pkg : String) := Json.mkObj [("name", .str name), ("package", .str pkg)]
def sig (ps rs : Array Json) (v : Bool := false) := Json.mkObj [("kind", .str "func"), ("params", .arr ps), ("results", .arr rs), ("variadic", .bool v)]
def method (name pkg : String) (s : Json) := Json.mkObj [("id", mem name pkg), ("signature", s)]
def iface (ms : Array Json) := Json.mkObj [("kind", .str "interface"), ("methods", .arr ms)]
def field (name pkg : String) (ty : Json) (e : Bool) (tag : Array Json) := Json.mkObj [("id",mem name pkg),("type",ty),("embedded",.bool e),("tagBytes",.arr tag)]
def structTy (fs : Array Json) := Json.mkObj [("kind",.str "struct"),("fields",.arr fs)]
def ensure (condition : Bool) (label : String) : IO Unit := unless condition do throw (IO.userError label)
def rejects (ns : Nominals) (j : Json) : Bool := match decode ns j with | .error _ => true | .ok _ => false

def main : IO Unit := do
  let ns : Nominals := [(⟨"N"⟩,2), (⟨"M"⟩,2)]
  let n ← IO.ofExcept (decode ns (named "N" #[b "int", b "bool"]))
  for j in [named "N" #[b "bool",b "int"], named "M" #[b "int",b "bool"]] do
    ensure (n != (← IO.ofExcept (decode ns j))) "nominal argument/order identity collision"
  ensure (rejects ns (named "N" #[b "int"])) "nominal arity accepted"
  ensure (rejects ns (named "N" #[b "int",named "Missing" #[]])) "nested unknown nominal accepted"
  ensure (rejects [(⟨"N"⟩,2),(⟨"N"⟩,3)] (b "bool")) "duplicate inventory ignored on basic type"
  let ms := #[method "z" "p" (sig #[b "int"] #[]), method "z" "q" (sig #[] #[b "bool"])]
  let a ← IO.ofExcept (decode [] (iface ms))
  let z ← IO.ofExcept (decode [] (iface ms.reverse))
  ensure (a == z) "package-sensitive method order failed"
  ensure (rejects [] (iface #[ms[0]!,method "z" "p" (sig #[] #[])])) "conflicting method duplicate accepted"
  let wrap := fun x => sig #[x] #[iface #[method "Outer" "" (sig #[x] #[])]]
  ensure ((← IO.ofExcept (decode [] (wrap (iface ms)))) == (← IO.ofExcept (decode [] (wrap (iface ms.reverse))))) "nested normalization failed"
  let f := field "x" "p" (b "bool") false #[Json.num 0,Json.num 255,Json.num 128]
  let fv ← IO.ofExcept (decode [] (structTy #[f]))
  for j in [field "x" "q" (b "bool") false #[Json.num 0,Json.num 255,Json.num 128],
    field "x" "p" (b "bool") true #[Json.num 0,Json.num 255,Json.num 128],
    field "x" "p" (b "bool") false #[Json.num 0,Json.num 255,Json.num 129]] do
    ensure (fv != (← IO.ofExcept (decode [] (structTy #[j])))) "field identity collision"
  ensure (rejects [] (structTy #[field "x" "p" (b "bool") false #[Json.num 256]])) "bad byte accepted"
  ensure (rejects [] (iface #[method "" "p" (sig #[] #[])])) "empty method name accepted"
  ensure (rejects [] (sig #[b "int"] #[] true)) "invalid variadic accepted"
  ensure (rejects [] (Json.mkObj [("kind",.str "basic"),("basic",.str "bool"),("supported",.bool true)])) "extra support flag accepted"
  IO.println "Independent I1 decoder: 15 nested/order/alias/schema challenges PASS"

example (a b : Ty) : (a == b) = true ↔ a = b := equality_exact.1 a b
#print axioms GoLean.GoCore.Declaration.equality_exact
