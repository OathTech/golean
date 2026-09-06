import GoLean.NativeDeclaration
import GoLean.GoCore.DeclarationContext

/-! Exact package metadata input, separate from executable lowering.
The byte API parses the entire native document before field projection.
Bindings check final table indices/identities and signature shape. Source
typing and the correspondence of positive types to executable wire types
remain the compiler-correctness arrow, tested against the actual Go emitter;
this decoder supplies no execution, layout or runtime-query authority.
-/
namespace GoLean.NativeDeclarationPackage

open Lean GoLean.StrictJson
open GoLean.GoCore.Declaration

inductive FunctionOrigin where
  | source
  | closure
  | synthetic (helper : String)
  deriving Repr

structure FunctionBinding where
  declaration : FunctionDeclaration
  origin : FunctionOrigin
  sourceSignature : Option Signature
  captures : List Ty
  deriving Repr

inductive MethodOrigin where
  | source | promoted | interfaceAnchor | imported | sync | model
  deriving Repr

structure MethodBinding where
  declaration : MethodDeclaration
  origin : MethodOrigin
  receiverId : TypeId
  sourceReceiver : Ty
  deriving Repr

structure Package where
  packages : Array String
  nominals : NativeDeclaration.Nominals
  sourceNominals : List TypeId
  functions : Array FunctionBinding
  methods : Array MethodBinding
  interfaces : Array InterfaceDeclaration
  deriving Repr

def Package.context (p : Package) : Context := {
  functions := p.functions.map (·.declaration)
  methods := p.methods.map (·.declaration)
  interfaces := p.interfaces
}

private def str (p : String) (o : Obj) (k : String) : Except String String := do
  string (p ++ "." ++ k) (← field p o k)

private def arr (p : String) (o : Obj) (k : String) : Except String (Array Json) := do
  array (p ++ "." ++ k) (← field p o k)

private def flag (p : String) (o : Obj) (k : String) : Except String Bool := do
  bool (p ++ "." ++ k) (← field p o k)

private def nonempty (p value : String) : Except String String := do
  if value.isEmpty then throw s!"{p}: empty identity"
  return value

private def signature (ns : NativeDeclaration.Nominals) (p : String) (j : Json) :
    Except String Signature := do
  match ← NativeDeclaration.decode ns j with
  | .function ps rs v => return ⟨ps, rs, v⟩
  | _ => throw s!"{p}: declaration signature is not a function"

private def member (p : String) (j : Json) : Except String MemberId := do
  let o ← obj p j
  requireExactKeys p o ["name", "package"]
  return ⟨← nonempty p (← str p o "name"), ← str p o "package"⟩

private def indexIdentity (p : String) (o : Obj) (index : Nat) (id : String) :
    Except String Unit := do
  if (← nat (p ++ ".index") (← field p o "index")) != index then
    throw s!"{p}: declaration index differs from final native table index {index}"
  if (← str p o "id") != id then throw s!"{p}: declaration identity differs from native '{id}'"

private def shape (p : String) (o : Obj) (s : Signature) : Except String Unit := do
  if (← arr p o "params").size != s.params.length then throw s!"{p}: parameter arity differs"
  if (← arr p o "results").size != s.results.length then throw s!"{p}: result arity differs"
  if (← flag p o "variadic") != s.variadic then throw s!"{p}: variadic marker differs"

private def bindingParams (p : String) (o : Obj) : Except String Unit := do
  for key in ["params", "results"] do
    for j in (← arr p o key) do
      let param ← obj (p ++ "." ++ key) j
      requireExactKeys (p ++ "." ++ key) param ["id", "type"]
      let _ ← str p param "id"
      pure ()

private def helperRoles : List String := ["pkginit", "fmt", "fmt-composite", "fmt-slice",
  "defer-recover", "defer-close", "once-done", "once-do", "defer-sync", "sync-once-done"]

private def functionBinding (ns : NativeDeclaration.Nominals) (index : Nat)
    (wire facts : Json) : Except String FunctionBinding := do
  let p := s!"declarations.funcs[{index}]"
  let w ← obj (p ++ ".native") wire
  let id ← nonempty p (← str p w "name")
  let f ← obj p facts
  indexIdentity p f index id
  let sig ← signature ns p (← field p f "signature")
  let kind ← str p f "kind"
  let common := ["index", "id", "kind", "signature"]
  let (origin, source, captures) ← match kind with
    | "source" => do
        requireExactKeys p f (common ++ ["sourceSignature"])
        let s ← signature ns p (← field p f "sourceSignature")
        if s != sig then throw s!"{p}: source and ABI signatures differ"
        pure (FunctionOrigin.source, some s, [])
    | "closure" => do
        requireExactKeys p f (common ++ ["sourceSignature", "captures"])
        let s ← signature ns p (← field p f "sourceSignature")
        let cs ← mapArrayIdx (← arr p f "captures") fun _ j => NativeDeclaration.decode ns j
        for c in cs do
          match c with
          | .pointer _ => pure ()
          | _ => throw s!"{p}: closure capture ABI is not a pointer"
        if sig != { s with params := cs.toList ++ s.params } then
          throw s!"{p}: closure capture/source prefix does not equal ABI signature"
        pure (FunctionOrigin.closure, some s, cs.toList)
    | "synthetic" => do
        requireExactKeys p f (common ++ ["helper"])
        let h ← str p f "helper"
        if !helperRoles.contains h then throw s!"{p}: unknown synthetic helper role '{h}'"
        if sig.variadic then throw s!"{p}: synthetic helper signature is variadic"
        pure (FunctionOrigin.synthetic h, none, [])
    | _ => throw s!"{p}: unknown function declaration role '{kind}'"
  if w.contains "unsupported" then
    requireExactKeys (p ++ ".native") w ["name", "unsupported", "arity"]
    let _ ← str p w "unsupported"
    if (← nat p (← field p w "arity")) != sig.params.length then
      throw s!"{p}: refused function arity differs"
    match origin with
    | .source => pure ()
    | _ => throw s!"{p}: refused function is not a source declaration"
  else
    requireExactKeys (p ++ ".native") w ["name", "params", "results", "variadic", "body"]
    bindingParams p w
    shape p w sig
  return ⟨⟨⟨id⟩, sig⟩, origin, source, captures⟩

private def methodBinding (ns : NativeDeclaration.Nominals) (index : Nat)
    (wire facts : Json) : Except String MethodBinding := do
  let p := s!"declarations.methods[{index}]"
  let w ← obj (p ++ ".native") wire
  let name ← nonempty p (← str p w "name")
  let recvId ← nonempty p (← str p w "recvType")
  let id := recvId ++ "." ++ name
  let f ← obj p facts
  requireExactKeys p f ["index", "id", "kind", "signature", "member", "receiver",
    "sourceReceiver", "receiverId"]
  indexIdentity p f index id
  if (← str p f "receiverId") != recvId then throw s!"{p}: adapter receiver identity differs"
  let mid ← member p (← field p f "member")
  if mid.name != name then throw s!"{p}: method member identity differs"
  let sig ← signature ns p (← field p f "signature")
  let receiver ← NativeDeclaration.decode ns (← field p f "receiver")
  let original ← NativeDeclaration.decode ns (← field p f "sourceReceiver")
  let kind ← str p f "kind"
  let origin ← match kind with
    | "source" => pure MethodOrigin.source
    | "promoted" => pure MethodOrigin.promoted
    | "interface" => pure MethodOrigin.interfaceAnchor
    | "imported" => pure MethodOrigin.imported
    | "sync" => pure MethodOrigin.sync
    | "model" => pure MethodOrigin.model
    | _ => throw s!"{p}: unknown method declaration role '{kind}'"
  let optional := ["body", "unsupported", "wrapper", "interface"].filter (w.contains ·)
  requireExactKeys (p ++ ".native") w
    (["name", "recvType", "recv", "params", "results", "variadic"] ++ optional)
  for key in ["wrapper", "interface"] do
    if w.contains key then let _ ← flag p w key; pure ()
  if w.contains "unsupported" then let _ ← str p w "unsupported"; pure ()
  let anchor ← if w.contains "interface" then flag p w "interface" else pure false
  if anchor != (kind == "interface") then throw s!"{p}: interface anchor role differs"
  if (w.contains "body") == (w.contains "unsupported" || anchor) then
    throw s!"{p}: conflicting or absent native declaration body role"
  if kind == "source" && receiver != original then throw s!"{p}: source receiver differs"
  let recv ← obj (p ++ ".native.recv") (← field p w "recv")
  requireExactKeys (p ++ ".native.recv") recv ["id", "type"]
  let _ ← str p recv "id"
  bindingParams p w
  shape p w sig
  return ⟨⟨⟨id⟩, mid, receiver, sig⟩, origin, ⟨recvId⟩, original⟩

private def interfaceBinding (ns : NativeDeclaration.Nominals) (types : Array Json)
    (j : Json) : Except String (Nat × InterfaceDeclaration) := do
  let p := "declarations.interfaces"
  let o ← obj p j
  requireExactKeys p o ["index", "id", "type"]
  let index ← nat p (← field p o "index")
  let some wire := types[index]? | throw s!"{p}: interface type index out of range"
  let td ← obj p wire
  let id ← nonempty p (← str p td "name")
  indexIdentity p o index id
  let defn ← obj p (← field p td "def")
  if (← str p defn "kind") != "interface" then throw s!"{p}: native type is not an interface"
  let .interfaceType methods ← NativeDeclaration.decode ns (← field p o "type")
    | throw s!"{p}: requirement declaration is not an interface"
  let old ← arr p defn "methods"
  if old.size != methods.length then throw s!"{p}: incomplete interface requirement set"
  -- The old runtime headers omit declaring packages. Distinct private
  -- requirements may therefore share a name, even with different shapes.
  -- Match their projected header multiset once each; retain full positive
  -- MemberIds. This shape check supplies no lost package/type information.
  let mut remaining := methods
  for wireMethod in old do
    let m ← obj p wireMethod
    requireExactKeys p m ["name", "params", "results", "variadic"]
    let name ← str p m "name"
    let params ← arr p m "params"
    let results ← arr p m "results"
    let variadic ← flag p m "variadic"
    let some matched := remaining.find? fun (.mk id ps rs v) =>
        id.name == name && ps.length == params.size && rs.length == results.size && v == variadic
      | throw s!"{p}: native interface header has no remaining requirement with matching name/arity/variadicness"
    remaining := remaining.erase matched
  return (index, ⟨⟨id⟩, methods⟩)

/-- A parsed-object API cannot recover duplicates or Unicode already lost by
its caller. Use `decodeBytes` at an external package boundary. The executable
body, non-interface layouts and globals are not validated by this API. -/
def decode (json : Json) : Except String Package := do
  let root ← obj "program" json
  let optional := ["globals"].filter (root.contains ·)
  requireExactKeys "program" root (["schema", "package", "types", "funcs", "methods",
    "methodSets", "fileOrder", "declarations"] ++ optional)
  if (← str "program" root "schema") != "golean-native-v1" then throw "program: wrong native schema"
  let o ← obj "declarations" (← field "program" root "declarations")
  requireExactKeys "declarations" o ["schema", "packages", "nominals", "sourceNominals",
    "funcs", "methods", "interfaces"]
  if (← str "declarations" o "schema") != "golean-declarations-v1" then
    throw "declarations: wrong envelope schema"
  let packages ← mapArrayIdx (← arr "declarations" o "packages") fun _ j => do
    nonempty "declarations.packages" (← string "declarations.packages" j)
  if packages.isEmpty || packages.toList.eraseDups.length != packages.size then
    throw "declarations: empty or duplicate package unit inventory"
  let order ← arr "program" root "fileOrder"
  if order.size != packages.size then throw "declarations: package/file-order inventory differs"
  for i in [:order.size] do
    let entry ← obj "fileOrder" order[i]!
    if (← str "fileOrder" entry "package") != packages[i]! then
      throw "declarations: package unit order differs from actual native file order"
  let ns ← mapArrayIdx (← arr "declarations" o "nominals") fun _ j => do
    let n ← obj "nominals" j
    requireExactKeys "nominals" n ["id", "arity"]
    return (TypeId.mk (← nonempty "nominals" (← str "nominals" n "id")),
      ← nat "nominals.arity" (← field "nominals" n "arity"))
  let ns := ns.toList
  -- Validate even an envelope whose signatures reference no nominal type.
  let _ ← NativeDeclaration.decode ns (Json.mkObj [("kind", .str "basic"), ("basic", .str "bool")])
  let source ← mapArrayIdx (← arr "declarations" o "sourceNominals") fun _ j => do
    return TypeId.mk (← nonempty "sourceNominals" (← string "sourceNominals" j))
  let source := source.toList
  if source.eraseDups.length != source.length then throw "declarations: duplicate source nominal origin"
  let wf ← arr "program" root "funcs"
  let ff ← arr "declarations" o "funcs"
  let wm ← arr "program" root "methods"
  let fm ← arr "declarations" o "methods"
  if wf.size != ff.size || wm.size != fm.size then throw "declarations: function/method inventory differs"
  let fs ← mapArrayIdx ff fun i j => functionBinding ns i wf[i]! j
  let ms ← mapArrayIdx fm fun i j => methodBinding ns i wm[i]! j
  let ids := (fs.toList.map (·.declaration.id)) ++ (ms.toList.map (·.declaration.funcId))
  if ids.eraseDups.length != ids.length then throw "declarations: duplicate function identity"
  let ts ← arr "program" root "types"
  let bindings ← mapArrayIdx (← arr "declarations" o "interfaces") fun _ j => interfaceBinding ns ts j
  let mut expected : List (Nat × TypeId) := []
  let mut typeIds : List String := []
  for index in [:ts.size] do
    let td ← obj "program.types" ts[index]!
    let id ← nonempty "program.types" (← str "program.types" td "name")
    if typeIds.contains id then throw "declarations: duplicate native type identity"
    typeIds := id :: typeIds
    let d ← obj "program.types.def" (← field "program.types" td "def")
    if (← str "program.types.def" d "kind") == "interface" then
      expected := expected ++ [(index, ⟨id⟩)]
  if bindings.toList.map (fun (index, decl) => (index, decl.id)) != expected then
    throw "declarations: incomplete or reordered interface inventory"
  let intfs := bindings.map Prod.snd
  let mut refs := source
  for f in fs do
    refs := refs ++ f.declaration.signature.type.nominalRefs
    if let some s := f.sourceSignature then refs := refs ++ s.type.nominalRefs
  for m in ms do
    refs := refs ++ m.declaration.signature.type.nominalRefs ++
      m.declaration.receiver.nominalRefs ++ m.sourceReceiver.nominalRefs
  for i in intfs do refs := refs ++ methodsNominalRefs i.methods
  let allIds := ns.map Prod.fst
  if !(refs.all allIds.contains) || !(allIds.all refs.contains) then
    throw "declarations: nominal origin inventory does not equal source/reference closure"
  return ⟨packages, ns, source, fs, ms, intfs⟩

def decodeBytes (input : ByteArray) : Except String Package := do
  decode (← GoLean.StrictJson.parseBytes input)

end GoLean.NativeDeclarationPackage
