import GoLean.NativeDeclarationPackage

namespace GoLean.DeclarationPackageTests

open Lean GoLean.StrictJson GoLean.GoCore.Declaration

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

/-- Read the actual enclosing native bytes. The optional second input contains
fresh Go equality observations, never pre-decoded Lean declaration values. -/
def main (args : List String) : IO UInt32 := do
  let path :: rest := args | throw (IO.userError "expected native package path")
  let p ← IO.ofExcept (NativeDeclarationPackage.decodeBytes (← IO.FS.readBinFile path))
  match rest with
  | [] => pure ()
  | [queries] =>
      let input ← IO.FS.readBinFile queries
      let rows ← IO.ofExcept do array "queries" (← GoLean.StrictJson.parseBytes input)
      for row in rows do
        let o ← IO.ofExcept (obj "query" row)
        if o.contains "nominal" then
          let (id, arity) ← IO.ofExcept do
            requireExactKeys "query" o ["nominal", "arity"]
            return (← string "nominal" (← field "query" o "nominal"),
              ← nat "arity" (← field "query" o "arity"))
          let some (_, actual) := p.nominals.find? (fun n => n.1.key == id)
            | throw (IO.userError s!"missing Go source origin {id}")
          check (actual == arity) s!"Go/Lean nominal arity differs: {id}"
          continue
        if o.contains "method" then
          let (id, receiver, original, ifaceId, want) ← IO.ofExcept do
            requireExactKeys "query" o ["method", "receiver", "declaringReceiver", "interface", "satisfies"]
            return (← string "method" (← field "query" o "method"),
              ← string "receiver" (← field "query" o "receiver"),
              ← string "declaringReceiver" (← field "query" o "declaringReceiver"),
              ← string "interface" (← field "query" o "interface"),
              ← bool "satisfies" (← field "query" o "satisfies"))
          let some m := p.methods.toList.find? (fun m => m.declaration.funcId.key == id)
            | throw (IO.userError s!"missing Go method {id}")
          check (m.declaration.receiver == Ty.named ⟨receiver⟩ []) s!"Go/Lean adapter receiver differs: {id}"
          check (m.sourceReceiver == Ty.named ⟨original⟩ []) s!"Go/Lean declaring receiver differs: {id}"
          let some required := p.interfaces.toList.find? (fun i => i.id.key == ifaceId)
            | throw (IO.userError s!"missing Go interface {ifaceId}")
          -- This fixture has exactly one requirement. It checks an actual
          -- selected method, not a general dynamic-dispatch algorithm.
          check (required.methods.length == 1) "Go method query inventory differs"
          let got := required.methods.all fun (.mk mid ps rs v) =>
            m.declaration.member == mid && p.context.methodMatches ⟨id⟩ ⟨ps, rs, v⟩
          check (got == want) s!"Go/Lean selected method satisfaction differs: {id}"
          continue
        if o.contains "requirements" then
          let (id, requirements) ← IO.ofExcept do
            requireExactKeys "query" o ["interface", "requirements"]
            return (← string "interface" (← field "query" o "interface"),
              ← array "requirements" (← field "query" o "requirements"))
          let some actual := p.interfaces.toList.find? (fun i => i.id.key == id)
            | throw (IO.userError s!"missing Go interface {id}")
          check (actual.methods.length == requirements.size) "Go/Lean private requirement count differs"
          let mut seen : List MemberId := []
          for requirement in requirements do
            let (member, params, results, variadic) ← IO.ofExcept do
              let r ← obj "requirement" requirement
              requireExactKeys "requirement" r ["name", "package", "params", "results", "variadic"]
              return (MemberId.mk (← string "name" (← field "requirement" r "name"))
                  (← string "package" (← field "requirement" r "package")),
                ← nat "params" (← field "requirement" r "params"),
                ← nat "results" (← field "requirement" r "results"),
                ← bool "variadic" (← field "requirement" r "variadic"))
            check (!seen.contains member) "duplicate private requirement oracle identity"
            seen := member :: seen
            check (actual.methods.any fun (.mk mid ps rs v) => mid == member &&
              ps.length == params && rs.length == results && v == variadic)
              "Go/Lean private requirement identity or shape differs"
          continue
        let (left, right, want) ← IO.ofExcept do
          requireExactKeys "query" o ["left", "right", "equal"]
          return (← string "left" (← field "query" o "left"),
            ← string "right" (← field "query" o "right"),
            ← bool "equal" (← field "query" o "equal"))
        let some a := p.context.functionSignature? ⟨left⟩
          | throw (IO.userError s!"missing source function {left}")
        let some b := p.context.functionSignature? ⟨right⟩
          | throw (IO.userError s!"missing source function {right}")
        check ((a == b) == want) s!"Go/Lean source signature differs: {left}/{right}"
  | _ => throw (IO.userError "expected package and optional Go-query path")
  IO.println s!"Package declarations: PASS; {p.functions.size} functions, {p.methods.size} methods, {p.nominals.length} nominal origins, {p.interfaces.size} interfaces"
  return 0

end GoLean.DeclarationPackageTests
