import GoLean.GobraEval

namespace Tests.GobraEval

open GoLean

private def source : GobraJson.Source :=
  .internal

private def intTy : GobraJson.Ty :=
  .int .exclusive (.bounded "int" 64 (-1000000) 1000000)

private def param (id : String) : GobraJson.Parameter :=
  { source, id, typ := intTy }

private def x : GobraJson.Parameter := param "x"
private def y : GobraJson.Parameter := param "y"
private def z : GobraJson.Parameter := param "z"

private def addExpr : GobraJson.Expr :=
  .add source (.var (.inParam x)) (.var (.inParam y))

private def addFunction : GobraJson.FunctionMember := {
  source,
  name := { source, name := "add_F" },
  args := #[x, y],
  results := #[z],
  pres := #[],
  posts := #[.exprAssertion source (.eqCmp source (.var (.outParam z)) addExpr)],
  terminationMeasures := #[],
  backendAnnotations := #[],
  body := some {
    source,
    decls := #[],
    seqn := {
      source,
      stmts := #[.singleAss source (.var source (.outParam z)) addExpr]
    },
    postprocessing := #[]
  }
}

private def doc : GobraJson.Document := {
  schema := {
    name := "gobra.internal",
    version := 1,
    encoding := "structural-adt",
    failClosed := true
  },
  inputs := #["synthetic.gobra"],
  program := {
    source,
    types := #[],
    members := #[.function addFunction]
  }
}

private def expectIntResult (name : String) (result : Except String GoLean.GobraEval.Result)
    (expected : Int) : IO Bool := do
  match result with
  | .ok result =>
      if result.values == #[.int expected] then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: expected {expected}, got {repr result.values}"
        return false
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {err}"
      return false

private def expectError (name : String) (result : Except String GoLean.GobraEval.Result) :
    IO Bool := do
  match result with
  | .ok result =>
      IO.eprintln s!"FAIL: {name}: expected failure, got {repr result}"
      return false
  | .error _ =>
      IO.println s!"ok: {name}"
      return true

def main : IO UInt32 := do
  let mut passed := true
  passed := passed && (← expectIntResult "add function" (GoLean.GobraEval.runFunctionInts 100 doc "add_F" #[2, 3]) 5)
  passed := passed && (← expectError "missing function" (GoLean.GobraEval.runFunctionInts 100 doc "missing_F" #[]))
  passed := passed && (← expectError "wrong arity" (GoLean.GobraEval.runFunctionInts 100 doc "add_F" #[2]))
  if passed then
    return 0
  else
    return 1

end Tests.GobraEval

def main : IO UInt32 :=
  Tests.GobraEval.main
