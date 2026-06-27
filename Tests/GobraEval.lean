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

private def coreParam (id : String) : GoCore.Param :=
  { id, typ := .int }

private def coreAddExpr : GoCore.Expr :=
  .add (.var "x") (.var "y")

private def coreAddFunction : GoCore.Func := {
  name := "add_F",
  args := #[coreParam "x", coreParam "y"],
  results := #[coreParam "z"],
  pres := #[],
  posts := #[.expr (.eqCmp (.var "z") coreAddExpr)],
  body := .assign (.var "z") coreAddExpr
}

private def corePointerIdentityFunction : GoCore.Func := {
  name := "pointer_identity_F",
  args := #[],
  results := #[],
  pres := #[],
  posts := #[],
  body := .block
    #[
      { id := "v", typ := .int },
      { id := "ar", typ := .pointer .int },
      { id := "br", typ := .pointer .int },
      { id := "arr", typ := .pointer (.pointer .int) },
      { id := "brr", typ := .pointer (.pointer .int) }
    ]
    #[
      .assign (.var "v") (.intLit 42),
      .assign (.var "ar") (.ref "v"),
      .assign (.var "br") (.ref "v"),
      .assert (.expr (.eqCmp (.var "ar") (.var "br"))),
      .assign (.var "arr") (.ref "ar"),
      .assign (.var "brr") (.ref "br"),
      .assert (.expr (.eqCmp (.var "arr") (.var "brr")))
    ]
}

private def coreCellTypes : GoCore.TypeEnv :=
  [("cell", .struct #[{ name := "valA", typ := .int }])]

private def coreStructFunction : GoCore.Func := {
  name := "struct_F",
  args := #[],
  results := #[],
  pres := #[],
  posts := #[],
  body := .block
    #[{ id := "x", typ := .defined "cell" }]
    #[
      .assign (.var "x") (.structLit (.defined "cell") #[.intLit 42]),
      .assert (.expr (.eqCmp (.fieldGet (.var "x") "cell" "valA") (.intLit 42))),
      .assign (.addr (.fieldAddr (.ref "x") "cell" "valA")) (.intLit 17),
      .assert (.expr (.eqCmp (.var "x") (.structLit (.defined "cell") #[.intLit 17]))),
      .assert (.expr (.eqCmp (.deref (.ref "x") (.defined "cell")) (.var "x")))
    ]
}

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

private def expectOk (name : String) (result : Except String GoLean.GobraEval.Result) :
    IO Bool := do
  match result with
  | .ok _ =>
      IO.println s!"ok: {name}"
      return true
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {err}"
      return false

def main : IO UInt32 := do
  let mut passed := true
  passed := passed && (← expectIntResult "GoCore add function" (GoCore.runFunction 100 coreAddFunction #[.int 2, .int 3]) 5)
  passed := passed && (← expectError "GoCore pointer identity" (GoCore.runFunction 100 corePointerIdentityFunction #[]))
  passed := passed && (← expectOk "GoCore struct field update" (GoCore.runFunctionWithTypes 100 coreCellTypes coreStructFunction #[]))
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
