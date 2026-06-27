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

private def coreBoolParam (id : String) : GoCore.Param :=
  { id, typ := .bool }

private def coreAddExpr : GoCore.Expr :=
  .add (.var "x") (.var "y")

private def coreAddFunction : GoCore.Func := {
  name := "add_F",
  args := #[coreParam "x", coreParam "y"],
  results := #[coreParam "z"],
  body := .assign (.var "z") coreAddExpr
}

private def corePointerIdentityFunction : GoCore.Func := {
  name := "pointer_identity_F",
  args := #[],
  results := #[coreBoolParam "same"],
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
      .assign (.var "arr") (.ref "ar"),
      .assign (.var "brr") (.ref "br"),
      .assign (.var "same") (.eqCmp (.var "arr") (.var "brr"))
    ]
}

private def coreCellTypes : GoCore.TypeEnv :=
  [("cell", .struct #[{ name := "valA", typ := .int }])]

private def coreStructFunction : GoCore.Func := {
  name := "struct_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .defined "cell" }]
    #[
      .assign (.var "x") (.structLit (.defined "cell") #[.intLit 42]),
      .assign (.addr (.fieldAddr (.ref "x") "cell" "valA")) (.intLit 17),
      .assign (.var "z") (.fieldGet (.deref (.ref "x") (.defined "cell")) "cell" "valA")
    ]
}

private def coreSetCellFunction : GoCore.Func := {
  name := "setCell_F",
  args := #[
    { id := "p", typ := .pointer (.defined "cell") },
    { id := "v", typ := .int }
  ],
  results := #[],
  body := .assign
    (.addr (.fieldAddr (.var "p") "cell" "valA"))
    (.var "v")
}

private def coreCallFunction : GoCore.Func := {
  name := "call_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .defined "cell" }]
    #[
      .assign (.var "x") (.structLit (.defined "cell") #[.intLit 42]),
      .call #[] "setCell_F" #[.ref "x", .intLit 9],
      .assign (.var "z") (.fieldGet (.var "x") "cell" "valA")
    ]
}

private def coreScalarFunction : GoCore.Func := {
  name := "scalars_F",
  args := #[coreParam "x", coreParam "y"],
  results := #[coreParam "z"],
  body := .seqn #[
      .assign (.var "z") (.sub (.var "x") (.var "y"))
    ]
}

private def coreArrayFunction : GoCore.Func := {
  name := "arrays_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "a", typ := .array 3 .int }]
    #[
      .assign (.var "a") (.arrayLit 3 .int #[(0, .intLit 1), (1, .intLit 2), (2, .intLit 3)]),
      .assign (.var "z") (.add (.indexGet (.var "a") (.intLit 0)) (.indexGet (.var "a") (.intLit 2))),
      .assign (.addr (.indexAddr (.ref "a") (.intLit 1))) (.intLit 7),
      .assign (.var "z") (.add (.var "z") (.indexGet (.var "a") (.intLit 1)))
    ]
}

private def coreArrayLenCapFunction : GoCore.Func := {
  name := "array_len_cap_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "a", typ := .array 3 .int }]
    #[
      .assign (.var "a") (.arrayLit 3 .int #[(0, .intLit 1), (1, .intLit 2), (2, .intLit 3)]),
      .assign (.var "z") (.add (.length (.var "a")) (.capacity (.var "a")))
    ]
}

private def coreArrayDefaultFunction : GoCore.Func := {
  name := "array_default_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "a", typ := .array 2 .int }]
    #[
      .assign (.var "a") (.defaultValue (.array 2 .int)),
      .assign (.var "z") (.add (.indexGet (.var "a") (.intLit 0)) (.indexGet (.var "a") (.intLit 1)))
    ]
}

private def coreNilDerefFunction : GoCore.Func := {
  name := "nil_deref_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "p", typ := .pointer .int }]
    #[
      .assign (.var "z") (.deref (.var "p") .int)
    ]
}

private def coreDivideByZeroFunction : GoCore.Func := {
  name := "divide_by_zero_F",
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.div (.intLit 1) (.intLit 0))
}

private def coreIndexAddrBoundsFunction : GoCore.Func := {
  name := "index_addr_bounds_F",
  args := #[],
  results := #[],
  body := .block
    #[{ id := "a", typ := .array 2 .int }]
    #[
      .assign (.addr (.indexAddr (.ref "a") (.intLit 2))) (.intLit 7)
    ]
}

private def coreMismatchedEqualityFunction : GoCore.Func := {
  name := "mismatched_equality_F",
  args := #[],
  results := #[coreBoolParam "ok"],
  body := .assign (.var "ok") (.eqCmp (.intLit 0) (.boolLit false))
}

private def coreShiftIndexFunction : GoCore.Func := {
  name := "shiftIndex_F",
  args := #[{ id := "p", typ := .pointer .int }],
  results := #[coreParam "z"],
  body := .seqn #[
    .assign (.addr (.var "p")) (.intLit 1),
    .assign (.var "z") (.intLit 9)
  ]
}

private def coreCallTargetSequencingFunction : GoCore.Func := {
  name := "call_target_sequencing_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "i", typ := .int },
      { id := "a", typ := .array 2 .int }
    ]
    #[
      .assign (.var "i") (.intLit 0),
      .assign (.var "a") (.arrayLit 2 .int #[(0, .intLit 0), (1, .intLit 0)]),
      .call #[.addr (.indexAddr (.ref "a") (.var "i"))] "shiftIndex_F" #[.ref "i"],
      .assign (.var "z")
        (.add
          (.add
            (.mul (.indexGet (.var "a") (.intLit 0)) (.intLit 100))
            (.mul (.indexGet (.var "a") (.intLit 1)) (.intLit 10)))
          (.var "i"))
    ]
}

private def coreIfReturnFunction : GoCore.Func := {
  name := "if_return_F",
  args := #[coreParam "x"],
  results := #[coreParam "z"],
  body := .seqn #[
    .assign (.var "z") (.intLit 100),
    .ifThenElse (.greaterCmp (.var "x") (.intLit 0))
      (.seqn #[
        .assign (.var "z") (.var "x"),
        .returnStmt
      ])
      (.assign (.var "z") (.sub (.intLit 0) (.var "x"))),
    .assign (.var "z") (.add (.var "z") (.intLit 100))
  ]
}

private def coreBreakContinueFunction : GoCore.Func := {
  name := "break_continue_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "i", typ := .int }]
    #[
      .assign (.var "i") (.intLit 0),
      .assign (.var "z") (.intLit 0),
      .while (.lessCmp (.var "i") (.intLit 5))
        (.seqn #[
          .assign (.var "i") (.add (.var "i") (.intLit 1)),
          .ifThenElse (.eqCmp (.var "i") (.intLit 2))
            .continueStmt
            (.seqn #[]),
          .assign (.var "z") (.add (.var "z") (.var "i")),
          .ifThenElse (.eqCmp (.var "i") (.intLit 4))
            .breakStmt
            (.seqn #[])
        ])
    ]
}

private def addExpr : GobraJson.Expr :=
  .add source (.var (.inParam x)) (.var (.inParam y))

private def falseAssertion : GobraJson.Assertion :=
  .exprAssertion source (.boolLit source false)

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

private def bodylessFunction : GobraJson.FunctionMember := {
  addFunction with
  name := { source, name := "bodyless_F" },
  args := #[],
  results := #[],
  pres := #[],
  posts := #[],
  body := none
}

private def specErasureFunction : GobraJson.FunctionMember := {
  addFunction with
  name := { source, name := "spec_erasure_F" },
  pres := #[falseAssertion],
  posts := #[falseAssertion],
  body := some {
    source,
    decls := #[],
    seqn := {
      source,
      stmts := #[
        .assert source falseAssertion,
        .singleAss source (.var source (.outParam z)) addExpr
      ]
    },
    postprocessing := #[.assert source falseAssertion]
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

private def bodylessDoc : GobraJson.Document := {
  doc with program := { doc.program with members := #[.function bodylessFunction] }
}

private def specErasureDoc : GobraJson.Document := {
  doc with program := { doc.program with members := #[.function specErasureFunction] }
}

private def expectIntResult (name : String) (result : Except GoError GoLean.GobraEval.Result)
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
      IO.eprintln s!"FAIL: {name}: expected success, got {repr err}"
      return false

private def expectBoolResult (name : String) (result : Except GoError GoLean.GobraEval.Result)
    (expected : Bool) : IO Bool := do
  match result with
  | .ok result =>
      if result.values == #[.bool expected] then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: expected {expected}, got {repr result.values}"
        return false
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {repr err}"
      return false

private def expectErrorStatus (name : String) (result : Except GoError GoLean.GobraEval.Result)
    (expected : String) : IO Bool := do
  match result with
  | .ok result =>
      IO.eprintln s!"FAIL: {name}: expected {expected}, got {repr result}"
      return false
  | .error err =>
      if err.status == expected then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: expected {expected}, got {err.status}: {err.message}"
        return false

private def expectOk (name : String) (result : Except GoError GoLean.GobraEval.Result) :
    IO Bool := do
  match result with
  | .ok _ =>
      IO.println s!"ok: {name}"
      return true
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {repr err}"
      return false

def main : IO UInt32 := do
  let mut passed := true
  passed := passed && (← expectIntResult "GoCore add function" (GoCore.runFunction 100 coreAddFunction #[.int 2, .int 3]) 5)
  passed := passed && (← expectBoolResult "GoCore pointer identity" (GoCore.runFunction 100 corePointerIdentityFunction #[]) false)
  passed := passed && (← expectIntResult "GoCore struct field update" (GoCore.runFunctionWithTypes 100 coreCellTypes coreStructFunction #[]) 17)
  passed := passed && (← expectIntResult "GoCore shared-heap function call"
    (GoCore.runFunctionWithContext 100 coreCellTypes #[coreSetCellFunction, coreCallFunction] coreCallFunction #[]) 9)
  passed := passed && (← expectIntResult "GoCore scalar operators" (GoCore.runFunction 100 coreScalarFunction #[.int 10, .int 3]) 7)
  passed := passed && (← expectIntResult "GoCore array indexing" (GoCore.runFunction 100 coreArrayFunction #[]) 11)
  passed := passed && (← expectIntResult "GoCore array len cap" (GoCore.runFunction 100 coreArrayLenCapFunction #[]) 6)
  passed := passed && (← expectIntResult "GoCore array default value" (GoCore.runFunction 100 coreArrayDefaultFunction #[]) 0)
  passed := passed && (← expectErrorStatus "GoCore nil dereference panic" (GoCore.runFunction 100 coreNilDerefFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore divide by zero panic" (GoCore.runFunction 100 coreDivideByZeroFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore index address bounds panic" (GoCore.runFunction 100 coreIndexAddrBoundsFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore mismatched equality stuck" (GoCore.runFunction 100 coreMismatchedEqualityFunction #[]) "stuck")
  passed := passed && (← expectIntResult "GoCore call target sequencing"
    (GoCore.runFunctionWithContext 100 [] #[coreShiftIndexFunction, coreCallTargetSequencingFunction] coreCallTargetSequencingFunction #[]) 901)
  passed := passed && (← expectIntResult "GoCore if return positive" (GoCore.runFunction 100 coreIfReturnFunction #[.int 7]) 7)
  passed := passed && (← expectIntResult "GoCore if return negative" (GoCore.runFunction 100 coreIfReturnFunction #[.int (-3)]) 103)
  passed := passed && (← expectIntResult "GoCore break continue" (GoCore.runFunction 100 coreBreakContinueFunction #[]) 8)
  passed := passed && (← expectIntResult "add function" (GoLean.GobraEval.runFunctionInts 100 doc "add_F" #[2, 3]) 5)
  passed := passed && (← expectIntResult "Gobra specs and asserts erased"
    (GoLean.GobraEval.runFunctionInts 100 specErasureDoc "spec_erasure_F" #[2, 3]) 5)
  passed := passed && (← expectErrorStatus "missing function" (GoLean.GobraEval.runFunctionInts 100 doc "missing_F" #[]) "stuck")
  passed := passed && (← expectErrorStatus "wrong arity" (GoLean.GobraEval.runFunctionInts 100 doc "add_F" #[2]) "stuck")
  passed := passed && (← expectErrorStatus "bodyless function unsupported" (GoLean.GobraEval.runFunctionInts 100 bodylessDoc "bodyless_F" #[]) "unsupported")
  if passed then
    return 0
  else
    return 1

end Tests.GobraEval

def main : IO UInt32 :=
  Tests.GobraEval.main
