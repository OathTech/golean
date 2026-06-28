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

private def corePointerArrayFunction : GoCore.Func := {
  name := "pointer_array_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := .array 2 .int },
      { id := "p", typ := .pointer (.array 2 .int) }
    ]
    #[
      .assign (.var "a") (.arrayLit 2 .int #[(0, .intLit 4), (1, .intLit 5)]),
      .assign (.var "p") (.ref "a"),
      .assign (.var "z") (.indexGet (.deref (.var "p") (.array 2 .int)) (.intLit 1)),
      .assign (.addr (.indexAddr (.var "p") (.intLit 0))) (.intLit 9),
      .assign (.var "z") (.add (.var "z") (.indexGet (.var "a") (.intLit 0)))
    ]
}

private def coreNilSliceLenCapFunction : GoCore.Func := {
  name := "nil_slice_len_cap_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "s", typ := .slice .int }]
    #[
      .assign (.var "z") (.add (.length (.var "s")) (.capacity (.var "s")))
    ]
}

private def coreArraySliceAliasFunction : GoCore.Func := {
  name := "array_slice_alias_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := .array 3 .int },
      { id := "s", typ := .slice .int }
    ]
    #[
      .assign (.var "a") (.arrayLit 3 .int #[(0, .intLit 1), (1, .intLit 2), (2, .intLit 3)]),
      .assign (.var "s") (.slice (.ref "a") (.intLit 1) (.intLit 3) none),
      .assign (.addr (.indexAddr (.var "s") (.intLit 0))) (.intLit 9),
      .assign (.var "z")
        (.add
          (.add (.indexGet (.var "a") (.intLit 1))
            (.mul (.length (.var "s")) (.intLit 10)))
          (.mul (.capacity (.var "s")) (.intLit 100)))
    ]
}

private def coreSliceResliceFunction : GoCore.Func := {
  name := "slice_reslice_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := .array 4 .int },
      { id := "s", typ := .slice .int },
      { id := "t", typ := .slice .int }
    ]
    #[
      .assign (.var "a") (.arrayLit 4 .int #[
        (0, .intLit 1), (1, .intLit 2), (2, .intLit 3), (3, .intLit 4)
      ]),
      .assign (.var "s") (.slice (.ref "a") (.intLit 1) (.intLit 4) none),
      .assign (.var "t") (.slice (.var "s") (.intLit 1) (.intLit 2) none),
      .assign (.var "z")
        (.add
          (.add (.indexGet (.var "t") (.intLit 0))
            (.mul (.length (.var "t")) (.intLit 10)))
          (.mul (.capacity (.var "t")) (.intLit 100)))
    ]
}

private def coreSliceExtendToCapacityFunction : GoCore.Func := {
  name := "slice_extend_to_capacity_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "s", typ := .slice .int },
      { id := "t", typ := .slice .int }
    ]
    #[
      .makeSlice (.var "s") .int (.intLit 3) (some (.intLit 4)),
      .assign (.var "t") (.slice (.var "s") (.intLit 0) (.intLit 4) none),
      .assign (.var "z")
        (.add
          (.add
            (.mul (.length (.var "s")) (.intLit 1000))
            (.mul (.capacity (.var "s")) (.intLit 100)))
          (.add
            (.mul (.length (.var "t")) (.intLit 10))
            (.capacity (.var "t"))))
    ]
}

private def coreFullSliceFunction : GoCore.Func := {
  name := "full_slice_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := .array 4 .int },
      { id := "s", typ := .slice .int }
    ]
    #[
      .assign (.var "a") (.arrayLit 4 .int #[
        (0, .intLit 1), (1, .intLit 2), (2, .intLit 3), (3, .intLit 4)
      ]),
      .assign (.var "s") (.slice (.ref "a") (.intLit 1) (.intLit 3) (some (.intLit 4))),
      .assign (.var "z") (.add (.length (.var "s")) (.capacity (.var "s")))
    ]
}

private def coreMakeSliceFunction : GoCore.Func := {
  name := "make_slice_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "s", typ := .slice .int }]
    #[
      .makeSlice (.var "s") .int (.intLit 3) (some (.intLit 5)),
      .assign (.addr (.indexAddr (.var "s") (.intLit 0))) (.intLit 7),
      .assign (.var "z")
        (.add
          (.add (.indexGet (.var "s") (.intLit 0))
            (.mul (.length (.var "s")) (.intLit 10)))
          (.mul (.capacity (.var "s")) (.intLit 100)))
    ]
}

private def coreMapBasicFunction : GoCore.Func := {
  name := "map_basic_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "nilMap", typ := .map .int .int },
      { id := "m", typ := .map .int .int },
      { id := "alias", typ := .map .int .int },
      { id := "v", typ := .int },
      { id := "ok", typ := .bool }
    ]
    #[
      .makeMap (.var "m") .int .int (some (.intLit 2)),
      .assign (.var "alias") (.var "m"),
      .mapAssign (.var "m") (.intLit 3) (.intLit 10),
      .mapAssign (.var "alias") (.intLit 3) (.intLit 7),
      .mapLookup (.var "v") (.var "ok") (.var "m") (.intLit 3) .int,
      .assign (.var "z")
        (.add
          (.add
            (.add
              (.mul (.length (.var "m")) (.intLit 1000))
              (.mul (.mapGet (.var "nilMap") (.intLit 9) .int) (.intLit 100)))
            (.mul (.var "v") (.intLit 10)))
          (.mapGet (.var "m") (.intLit 4) .int)
        )
    ]
}

private def coreStringFunction : GoCore.Func := {
  name := "string_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "empty", typ := .string },
      { id := "s", typ := .string },
      { id := "t", typ := .string },
      { id := "p", typ := .pointer .string }
    ]
    #[
      .assign (.var "s") (.stringLit "hi"),
      .assign (.var "t") (.add (.var "s") (.stringLit "!")),
      .assign (.var "p") (.ref "t"),
      .assign (.addr (.var "p")) (.stringLit "go"),
      .assign (.var "z")
        (.add
          (.add
            (.mul (.length (.var "empty")) (.intLit 100))
            (.mul (.length (.var "s")) (.intLit 10)))
          (.length (.deref (.var "p") .string)))
    ]
}

private def coreStringByteLenFunction : GoCore.Func := {
  name := "string_byte_len_F",
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.length (.stringLit "h\u00e9llo"))
}

private def coreNewFunction : GoCore.Func := {
  name := "new_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "p", typ := .pointer .int },
      { id := "s", typ := .pointer (.slice .int) }
    ]
    #[
      .newValue (.var "p") (.defaultValue .int),
      .assign (.addr (.var "p")) (.intLit 7),
      .newValue (.var "s") (.defaultValue (.slice .int)),
      .assign (.var "z")
        (.add
          (.mul (.deref (.var "p") .int) (.intLit 10))
          (.length (.deref (.var "s") (.slice .int))))
    ]
}

private def coreNilMapAssignFunction : GoCore.Func := {
  name := "nil_map_assign_F",
  args := #[],
  results := #[],
  body := .block
    #[{ id := "m", typ := .map .int .int }]
    #[
      .mapAssign (.var "m") (.intLit 1) (.intLit 2)
    ]
}

private def coreSliceBoundsFunction : GoCore.Func := {
  name := "slice_bounds_F",
  args := #[],
  results := #[],
  body := .block
    #[{ id := "a", typ := .array 2 .int }]
    #[
      .assign (.var "a") (.arrayLit 2 .int #[(0, .intLit 1), (1, .intLit 2)]),
      .assign (.var "a") (.slice (.ref "a") (.intLit 0) (.intLit 3) none)
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

private def coreAssignManySequencingFunction : GoCore.Func := {
  name := "assign_many_sequencing_F",
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := .array 3 .int },
      { id := "s", typ := .slice .int },
      { id := "i", typ := .int }
    ]
    #[
      .assign (.var "a") (.arrayLit 3 .int #[(0, .intLit 0), (1, .intLit 0), (2, .intLit 0)]),
      .assign (.var "s") (.slice (.ref "a") (.intLit 0) (.intLit 3) none),
      .assign (.var "i") (.intLit 0),
      .assignMany
        #[.var "i", .addr (.indexAddr (.var "s") (.var "i"))]
        #[.intLit 1, .intLit 2],
      .assign (.var "z")
        (.add
          (.mul (.var "i") (.intLit 1000))
          (.add
            (.mul (.indexGet (.var "s") (.intLit 0)) (.intLit 100))
            (.add
              (.mul (.indexGet (.var "s") (.intLit 1)) (.intLit 10))
              (.indexGet (.var "s") (.intLit 2)))))
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
  passed := passed && (← expectIntResult "GoCore pointer-to-array indexing" (GoCore.runFunction 100 corePointerArrayFunction #[]) 14)
  passed := passed && (← expectIntResult "GoCore nil slice len cap" (GoCore.runFunction 100 coreNilSliceLenCapFunction #[]) 0)
  passed := passed && (← expectIntResult "GoCore array slice alias" (GoCore.runFunction 100 coreArraySliceAliasFunction #[]) 229)
  passed := passed && (← expectIntResult "GoCore slice reslice" (GoCore.runFunction 100 coreSliceResliceFunction #[]) 213)
  passed := passed && (← expectIntResult "GoCore slice extend to capacity" (GoCore.runFunction 100 coreSliceExtendToCapacityFunction #[]) 3444)
  passed := passed && (← expectIntResult "GoCore full slice" (GoCore.runFunction 100 coreFullSliceFunction #[]) 5)
  passed := passed && (← expectIntResult "GoCore make slice" (GoCore.runFunction 100 coreMakeSliceFunction #[]) 537)
  passed := passed && (← expectIntResult "GoCore map basic" (GoCore.runFunction 100 coreMapBasicFunction #[]) 1070)
  passed := passed && (← expectIntResult "GoCore string basic" (GoCore.runFunction 100 coreStringFunction #[]) 22)
  passed := passed && (← expectIntResult "GoCore string byte length" (GoCore.runFunction 100 coreStringByteLenFunction #[]) 6)
  passed := passed && (← expectIntResult "GoCore new allocation" (GoCore.runFunction 100 coreNewFunction #[]) 70)
  passed := passed && (← expectErrorStatus "GoCore nil dereference panic" (GoCore.runFunction 100 coreNilDerefFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore divide by zero panic" (GoCore.runFunction 100 coreDivideByZeroFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore index address bounds panic" (GoCore.runFunction 100 coreIndexAddrBoundsFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore slice bounds panic" (GoCore.runFunction 100 coreSliceBoundsFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore nil map assignment panic" (GoCore.runFunction 100 coreNilMapAssignFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore mismatched equality stuck" (GoCore.runFunction 100 coreMismatchedEqualityFunction #[]) "stuck")
  passed := passed && (← expectIntResult "GoCore call target sequencing"
    (GoCore.runFunctionWithContext 100 [] #[coreShiftIndexFunction, coreCallTargetSequencingFunction] coreCallTargetSequencingFunction #[]) 901)
  passed := passed && (← expectIntResult "GoCore simultaneous assignment sequencing"
    (GoCore.runFunction 100 coreAssignManySequencingFunction #[]) 1200)
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
