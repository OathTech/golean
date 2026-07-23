import GoLean.GoCore

namespace Tests.GoCoreEval

open GoLean

private def coreParam (id : String) : GoCore.Param :=
  { id, typ := .int }

private def coreBoolParam (id : String) : GoCore.Param :=
  { id, typ := .bool }

private def coreAddExpr : GoCore.Expr :=
  .add (.var "x") (.var "y")

private def coreStringLit (value : String) : GoCore.Expr :=
  .stringLit (GoString.fromLeanString value)

private def coreStringByteLit (bytes : Array Nat) : GoCore.Expr :=
  .stringLit { bytes := bytes.map UInt8.ofNat }

private def coreAddFunction : GoCore.Func := {
  id := ⟨"add_F"⟩,
  args := #[coreParam "x", coreParam "y"],
  results := #[coreParam "z"],
  body := .assign (.var "z") coreAddExpr
}

private def corePointerIdentityFunction : GoCore.Func := {
  id := ⟨"pointer_identity_F"⟩,
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
      .assign (.var "same") (.eqCmp (.pointer (.pointer .int)) (.var "arr") (.var "brr"))
    ]
}

private def coreCellTypes : GoCore.TypeEnv :=
  [(⟨"cell"⟩, .struct #[{ name := "valA", typ := .int }])]

private def coreStructFunction : GoCore.Func := {
  id := ⟨"struct_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .defined ⟨"cell"⟩ }]
    #[
      .assign (.var "x") (.structLit (.defined ⟨"cell"⟩) #[.intLit 42]),
      .assign (.addr (.fieldAddr (.ref "x") ⟨"cell"⟩ "valA")) (.intLit 17),
      .assign (.var "z") (.fieldGet (.deref (.ref "x") (.defined ⟨"cell"⟩)) ⟨"cell"⟩ "valA")
    ]
}

private def coreSetCellFunction : GoCore.Func := {
  id := ⟨"setCell_F"⟩,
  args := #[
    { id := "p", typ := .pointer (.defined ⟨"cell"⟩) },
    { id := "v", typ := .int }
  ],
  results := #[],
  body := .assign
    (.addr (.fieldAddr (.var "p") ⟨"cell"⟩ "valA"))
    (.var "v")
}

private def coreCallFunction : GoCore.Func := {
  id := ⟨"call_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .defined ⟨"cell"⟩ }]
    #[
      .assign (.var "x") (.structLit (.defined ⟨"cell"⟩) #[.intLit 42]),
      .call #[] ⟨"setCell_F"⟩ #[.ref "x", .intLit 9],
      .assign (.var "z") (.fieldGet (.var "x") ⟨"cell"⟩ "valA")
    ]
}

private def coreScalarFunction : GoCore.Func := {
  id := ⟨"scalars_F"⟩,
  args := #[coreParam "x", coreParam "y"],
  results := #[coreParam "z"],
  body := .seqn #[
      .assign (.var "z") (.sub (.var "x") (.var "y"))
    ]
}

private def coreInt8WrapFunction : GoCore.Func := {
  id := ⟨"int8_wrap_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .int .int8 }]
    #[
      .assign (.var "x") (.intLit 127),
      .assign (.var "x") (.add (.var "x") (.intLit 1)),
      .assign (.var "z") (.var "x")
    ]
}

private def coreByteConversionFunction : GoCore.Func := {
  id := ⟨"byte_conversion_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "big", typ := .int .int32 }, { id := "b", typ := .int .uint8 }]
    #[
      .assign (.var "big") (.intLit 300),
      .assign (.var "b") (.convert (.int .uint8) (.var "big")),
      .assign (.var "z") (.var "b")
    ]
}

private def coreUnsupportedConversionFunction : GoCore.Func := {
  id := ⟨"unsupported_conversion_F"⟩,
  args := #[],
  results := #[{ id := "z", typ := .string }],
  body := .assign (.var "z") (.convert .string (.intLit 65))
}

private def coreShiftFunction : GoCore.Func := {
  id := ⟨"shift_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .int .uint8 }, { id := "y", typ := .int .int8 }]
    #[
      .assign (.var "x") (.intLit 1),
      .assign (.var "x") (.shiftLeft (.var "x") (.intLit 8)),
      .assign (.var "y") (.intLit (-3)),
      .assign (.var "y") (.shiftRight (.var "y") (.intLit 1)),
      .assign (.var "z") (.add (.mul (.convert .int (.var "x")) (.intLit 10)) (.convert .int (.var "y")))
    ]
}

private def coreNegativeShiftFunction : GoCore.Func := {
  id := ⟨"negative_shift_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.shiftLeft (.intLit 1) (.intLit (-1)))
}

private def coreBitwiseFunction : GoCore.Func := {
  id := ⟨"bitwise_F"⟩,
  args := #[],
  results := #[
    { id := "a", typ := .int .uint8 },
    { id := "b", typ := .int .uint8 },
    { id := "c", typ := .int .uint8 },
    { id := "d", typ := .int .uint8 },
    { id := "e", typ := .int .uint8 },
    { id := "f", typ := .int .int8 }
  ],
  body := .block
    #[
      { id := "x", typ := .int .uint8 },
      { id := "y", typ := .int .uint8 },
      { id := "zero", typ := .int .uint8 },
      { id := "signedZero", typ := .int .int8 }
    ]
    #[
      .assign (.var "x") (.intLit 15),
      .assign (.var "y") (.intLit 5),
      .assign (.var "zero") (.intLit 0),
      .assign (.var "signedZero") (.intLit 0),
      .assign (.var "a") (.bitAnd (.var "x") (.var "y")),
      .assign (.var "b") (.bitOr (.var "x") (.var "y")),
      .assign (.var "c") (.bitXor (.var "x") (.var "y")),
      .assign (.var "d") (.bitClear (.var "x") (.var "y")),
      .assign (.var "e") (.bitNeg (.var "zero")),
      .assign (.var "f") (.bitNeg (.var "signedZero"))
    ]
}

private def coreArrayFunction : GoCore.Func := {
  id := ⟨"arrays_F"⟩,
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
  id := ⟨"array_len_cap_F"⟩,
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
  id := ⟨"array_default_F"⟩,
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
  id := ⟨"pointer_array_F"⟩,
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
  id := ⟨"nil_slice_len_cap_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "s", typ := .slice .int }]
    #[
      .assign (.var "z") (.add (.length (.var "s")) (.capacity (.var "s")))
    ]
}

private def coreArraySliceAliasFunction : GoCore.Func := {
  id := ⟨"array_slice_alias_F"⟩,
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
  id := ⟨"slice_reslice_F"⟩,
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
  id := ⟨"slice_extend_to_capacity_F"⟩,
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
  id := ⟨"full_slice_F"⟩,
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
  id := ⟨"make_slice_F"⟩,
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
  id := ⟨"map_basic_F"⟩,
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
      .mapAssign (.var "m") (.intLit 3) (.intLit 10) .int .int,
      .mapAssign (.var "alias") (.intLit 3) (.intLit 7) .int .int,
      .mapLookup (.var "v") (.var "ok") (.var "m") (.intLit 3) .int .int,
      .assign (.var "z")
        (.add
          (.add
            (.add
              (.mul (.length (.var "m")) (.intLit 1000))
              (.mul (.mapGet (.var "nilMap") (.intLit 9) .int .int) (.intLit 100)))
            (.mul (.var "v") (.intLit 10)))
          (.mapGet (.var "m") (.intLit 4) .int .int)
        )
    ]
}

private def coreStringFunction : GoCore.Func := {
  id := ⟨"string_F"⟩,
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
      .assign (.var "s") (coreStringLit "hi"),
      .assign (.var "t") (.add (.var "s") (coreStringLit "!")),
      .assign (.var "p") (.ref "t"),
      .assign (.addr (.var "p")) (coreStringLit "go"),
      .assign (.var "z")
        (.add
          (.add
            (.mul (.length (.var "empty")) (.intLit 100))
            (.mul (.length (.var "s")) (.intLit 10)))
          (.length (.deref (.var "p") .string)))
    ]
}

private def coreStringByteLenFunction : GoCore.Func := {
  id := ⟨"string_byte_len_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.length (coreStringLit "h\u00e9llo"))
}

private def coreStringIndexFunction : GoCore.Func := {
  id := ⟨"string_index_F"⟩,
  args := #[],
  results := #[{ id := "a", typ := .int .uint8 }, { id := "b", typ := .int .uint8 }],
  body := .block
    #[{ id := "s", typ := .string }]
    #[
      .assign (.var "s") (coreStringLit "h\u00e9"),
      .assign (.var "a") (.indexGet (.var "s") (.intLit 1)),
      .assign (.var "b") (.indexGet (.var "s") (.intLit 2))
    ]
}

private def coreStringSliceFunction : GoCore.Func := {
  id := ⟨"string_slice_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "s", typ := .string }, { id := "t", typ := .string }]
    #[
      .assign (.var "s") (coreStringLit "h\u00e9"),
      .assign (.var "t") (.slice (.var "s") (.intLit 1) (.intLit 2) none),
      .assign (.var "z")
        (.add
          (.mul (.length (.var "t")) (.intLit 100))
          (.convert .int (.indexGet (.var "t") (.intLit 0))))
    ]
}

private def coreStringByteConversionFunction : GoCore.Func := {
  id := ⟨"string_byte_conversion_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "s", typ := .string },
      { id := "bs", typ := .slice (.int .uint8) },
      { id := "t", typ := .string }
    ]
    #[
      .assign (.var "s") (coreStringByteLit #[65, 255, 10, 195, 169]),
      .assign (.var "bs") (.bytesFromString (.var "s")),
      .assign (.addr (.indexAddr (.var "bs") (.intLit 0))) (.intLit 66),
      .assign (.var "t") (.stringFromByteSlice (.var "bs")),
      .assign (.var "z")
        (.add
          (.add
            (.mul (.length (.var "bs")) (.intLit 1000000))
            (.mul (.convert .int (.indexGet (.var "s") (.intLit 0))) (.intLit 10000)))
          (.add
            (.mul (.convert .int (.indexGet (.var "t") (.intLit 0))) (.intLit 100))
            (.convert .int (.indexGet (.var "t") (.intLit 1)))))
    ]
}

private def coreStringRuneConversionFunction : GoCore.Func := {
  id := ⟨"string_rune_conversion_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "s", typ := .string },
      { id := "t", typ := .string },
      { id := "bad", typ := .string }
    ]
    #[
      .assign (.var "s") (.stringFromRune (.intLit 65)),
      .assign (.var "t") (.stringFromRune (.intLit 255 (.uint8))),
      .assign (.var "bad") (.stringFromRune (.intLit (-1))),
      .assign (.var "z")
        (.add
          (.add
            (.mul (.length (.var "s")) (.intLit 1000000))
            (.mul (.convert .int (.indexGet (.var "s") (.intLit 0))) (.intLit 10000)))
          (.add
            (.add
              (.mul (.length (.var "t")) (.intLit 1000))
              (.mul (.convert .int (.indexGet (.var "t") (.intLit 0))) (.intLit 10)))
            (.length (.var "bad"))))
    ]
}

private def coreNewFunction : GoCore.Func := {
  id := ⟨"new_F"⟩,
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
  id := ⟨"nil_map_assign_F"⟩,
  args := #[],
  results := #[],
  body := .block
    #[{ id := "m", typ := .map .int .int }]
    #[
      .mapAssign (.var "m") (.intLit 1) (.intLit 2) .int .int
    ]
}

private def coreSliceBoundsFunction : GoCore.Func := {
  id := ⟨"slice_bounds_F"⟩,
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
  id := ⟨"nil_deref_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "p", typ := .pointer .int }]
    #[
      .assign (.var "z") (.deref (.var "p") .int)
    ]
}

private def coreDivideByZeroFunction : GoCore.Func := {
  id := ⟨"divide_by_zero_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.div (.intLit 1) (.intLit 0))
}

private def coreIndexAddrBoundsFunction : GoCore.Func := {
  id := ⟨"index_addr_bounds_F"⟩,
  args := #[],
  results := #[],
  body := .block
    #[{ id := "a", typ := .array 2 .int }]
    #[
      .assign (.addr (.indexAddr (.ref "a") (.intLit 2))) (.intLit 7)
    ]
}

private def coreMismatchedEqualityFunction : GoCore.Func := {
  id := ⟨"mismatched_equality_F"⟩,
  args := #[],
  results := #[coreBoolParam "ok"],
  body := .assign (.var "ok") (.eqCmp .int (.intLit 0) (.boolLit false))
}

private def coreShiftIndexFunction : GoCore.Func := {
  id := ⟨"shiftIndex_F"⟩,
  args := #[{ id := "p", typ := .pointer .int }],
  results := #[coreParam "z"],
  body := .seqn #[
    .assign (.addr (.var "p")) (.intLit 1),
    .assign (.var "z") (.intLit 9)
  ]
}

private def coreCallTargetSequencingFunction : GoCore.Func := {
  id := ⟨"call_target_sequencing_F"⟩,
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
      .call #[.addr (.indexAddr (.ref "a") (.var "i"))] ⟨"shiftIndex_F"⟩ #[.ref "i"],
      .assign (.var "z")
        (.add
          (.add
            (.mul (.indexGet (.var "a") (.intLit 0)) (.intLit 100))
            (.mul (.indexGet (.var "a") (.intLit 1)) (.intLit 10)))
          (.var "i"))
    ]
}

private def coreAssignManySequencingFunction : GoCore.Func := {
  id := ⟨"assign_many_sequencing_F"⟩,
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
  id := ⟨"if_return_F"⟩,
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
  id := ⟨"break_continue_F"⟩,
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
          .ifThenElse (.eqCmp .int (.var "i") (.intLit 2))
            .continueStmt
            (.seqn #[]),
          .assign (.var "z") (.add (.var "z") (.var "i")),
          .ifThenElse (.eqCmp .int (.var "i") (.intLit 4))
            .breakStmt
            (.seqn #[])
        ])
    ]
}

private def expectIntResult (name : String) (result : Except GoError GoLean.GoCore.Result)
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

private def expectBoolResult (name : String) (result : Except GoError GoLean.GoCore.Result)
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

private def expectValues (name : String) (result : Except GoError GoLean.GoCore.Result)
    (expected : Array GoValue) : IO Bool := do
  match result with
  | .ok result =>
      if result.values == expected then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: expected {repr expected}, got {repr result.values}"
        return false
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {repr err}"
      return false

private def expectErrorStatus (name : String) (result : Except GoError GoLean.GoCore.Result)
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

private def expectOk (name : String) (result : Except GoError GoLean.GoCore.Result) :
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
  passed := passed && (← expectIntResult "GoCore add function" (GoCore.Machine.runFunctionM 100000 coreAddFunction #[.int 2, .int 3]) 5)
  passed := passed && (← expectBoolResult "GoCore pointer identity" (GoCore.Machine.runFunctionM 100000 corePointerIdentityFunction #[]) false)
  passed := passed && (← expectIntResult "GoCore struct field update" (GoCore.Machine.runFunctionWithTypesM 100000 coreCellTypes coreStructFunction #[]) 17)
  passed := passed && (← expectIntResult "GoCore shared-heap function call"
    (GoCore.Machine.runFunctionWithContextM 100000 coreCellTypes #[coreSetCellFunction, coreCallFunction] coreCallFunction #[]) 9)
  passed := passed && (← expectIntResult "GoCore scalar operators" (GoCore.Machine.runFunctionM 100000 coreScalarFunction #[.int 10, .int 3]) 7)
  passed := passed && (← expectIntResult "GoCore int8 wrap" (GoCore.Machine.runFunctionM 100000 coreInt8WrapFunction #[]) (-128))
  passed := passed && (← expectIntResult "GoCore byte conversion wrap" (GoCore.Machine.runFunctionM 100000 coreByteConversionFunction #[]) 44)
  passed := passed && (← expectErrorStatus "GoCore unsupported non-integer conversion" (GoCore.Machine.runFunctionM 100000 coreUnsupportedConversionFunction #[]) "unsupported")
  passed := passed && (← expectIntResult "GoCore shifts" (GoCore.Machine.runFunctionM 100000 coreShiftFunction #[]) (-2))
  passed := passed && (← expectErrorStatus "GoCore negative shift panic" (GoCore.Machine.runFunctionM 100000 coreNegativeShiftFunction #[]) "panic")
  passed := passed && (← expectValues "GoCore bitwise operators"
    (GoCore.Machine.runFunctionM 100000 coreBitwiseFunction #[])
    #[.int 5 .uint8, .int 15 .uint8, .int 10 .uint8, .int 10 .uint8, .int 255 .uint8, .int (-1) .int8])
  passed := passed && (← expectIntResult "GoCore array indexing" (GoCore.Machine.runFunctionM 100000 coreArrayFunction #[]) 11)
  passed := passed && (← expectIntResult "GoCore array len cap" (GoCore.Machine.runFunctionM 100000 coreArrayLenCapFunction #[]) 6)
  passed := passed && (← expectIntResult "GoCore array default value" (GoCore.Machine.runFunctionM 100000 coreArrayDefaultFunction #[]) 0)
  passed := passed && (← expectIntResult "GoCore pointer-to-array indexing" (GoCore.Machine.runFunctionM 100000 corePointerArrayFunction #[]) 14)
  passed := passed && (← expectIntResult "GoCore nil slice len cap" (GoCore.Machine.runFunctionM 100000 coreNilSliceLenCapFunction #[]) 0)
  passed := passed && (← expectIntResult "GoCore array slice alias" (GoCore.Machine.runFunctionM 100000 coreArraySliceAliasFunction #[]) 229)
  passed := passed && (← expectIntResult "GoCore slice reslice" (GoCore.Machine.runFunctionM 100000 coreSliceResliceFunction #[]) 213)
  passed := passed && (← expectIntResult "GoCore slice extend to capacity" (GoCore.Machine.runFunctionM 100000 coreSliceExtendToCapacityFunction #[]) 3444)
  passed := passed && (← expectIntResult "GoCore full slice" (GoCore.Machine.runFunctionM 100000 coreFullSliceFunction #[]) 5)
  passed := passed && (← expectIntResult "GoCore make slice" (GoCore.Machine.runFunctionM 100000 coreMakeSliceFunction #[]) 537)
  passed := passed && (← expectIntResult "GoCore map basic" (GoCore.Machine.runFunctionM 100000 coreMapBasicFunction #[]) 1070)
  passed := passed && (← expectIntResult "GoCore string basic" (GoCore.Machine.runFunctionM 100000 coreStringFunction #[]) 22)
  passed := passed && (← expectIntResult "GoCore string byte length" (GoCore.Machine.runFunctionM 100000 coreStringByteLenFunction #[]) 6)
  passed := passed && (← expectValues "GoCore string byte indexing"
    (GoCore.Machine.runFunctionM 100000 coreStringIndexFunction #[]) #[.int 195 .uint8, .int 169 .uint8])
  passed := passed && (← expectIntResult "GoCore string byte slicing" (GoCore.Machine.runFunctionM 100000 coreStringSliceFunction #[]) 295)
  passed := passed && (← expectIntResult "GoCore string byte conversions"
    (GoCore.Machine.runFunctionM 100000 coreStringByteConversionFunction #[]) 5656855)
  passed := passed && (← expectIntResult "GoCore string rune conversions"
    (GoCore.Machine.runFunctionM 100000 coreStringRuneConversionFunction #[]) 1653953)
  passed := passed && (← expectIntResult "GoCore new allocation" (GoCore.Machine.runFunctionM 100000 coreNewFunction #[]) 70)
  passed := passed && (← expectErrorStatus "GoCore nil dereference panic" (GoCore.Machine.runFunctionM 100000 coreNilDerefFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore divide by zero panic" (GoCore.Machine.runFunctionM 100000 coreDivideByZeroFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore index address bounds panic" (GoCore.Machine.runFunctionM 100000 coreIndexAddrBoundsFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore slice bounds panic" (GoCore.Machine.runFunctionM 100000 coreSliceBoundsFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore nil map assignment panic" (GoCore.Machine.runFunctionM 100000 coreNilMapAssignFunction #[]) "panic")
  passed := passed && (← expectErrorStatus "GoCore mismatched equality stuck" (GoCore.Machine.runFunctionM 100000 coreMismatchedEqualityFunction #[]) "stuck")
  passed := passed && (← expectIntResult "GoCore call target sequencing"
    (GoCore.Machine.runFunctionWithContextM 100000 [] #[coreShiftIndexFunction, coreCallTargetSequencingFunction] coreCallTargetSequencingFunction #[]) 901)
  passed := passed && (← expectIntResult "GoCore simultaneous assignment sequencing"
    (GoCore.Machine.runFunctionM 100000 coreAssignManySequencingFunction #[]) 1200)
  passed := passed && (← expectIntResult "GoCore if return positive" (GoCore.Machine.runFunctionM 100000 coreIfReturnFunction #[.int 7]) 7)
  passed := passed && (← expectIntResult "GoCore if return negative" (GoCore.Machine.runFunctionM 100000 coreIfReturnFunction #[.int (-3)]) 103)
  passed := passed && (← expectIntResult "GoCore break continue" (GoCore.Machine.runFunctionM 100000 coreBreakContinueFunction #[]) 8)
  if passed then
    return 0
  else
    return 1

end Tests.GoCoreEval

def main : IO UInt32 :=
  Tests.GoCoreEval.main
