import GoLean.GoCore
import GoLean.CLI
-- The UNTRUSTED dedup engine, explicitly: the certificate-mutation
-- regression tests below manufacture a real certificate with it and
-- then assert only about the verified checker. Tests are a CLI-side
-- consumer, outside the engine-isolation clause's scope (core/proofs);
-- the import is spelled out rather than inherited through CLI so that
-- dependency is legible.
import GoLean.EnumDedup
import Tests.FloatVectors

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

/-! ### Channel statements (channels arc slice 1): make/send/recv/close/
len/cap FIFO behavior, the deadlocked terminal, the nil-close panic, and
deterministic select (one-ready; default fallthrough). -/

private def coreChanBasicFunction : GoCore.Func := {
  id := ⟨"chanBasic_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "chv", typ := .chan .both .int },
      { id := "a", typ := .int },
      { id := "b", typ := .int },
      { id := "okv", typ := .bool },
      { id := "score", typ := .int }
    ]
    #[
      .makeChan (.var "chv") .int (some (.intLit 2)),
      .chanSend (.var "chv") (.intLit 7) .int,
      .chanSend (.var "chv") (.intLit 8) .int,
      -- len 2, cap 2 while queued
      .assign (.var "score")
        (.add (.mul (.length (.var "chv") (some (.chan .both .int))) (.intLit 10))
          (.capacity (.var "chv") (some (.chan .both .int)))),
      .chanRecv #[.var "a", .var "okv"] (.var "chv") .int,
      .closeChan (.var "chv"),
      -- close does not drain: the queued 8 still arrives, FIFO
      .chanRecv #[.var "b"] (.var "chv") .int,
      -- closed-and-drained: zero value, ok = false
      .chanRecv #[.var "z", .var "okv"] (.var "chv") .int,
      .ifThenElse (.var "okv")
        (.assign (.var "z") (.intLit 999))
        (.assign (.var "z")
          (.add (.mul (.var "score") (.intLit 100))
            (.add (.mul (.var "a") (.intLit 10)) (.var "b"))))
    ]
}

private def coreChanDeadlockFunction : GoCore.Func := {
  id := ⟨"chanDeadlock_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      -- unbuffered self-send: blocks; the sequential driver classifies
      -- the blocked configuration as the deadlocked run
      .chanSend (.var "chv") (.intLit 1) .int
    ]
}

private def coreChanCloseNilFunction : GoCore.Func := {
  id := ⟨"chanCloseNil_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[.closeChan (.var "chv")]
}

private def coreChanSelectFunction : GoCore.Func := {
  id := ⟨"chanSelect_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "chv", typ := .chan .both .int },
      { id := "nilv", typ := .chan .both .int },
      { id := "rv", typ := .int },
      { id := "okv", typ := .bool }
    ]
    #[
      .makeChan (.var "chv") .int (some (.intLit 1)),
      .chanSend (.var "chv") (.intLit 5) .int,
      .selectStmt #[
        (.recv #[.var "rv", .var "okv"] (.var "nilv") .int,
          .assign (.var "z") (.intLit 111)),
        (.recv #[.var "rv", .var "okv"] (.var "chv") .int,
          .assign (.var "z") (.mul (.var "rv") (.intLit 3)))
      ] none
    ]
}

private def coreChanSelectDefaultFunction : GoCore.Func := {
  id := ⟨"chanSelectDefault_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "chv", typ := .chan .both .int },
      { id := "rv", typ := .int }
    ]
    #[
      .makeChan (.var "chv") .int (some (.intLit 1)),
      .selectStmt #[
        (.recv #[.var "rv"] (.var "chv") .int,
          .assign (.var "z") (.intLit 333))
      ] (some (.assign (.var "z") (.intLit 444)))
    ]
}

/-! ### The ThreadPool (channels arc slice 2): spawn + rendezvous,
multi-goroutine deadlock, main-exit kills goroutines (D6), close-wake,
and the nil-spawn fail-closed refusal — hand-built Programs run on the
pool driver (`runProgramPoolM`). -/

private def poolWorkerSendFunction : GoCore.Func := {
  id := ⟨"poolWorkerSend_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 42) .int]
}

private def poolSpawnMainFunction : GoCore.Func := {
  id := ⟨"poolSpawnMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"poolWorkerSend_F"⟩ #[]) #[.var "chv"],
      -- main parks; the worker's arriving send pairs with it (rendezvous)
      .chanRecv #[.var "z"] (.var "chv") .int
    ]
}

private def poolWorkerRecvFunction : GoCore.Func := {
  id := ⟨"poolWorkerRecv_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanRecv #[] (.var "ch") .int]
}

private def poolDeadlockMainFunction : GoCore.Func := {
  id := ⟨"poolDeadlockMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "av", typ := .chan .both .int },
      { id := "bv", typ := .chan .both .int }]
    #[
      .makeChan (.var "av") .int none,
      .makeChan (.var "bv") .int none,
      .goStmt (.funcVal ⟨"poolWorkerRecv_F"⟩ #[]) #[.var "av"],
      -- worker parks on a, main parks on b: ALL goroutines asleep
      .chanRecv #[.var "z"] (.var "bv") .int
    ]
}

private def poolMainExitFunction : GoCore.Func := {
  id := ⟨"poolMainExit_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"poolWorkerRecv_F"⟩ #[]) #[.var "chv"],
      -- main returns with the worker parked forever: program exits with
      -- main's outcome (D6), the leaked goroutine unobserved
      .assign (.var "z") (.intLit 7)
    ]
}

private def poolCloseWakeWorkerFunction : GoCore.Func := {
  id := ⟨"poolCloseWakeWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int },
            { id := "done", typ := .chan .both .int }],
  results := #[],
  body := .block
    #[{ id := "v", typ := .int }, { id := "okv", typ := .bool }]
    #[
      .chanRecv #[.var "v", .var "okv"] (.var "ch") .int,
      .ifThenElse (.var "okv")
        (.chanSend (.var "done") (.intLit 999) .int)
        (.chanSend (.var "done") (.intLit 55) .int)
    ]
}

private def poolCloseWakeMainFunction : GoCore.Func := {
  id := ⟨"poolCloseWakeMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "donev", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .makeChan (.var "donev") .int none,
      .goStmt (.funcVal ⟨"poolCloseWakeWorker_F"⟩ #[]) #[.var "chv", .var "donev"],
      -- close wakes the parked receiver into the drained zero (ok=false)
      .closeChan (.var "chv"),
      .chanRecv #[.var "z"] (.var "donev") .int
    ]
}

private def poolNilSpawnFunction : GoCore.Func := {
  id := ⟨"poolNilSpawn_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  -- gc: "fatal error: go of nil func value" at the spawn — the fatal
  -- class is unmodeled; the pool refuses fail-closed (probed
  -- 2026-08-07, refuting the child-panic analysis)
  body := .seqn #[.goStmt (.nil none) #[]]
}

private def poolProgram : GoCore.Program := {
  funcs := #[poolWorkerSendFunction, poolSpawnMainFunction,
    poolWorkerRecvFunction, poolDeadlockMainFunction, poolMainExitFunction,
    poolCloseWakeWorkerFunction, poolCloseWakeMainFunction,
    poolNilSpawnFunction]
}


/-! ### The D5-precision poller family (slice-5 audit response, MAJOR):
the DISCRIMINATING record for the stream-vs-branch distinction. Main
spawns a sender on `done` and a select-default POLLER on `poll` (which
never fires), then receives from `done`. EVERY finite stream terminates
main-`.normal` 42 — but the minimum fuel grows without bound in the
stream length (probed: ≈9n+21 for streams `[2]*n`, which keep picking
the poller), so NO uniform fuel bound exists and `TerminatesNormallyC`
is FALSE for this program even though "no (finite) stream diverges"
holds. ∀-stream facts quantify only the eventually-canonical branches
of the pick tree; the exact `TerminatesNormallyC` characterization is
the FINITE PICK TREE (docs/2026-08-07_fairness-precision-note.md §1).
The two pins fix one fuel and exhibit the growth: the shorter stream
completes, the longer one exhausts the same fuel. -/

private def pollerSendOneFunction : GoCore.Func := {
  id := ⟨"pollerSendOne_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 42) .int]
}

private def pollerLoopFunction : GoCore.Func := {
  id := ⟨"pollerLoop_F"⟩,
  args := #[{ id := "poll", typ := .chan .both .int }],
  results := #[],
  body := .while (.boolLit true)
    (.selectStmt #[(.recv #[] (.var "poll") .int, .seqn #[])]
      (some (.seqn #[])))
}

private def pollerMainFunction : GoCore.Func := {
  id := ⟨"pollerMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "pollv", typ := .chan .both .int },
      { id := "donev", typ := .chan .both .int }]
    #[
      .makeChan (.var "pollv") .int none,
      .makeChan (.var "donev") .int none,
      .goStmt (.funcVal ⟨"pollerSendOne_F"⟩ #[]) #[.var "donev"],
      .goStmt (.funcVal ⟨"pollerLoop_F"⟩ #[]) #[.var "pollv"],
      .chanRecv #[.var "z"] (.var "donev") .int
    ]
}

private def pollerProgram : GoCore.Program := {
  funcs := #[pollerSendOneFunction, pollerLoopFunction, pollerMainFunction]
}

/-! ### Waiter-queue priority (S2 audit response, major findings):
gc consults parked waiters BEFORE the buffer. Stream-pinned pool runs
— deterministic given the stream — discriminate handoff/refill from
the old buffer-transit model; go-run oracle values recorded per pin.
Streams [1,1] drive the worker to park FIRST (pick the worker at the
two scheduling points); [] leaves the worker unstarted at main's
decision point. -/

private def prioRecvOutWorkerFunction : GoCore.Func := {
  id := ⟨"prioRecvOutWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int },
            { id := "out", typ := .chan .both .int }],
  results := #[],
  body := .block
    #[{ id := "v", typ := .int }]
    #[
      .chanRecv #[.var "v"] (.var "ch") .int,
      .chanSend (.var "out") (.var "v") .int
    ]
}

-- go oracle (handoff): parked receiver + buffered send -> DIRECT
-- handoff, len stays 0 => 1*100 + 0*10 = 100 (old model buffered:
-- len 1 => 110).
private def prioSendHandoffMainFunction : GoCore.Func := {
  id := ⟨"prioSendHandoffMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "outv", typ := .chan .both .int },
      { id := "l", typ := .int },
      { id := "r", typ := .int }]
    #[
      .makeChan (.var "chv") .int (some (.intLit 2)),
      .makeChan (.var "outv") .int (some (.intLit 1)),
      .goStmt (.funcVal ⟨"prioRecvOutWorker_F"⟩ #[]) #[.var "chv", .var "outv"],
      .chanSend (.var "chv") (.intLit 1) .int,
      .assign (.var "l") (.length (.var "chv") (some (.chan .both .int))),
      .chanRecv #[.var "r"] (.var "outv") .int,
      .assign (.var "z")
        (.add (.mul (.var "r") (.intLit 100)) (.mul (.var "l") (.intLit 10)))
    ]
}

private def prioSendSendWorkerFunction : GoCore.Func := {
  id := ⟨"prioSendSendWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int },
            { id := "out", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .chanSend (.var "ch") (.intLit 9) .int,
    .chanSend (.var "out") (.intLit 1) .int
  ]
}

-- go oracle (refill): receive against a parked sender over a FULL
-- buffer takes the head AND refills from the sender in one step —
-- len stays 1 => 5*1000 + 1*100 + 9*10 + 1 = 5191 (old model: len 0
-- until the sender's separate room-wake => 5091).
private def prioRecvRefillMainFunction : GoCore.Func := {
  id := ⟨"prioRecvRefillMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "outv", typ := .chan .both .int },
      { id := "l", typ := .int },
      { id := "r", typ := .int },
      { id := "r2", typ := .int },
      { id := "o", typ := .int }]
    #[
      .makeChan (.var "chv") .int (some (.intLit 1)),
      .makeChan (.var "outv") .int (some (.intLit 1)),
      .chanSend (.var "chv") (.intLit 5) .int,
      .goStmt (.funcVal ⟨"prioSendSendWorker_F"⟩ #[]) #[.var "chv", .var "outv"],
      .chanRecv #[.var "r"] (.var "chv") .int,
      .assign (.var "l") (.length (.var "chv") (some (.chan .both .int))),
      .chanRecv #[.var "r2"] (.var "chv") .int,
      .chanRecv #[.var "o"] (.var "outv") .int,
      .assign (.var "z")
        (.add (.mul (.var "r") (.intLit 1000))
          (.add (.mul (.var "l") (.intLit 100))
            (.add (.mul (.var "r2") (.intLit 10)) (.var "o"))))
    ]
}

private def prioSendSevenWorkerFunction : GoCore.Func := {
  id := ⟨"prioSendSevenWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 7) .int]
}

-- go oracle: a select WITH default sees a parked sender (selectgo
-- consults the sudog queues) => communication case, 7. Old model:
-- cell-blind readiness took default => 99.
private def prioSelectDefaultRecvMainFunction : GoCore.Func := {
  id := ⟨"prioSelectDefaultRecvMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"prioSendSevenWorker_F"⟩ #[]) #[.var "chv"],
      .selectStmt #[
        (.recv #[.var "z"] (.var "chv") .int, .seqn #[])
      ] (some (.assign (.var "z") (.intLit 99)))
    ]
}

private def prioRecvForwardWorkerFunction : GoCore.Func := {
  id := ⟨"prioRecvForwardWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int },
            { id := "out", typ := .chan .both .int }],
  results := #[],
  body := .block
    #[{ id := "v", typ := .int }]
    #[
      .chanRecv #[.var "v"] (.var "ch") .int,
      .chanSend (.var "out") (.var "v") .int
    ]
}

-- go oracle: a select WITH default sees a parked receiver on its SEND
-- clause => communication case, worker forwards 3 => 10 + 3 = 13.
-- Old model: default => 99.
private def prioSelectDefaultSendMainFunction : GoCore.Func := {
  id := ⟨"prioSelectDefaultSendMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "outv", typ := .chan .both .int },
      { id := "o", typ := .int }]
    #[
      .makeChan (.var "chv") .int none,
      .makeChan (.var "outv") .int (some (.intLit 1)),
      .goStmt (.funcVal ⟨"prioRecvForwardWorker_F"⟩ #[]) #[.var "chv", .var "outv"],
      .selectStmt #[
        (.send (.var "chv") (.intLit 3) .int,
          .seqn #[
            .chanRecv #[.var "o"] (.var "outv") .int,
            .assign (.var "z") (.add (.intLit 10) (.var "o"))
          ])
      ] (some (.assign (.var "z") (.intLit 99)))
    ]
}

-- S2 convergence round (CRITICAL): an arriving SELECT must take the
-- closed CELL semantics, never a pairing — gc checks closed before any
-- waiter dequeue. Stream [1,1] parks the worker BEFORE main closes and
-- selects (the schedule the strict lane's four streams never realize).

private def closedRecvWorkerFunction : GoCore.Func := {
  id := ⟨"closedRecvWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .block
    #[{ id := "v", typ := .int }, { id := "okv", typ := .bool }]
    #[.chanRecv #[.var "v", .var "okv"] (.var "ch") .int]
}

-- go oracle: close precedes the select in program order => the send
-- clause panics "send on closed channel" under EVERY schedule (probed
-- 200000/200000). The waiter-blind bug paired with the parked receiver
-- instead => 103.
private def closedSelSendMainFunction : GoCore.Func := {
  id := ⟨"closedSelSendMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"closedRecvWorker_F"⟩ #[]) #[.var "chv"],
      .closeChan (.var "chv"),
      .selectStmt #[
        (.send (.var "chv") (.intLit 3) .int,
          .assign (.var "z") (.intLit 103))
      ] (some (.assign (.var "z") (.intLit 99)))
    ]
}

private def closedSendWorkerFunction : GoCore.Func := {
  id := ⟨"closedSendWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 7) .int]
}

-- go oracle: the recv clause on a closed channel is the drained zero
-- with ok=false (=> 5); the parked sender is close-woken into its own
-- panic, never delivered. The waiter-blind bug handed the select the
-- parked sender's 7 with ok=true => 7100.
-- BUG-045/BUG-046: the closed-guard-past-parked-sender shape is
-- correctly raceDetected for BOTH waiter kinds — the plain send's
-- entry read AND (BUG-046, reversing this comment's original false
-- "selectgo performs no chan-object access" claim) the select-send's
-- POLL read (selectgo pass 1 racereadpc, select.go:288) each conflict
-- with the close's write when unordered. The shape below is TSan-red
-- 30/30; its pin expects race. Invariant (iv)'s
-- arriving-select-past-parked-sender guard is therefore
-- detector-unreachable in race-free programs for ANY parked-sender
-- kind (an HB-ordered close hits sclose/send-on-closed at the poll
-- instead of parking); the green twin below exercises the poll read
-- plus a close race-free via the op-x-select pairing order.
private def closedSelSendWorkerFunction : GoCore.Func := {
  id := ⟨"closedSelSendWorker_F"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.selectStmt #[
    (.send (.var "ch") (.intLit 7) .int, .seqn #[])] none]
}

private def closedSelRecvMainFunction : GoCore.Func := {
  id := ⟨"closedSelRecvMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "v", typ := .int }, { id := "okv", typ := .bool }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"closedSendWorker_F"⟩ #[]) #[.var "chv"],
      .closeChan (.var "chv"),
      .selectStmt #[
        (.recv #[.var "v", .var "okv"] (.var "chv") .int,
          .ifThenElse (.var "okv")
            (.assign (.var "z")
              (.add (.mul (.var "v") (.intLit 1000)) (.intLit 100)))
            (.assign (.var "z")
              (.add (.mul (.var "v") (.intLit 1000)) (.intLit 5))))
      ] none
    ]
}

-- The race-free guard twin (BUG-045 comment above): identical shape,
-- worker parked on a single-clause SELECT-send.
private def closedSelRecvSelWaiterMainFunction : GoCore.Func := {
  id := ⟨"closedSelRecvSelWaiterMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int },
      { id := "v", typ := .int }, { id := "okv", typ := .bool }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"closedSelSendWorker_F"⟩ #[]) #[.var "chv"],
      .closeChan (.var "chv"),
      .selectStmt #[
        (.recv #[.var "v", .var "okv"] (.var "chv") .int,
          .ifThenElse (.var "okv")
            (.assign (.var "z")
              (.add (.mul (.var "v") (.intLit 1000)) (.intLit 100)))
            (.assign (.var "z")
              (.add (.mul (.var "v") (.intLit 1000)) (.intLit 5))))
      ] none
    ]
}

-- BUG-046 green twin: main receives FROM the parked select-send (the
-- op-x-select pairing joins the clocks), so the later close is ordered
-- after the worker's poll read — race-free, value 7, and the poll-read
-- machinery is exercised on a green path.
private def selSendPairedCloseMainFunction : GoCore.Func := {
  id := ⟨"selSendPairedCloseMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .goStmt (.funcVal ⟨"closedSelSendWorker_F"⟩ #[]) #[.var "chv"],
      .chanRecv #[.var "z"] (.var "chv") .int,
      .closeChan (.var "chv")
    ]
}

private def prioProgram : GoCore.Program := {
  funcs := #[prioRecvOutWorkerFunction, prioSendHandoffMainFunction,
    prioSendSendWorkerFunction, prioRecvRefillMainFunction,
    prioSendSevenWorkerFunction, prioSelectDefaultRecvMainFunction,
    prioRecvForwardWorkerFunction, prioSelectDefaultSendMainFunction,
    closedRecvWorkerFunction, closedSelSendMainFunction,
    closedSendWorkerFunction, closedSelRecvMainFunction,
    closedSelSendWorkerFunction, closedSelRecvSelWaiterMainFunction,
    selSendPairedCloseMainFunction]
}

/-! ### Race detection (channels arc slice 3, D2+D3(b)): stream-pinned
pool runs of racy programs — refusal must be `raceDetected` on every
tested stream when the race executes on every schedule, and the
exit-no-sync shape pins the SCHEDULE-DEPENDENT refusal the corpus
cannot express (main-first schedules never execute the child's write:
value leaf under [], race leaf under [1] — one racy leaf poisons the
CASE, which is the slice-4 enumerator's job; recorded in the design
note). -/

-- Slice 4 (L2 live): the WAKE-path head-commit discriminator — a
-- parked select whose channels BOTH become ready via closes (closes
-- never pair, so the wake is cell-based). The b-clause is listed FIRST:
-- a wake that head-commits the first wake-ready clause gives 2 on the
-- park-then-both-closes schedule REGARDLESS of further stream content,
-- while a (forbidden) re-randomizing wake would consume the next pick
-- and could give 1 — the trailing 1s in the pinned stream are the
-- discriminator.
private def wakeMultiWorkerFunction : GoCore.Func := {
  id := ⟨"wakeMultiWorker_F"⟩,
  args := #[{ id := "a", typ := .chan .both .int },
            { id := "b", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.closeChan (.var "a"), .closeChan (.var "b")]
}

private def wakeMultiMainFunction : GoCore.Func := {
  id := ⟨"wakeMultiMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "av", typ := .chan .both .int },
      { id := "bv", typ := .chan .both .int }]
    #[
      .makeChan (.var "av") .int (some (.intLit 1)),
      .makeChan (.var "bv") .int (some (.intLit 1)),
      .goStmt (.funcVal ⟨"wakeMultiWorker_F"⟩ #[]) #[.var "av", .var "bv"],
      .selectStmt #[
        (.recv #[] (.var "bv") .int, .assign (.var "z") (.intLit 2)),
        (.recv #[] (.var "av") .int, .assign (.var "z") (.intLit 1))
      ] none
    ]
}

private def raceStoreWorkerFunction : GoCore.Func := {
  id := ⟨"raceStoreWorker_F"⟩,
  args := #[{ id := "p", typ := .pointer .int },
            { id := "done", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .assign (.addr (.var "p")) (.intLit 1),
    .chanSend (.var "done") (.intLit 0) .int
  ]
}

-- Write/write on every schedule: main's store to x is sequenced before
-- its receive; the worker's store before its send — HB-unordered under
-- every pick sequence.
private def raceWriteWriteMainFunction : GoCore.Func := {
  id := ⟨"raceWriteWriteMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .int },
      { id := "donev", typ := .chan .both .int }]
    #[
      .makeChan (.var "donev") .int none,
      .goStmt (.funcVal ⟨"raceStoreWorker_F"⟩ #[]) #[.ref "x", .var "donev"],
      .assign (.var "x") (.intLit 2),
      .chanRecv #[] (.var "donev") .int,
      .assign (.var "z") (.var "x")
    ]
}

private def raceStoreOnlyWorkerFunction : GoCore.Func := {
  id := ⟨"raceStoreOnlyWorker_F"⟩,
  args := #[{ id := "p", typ := .pointer .int }],
  results := #[],
  body := .seqn #[.assign (.addr (.var "p")) (.intLit 7)]
}

-- Exit-no-sync: goroutine exit is NOT synchronized-before anything
-- (go_mem), so when the child's write executes before main's read the
-- run must refuse — but a main-first schedule never runs the child at
-- all (main returns, the spawned write is discarded) and the run is a
-- legitimate value leaf. Both leaves pinned below.
private def raceExitNoSyncMainFunction : GoCore.Func := {
  id := ⟨"raceExitNoSyncMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .int }]
    #[
      .goStmt (.funcVal ⟨"raceStoreOnlyWorker_F"⟩ #[]) #[.ref "x"],
      .assign (.var "z") (.var "x")
    ]
}

-- The rendezvous edge, machine-level: the worker's store is ordered
-- before main's read THROUGH the unbuffered send/recv pairing — green
-- on every stream (the corpus litmus lane pins the other edges).
private def raceHbWorkerFunction : GoCore.Func := {
  id := ⟨"raceHbWorker_F"⟩,
  args := #[{ id := "p", typ := .pointer .int },
            { id := "done", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .assign (.addr (.var "p")) (.intLit 9),
    .chanSend (.var "done") (.intLit 0) .int
  ]
}

private def raceHbGreenMainFunction : GoCore.Func := {
  id := ⟨"raceHbGreenMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "x", typ := .int },
      { id := "donev", typ := .chan .both .int }]
    #[
      .makeChan (.var "donev") .int none,
      .goStmt (.funcVal ⟨"raceHbWorker_F"⟩ #[]) #[.ref "x", .var "donev"],
      .chanRecv #[] (.var "donev") .int,
      .assign (.var "z") (.var "x")
    ]
}

private def raceProgram : GoCore.Program := {
  funcs := #[raceStoreWorkerFunction, raceWriteWriteMainFunction,
    raceStoreOnlyWorkerFunction, raceExitNoSyncMainFunction,
    raceHbWorkerFunction, raceHbGreenMainFunction]
}

private def wakeMultiProgram : GoCore.Program := {
  funcs := #[wakeMultiWorkerFunction, wakeMultiMainFunction]
}

/-! ### Sync primitives (spec-parity slice 2): pool pins for behaviors
no corpus lane can express (the schedule-pinned classes). -/

private def syncWgWaiterFunction : GoCore.Func := {
  id := ⟨"syncWgWaiter_F"⟩,
  args := #[{ id := "wgp", typ := .pointer (.sync .waitGroup) }],
  results := #[],
  body := .seqn #[.syncStmt .wgWait #[.var "wgp"] #[]]
}

private def syncWgMisuseMainFunction : GoCore.Func := {
  id := ⟨"syncWgMisuseMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "wg", typ := .sync .waitGroup }]
    #[
      .syncStmt .wgAdd #[.ref "wg", .intLit 1] #[],
      .goStmt (.funcVal ⟨"syncWgWaiter_F"⟩ #[]) #[.ref "wg"],
      .syncStmt .wgAdd #[.ref "wg", .intLit (-1)] #[],
      .syncStmt .wgAdd #[.ref "wg", .intLit 1] #[],
      .assign (.var "z") (.intLit 1)
    ]
}

private def syncMuWorkerFunction : GoCore.Func := {
  id := ⟨"syncMuWorker_F"⟩,
  args := #[{ id := "mp", typ := .pointer (.sync .mutex) },
            { id := "done", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .syncStmt .lock #[.var "mp"] #[],
    .syncStmt .unlock #[.var "mp"] #[],
    .chanSend (.var "done") (.intLit 5) .int]
}

private def syncMuWakeMainFunction : GoCore.Func := {
  id := ⟨"syncMuWakeMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "mu", typ := .sync .mutex },
      { id := "donev", typ := .chan .both .int }]
    #[
      .makeChan (.var "donev") .int none,
      .syncStmt .lock #[.ref "mu"] #[],
      .goStmt (.funcVal ⟨"syncMuWorker_F"⟩ #[]) #[.ref "mu", .var "donev"],
      .syncStmt .unlock #[.ref "mu"] #[],
      .chanRecv #[.var "z"] (.var "donev") .int
    ]
}

private def syncWgWaiterSendFunction : GoCore.Func := {
  id := ⟨"syncWgWaiterSend_F"⟩,
  args := #[{ id := "wgp", typ := .pointer (.sync .waitGroup) },
            { id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .syncStmt .wgWait #[.var "wgp"] #[],
    .chanSend (.var "ch") (.intLit 1) .int]
}

/-- The REUSE-WINDOW discriminator (audit fix round 2026-08-10, the
verifier's two-waiter shape): W1 waits and then hands main an HB edge
over the channel; W2 only waits. On the stream that parks BOTH waiters
before main's zeroing Done, the post-window `Add(1)` runs with W1's
first-waiter sema WRITE HB-covered (the channel handoff) and W2 still
parked — so no race fires, and a resume-time waiter retirement would
panic in the ADDER ("Add called concurrently with Wait") where gc's
ADD side is silent (waitgroup.go:135 resets the wait count inside the
zeroing Add, before the semreleases). Precision (delta-review round
2): gc's misuse detection moves to the WAITER (waitgroup.go:213),
which CAN panic in the general window on other schedules; THIS shape's
channel handoff forces the woken waiter to have resumed before the
Adds — that causal claim covers W1 only; W2 (a bare Wait, not
channel-ordered) is excluded from the panic EMPIRICALLY (the round-2
verifier's 5400-run probe of this shape found no waiter-side panic),
not by a forcing edge — so gc is clean on this shape end-to-end
(probed); the general waiter-side panic is the recorded §8
narrowing. -/
private def syncWgReuseMainFunction : GoCore.Func := {
  id := ⟨"syncWgReuseMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "wg", typ := .sync .waitGroup },
      { id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .syncStmt .wgAdd #[.ref "wg", .intLit 1] #[],
      .goStmt (.funcVal ⟨"syncWgWaiterSend_F"⟩ #[]) #[.ref "wg", .var "chv"],
      .goStmt (.funcVal ⟨"syncWgWaiter_F"⟩ #[]) #[.ref "wg"],
      .syncStmt .wgAdd #[.ref "wg", .intLit (-1)] #[],
      .chanRecv #[.var "z"] (.var "chv") .int,
      .syncStmt .wgAdd #[.ref "wg", .intLit 1] #[],
      .syncStmt .wgAdd #[.ref "wg", .intLit (-1)] #[]
    ]
}

private def syncXUnlockW1Function : GoCore.Func := {
  id := ⟨"syncXUnlockW1_F"⟩,
  args := #[{ id := "mp", typ := .pointer (.sync .mutex) }],
  results := #[],
  body := .seqn #[.syncStmt .unlock #[.var "mp"] #[]]
}

private def syncXUnlockW2Function : GoCore.Func := {
  id := ⟨"syncXUnlockW2_F"⟩,
  args := #[{ id := "mp", typ := .pointer (.sync .mutex) },
            { id := "gp", typ := .pointer .int },
            { id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[
    .syncStmt .lock #[.var "mp"] #[],
    .chanSend (.var "ch") (.deref (.var "gp") .int) .int]
}

/-- The U5 divergence pin (RE-ENCODED at delta-review round 2,
2026-08-10 — the first version published BEFORE the spawns, so the
spawn edge HB-ordered the pair under ANY release rule: a vacuous pin
with a false oracle claim; delta-review verifiers .tmp/verify-f2 +
.tmp/verify/u5disc constructed this correct shape and mutation-tested
the model). The shape: BOTH goroutines spawn while main holds the
lock and BEFORE the publish, so neither inherits an HB edge over the
write; main publishes, releases (the merge keeps main's clock in
semA), and re-acquires; W1 — which never acquired — performs the
owner-free unlock (probe p09: legal); W2 then locks and reads the
published value. Under the MERGE release semA still carries main's
critical section at W2's acquire, so the read is HB-ordered and the
run is GREEN — the memory-model sentence verbatim. gc's TSan hook is
overwrite `race.Release`: W1's unlock REPLACES semA with W1's clock
(which predates the write), and `go run -race` reports a DATA RACE on
exactly this shape (delta-review probes: 3/3 runs, exit 66, on
go1.26.5 with the interleaving forced by delays; the machine realizes
it by stream instead). TSan-red/ours-green — the recorded U5
narrowing; un-lane-able as a corpus row (mixed oracle). -/
private def syncXUnlockMainFunction : GoCore.Func := {
  id := ⟨"syncXUnlockMain_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "mu", typ := .sync .mutex },
      { id := "g", typ := .int },
      { id := "chv", typ := .chan .both .int }]
    #[
      .makeChan (.var "chv") .int none,
      .syncStmt .lock #[.ref "mu"] #[],
      .goStmt (.funcVal ⟨"syncXUnlockW1_F"⟩ #[]) #[.ref "mu"],
      .goStmt (.funcVal ⟨"syncXUnlockW2_F"⟩ #[]) #[.ref "mu", .ref "g", .var "chv"],
      .assign (.var "g") (.intLit 1),
      .syncStmt .unlock #[.ref "mu"] #[],
      .syncStmt .lock #[.ref "mu"] #[],
      .chanRecv #[.var "z"] (.var "chv") .int
    ]
}

private def syncEvalProgram : GoCore.Program := {
  funcs := #[syncWgWaiterFunction, syncWgMisuseMainFunction,
    syncMuWorkerFunction, syncMuWakeMainFunction,
    syncWgWaiterSendFunction, syncWgReuseMainFunction,
    syncXUnlockW1Function, syncXUnlockW2Function,
    syncXUnlockMainFunction]
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
      .allocNew (.var "p") (.defaultValue .int) .int,
      .assign (.addr (.var "p")) (.intLit 7),
      .allocNew (.var "s") (.defaultValue (.slice .int)) (.slice .int),
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

private def expectIntResult (name : String) (result : Except Stop GoLean.GoCore.Readout)
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

private def expectTrue (name : String) (b : Bool) : IO Bool := do
  if b then
    IO.println s!"ok: {name}"
    return true
  else
    IO.eprintln s!"FAIL: {name}: condition is false"
    return false

private def expectBoolResult (name : String) (result : Except Stop GoLean.GoCore.Readout)
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

private def expectValues (name : String) (result : Except Stop GoLean.GoCore.Readout)
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

private def expectErrorStatus (name : String) (result : Except Stop GoLean.GoCore.Readout)
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

private def expectOk (name : String) (result : Except Stop GoLean.GoCore.Readout) :
    IO Bool := do
  match result with
  | .ok _ =>
      IO.println s!"ok: {name}"
      return true
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {repr err}"
      return false

/-- The lifted body of `func() { x++ }` (W5 §8): captures arrive as pointer
parameters, so the closure and its creator share the cell. -/
def coreClosureBodyFunction : GoCore.Func := {
  id := ⟨"main$lit0"⟩
  args := #[⟨"x$ptr", .pointer (.int .int)⟩]
  results := #[]
  body := .seqn #[
    .assign (.addr (.var "x$ptr"))
      (.add (.deref (.var "x$ptr") (.int .int)) (.intLit 1 .int))]
}

/-- `x := 0; f := func(){ x++ }; f(); f(); return x` — the machine half of
`functions/closure-share`: TWO calls through one func value must both hit the
SAME captured cell, which is what capture-by-reference means. -/
def coreClosureShareFunction : GoCore.Func := {
  id := ⟨"closureShare"⟩
  args := #[]
  results := #[⟨"r", .int .int⟩]
  body := .seqn #[
    .initialization ⟨"x", .int .int⟩,
    .initialization ⟨"f", .funcType [] [] false⟩,
    .assign (.var "f") (.funcVal ⟨"main$lit0"⟩ #[.ref "x"]),
    .callValue #[] (.var "f") #[],
    .callValue #[] (.var "f") #[],
    .assign (.var "r") (.var "x"),
    .returnStmt]
}

/-- The lifted body of `func(rp *int) { if recover() != nil { *rp = 7 } }` —
the canonical recover-er, receiving the captured address of a result cell. -/
def coreRecoverBodyFunction : GoCore.Func := {
  id := ⟨"main$rec0"⟩
  args := #[⟨"rp", .pointer (.int .int)⟩]
  results := #[]
  body := .seqn #[
    .ifThenElse
      (.neqCmp (.interface ⟨"empty_interface"⟩) .recoverCall (.nil none))
      (.assign (.addr (.var "rp")) (.intLit 7))
      (.seqn #[]),
    .returnStmt]
}

/-- `r := 0; defer rec(&r); panic("boom"); r` — the deferred call runs on
the panic path, `recover` cancels the unwind, and the function returns
normally with the named result the recover-er wrote (the unwinding arc). -/
def coreRecoverCatchFunction : GoCore.Func := {
  id := ⟨"recoverCatch"⟩
  args := #[]
  results := #[⟨"r", .int .int⟩]
  body := .seqn #[
    .deferCall (.funcVal ⟨"main$rec0"⟩ #[.ref "r"]) #[],
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string (.stringLit (GoString.fromLeanString "boom"))),
    .returnStmt]
}

/-- Same recover-er drained on the NORMAL exit path: `recover` returns nil
(nothing is panicking), so the result keeps its assigned value. -/
def coreRecoverNormalNilFunction : GoCore.Func := {
  id := ⟨"recoverNormalNil"⟩
  args := #[]
  results := #[⟨"r", .int .int⟩]
  body := .seqn #[
    .deferCall (.funcVal ⟨"main$rec0"⟩ #[.ref "r"]) #[],
    .assign (.var "r") (.intLit 5),
    .returnStmt]
}

/-- `panic(4)` with no recover: the chain unwinds to the entry frame and
aborts with panic status (message pinned by the differential). -/
def corePanicAbortFunction : GoCore.Func := {
  id := ⟨"panicAbort"⟩
  args := #[]
  results := #[⟨"r", .int .int⟩]
  body := .seqn #[
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) (.int .int) (.intLit 4 .int)),
    .returnStmt]
}

/-! ## Membership-lane enumerator pins (audit response, 2026-08-05)

F3: `appendGrowthCap` value pins. Before the membership lane, a
machine-side growth-formula regression flipped `slices/full-slice-cap-zero`
nondet→differential in the baseline; under the lane, Go staying inside the
window keeps the case PASS, so the formula needs its own machine-side pin.

F1: the status-discipline guardrail — a shape that appends into a
zero-cap window and panics on one specific capacity (`cap == 7`, i.e.
spill extra 3): the machine panics under streams Go can never realize,
and an `--expect-status ok` enumeration must FAIL loud, never bury the
panic member in the set.

F5: driver-agreement pins — `CLI.enumSetup`/`CLI.enumRunProgram`/
`CLI.enumPoolRun`/`CLI.enumInitRun` (and, slice 4, the stepwise
engine's `CLI.stepNeeds` consumption accountant) COPY
`runProgramPoolM`/`execProgLoop`/`runConfig`'s wiring (no
shared driver helper BY POLICY — the lane adds nothing to GoCore; the
old "GoCore stays bit-identical" wording was the membership slice's
own constraint, stale as a standing fact — arc-final audit F16,
2026-08-06; `seedGlobals` IS shared
— stream-independent setup); these tests pin the copies against the
originals: the single-run driver's observation (`observationOfRun ∘
runProgramM`, the exact engine behind `native-json-run`) must be a
member of the enumerated set, per consumption-site class (append spill;
map-range pick-next, including the panic-observation path; the
`$pkginit` init phase since the init slice). The go-side half of this
pin is the harness's per-case coupling check in
`scripts/diff-coverage`. -/

private def coreEnumCapPanicFunction : GoCore.Func := {
  id := ⟨"enum_cap_panic_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "s", typ := .slice .int },
      { id := "e", typ := .slice .int }
    ]
    #[
      .makeSlice (.var "s") .int (.intLit 0) (some (.intLit 0)),
      .makeSlice (.var "e") .int (.intLit 1) none,
      .appendSlice (.var "s") .int (.var "s") (.var "e"),
      .ifThenElse (.eqCmp .int (.capacity (.var "s")) (.intLit 7))
        (.panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) (.int .int) (.intLit 7 .int)))
        (.seqn #[]),
      .assign (.var "z") (.capacity (.var "s"))
    ]
}

private def coreEnumFirstKeyFunction : GoCore.Func := {
  id := ⟨"enum_first_key_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "m", typ := .map .int .int },
      { id := "first", typ := .int }
    ]
    #[
      .makeMap (.var "m") .int .int none,
      .mapAssign (.var "m") (.intLit 1) (.intLit 10) .int .int,
      .mapAssign (.var "m") (.intLit 2) (.intLit 20) .int .int,
      .mapAssign (.var "m") (.intLit 3) (.intLit 30) .int .int,
      .assign (.var "first") (.intLit (-1)),
      .mapRange (some "k") none (.var "m") .int .int
        (.ifThenElse (.lessCmp (.var "first") (.intLit 0))
          (.assign (.var "first") (.var "k"))
          (.seqn #[])),
      .assign (.var "z") (.var "first")
    ]
}

private def enumCapPanicProgram : GoCore.Program := { funcs := #[coreEnumCapPanicFunction] }
private def enumFirstKeyProgram : GoCore.Program := { funcs := #[coreEnumFirstKeyFunction] }

/-- Init-slice driver-agreement shape: `$pkginit` consumes choices (a
map-range pick) and writes the picked key into global cell 0; the
subject only reads the global. Pins that BOTH drivers run `$pkginit`
per stream — an enumerator that ran init once with a fixed stream, or a
driver that skipped seeding, diverges loudly here. -/
private def coreEnumInitPickInit : GoCore.Func := {
  id := GoCore.pkgInitFuncId,
  args := #[],
  results := #[],
  body := .block
    #[
      { id := "m", typ := .map .int .int },
      { id := "first", typ := .int }
    ]
    #[
      .makeMap (.var "m") .int .int none,
      .mapAssign (.var "m") (.intLit 1) (.intLit 10) .int .int,
      .mapAssign (.var "m") (.intLit 2) (.intLit 20) .int .int,
      .mapAssign (.var "m") (.intLit 3) (.intLit 30) .int .int,
      .assign (.var "first") (.intLit (-1)),
      .mapRange (some "k") none (.var "m") .int .int
        (.ifThenElse (.lessCmp (.var "first") (.intLit 0))
          (.assign (.var "first") (.var "k"))
          (.seqn #[])),
      .assign (.addr (.global 0)) (.var "first")
    ]
}

private def coreEnumInitReadFunction : GoCore.Func := {
  id := ⟨"enum_init_read_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .assign (.var "z") (.deref (.global 0) .int)
}

private def enumInitPickProgram : GoCore.Program := {
  funcs := #[coreEnumInitReadFunction, coreEnumInitPickInit],
  globals := #[{ name := "g", typ := .int }]
}

/-- Init-panic shape (audit response 2026-08-05, C4): `$pkginit` panics
before the subject can run — the enumerator's init-phase panic branch
(`enumRunProgram`'s `.inr` arm) must surface it as the run's (only)
member, and the whole-program driver must agree. -/
private def coreEnumInitPanicInit : GoCore.Func := {
  id := GoCore.pkgInitFuncId,
  args := #[],
  results := #[],
  body := .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string
    (.stringLit { bytes := "init boom".toUTF8.data }))
}

private def enumInitPanicProgram : GoCore.Program := {
  funcs := #[coreEnumInitReadFunction, coreEnumInitPanicInit],
  globals := #[{ name := "g", typ := .int }]
}

private def enumerate (program : GoCore.Program) (name : String)
    (expectStatus : Option (List String)) : Except String CLI.EnumOutcome :=
  match CLI.enumSetup program name #[] with
  | .error err => .error s!"setup failed: {repr err}"
  | .ok ep =>
      -- Width 32: the append-spill site's bound at the cap-panic shape
      -- (oldCap 0, newLen 1) is appendSpillWidth 0 1 = 32 since the F2
      -- envelope widening (arc-final audit, 2026-08-06); map shapes
      -- need at most 3; pool sites (slice 4) are bounded by the
      -- goroutine count. Since slice 4 the engine is the stepwise
      -- pool explorer with mechanically-computed per-site bounds
      -- (`CLI.explore`) — width is the mechanical cap.
      CLI.explore ep 1000000 32 16 64 500000 expectStatus

private def expectNatEq (name : String) (actual expected : Nat) : IO Bool := do
  if actual == expected then
    IO.println s!"ok: {name}"
    return true
  else
    IO.eprintln s!"FAIL: {name}: expected {expected}, got {actual}"
    return false

private def expectStrEq (name : String) (actual expected : String) : IO Bool := do
  if actual == expected then
    IO.println s!"ok: {name}"
    return true
  else
    IO.eprintln s!"FAIL: {name}: expected {repr expected}, got {repr actual}"
    return false

private def expectEnumFailure (name : String) (result : Except String CLI.EnumOutcome)
    (needle : String) : IO Bool := do
  match result with
  | .error msg =>
      if (msg.splitOn needle).length > 1 then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: enumeration failed but without {repr needle}: {msg}"
        return false
  | .ok out =>
      IO.eprintln s!"FAIL: {name}: expected loud enumeration failure, got {out.observations.size} member(s)"
      return false

private def expectEnumMembers (name : String) (result : Except String CLI.EnumOutcome)
    (expected : Nat) : IO Bool := do
  match result with
  | .error msg =>
      IO.eprintln s!"FAIL: {name}: enumeration failed: {msg}"
      return false
  | .ok out =>
      if out.observations.size == expected then
        IO.println s!"ok: {name}"
        return true
      else
        IO.eprintln s!"FAIL: {name}: expected {expected} member(s), got {out.observations.size}"
        return false

/-- The F5 pin proper: for each stream, the single-run driver's canonical
observation must be a member of the enumerated set. -/
private def expectDriverAgreement (name : String) (program : GoCore.Program)
    (fname : String) (expectStatus : Option (List String))
    (streams : List (List Nat)) : IO Bool := do
  match enumerate program fname expectStatus with
  | .error msg =>
      IO.eprintln s!"FAIL: {name}: enumeration failed: {msg}"
      return false
  | .ok out =>
      for s in streams do
        let obs := CLI.observationOfRun
          (GoCore.Machine.runProgramM 1000000 program fname #[] s)
        if !out.observations.contains obs then
          IO.eprintln s!"FAIL: {name}: driver observation under stream {s} is not in the enumerated set: {obs.compress}"
          return false
      IO.println s!"ok: {name}"
      return true

/-- The slice-4 POOL half of the F5 pin: the enumerated set must contain
the POOL driver's observation under each stream. The stepwise engine
reuses `stepMulti`/`raceUpdate` but hand-mirrors the loop and the
consumption ACCOUNTANT (`CLI.stepNeeds`) — this pin is the accountant's
drift alarm: an accountant bound smaller than the machine's real one
would leave a driver-reachable observation out of the set. -/
private def expectPoolDriverAgreement (name : String) (program : GoCore.Program)
    (fname : String) (expectStatus : Option (List String))
    (streams : List (List Nat)) : IO Bool := do
  match enumerate program fname expectStatus with
  | .error msg =>
      IO.eprintln s!"FAIL: {name}: enumeration failed: {msg}"
      return false
  | .ok out =>
      for s in streams do
        let obs := CLI.observationOfRun
          (GoCore.Machine.runProgramPoolM 1000000 program fname #[] s)
        if !out.observations.contains obs then
          IO.eprintln s!"FAIL: {name}: pool driver observation under stream {s} is not in the enumerated set: {obs.compress}"
          return false
      IO.println s!"ok: {name}"
      return true

/-! ## FloatBits oracle vectors (floats slice F1, 2026-08-05)

`Tests/FloatVectors.lean` is GENERATED by `tools/floatvectors`:
hardware-computed IEEE-754 bit vectors (the differential oracle's own
platform semantics — per-op round-to-nearest-even, the pinned envelope
point) plus strconv-correctly-rounded rationals, over
`runtime/softfloat64_test.go`'s base list, value-class specials, and
seeded randoms. The checker below runs EVERY vector against the
transcribed kernel and fails loud on the first mismatches; the count is
pinned so an empty/truncated vector string cannot vacuously pass. NaN
outputs are canonicalized on both sides (generator header; design note
§4 — payloads are platform noise the language cannot observe). -/

open GoCore.FloatBits in
private def canon64 (bits : Nat) : Nat :=
  if (bits >>> 52) &&& 0x7FF == 0x7FF && bits &&& ((1 <<< 52) - 1) != 0 then
    nan64
  else bits

open GoCore.FloatBits in
private def canon32 (bits : Nat) : Nat :=
  if (bits >>> 23) &&& 0xFF == 0xFF && bits &&& ((1 <<< 23) - 1) != 0 then
    nan32
  else bits

open GoCore.FloatBits in
/-- Check one vector line; `none` = pass, `some msg` = mismatch. FAIL
CLOSED on parse: an unparsable field is a failure, never a skip (an
Option-`do` version silently passed on parse failure — caught before it
shipped). -/
private def checkFloatVector (parts : List String) : Option String :=
  let bin (canon : Nat → Nat) (f : Nat → Nat → Nat) (xs ys zs : String) :
      Option String :=
    match xs.toNat?, ys.toNat?, zs.toNat? with
    | some x, some y, some z =>
        let got := canon (f x y)
        if got == z then none else some s!"got {got}, want {z}"
    | _, _, _ => some "unparsable operands"
  let cmp (eq lt le : Nat → Nat → Bool) (xs ys cs : String) : Option String :=
    match xs.toNat?, ys.toNat?, cs.toNat? with
    | some x, some y, some c =>
        let got := (if eq x y then 1 else 0) + (if lt x y then 2 else 0)
          + (if le x y then 4 else 0)
        if got == c then none else some s!"cmp got {got}, want {c}"
    | _, _, _ => some "unparsable operands"
  let un (canon : Nat → Nat) (f : Nat → Nat) (xs zs : String) : Option String :=
    match xs.toNat?, zs.toNat? with
    | some x, some z =>
        let got := canon (f x)
        if got == z then none else some s!"got {got}, want {z}"
    | _, _ => some "unparsable operands"
  let rat (canon : Nat → Nat) (f : Int → Nat → Nat) (nums dens zs : String) :
      Option String :=
    match nums.toInt?, dens.toNat?, zs.toNat? with
    | some num, some den, some z =>
        let got := canon (f num den)
        if got == z then none else some s!"got {got}, want {z}"
    | _, _, _ => some "unparsable operands"
  match parts with
  | ["a64", x, y, z] => bin canon64 fadd64 x y z
  | ["s64", x, y, z] => bin canon64 fsub64 x y z
  | ["m64", x, y, z] => bin canon64 fmul64 x y z
  | ["d64", x, y, z] => bin canon64 fdiv64 x y z
  | ["a32", x, y, z] => bin canon32 fadd32 x y z
  | ["s32", x, y, z] => bin canon32 fsub32 x y z
  | ["m32", x, y, z] => bin canon32 fmul32 x y z
  | ["d32", x, y, z] => bin canon32 fdiv32 x y z
  | ["c64", x, y, c] => cmp feq64 flt64 fle64 x y c
  | ["c32", x, y, c] => cmp feq32 flt32 fle32 x y c
  | ["t32", x, z] => un canon32 f64to32 x z
  | ["t64", x, z] => un canon64 f32to64 x z
  | ["n64", x, z] => un id fneg64 x z
  | ["i64", xs, ns] =>
      match xs.toNat?, ns.toInt? with
      | some x, some n =>
          match f64truncInt? x with
          | some got => if got == n then none else some s!"got {got}, want {n}"
          | none => some s!"got none, want {n}"
      | _, _ => some "unparsable operands"
  | ["i32", xs, ns] =>
      match xs.toNat?, ns.toInt? with
      | some x, some n =>
          match f32truncInt? x with
          | some got => if got == n then none else some s!"got {got}, want {n}"
          | none => some s!"got none, want {n}"
      | _, _ => some "unparsable operands"
  | ["r64", num, den, z] => rat canon64 ratToFloat64 num den z
  | ["r32", num, den, z] => rat canon32 ratToFloat32 num den z
  | _ => some "malformed vector line"

private def expectFloatVectors (name : String) : IO Bool := do
  let mut checked := 0
  let mut failures := 0
  for line in Tests.FloatVectors.lines.splitOn "\n" do
    if line.isEmpty then
      continue
    match checkFloatVector (line.splitOn " ") with
    | none => checked := checked + 1
    | some msg =>
        if failures < 10 then
          IO.eprintln s!"FAIL: {name}: vector `{line}`: {msg}"
        failures := failures + 1
        checked := checked + 1
  if failures != 0 then
    IO.eprintln s!"FAIL: {name}: {failures} of {checked} vector(s) mismatched"
    return false
  if checked != Tests.FloatVectors.expectedCount then
    IO.eprintln s!"FAIL: {name}: checked {checked} vector(s), generator recorded {Tests.FloatVectors.expectedCount} (truncated vector data?)"
    return false
  IO.println s!"ok: {name} ({checked} vectors)"
  return true

/-! ## Float machine-arm tests (floats slice F2)

Hand-built GoCore terms driving the new arms through the MACHINE (the
corpus stays frontend-export red until F3): literal rounding, per-op
arithmetic, IEEE equality/ordering (NaN, ±0), value-directed negation,
no-panic float division, conversions (f64→f32 rounding, in-range
float→int truncation, the int64→float32 single-rounding discriminator),
the fail-closed out-of-range refusal, and NaN map-key identity. -/

private def floatTy : GoCore.Ty := .float .float64
private def float32Ty : GoCore.Ty := .float .float32

private def f64Lit (num : Int) (den : Nat := 1) : GoCore.Expr :=
  .floatLit num den .float64

private def coreFloatArithFunction : GoCore.Func := {
  id := ⟨"float_arith_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "a", typ := floatTy }, { id := "b", typ := floatTy },
      { id := "c", typ := floatTy }, { id := "zero", typ := floatTy },
      { id := "nan", typ := floatTy }, { id := "negz", typ := floatTy },
      { id := "d", typ := floatTy }
    ]
    #[
      .assign (.var "a") (f64Lit 1),
      .assign (.var "b") (f64Lit 3),
      .assign (.var "c") (.div (.var "a") (.var "b")),
      .ifThenElse (.lessCmp (.var "c") (f64Lit 1 2))
        (.assign (.var "z") (.add (.var "z") (.intLit 1))) (.seqn #[]),
      .assign (.var "zero") (.sub (.var "a") (.var "a")),
      -- 0.0/0.0: NaN, never a panic (design note §3.2)
      .assign (.var "nan") (.div (.var "zero") (.var "zero")),
      .ifThenElse (.neqCmp floatTy (.var "nan") (.var "nan"))
        (.assign (.var "z") (.add (.var "z") (.intLit 10))) (.seqn #[]),
      -- proper negation: -(+0) = -0; +0 == -0 under Go ==
      .assign (.var "negz") (.neg (.var "zero")),
      .ifThenElse (.eqCmp floatTy (.var "negz") (.var "zero"))
        (.assign (.var "z") (.add (.var "z") (.intLit 100))) (.seqn #[]),
      -- 1 / -0 = -Inf < 0
      .assign (.var "d") (.div (.var "a") (.var "negz")),
      .ifThenElse (.lessCmp (.var "d") (f64Lit 0))
        (.assign (.var "z") (.add (.var "z") (.intLit 1000))) (.seqn #[])
    ]
}

private def coreFloatConvertFunction : GoCore.Func := {
  id := ⟨"float_convert_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "big", typ := floatTy }, { id := "f32", typ := float32Ty },
      { id := "u", typ := .int .uint8 },
      { id := "g", typ := float32Ty }, { id := "h", typ := float32Ty }
    ]
    #[
      -- f64→f32 conversion rounding: 16777217.0 → 16777216.0f
      .assign (.var "big") (f64Lit 16777217),
      .assign (.var "f32") (.convert float32Ty (.var "big")),
      .ifThenElse (.eqCmp float32Ty (.var "f32") (.floatLit 16777216 1 .float32))
        (.assign (.var "z") (.add (.var "z") (.intLit 1))) (.seqn #[]),
      -- in-range float→int truncates toward zero: 253.5 → 253 at uint8
      .assign (.var "u") (.convert (.int .uint8) (f64Lit 507 2)),
      .ifThenElse (.eqCmp (.int .uint8) (.var "u") (.intLit 253 .uint8))
        (.assign (.var "z") (.add (.var "z") (.intLit 10))) (.seqn #[]),
      -- int64→float32 single rounding (the probed discriminator):
      -- 9007199791611905 → 0x5A000001 ≠ float32(2^53)
      .assign (.var "g") (.convert float32Ty (.intLit 9007199791611905 .int64)),
      .assign (.var "h") (.convert float32Ty (.intLit 9007199254740992 .int64)),
      .ifThenElse (.neqCmp float32Ty (.var "g") (.var "h"))
        (.assign (.var "z") (.add (.var "z") (.intLit 100))) (.seqn #[])
    ]
}

/-- The §3.3 refusal at machine level — the negative pin's core half
(the corpus half is `floats/to-int-out-of-range`, permanently red). -/
private def coreFloatToIntRefusalFunction : GoCore.Func := {
  id := ⟨"float_to_int_refusal_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[{ id := "big", typ := floatTy }]
    #[
      .assign (.var "big") (f64Lit 1000000000000000000000),  -- 1e21
      .assign (.var "z") (.convert (.int .int64) (.var "big"))
    ]
}

/-- NaN map keys at machine level: two inserts append two DISTINCT
entries (valueEq's IEEE arm inside `mapEntryIndex?`). -/
private def coreFloatNaNMapFunction : GoCore.Func := {
  id := ⟨"float_nan_map_F"⟩,
  args := #[],
  results := #[coreParam "z"],
  body := .block
    #[
      { id := "m", typ := .map floatTy .int },
      { id := "zero", typ := floatTy }, { id := "nan", typ := floatTy }
    ]
    #[
      .makeMap (.var "m") floatTy .int none,
      .assign (.var "zero") (f64Lit 0),
      .assign (.var "nan") (.div (.var "zero") (.var "zero")),
      .mapAssign (.var "m") (.var "nan") (.intLit 1) floatTy .int,
      .mapAssign (.var "m") (.var "nan") (.intLit 2) floatTy .int,
      .assign (.var "z") (.length (.var "m") none)
    ]
}

set_option maxRecDepth 4096 in
def main : IO UInt32 := do
  let mut passed := true
  passed := passed && (← expectFloatVectors "FloatBits hardware-oracle vectors")
  passed := passed && (← expectIntResult "GoCore float arithmetic/compare/neg (IEEE, no div panic)"
    (GoCore.Machine.runFunctionM 100000 coreFloatArithFunction #[]) 1111)
  passed := passed && (← expectIntResult "GoCore float conversions (round-once paths)"
    (GoCore.Machine.runFunctionM 100000 coreFloatConvertFunction #[]) 111)
  passed := passed && (← expectErrorStatus "GoCore float→int out-of-range refuses (fail closed)"
    (GoCore.Machine.runFunctionM 100000 coreFloatToIntRefusalFunction #[]) "unsupported")
  passed := passed && (← expectIntResult "GoCore NaN map keys are distinct entries"
    (GoCore.Machine.runFunctionM 100000 coreFloatNaNMapFunction #[]) 2)
  passed := passed && (← expectIntResult "GoCore add function" (GoCore.Machine.runFunctionM 100000 coreAddFunction #[.int 2, .int 3]) 5)
  passed := passed && (← expectBoolResult "GoCore pointer identity" (GoCore.Machine.runFunctionM 100000 corePointerIdentityFunction #[]) false)
  passed := passed && (← expectIntResult "GoCore struct field update" (GoCore.Machine.runFunctionWithTypesM 100000 coreCellTypes coreStructFunction #[]) 17)
  passed := passed && (← expectIntResult "GoCore shared-heap function call"
    (GoCore.Machine.runFunctionWithContextM 100000 coreCellTypes #[coreSetCellFunction, coreCallFunction] coreCallFunction #[]) 9)
  -- BUG-085 guard (fail-closed heap store; grumpy-professor review §2 U5 /
  -- §3 A2): a store to a `.base` address with NO heap cell must REFUSE,
  -- never materialize a phantom untyped cell. No corpus row can reach this
  -- arm (allocation goes through `ExecState.alloc`, which creates the cell
  -- before any store; `StateWf` bounds every address), so the guard lives
  -- here at the Lean level. Positive control first: the same store to an
  -- ALLOCATED cell succeeds, so the refusal below is not "refuses everything".
  passed := passed && (← expectTrue "GoCore storeLoc to an ALLOCATED .base cell succeeds (positive control for the BUG-085 guard)"
    (let (loc, s) := (({} : GoCore.ExecState).alloc (.int 0) .int)
     match GoCore.storeLoc s loc (.int 7) with
     | .ok s' =>
         match GoCore.loadLoc s' loc with
         | .ok (.int 7 _) => true
         | _ => false
     | .error _ => false))
  passed := passed && (← expectTrue "GoCore storeLoc to an UNALLOCATED .base address REFUSES `.internal` (BUG-085: no phantom cell, fail closed)"
    (match GoCore.storeLoc ({} : GoCore.ExecState) (.base ⟨0⟩) (.int 7) with
     | .error (.internal _) => true
     | _ => false))
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
  passed := passed && (← expectIntResult "GoCore channel make/send/recv/close (FIFO, comma-ok, close-does-not-drain)"
    (GoCore.Machine.runFunctionM 100000 coreChanBasicFunction #[]) 2278)
  passed := passed && (← expectErrorStatus "GoCore blocked channel op classifies deadlock"
    (GoCore.Machine.runFunctionM 100000 coreChanDeadlockFunction #[]) "deadlock")
  passed := passed && (← expectErrorStatus "GoCore close of nil channel panics"
    (GoCore.Machine.runFunctionM 100000 coreChanCloseNilFunction #[]) "panic")
  passed := passed && (← expectIntResult "GoCore select exactly-one-ready receive (nil never ready)"
    (GoCore.Machine.runFunctionM 100000 coreChanSelectFunction #[]) 15)
  passed := passed && (← expectIntResult "GoCore select default fallthrough (none ready)"
    (GoCore.Machine.runFunctionM 100000 coreChanSelectDefaultFunction #[]) 444)
  passed := passed && (← expectIntResult "GoCore pool spawn + rendezvous pairing"
    (GoCore.Machine.runProgramPoolM 100000 poolProgram "poolSpawnMain_F" #[]) 42)
  passed := passed && (← expectErrorStatus "GoCore pool multi-goroutine deadlock (all asleep)"
    (GoCore.Machine.runProgramPoolM 100000 poolProgram "poolDeadlockMain_F" #[]) "deadlock")
  passed := passed && (← expectIntResult "GoCore pool main-exit kills parked goroutine (D6)"
    (GoCore.Machine.runProgramPoolM 100000 poolProgram "poolMainExit_F" #[]) 7)
  passed := passed && (← expectIntResult "GoCore pool close wakes parked receiver (drained zero)"
    (GoCore.Machine.runProgramPoolM 100000 poolProgram "poolCloseWakeMain_F" #[]) 55)
  passed := passed && (← expectErrorStatus "GoCore pool nil spawn callee is gc's runtime fatal (triage L10; the fatal class, not a refusal)"
    (GoCore.Machine.runProgramPoolM 100000 poolProgram "poolNilSpawn_F" #[]) "fatal")
  -- Stage D re-derivation (B2): the [2]*n family's picks now resolve
  -- against the backEdge-widened site sequence and no longer realize a
  -- deferral schedule; the [1]*n family does (slot 1 = the first
  -- non-current runnable at the postOp/backEdge menus): min fuel
  -- measured 59/74/90 at n=8/16/32 — still monotone in the stream, so
  -- the family's POINT (no uniform fuel bound over streams) survives
  -- the widening with new witnesses.
  passed := passed && (← expectIntResult "GoCore poller family: shorter stream completes at fuel 74 (min 74 at [1]*16; stage-D re-derivation — the deferral family is [1]*n under the widened sites)"
    (GoCore.Machine.runProgramPoolM 74 pollerProgram "pollerMain_F" #[]
      (List.replicate 16 1)) 42)
  passed := passed && (← expectErrorStatus "GoCore poller family: longer stream exhausts the same fuel (min 90 at [1]*32 — min fuel grows with the stream; no uniform bound)"
    (GoCore.Machine.runProgramPoolM 74 pollerProgram "pollerMain_F" #[]
      (List.replicate 32 1)) "fuel-out")
  passed := passed && (← expectIntResult "GoCore pool waiter priority: buffered send hands off to the parked receiver (len 0; gc chansend recvq-first)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "prioSendHandoffMain_F" #[] [1, 1]) 100)
  passed := passed && (← expectIntResult "GoCore pool waiter priority: receive refills from the parked sender (len preserved; gc recv same-slot)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "prioRecvRefillMain_F" #[] [1, 1]) 5191)
  passed := passed && (← expectIntResult "GoCore pool waiter-extended select: default loses to a parked sender"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "prioSelectDefaultRecvMain_F" #[] [1, 1]) 7)
  passed := passed && (← expectIntResult "GoCore pool waiter-extended select: default loses to a parked receiver (send clause)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "prioSelectDefaultSendMain_F" #[] [1, 1]) 13)
  passed := passed && (← expectIntResult "GoCore pool select default IS taken with no parked partner (envelope's other member, stream [])"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "prioSelectDefaultRecvMain_F" #[] []) 99)
  passed := passed && (← expectErrorStatus "GoCore pool arriving select: send clause on a CLOSED channel panics past a parked receiver (gc closed-before-dequeue)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "closedSelSendMain_F" #[] [1, 1]) "panic")
  -- BUG-045/BUG-046: the arriving-select-past-parked-sender guard is
  -- the chan-object race for BOTH waiter kinds (the corpus racy cases
  -- recv-parked-sender and send-close-race certify every-path
  -- refusal); the poll-read path is exercised green by the
  -- pairing-ordered twin below.
  passed := passed && (← expectErrorStatus "GoCore pool arriving select recv on CLOSED past a parked plain sender is the chan-object race (BUG-045)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "closedSelRecvMain_F" #[] [1, 1]) "race")
  passed := passed && (← expectErrorStatus "GoCore pool arriving select recv on CLOSED past a parked SELECT-send waiter is ALSO the chan-object race (BUG-046: selectgo's poll read)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "closedSelRecvSelWaiterMain_F" #[] [1, 1]) "race")
  passed := passed && (← expectIntResult "GoCore pool select-send poll read is HB-ordered by the op-x-select pairing: receive from the parked select-send, then close, race-free (BUG-046 green twin)"
    (GoCore.Machine.runProgramPoolM 100000 prioProgram "selSendPairedCloseMain_F" #[] [1, 1]) 7)
  -- Sync primitives (spec-parity slice 2; CORRECTED at the audit fix
  -- round 2026-08-10 — the original comment claimed the shape was
  -- "intrinsically TSan-racy" so the race "always precedes" the
  -- misuse panic, refuted by the verifier's two-waiter counterexample;
  -- the panic arm itself is retired with the reuse-window fix). The
  -- Add-from-0-beside-a-parked-waiter shape refuses as the WG-SEMA
  -- race exactly when the adder's read (waitgroup.go:111-116) is
  -- HB-uncovered against the parked waiter's first-waiter WRITE
  -- (waitgroup.go:185-190) — here it is (no edge exists), matching
  -- `go run -race` on the same shape. Stream [1,1,0]: worker picked
  -- at the fork's completion AND at its wgWait apply (parking it),
  -- main takes the final Add.
  passed := passed && (← expectErrorStatus "GoCore sync: Add-from-0 beside a parked waiter is the wg-sema race (misuse pair; the panic is the sub-detector member)"
    (GoCore.Machine.runProgramPoolM 100000 syncEvalProgram "syncWgMisuseMain_F" #[] [1, 1, 0]) "race")
  passed := passed && (← expectIntResult "GoCore sync: parked Lock wakes on Unlock and acquires (park -> wake -> acquire, worker-first stream)"
    (GoCore.Machine.runProgramPoolM 100000 syncEvalProgram "syncMuWakeMain_F" #[] [1, 0]) 5)
  -- The reuse window (audit fix round 2026-08-10): gc's zeroing Add
  -- RESETS the wait count before releasing the semaphores
  -- (waitgroup.go:135), so an Add issued in the wake window sees w == 0
  -- and gc's ADD side is silent; THIS shape is gc-clean end-to-end
  -- (the channel handoff resumes W1 before the Adds and HB-covers the
  -- first-waiter sema write; W2's exclusion is probed-empirical — see
  -- the program docstring; the general window's WAITER-side reuse
  -- panic is the recorded §8 narrowing). Stream [1,1,1,1] parks both
  -- waiters before main's zeroing Done and realizes exactly that
  -- window. NON-VACUITY (checkable): at the pre-fix machine — tip
  -- 8b8fa09f plus only this program+pin, before the Machine.lean
  -- waiter-reset landed in 537fa219 — `lake exe gocore-eval-tests`
  -- FAILED this pin with exactly `Stop.panic "sync: WaitGroup
  -- misuse: Add called concurrently with Wait"` (the Add-side arm
  -- since removed).
  passed := passed && (← expectIntResult "GoCore sync: Add in the reuse window is CLEAN (gc resets the wait count in the zeroing Add; two-waiter shape, both parked)"
    (GoCore.Machine.runProgramPoolM 100000 syncEvalProgram "syncWgReuseMain_F" #[] [1, 1, 1, 1]) 1)
  -- U5 (RE-ENCODED at delta-review round 2 — the first pin published
  -- before the spawns and was VACUOUS: the spawn edge ordered the pair
  -- under any release rule, and its "-race red (verified by the
  -- audit)" claim was refuted by probe, 60/60 green). This shape (see
  -- syncXUnlockMainFunction's docstring) is the delta-review
  -- verifiers' discriminator: `go run -race` RED on it (3/3, exit 66;
  -- .tmp/verify/u5disc + .tmp/verify-f2/true2.go, go1.26.5), and the
  -- machine realizes the same interleaving on the EMPTY stream
  -- (default picks: main runs publish/unlock/re-lock, parks at the
  -- recv; W1's owner-free unlock; W2's acquire + read). Sensitivity
  -- verified by MUTATION BUILD at this fix round (tree copy with
  -- syncRelease's merge replaced by TSan's overwrite `semA := vt`):
  -- this pin flips to raceDetected there — the exact discrimination
  -- the first version lacked.
  passed := passed && (← expectIntResult "GoCore sync: owner-free cross-goroutine unlock keeps the publish HB-ordered under the merge release (U5: TSan-red/ours-green, mutation-tested)"
    (GoCore.Machine.runProgramPoolM 100000 syncEvalProgram "syncXUnlockMain_F" #[] []) 1)
  passed := passed && (← expectErrorStatus "GoCore race: write/write refuses on the default stream"
    (GoCore.Machine.runProgramPoolM 100000 raceProgram "raceWriteWriteMain_F" #[] []) "race")
  passed := passed && (← expectErrorStatus "GoCore race: write/write refuses on the worker-first stream"
    (GoCore.Machine.runProgramPoolM 100000 raceProgram "raceWriteWriteMain_F" #[] [1, 1]) "race")
  -- BUG-040 FIXED (slice 4): the post-spawn reschedule point exists —
  -- `spawnStep` leaves the parent on the `.spawned` marker, a registry
  -- boundary of its own, so stream [1] picks the CHILD at the fork's
  -- completion: the child's write executes before main's read with no
  -- ordering edge (goroutine exit synchronizes nothing — go_mem), and
  -- the exit-no-sync race class is DETECTABLE (race leaf on the
  -- child-first stream). The main-first empty stream keeps the value
  -- leaf (the child never runs; gc's dominant schedule) — one racy
  -- leaf beside a value leaf is exactly why this class is eval-pinned,
  -- not a corpus race case (the enumerated set is mixed).
  passed := passed && (← expectErrorStatus "GoCore race BUG-040 fixed: exit-no-sync refuses on the child-first stream [1] (post-spawn reschedule point live)"
    (GoCore.Machine.runProgramPoolM 100000 raceProgram "raceExitNoSyncMain_F" #[] [1]) "race")
  passed := passed && (← expectIntResult "GoCore race BUG-040: exit-no-sync main-first stream stays a value leaf (child never runs; matches gc's dominant schedule)"
    (GoCore.Machine.runProgramPoolM 100000 raceProgram "raceExitNoSyncMain_F" #[] []) 0)
  passed := passed && (← expectIntResult "GoCore race: rendezvous HB edge keeps the ordered store/read green (worker-first stream)"
    (GoCore.Machine.runProgramPoolM 100000 raceProgram "raceHbGreenMain_F" #[] [1, 1]) 9)
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
  -- RETUNED at the BUG-052 order pin (S1 audit, 2026-08-09): the call
  -- write-back reads target operands AFTER the call (gc's realized
  -- point inside spec §Order of evaluation's unordered carve-out), so
  -- `a[i] = shiftIndex(&i)` with the callee setting i := 1 stores into
  -- a[1], not a[0]: 901 (operand-first, the retired order) → 91. The
  -- oracle-backed guards are multi-assign/call-write-back-order/*.
  passed := passed && (← expectIntResult "GoCore call target sequencing (BUG-052: operands read post-call)"
    (GoCore.Machine.runFunctionWithContextM 100000 [] #[coreShiftIndexFunction, coreCallTargetSequencingFunction] coreCallTargetSequencingFunction #[]) 91)
  passed := passed && (← expectIntResult "GoCore simultaneous assignment sequencing"
    (GoCore.Machine.runFunctionM 100000 coreAssignManySequencingFunction #[]) 1200)
  passed := passed && (← expectIntResult "GoCore if return positive" (GoCore.Machine.runFunctionM 100000 coreIfReturnFunction #[.int 7]) 7)
  passed := passed && (← expectIntResult "GoCore if return negative" (GoCore.Machine.runFunctionM 100000 coreIfReturnFunction #[.int (-3)]) 103)
  passed := passed && (← expectIntResult "GoCore break continue" (GoCore.Machine.runFunctionM 100000 coreBreakContinueFunction #[]) 8)
  passed := passed && (← expectIntResult "GoCore closure shares captured cell"
    (GoCore.Machine.runFunctionWithContextM 100000 []
      #[coreClosureBodyFunction, coreClosureShareFunction] coreClosureShareFunction #[]) 2)
  passed := passed && (← expectIntResult "GoCore recover catches panic-path defer"
    (GoCore.Machine.runFunctionWithContextM 100000 []
      #[coreRecoverBodyFunction, coreRecoverCatchFunction] coreRecoverCatchFunction #[]) 7)
  passed := passed && (← expectIntResult "GoCore recover nil on normal drain"
    (GoCore.Machine.runFunctionWithContextM 100000 []
      #[coreRecoverBodyFunction, coreRecoverNormalNilFunction] coreRecoverNormalNilFunction #[]) 5)
  passed := passed && (← expectErrorStatus "GoCore unrecovered panic aborts"
    (GoCore.Machine.runFunctionM 100000 corePanicAbortFunction #[]) "panic")
  -- Fuel exhaustion is its OWN classification, distinct from stuck
  -- (sem-adequacy arc slice 2, 2026-08-03: interpreter-side Progress says
  -- "only .ok or fuel-out" — that reading is meaningless if the machine
  -- reports running out of fuel as being stuck). Guardrail authored
  -- BEFORE the Stop.fuelOut refinement; red against the old core.
  passed := passed && (← expectErrorStatus "GoCore fuel exhaustion is fuel-out, not stuck"
    (GoCore.Machine.runFunctionWithContextM 1 []
      #[coreClosureBodyFunction, coreClosureShareFunction] coreClosureShareFunction #[]) "fuel-out")
  passed := passed && (← expectErrorStatus "GoCore zero fuel is fuel-out"
    (GoCore.Machine.runFunctionM 0 corePanicAbortFunction #[]) "fuel-out")
  -- Membership-lane pins (audit response 2026-08-05; see the section
  -- comment above the enum shapes).
  -- F3: appendGrowthCap value pins — the machine side of the cap-zero
  -- envelope (the growth formula is the envelope's CENTER and the
  -- empty-stream point since F2's widening to [newLen, max(32,
  -- 2*growth)]; the old [0,8) window is gone) plus the formula's other
  -- regimes.
  -- TypeId.unqualified: the observation channel's reflect.Type.Name()
  -- contract, extended to MANGLED generic-instantiation keys (generics
  -- design note 2026-08-05 §3.1/§3.4 — probe outputs pinned verbatim).
  -- Only the LEADING package segment strips; type-argument qualifiers
  -- inside the brackets are part of Name().
  passed := passed && (← expectStrEq "TypeId.unqualified plain qualified key"
    (TypeId.unqualified ⟨"main.T"⟩) "T")
  passed := passed && (← expectStrEq "TypeId.unqualified unqualified key unchanged"
    (TypeId.unqualified ⟨"struct{}"⟩) "struct{}")
  passed := passed && (← expectStrEq "TypeId.unqualified predeclared key unchanged"
    (TypeId.unqualified ⟨"error"⟩) "error")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, builtin arg"
    (TypeId.unqualified ⟨"main.Pair[int]"⟩) "Pair[int]")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, package-qualified arg"
    (TypeId.unqualified ⟨"main.Pair[main.Inner]"⟩) "Pair[main.Inner]")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, pointer arg"
    (TypeId.unqualified ⟨"main.Pair[*main.Inner]"⟩) "Pair[*main.Inner]")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, nested instantiation"
    (TypeId.unqualified ⟨"main.Pair[main.Pair[int]]"⟩) "Pair[main.Pair[int]]")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, two args"
    (TypeId.unqualified ⟨"main.keyPair[int,string]"⟩) "keyPair[int,string]")
  passed := passed && (← expectStrEq "TypeId.unqualified mangled key, map arg with qualified value"
    (TypeId.unqualified ⟨"main.Vec[map[string]main.Inner]"⟩) "Vec[map[string]main.Inner]")
  passed := passed && (← expectNatEq "GoCore appendGrowthCap zero-cap single elem (cap-zero window base)"
    (GoCore.appendGrowthCap 0 1) 4)
  passed := passed && (← expectNatEq "GoCore appendGrowthCap zero-cap beyond floor"
    (GoCore.appendGrowthCap 0 7) 7)
  passed := passed && (← expectNatEq "GoCore appendGrowthCap small doubling"
    (GoCore.appendGrowthCap 1 2) 2)
  passed := passed && (← expectNatEq "GoCore appendGrowthCap doubling regime"
    (GoCore.appendGrowthCap 4 5) 8)
  passed := passed && (← expectNatEq "GoCore appendGrowthCap overshoot takes newLen"
    (GoCore.appendGrowthCap 2 5) 5)
  passed := passed && (← expectNatEq "GoCore appendGrowthCap large-cap 1.25x regime"
    (GoCore.appendGrowthCap 256 257) 512)
  -- F1 guardrail: the stream-panicking shape (panic iff spill capacity
  -- lands on 7) must FAIL an expect-status=ok enumeration loudly.
  passed := passed && (← expectEnumFailure "GoCore enumerator rejects stream-dependent panic under expect-status ok"
    (enumerate enumCapPanicProgram "enum_cap_panic_F" (some ["ok"])) "status divergence")
  -- Without a status expectation the same shape enumerates 32 members:
  -- the widened envelope [newLen, max(32, 2*growth)] = [1, 32] gives 31
  -- ok capacities + the cap-7 panic observation (arc-final audit F2 —
  -- was 8 under the old growth+[0,8) window).
  passed := passed && (← expectEnumMembers "GoCore enumerator admits the panic member without a status expectation"
    (enumerate enumCapPanicProgram "enum_cap_panic_F" none) 32)
  passed := passed && (← expectEnumMembers "GoCore enumerator first-key set is {1,2,3}"
    (enumerate enumFirstKeyProgram "enum_first_key_F" (some ["ok"])) 3)
  -- F5: driver-agreement pins, per consumption-site class (incl. the
  -- panic-observation path via stream [3] on the append shape: the
  -- envelope offset keeps extra 3 landing on cap 7 — newLen 1 +
  -- ((growth 4 - 1 + 3) % 32) = 7).
  passed := passed && (← expectDriverAgreement "GoCore enumerator agrees with the single-run driver (append spill incl. panic path)"
    enumCapPanicProgram "enum_cap_panic_F" none [[], [1], [3], [7], [12, 9]])
  passed := passed && (← expectDriverAgreement "GoCore enumerator agrees with the single-run driver (map-range pick-next)"
    enumFirstKeyProgram "enum_first_key_F" (some ["ok"]) [[], [1], [2], [5, 3, 1], [9, 8, 7, 6]])
  -- Init slice: $pkginit's choice consumption is part of the run in
  -- BOTH drivers (globals seeded, init run per stream).
  passed := passed && (← expectEnumMembers "GoCore enumerator init-phase pick set is {1,2,3}"
    (enumerate enumInitPickProgram "enum_init_read_F" (some ["ok"])) 3)
  passed := passed && (← expectDriverAgreement "GoCore enumerator agrees with the whole-program driver ($pkginit map-range pick)"
    enumInitPickProgram "enum_init_read_F" (some ["ok"]) [[], [1], [2], [5, 3, 1], [9, 8, 7, 6]])
  -- Audit response 2026-08-05, C4: the enumerator's init-phase PANIC
  -- branch — a panicking $pkginit is the run's single (panic) member,
  -- and both drivers surface the same observation.
  passed := passed && (← expectEnumMembers "GoCore enumerator surfaces the $pkginit panic member"
    (enumerate enumInitPanicProgram "enum_init_read_F" (some ["panic"])) 1)
  passed := passed && (← expectDriverAgreement "GoCore enumerator agrees with the whole-program driver ($pkginit panic)"
    enumInitPanicProgram "enum_init_read_F" (some ["panic"]) [[], [3], [7, 1]])
  -- Slice 4: the POOL engine's pins (stepwise explorer + consumption
  -- accountant), per pool consumption-site class.
  passed := passed && (← expectEnumMembers "GoCore pool enumerator: fork/join rendezvous is confluent (singleton over all schedules)"
    (enumerate poolProgram "poolSpawnMain_F" (some ["ok"])) 1)
  passed := passed && (← expectPoolDriverAgreement "GoCore pool enumerator agrees with the pool driver (fork/join; L1 + pairing)"
    poolProgram "poolSpawnMain_F" (some ["ok"]) [[], [1], [1, 1, 1], [9, 8, 7, 6]])
  passed := passed && (← expectEnumMembers "GoCore pool enumerator: waiter-extended select-with-default set is {7, 99} (the S2 audit envelope)"
    (enumerate prioProgram "prioSelectDefaultRecvMain_F" (some ["ok"])) 2)
  passed := passed && (← expectPoolDriverAgreement "GoCore pool enumerator agrees with the pool driver (waiter-extended select-with-default; L1 + L4)"
    prioProgram "prioSelectDefaultRecvMain_F" (some ["ok"]) [[], [1], [1, 1], [9, 8, 7, 6]])
  passed := passed && (← expectEnumMembers "GoCore pool enumerator: every enumerated path of write/write refuses (lane d, full strength)"
    (enumerate raceProgram "raceWriteWriteMain_F" (some ["race"])) 1)
  passed := passed && (← expectEnumMembers "GoCore pool enumerator: exit-no-sync has BOTH leaves (value + race — why the class is eval-pinned, not a corpus race case)"
    (enumerate raceProgram "raceExitNoSyncMain_F" none) 2)
  -- The wake-path head-commit discriminator (L2 envelope: NO
  -- re-randomization on the blocked path): under the pinned stream the
  -- select parks, BOTH channels close, and the wake commits the FIRST
  -- wake-ready clause in clause order (b-first => 2) — the trailing 1s
  -- prove no further pick is drawn at the wake (a re-randomizing wake
  -- would consume one and commit the a-clause instead).
  -- Stream [0,0,0,1,1,1] (re-derived at stage C — B1's post-op
  -- boundaries consume at new positions): picks — spawn-completion 0
  -- (main runs), main's select-apply boundary 0 (main parks),
  -- close-b COMPLETION (.opDone postOp, main now wake-ready) 0
  -- (worker continues), worker's close-a apply boundary 1 (worker
  -- closes a before the wake). The wake then sees BOTH clauses ready
  -- and head-commits b (listed first) WITHOUT consuming: the trailing
  -- 1s would flip the commit to the a-clause under a re-randomizing
  -- wake.
  passed := passed && (← expectIntResult "GoCore pool wake-path head-commit: both-closed wake commits the first clause in clause order, consuming nothing"
    (GoCore.Machine.runProgramPoolM 100000 wakeMultiProgram "wakeMultiMain_F" #[] [0, 0, 0, 1, 1, 1]) 2)
  passed := passed && (← expectEnumMembers "GoCore pool enumerator: wake/entry multi-ready select set is {1, 2}"
    (enumerate wakeMultiProgram "wakeMultiMain_F" (some ["ok"])) 2)
  -- S4 audit (the TWO-SIDED sentinel drift alarm's detection
  -- primitive, pinned both ways): at a consumption site the machine
  -- DRAWS the appended sentinel (so an accountant that missed the site
  -- — answering none — would trip poolStepDFS's leftover-!=-[sentinel]
  -- alarm), and away from a site the sentinel SURVIVES untouched. The
  -- site here is the L1 scheduler pick over two runnable no-clause
  -- selects (both at boundaries).
  passed := passed && (← expectTrue "GoCore accountant sentinel: an L1 site draws the sentinel (stepNeeds some 2, sentinel-run leftover [])"
    (let selB : GoCore.Machine.Config :=
      .exec (.selectStmt #[] (some (.seqn #[]))) [] .stop
     CLI.stepNeeds ⟨#[selB, selB], {}, 0⟩ [] == some 2
      && (match GoCore.Machine.stepMulti ⟨#[selB, selB], {}, 0⟩ [0] with
          | .ok (_, leftover, _) => leftover.isEmpty
          | .error _ => false)))
  passed := passed && (← expectTrue "GoCore accountant sentinel: a non-site leaves the sentinel (stepNeeds none, leftover [0])"
    (let selB : GoCore.Machine.Config :=
      .exec (.selectStmt #[] (some (.seqn #[]))) [] .stop
     CLI.stepNeeds ⟨#[selB], {}, 0⟩ [] == none
      && (match GoCore.Machine.stepMulti ⟨#[selB], {}, 0⟩ [0] with
          | .ok (_, leftover, _) => leftover == [0]
          | .error _ => false)))
  -- Audit response 2026-08-05, C6 (made NON-VACUOUS by delta-review M2 —
  -- the wp_assign lesson in test form: the original used the
  -- SUCCEEDING-init program, on which the OLD divergent orders already
  -- agreed byte-for-byte, so the pin passed on the very bug it guarded):
  -- the two drivers' pre-init wiring is ORDER-IDENTICAL (find -> arity
  -- -> seed -> init-shape). The DISCRIMINATING witness is the
  -- PANICKING-init program: under the old orders runProgramM ran init
  -- first and reported its panic while enumSetup reported the arity
  -- stuck; post-fix both refuse the arity BEFORE the init phase, with
  -- the same error. The succeeding-init shape stays as a second
  -- assertion.
  passed := passed && (← do
    let check (name : String) (program : GoCore.Program) : IO Bool := do
      let fromRun :=
        match GoCore.Machine.runProgramM 1000000 program "enum_init_read_F" #[.int 1] [] with
        | .error e => some (repr e).pretty
        | .ok _ => none
      let fromEnum :=
        match CLI.enumSetup program "enum_init_read_F" #[.int 1] with
        | .error e => some (repr e).pretty
        | .ok _ => none
      match fromRun, fromEnum with
      | some a, some b =>
          if a == b then
            if (a.splitOn "expected 0 argument(s)").length > 1 then
              IO.println s!"ok: {name}"
              pure true
            else do
              IO.eprintln s!"FAIL: {name}: both drivers refused but not with the arity error: {a}"
              pure false
          else do
            IO.eprintln s!"FAIL: {name}: driver errors diverge: {a} vs {b}"
            pure false
      | _, _ => do
          IO.eprintln s!"FAIL: {name}: expected both drivers to refuse the wrong-arity call"
          pure false
    let r₁ ← check
      "GoCore drivers agree on wrong-arity refusal before the init phase (panicking init — the discriminating shape)"
      enumInitPanicProgram
    let r₂ ← check
      "GoCore drivers agree on wrong-arity refusal before the init phase (succeeding init)"
      enumInitPickProgram
    pure (r₁ && r₂))
  -- F15 (spec-parity s1): the observation channel carries the integer
  -- KIND. The distinguishing pin is the BUG-042 family's exact hidden
  -- shape — same numeric value, different kind — which the value-only
  -- channel rendered IDENTICAL (this assertion is red against the old
  -- encoder; verified red-first before the encoder change landed).
  passed := passed && (← expectTrue "F15: observation channel distinguishes right-value wrong-kind (red under the value-only channel)"
    (CLI.observationOfRun (.ok { values := #[.int 6 .int] })
      != CLI.observationOfRun (.ok { values := #[.int 6 .uint8] })))
  -- The wire shape itself, pinned verbatim (both encoders must emit it).
  passed := passed && (← expectStrEq "F15: kind-carrying int observation shape"
    (CLI.observationOfRun (.ok { values := #[.int 6 .uint8] })).compress
    "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"kind\":\"uint8\",\"tag\":\"int\",\"value\":6}]}")
  -- Fail-closed decode discipline for the new fields (the float arm's
  -- mold): unknown kinds — including uintptr, which the frontend maps
  -- to uint64 so the machine can never answer it — and out-of-range
  -- values refuse; the machine encoder's own output round-trips.
  passed := passed && (← expectTrue "F15: decode accepts the machine encoder's kind-carrying output"
    (CLI.decodeObservation "left"
      (CLI.observationOfRun (.ok { values := #[.int (-5) .int8, .int 255 .uint8] })).compress).isOk)
  passed := passed && (← expectTrue "F15: decode refuses an unknown integer kind (uintptr)"
    !(CLI.decodeObservation "left"
      "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"kind\":\"uintptr\",\"value\":1}]}").isOk)
  passed := passed && (← expectTrue "F15: decode refuses a kindless int observation (the retired shape)"
    !(CLI.decodeObservation "left"
      "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":1}]}").isOk)
  passed := passed && (← expectTrue "F15: decode refuses an out-of-range unsigned value (256 at uint8)"
    !(CLI.decodeObservation "left"
      "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"kind\":\"uint8\",\"value\":256}]}").isOk)
  passed := passed && (← expectTrue "F15: decode refuses a negative value at an unsigned kind"
    !(CLI.decodeObservation "left"
      "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"kind\":\"uint64\",\"value\":-1}]}").isOk)
  passed := passed && (← expectTrue "F15: decode refuses an out-of-range signed value (128 at int8)"
    !(CLI.decodeObservation "left"
      "{\"output\":\"\",\"schema\":\"golean-observation-v1\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"kind\":\"int8\",\"value\":128}]}").isOk)
  -- MS: the method-set record contract's WIRE-BOUNDARY pins (class
  -- closure of BUG-053, docs/2026-08-10_method-set-record-contract.md
  -- §3 item 3): hand-crafted wires with a method-CARRYING type whose
  -- record is deliberately absent must REFUSE satisfaction — never
  -- answer, never stuck — and the same wire WITH the record answers
  -- the definite no (the refusal is the record's absence, nothing
  -- else). These are the pins that make a re-introduction of the
  -- class visible forever.
  passed := passed && (← expectTrue "MS: decode refuses a wire without methodSets (required field)"
    (match Lean.Json.parse "{\"schema\":\"golean-native-v1\",\"funcs\":[],\"types\":[],\"methods\":[]}" with
     | .error _ => false
     | .ok j => !(GoLean.NativeToIR.decodeProgram j).isOk))
  -- Row M (memo §3; lane fr4-rowm audit fix round A3): the `sort-slice`
  -- wire node is no longer decoded — the frontend never emits it, and a
  -- hand-edited wire must be REFUSED by name rather than run the retired
  -- one-step insertion sort (a different member than the real pdqsort the
  -- frontend now emits). A `clear-slice` of the same shape still decodes,
  -- so the refusal is the node's, not the shape's.
  let sortSliceWire (tag : String) : String :=
    "{\"schema\":\"golean-native-v1\",\"types\":[],\"methods\":[],\"methodSets\":[],\"globals\":[],\"funcs\":[{\"name\":\"f\",\"params\":[],\"results\":[],\"variadic\":false,\"body\":{\"stmt\":\"block\",\"body\":[{\"stmt\":\"" ++ tag ++ "\",\"base\":{\"expr\":\"nil\"},\"elem\":{\"kind\":\"int\",\"int\":\"int\"}}]}}]}"
  passed := passed && (← expectTrue "row M: decode refuses the retired sort-slice statement by name"
    (match Lean.Json.parse (sortSliceWire "sort-slice") with
     | .error _ => false
     | .ok j => match GoLean.NativeToIR.decodeProgram j with
       | .ok _ => false
       | .error e => (e.splitOn "unsupported statement sort-slice").length > 1))
  passed := passed && (← expectTrue "row M: the same wire shape as clear-slice still decodes (the refusal is the node's, not the shape's)"
    (match Lean.Json.parse (sortSliceWire "clear-slice") with
     | .error _ => false
     | .ok j => (GoLean.NativeToIR.decodeProgram j).isOk))
  passed := passed && (← expectTrue "MS: decode refuses an unknown coverage token"
    (match Lean.Json.parse "{\"schema\":\"golean-native-v1\",\"funcs\":[],\"types\":[],\"methods\":[],\"methodSets\":[{\"type\":\"main.T\",\"coverage\":\"partial\"}]}" with
     | .error _ => false
     | .ok j => !(GoLean.NativeToIR.decodeProgram j).isOk))
  passed := passed && (← expectTrue "MS: decode refuses a duplicate method-set record"
    (match Lean.Json.parse "{\"schema\":\"golean-native-v1\",\"funcs\":[],\"types\":[],\"methods\":[],\"methodSets\":[{\"type\":\"main.T\",\"coverage\":\"full\"},{\"type\":\"main.T\",\"coverage\":\"full\"}]}" with
     | .error _ => false
     | .ok j => !(GoLean.NativeToIR.decodeProgram j).isOk))
  -- WIRE-CORRUPTION backstops in decodeReturn / decodeTy (audit fix
  -- round 2026-09-01). BLOCKER 1: the BUG-075 slice's n=1 return fast
  -- path ran BEFORE the arity check, so a one-operand `return` at a
  -- TWO-result function decoded (result 1 silently zero-filled: the
  -- auditor's hand-patched wire — a 2-result function's return with
  -- one operand removed — answered 70 where 79 was owed, and main
  -- refused "return arity 1 does not match 2 results"). The decoder
  -- must refuse BY NAME; the message pin is the arity text itself.
  let retWire (results : String) : String :=
    "{\"schema\":\"golean-native-v1\",\"types\":[],\"methods\":[],\"methodSets\":[]," ++
    "\"funcs\":[{\"name\":\"pair\",\"params\":[],\"variadic\":false," ++
    "\"results\":[{\"id\":\"$res0\",\"type\":{\"kind\":\"int\",\"int\":\"int\"}},{\"id\":\"$res1\",\"type\":{\"kind\":\"int\",\"int\":\"int\"}}]," ++
    "\"body\":{\"stmt\":\"block\",\"body\":[{\"stmt\":\"return\",\"results\":[" ++ results ++ "]}]}}]}"
  let intLit (v : String) : String := "{\"expr\":\"int\",\"value\":\"" ++ v ++ "\",\"type\":{\"kind\":\"int\",\"int\":\"int\"}}"
  let decodeMsg (wire : String) : Except String Unit :=
    match Lean.Json.parse wire with
    | .error e => .error s!"json parse failed: {e}"
    | .ok j => (GoLean.NativeToIR.decodeProgram j).map (fun _ => ())
  passed := passed && (← expectTrue "RET: decode accepts a two-operand return at a two-result function (control)"
    (decodeMsg (retWire (intLit "7" ++ "," ++ intLit "9"))).isOk)
  passed := passed && (← expectTrue "RET: decode REFUSES a one-operand return at a two-result function, naming the arity (BLOCKER 1 — the n=1 fast path must not bypass the arity check)"
    (match decodeMsg (retWire (intLit "7")) with
     | .error msg => (msg.splitOn "return arity 1 does not match 2 results").length > 1
     | .ok _ => false))
  passed := passed && (← expectTrue "RET: decode REFUSES a three-operand return at a two-result function, naming the arity"
    (match decodeMsg (retWire (intLit "7" ++ "," ++ intLit "9" ++ "," ++ intLit "11")) with
     | .error msg => (msg.splitOn "return arity 3 does not match 2 results").length > 1
     | .ok _ => false))
  -- BUG-078: the array-type materialization budget refuses BY NAME at
  -- decode, one past the budget; at the budget it decodes. The wire
  -- carries only the TYPE (a global of that type), so the pin is on
  -- the decoder's bound, not on any materialization.
  let arrWire (len : Nat) : String :=
    "{\"schema\":\"golean-native-v1\",\"funcs\":[],\"types\":[],\"methods\":[],\"methodSets\":[]," ++
    "\"globals\":[{\"name\":\"main.big\",\"type\":{\"kind\":\"array\",\"len\":" ++ toString len ++ ",\"elem\":{\"kind\":\"int\",\"int\":\"uint8\"}}}]}"
  passed := passed && (← expectTrue "BUG-078: decode admits an array type AT the materialization budget"
    (decodeMsg (arrWire GoLean.NativeToIR.arrayLenBudget)).isOk)
  passed := passed && (← expectTrue "BUG-078: decode REFUSES an array type one past the materialization budget, naming the budget and the entry"
    (match decodeMsg (arrWire (GoLean.NativeToIR.arrayLenBudget + 1)) with
     | .error msg => (msg.splitOn "materialization budget").length > 1 && (msg.splitOn "BUG-078").length > 1
     | .ok _ => false))
  -- The class pin proper: main.T has a TypeDef on the wire (the OLD
  -- guard's presence key) but NO method-set record — satisfaction must
  -- refuse `unsupported`, proving the guard keys on the RECORD.
  let msWire (records : String) : String :=
    "{\"schema\":\"golean-native-v1\",\"funcs\":[],\"methods\":[]," ++
    "\"types\":[{\"name\":\"main.T\",\"def\":{\"kind\":\"defined\",\"target\":{\"kind\":\"int\",\"int\":\"int\"}}}," ++
    "{\"name\":\"main.locker\",\"def\":{\"kind\":\"interface\",\"methods\":[{\"name\":\"Lock\",\"params\":[],\"results\":[],\"variadic\":false}]}}]," ++
    "\"methodSets\":[" ++ records ++ "]}"
  let msQuery (records : String) : Except String (Except Stop Bool) :=
    match Lean.Json.parse (msWire records) with
    | .error e => .error e
    | .ok j =>
        match GoLean.NativeToIR.decodeProgram j with
        | .error e => .error e
        | .ok prog =>
            let state : GoCore.ExecState :=
              { types := prog.typeDefs.toList, functions := prog.funcs
                methods := prog.methods, methodSets := prog.methodSets }
            .ok (GoCore.dynamicImplementsInterface state
              (.defined ⟨"main.T"⟩) ⟨"main.locker"⟩)
  passed := passed && (← expectTrue "MS: satisfaction REFUSES a method-carrying type with no record (BUG-053 class pin; TypeDef present, record absent)"
    (match msQuery "" with
     | .ok (.error err) => err.status == "unsupported"
     | _ => false))
  passed := passed && (← expectTrue "MS: the same wire WITH the record answers the definite no (mutation sensitivity)"
    (match msQuery "{\"type\":\"main.T\",\"coverage\":\"full\"}" with
     | .ok (.ok b) => b == false
     | _ => false))
  -- The `.sync` carrier arm (the re-introduction pin): a sync box in a
  -- state with NO records refuses; with the exported record and the
  -- declaration-only stub it answers true — exactly the BUG-053
  -- polarity, now enforced for every carrier kind by one guard.
  let syncLockerTypes : GoCore.TypeEnv :=
    [(⟨"main.locker"⟩, .interfaceDef #[{ name := "Lock", params := #[], results := #[] }])]
  let syncStubFunc : GoCore.Func :=
    { id := ⟨"sync.Mutex.Lock"⟩,
      args := #[{ id := "$recv", typ := .pointer (.sync .mutex) }],
      results := #[],
      body := .unsupported "test stub" }
  let syncNoRecord : GoCore.ExecState := { types := syncLockerTypes }
  let syncWithRecord : GoCore.ExecState :=
    { types := syncLockerTypes,
      functions := #[syncStubFunc],
      methods := #[{ name := "Lock", funcId := ⟨"sync.Mutex.Lock"⟩,
                     recv := .pointer (.sync .mutex) }],
      methodSets := #[{ key := "sync.Mutex", coverage := .exported }] }
  passed := passed && (← expectTrue "MS: a sync carrier without a record refuses (re-introduction pin)"
    (match GoCore.dynamicImplementsInterface syncNoRecord
        (.pointer (.sync .mutex)) ⟨"main.locker"⟩ with
     | .error err => err.status == "unsupported"
     | .ok _ => false))
  passed := passed && (← expectTrue "MS: a sync carrier WITH the exported record and stub answers true"
    (match GoCore.dynamicImplementsInterface syncWithRecord
        (.pointer (.sync .mutex)) ⟨"main.locker"⟩ with
     | .ok b => b == true
     | .error _ => false))
  -- The DISPATCH half and RENDERER half of the record contract (S6
  -- audit fix: contract note §3 item 2 / §4 renderer bullet shipped
  -- these two consumer arms with NO pin — a revert of either would
  -- have passed every gate silently, since no corpus id and no MS pin
  -- above exercises them). State: an interface requirement
  -- (main.speaker/Speak, interface-receiver MethodInfo) and a defined
  -- carrier main.T with NO concrete Speak — the no-method arm.
  let dispTypes : GoCore.TypeEnv :=
    [(⟨"main.speaker"⟩, .interfaceDef #[{ name := "Speak", params := #[], results := #[] }]),
     (⟨"main.T"⟩, .defined (.int .int))]
  let speakIfaceFunc : GoCore.Func :=
    { id := ⟨"main.speaker.Speak"⟩,
      args := #[{ id := "$recv", typ := .interface ⟨"main.speaker"⟩ }],
      results := #[],
      body := .unsupported "test iface requirement stub" }
  let dispBox : GoValue := .interface (.defined ⟨"main.T"⟩) (.int 7 .int)
  let dispNoRecord : GoCore.ExecState :=
    { types := dispTypes,
      functions := #[speakIfaceFunc],
      methods := #[{ name := "Speak", funcId := ⟨"main.speaker.Speak"⟩,
                     recv := .interface ⟨"main.speaker"⟩ }] }
  let dispWithRecord : GoCore.ExecState :=
    { dispNoRecord with
      methodSets := #[{ key := "main.T", coverage := .full }] }
  passed := passed && (← expectTrue "MS: dispatch on a carrier with NO record refuses unsupported (dispatch-half pin — never an answer from absence)"
    (match GoCore.dynamicDispatch? dispNoRecord speakIfaceFunc #[dispBox] with
     | .error err => err.status == "unsupported"
     | .ok _ => false))
  passed := passed && (← expectTrue "MS: the same dispatch WITH the record fails stuck (the invariant-break arm; mutation sensitivity — the refusal above is the record's absence, nothing else)"
    (match GoCore.dynamicDispatch? dispWithRecord speakIfaceFunc #[dispBox] with
     | .error err => err.status == "stuck"
     | .ok _ => false))
  passed := passed && (← expectTrue "MS: renderPanicPayload on a defined carrier with NO record is unrenderable (renderer-half pin — never a fabricated main.T(v))"
    (GoCore.Machine.renderPanicPayload dispNoRecord dispBox).isNone)
  passed := passed && (← expectTrue "MS: the same payload WITH the record renders main.T(7) (mutation sensitivity)"
    (GoCore.Machine.renderPanicPayload dispWithRecord dispBox == some "main.T(7)"))
  -- THE DEDUP CERTIFIER'S REFUSALS (POR slice, audit fix 2026-08-21,
  -- finding B-LOW): the slice landed `checkCert` with its fail-closed
  -- behavior demonstrated ONCE, by hand, in a session probe — no
  -- standing test. A certificate the checker wrongly ACCEPTS is the
  -- whole trust surface of every `engine=dedup` row (the accepted
  -- certificate's member set is what `checkCertM_slowObs` then says is
  -- EQUAL to `SlowObs`), so the mutation refusals get a regression test
  -- of their own here. Fixture: the smallest real pool that closes — a
  -- 2-thread pool of default-taking selects, whose state graph is 13
  -- nodes with a single member. The engine is the UNTRUSTED side and is
  -- used only to MANUFACTURE the certificate; every assertion below is
  -- about the checker.
  let selCfg : GoCore.Machine.Config :=
    .exec (.selectStmt #[] (some (.seqn #[]))) [] .stop
  let dedupM0 : GoCore.Machine.MultiConfig := ⟨#[selCfg, selCfg], {}, 0⟩
  let dedupR0 : GoCore.Machine.RaceState := {}
  match GoLean.EnumDedup.buildCert [] dedupM0 dedupR0 100000 with
  | .error e =>
      passed := passed && (← expectTrue s!"DEDUP: engine builds the fixture certificate (got error: {e})" false)
  | .ok (cert, _) =>
    let accepts (c : GoCore.Machine.DedupCert) : Bool :=
      GoCore.Machine.checkCert GoCore.Machine.dedupNodeEqb [] dedupM0 dedupR0 c
    -- The positive control. Without it the four refusals below could all
    -- be a checker that refuses everything.
    passed := passed && (← expectTrue "DEDUP: the UNMUTATED certificate is ACCEPTED (13 nodes, 1 member — the positive control the refusals are measured against)"
      (cert.nodes.size == 13 && cert.members.size == 1 && accepts cert))
    -- M1: drop a member. Completeness direction — the graph still
    -- reaches an observation the member list no longer claims.
    passed := passed && (← expectTrue "DEDUP: M1 dropped member REFUSED (a reachable observation missing from the claimed set)"
      (!accepts { cert with members := cert.members.pop }))
    -- M2: redirect every successor hint to node 0. The checker re-runs
    -- the REAL stepMulti per edge and compares against the hint, so a
    -- lying hint cannot smuggle in a smaller graph.
    passed := passed && (← expectTrue "DEDUP: M2 successor hints all redirected to node 0 REFUSED (hints are re-derived, never trusted)"
      (!accepts { cert with succ := cert.succ.map (fun a => a.map (fun _ => 0)) }))
    -- M3: drop the last node. The graph is no longer closed under the
    -- real step relation.
    passed := passed && (← expectTrue "DEDUP: M3 dropped node REFUSED (the state graph is no longer closed under stepMulti)"
      (!accepts { cert with nodes := cert.nodes.pop }))
    -- M5: fabricate a member with a bogus witness. Soundness direction —
    -- the witness replay through the unmodified execProgLoop is what
    -- makes a claimed member earn its place.
    passed := passed && (← expectTrue "DEDUP: M5 fabricated member REFUSED (its witness does not replay to that observation)"
      (!accepts { cert with members := cert.members.push (.terminal (.panic "fabricated"), [], 10) }))
    -- F5 (wave-(iii) audit fix): the emit-site vocabulary guard refuses a
    -- FAKED fatal / deadlock member by name and passes the lanes' three.
    passed := passed && (← expectTrue "F5: a fatal member is refused by name at the emit site"
      (CLI.memberVocabularyRefusal? (.terminal (.fatal "sync: unlock of unlocked mutex"))).isSome)
    passed := passed && (← expectTrue "F5: a deadlock member is refused by name at the emit site"
      (CLI.memberVocabularyRefusal? (.terminal .deadlock)).isSome)
    passed := passed && (← expectTrue "F5: ok / panic / race members pass the vocabulary guard"
      ((CLI.memberVocabularyRefusal? (.ok [])).isNone
        && (CLI.memberVocabularyRefusal? (.terminal (.panic "x"))).isNone
        && (CLI.memberVocabularyRefusal? (.terminal .raceDetected)).isNone))
  if passed then
    return 0
  else
    return 1

end Tests.GoCoreEval

def main : IO UInt32 :=
  Tests.GoCoreEval.main
