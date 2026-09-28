<!-- VERBATIM COPY for GoLean's records. Source: golean-logic, branch docs/golean-note-0928, commit c01bf0d, file docs/2026-09-28_note-to-golean.md, sha256 89e9969c03aa50388db0cedc88980f29c549acbd2217623d096c718e9df07533. Relayed by the [USER] 2026-09-28; copied unchanged by the [AGENT] coordinator. -->

# Logic team's note to GoLean: window feedback — 2026-09-28

To the GoLean semantics team. **[USER]** Requested a combined feedback note
for the user to relay. **[AGENT]** Drafted from our
[migration readiness](2026-09-28_migration-readiness.md) (§5) and
[failure/prefix design](2026-09-28_failure-prefix-design.md) (§6), both
independently reviewed. We read GoLean main at `89792db1`. Our pin is still
`61958f2e`. Nothing here changes our answer to question 10, which we relayed
on 2026-09-28.

## Acknowledgements

- The landed statements (BridgeSet rows 35–64) cover our 09-23 requests:
  retained failure state, terminal consultation and fuel accounting,
  arbitrary prefixes, replay by record and refusal-separate
  classification. We have not yet checked them by building against them.
- The G-P design note meets our method conditions. In particular,
  `methodInfoByFuncId?` is unchanged, and `enterFrame_declared` gives the
  declared-callee entry our first receiver proof needs.
- `StringPanic.lean` already provides what we need for rendering a single
  string panic. The legacy triple and `os.Exit` ("refused by name") are
  both settled, and we plan around them.

## Requests

1. **Equations that reach the memory laws (packet D).** Our step
   discharges unfold helpers such as `deliverS`, `applyStrictOp`,
   `storeTarget`, `stepFrameExit`, `bindParams` and `allocDecls`. Please let
   the arm equations' premises bottom out in `loadLoc`/`loadRoot`/
   `storeLoc`/`Store.alloc` laws. One filing correction: the brief lists
   `callArgsK`, `callValCalleeK`, `callValArgsK`, `deferCalleeK` and
   `deferArgsK` under `.next`, but on main they are `.retV v` arms
   (`StepFn.lean:617ff`). `stmtOpK` is also not marked as a `.retV` arm.
2. **A pinned setup equation.** `program_bridge` assumes setup succeeded.
   Our closed theorems prove setup by unfolding `runProgramSetupM`, which
   has to be repaired at every re-pin. An equation for the case with no
   globals and no package initializer would remove that repair. It should
   give the entry configuration, the argument and result layout, and the
   remaining choice tape.
3. **The B6 name table as a Lean interface.** Please provide its Lean type
   and lemmas for three things: that table lookup agrees with the
   activation's runtime slot; that source spellings are retained; and
   whether `Param.id`/`Expr.var` become numeric. Please pin these in
   BridgeSet.
4. **C4 as a stated layout function.** When the C4 brief is written,
   please give the address shift for frame entry and block entry as a
   function, not only in prose. Please also provide lifetime lemmas for
   escaped result cells, shadowing, per-activation cells, and captured
   variables versus saved defer arguments.
5. **Pin the P entry equations.** Please add `enterFrame_declared`,
   `receiverAt_nil_path` and `resolveMethod?_declared` to BridgeSet. Please
   also confirm that narrowing `findFunctionIn?`'s domain leaves results
   for declared non-wrapper functions unchanged; four of our consumer
   theorems carry it as a premise.
6. **Callee identity at frame exit.** Please expose which function a
   frame belongs to when it exits, as either a frame field or a
   call/return channel in `StepLabel`. That would let a client observe
   "`f` returned `v`" as a per-step function of the execution. Our
   observation design only needs call entry for its first stage; later
   stages need this.
7. **Stable unwinding equations.** In the BridgeSet style, please provide
   equations for: `panicPassthrough` over sequence and block glue;
   `panicResumeK` resuming with an unrecovered chain; `CallSite.deferPanic`
   entry; and stripping a frame with an empty defer list. These are the
   steps our panic-with-cleanup rules unfold.
8. **Changelog scope.** Please also list changes to the tool interfaces
   our gate calls: `tools/nativefrontend` flags, the `scripts/diff-coverage`
   manifest schema, `NativeToIR.decodeProgram`'s signature, `runProgramM`'s
   `RunResult`, the Lean toolchain and the `deps/go` pin.
9. **Reminder (low priority).** The already-owed single-goroutine embedding
   without the `seqOpCount = 0` premise (your proposal, line 203) would
   remove a premise from our readout. It matters only once we use the pool
   driver.

## For information

We will handle the sequential panic bridge ourselves, by composing
`run_panic_iff` with our setup lemma. The sequential-to-pool terminal
projection matters to us only if we move to the pool driver.

We have landed multi-field records and UInt64 support at our current pin.
Our unfolding of `StructFields` is confined to one module. The repair
after your `storeLoc` rewrite (`d7b32f59`, `6a35dd92`) is limited to that
module and a few named cell lemmas.
