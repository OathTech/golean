import GoLean.GoCore.Machine
import GoLean.GoCore.StateWf

/-!
# The executable step function (reshape R2, S2c)

`stepFn` is the machine's instantiation: one arm per `Machine.Step` rule,
sharing the rule premises' functions verbatim (`strictPlan`,
`applyStrictOp`, `stmtPlan`, `applyStmtOp`, `enterFrame`, …), plus the
*why* on every configuration the relation is silent on — an explicit
`.stuck`/`.unsupported`/`.internal` error, never a silent approximation
(fail closed). Panics are in-model: a panic *step* produces a
`.panicking` configuration (`.ok`) that unwinds — running defers, open to
`recover` — and an unrecovered chain reaching `.stop` becomes `.panicked`,
which the driver reports as `GoError.panic`; only out-of-model conditions
are `Except` errors.

Nondeterminism: the two choice points (mapRange pick-next, appendSlice
spill capacity) consume from the external `Choices` stream, exactly as
the big-step interpreter did — the relation's corresponding rules
quantify over the choice.

Execution is fuel-bounded iteration (`runConfig`); fuel counts machine
steps (design note §5 — the CLI default retunes at S3). The function
driver `runFunctionWithContextM` mirrors the big-step entry point: bind
arguments, allocate results, pin their locations, run the body inside a
targetless `frame`, and read the pinned result locations at the terminal
configuration. The PROGRAM driver `runProgramM` (init slice) composes
global seeding and the `$pkginit` phase in front of the same wiring —
it is the only Program-level entry (the non-seeding
`runNamedFunctionM` pair was deleted, delta-review N4 2026-08-05).
Everything uses the machine's env-in-config representation throughout —
`ExecState.locals` is never touched (it is deleted at S4).

Per-rule soundness/completeness lemmas against `Machine.Step` land at S5.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- Ordinary call-frame entry with the frame-entry panic rule folded in
(2026-08-05, slice-2 stage 5): a `.panic` raised inside `enterFrame`
(dynamic dispatch on a nil interface; the auto-deref of a nil pointer
box) is an ordinary RECOVERABLE panic in Go, so it steps to `.panicking`
under the caller's continuation `k` — pinned by
`interfaces/recover-nil-dispatch/*`. Kept as ONE helper so each stepFn
call site remains a single `fun_cases` branch (the correspondence
proofs' case numbering is positional). The NORMAL-drain deferred-call
entries reuse it too (audit F1+F5, 2026-08-05: the entry panic is the
deferred invocation's panic and starts unwinding at the draining frame
— pass `k := .frame targets results ds k'`); the PANIC-PATH drain uses
`enterFrameDeferPanicking` below (chain join). -/
def enterFrameStep (s : ExecState) (fid : FuncId) (args : List GoValue)
    (mk : Func → LocalEnv → List Loc → Config) (k : Cont)
    (choices : Choices) : Except GoError (Config × ExecState × Choices) :=
  match enterFrame s fid args with
  | .ok (func, frameEnv, resultLocs, s') => .ok (mk func frameEnv resultLocs, s', choices)
  | .error (.panic msg) => .ok (.panicking [⟨runtimeErrorValue msg, false⟩] k, s, choices)
  | .error err => .error err

/-- DEFERRED-call frame entry ON THE PANIC PATH (audit F1+F5,
2026-08-05): an entry panic is the deferred INVOCATION's panic and JOINS
the suspended chain newest-last, exactly like the `.nil`-callee drain arm
below — remaining defers keep draining and `recover` answers the newest
entry. One helper so the stepFn site stays a single `fun_cases` branch.
The two NORMAL drain sites reuse `enterFrameStep` (no chain in flight —
their panic starts unwinding at this frame with its remaining defers). -/
def enterFrameDeferPanicking (s : ExecState) (fid : FuncId) (args : List GoValue)
    (mk : Func → LocalEnv → Config) (chain : List PanicEntry) (krest : Cont)
    (choices : Choices) : Except GoError (Config × ExecState × Choices) :=
  match enterFrame s fid args with
  | .ok (func, frameEnv, _resultLocs, s') => .ok (mk func frameEnv, s', choices)
  | .error (.panic msg) =>
      .ok (.panicking (chain ++ [⟨runtimeErrorValue msg, false⟩]) krest, s, choices)
  | .error err => .error err

/-- One machine step. `.ok` is a step the relation permits (including
steps *to* `.panicked`); `.error` means the machine is stuck here, with
the reason. Never call on a terminal configuration (the driver guards). -/
def stepFn (s : ExecState) (c : Config) (choices : Choices) :
    Except GoError (Config × ExecState × Choices) := do
  match c with
  | .panicked _ => throw (.internal "step on terminal panicked configuration")
  | .panicking chain k =>
      match k with
      | .frame _targets _results [] k' _ => return (.panicking chain k', s, choices)
      | .frame targets results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured =>
              -- Defers run on the panic path, above the suspended chain's
              -- marker (the shape `recover`'s walk detects). An ENTRY
              -- panic joins the chain (audit F1+F5). The deferred
              -- callee's frame carries ITS wrapper flag (BUG-015).
              enterFrameDeferPanicking s fid (captured ++ args)
                (fun func frameEnv =>
                  .exec func.body frameEnv
                    (.frame [] [] [] (.panicResumeK chain
                      (.frame targets results ds k' w)) func.wrapper))
                chain (.frame targets results ds k' w) choices
          | .nil =>
              -- The nil invocation's panic joins the chain; remaining
              -- defers keep draining.
              return (.panicking (chain ++ [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩])
                (.frame targets results ds k' w), s, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .panicResumeK suspended k' =>
          return (.panicking (suspended ++ chain) k', s, choices)
      | .stop =>
          match chain with
          | first :: rest =>
              match renderPanicHead s first rest with
              | some msg => return (.panicked msg, s, choices)
              | none => throw (.unsupported
                  s!"panic abort rendering for payload {repr first.value}")
          | [] => throw (.internal "empty panic chain at stop")
      | k =>
          match panicPassthrough k with
          | some k' => return (.panicking chain k', s, choices)
          | none => throw (.internal "unclassified continuation in panic unwinding")
  | .exec stmt env k =>
      match stmt with
      | .seqn ss => return (.next (seqCont ss.toList env k), s, choices)
      | .block decls ss => do
          let (env', s') ← allocDecls env.pushScope s decls.toList
          return (.next (.seq ss.toList env' k), s', choices)
      | .initialization p =>
          match k with
          | .seq rest kenv k' =>
              if kenv = env then do
                let v ← defaultValue s p.typ
                let (loc, s') := s.alloc v (some p.typ)
                return (.next (.seq rest (env.declare p.id loc) k'), s', choices)
              else throw (.internal "initialization under foreign-scope sequence")
          | _ => throw (.stuck "GoCore initialization outside a statement sequence")
      | .assign lhs rhs =>
          match assigneeExpr lhs with
          | some te => return (.evalE te env (.assignTargetK rhs env k), s, choices)
          | none =>
              match lhs with
              | .unsupported feature => throw (.unsupported feature)
              | _ => throw (.internal "unclassified assignee")
      | .ifThenElse c t e => return (.evalE c env (.ifK t e env k), s, choices)
      | .while c b => return (.evalE c env (.whileK c b env k), s, choices)
      | .returnStmt => return (.returning k, s, choices)
      | .breakStmt => return (.breaking k, s, choices)
      | .continueStmt => return (.continuing k, s, choices)
      | .label _ => return (.next k, s, choices)
      | .labeled name b => return (.exec b env (.labelK name k), s, choices)
      | .breakTo name => return (.breakingTo name k, s, choices)
      | .continueTo name => return (.continuingTo name k, s, choices)
      | .breakable b => return (.exec b env (.breakableK k), s, choices)
      | .deferCall callee args =>
          return (.evalE callee env (.deferCalleeK args.toList env k), s, choices)
      | .panicStmt e =>
          return (.evalE e env (.panicArgK k), s, choices)
      | .callValue targets callee args =>
          match assigneesExprs targets.toList with
          | some (te :: rest) =>
              return (.evalE te env (.callValTargetsK callee [] rest args.toList env k), s, choices)
          | some [] =>
              return (.evalE callee env (.callValCalleeK [] args.toList env k), s, choices)
          | none => throw (.unsupported "unsupported value-call target assignee")
      | .call targets fid args =>
          match assigneesExprs targets.toList with
          | some (te :: rest) =>
              return (.evalE te env (.callTargetsK fid [] rest args.toList env k), s, choices)
          | some [] =>
              match args.toList with
              | a :: rest =>
                  return (.evalE a env (.callArgsK fid [] [] rest env k), s, choices)
              | [] =>
                  enterFrameStep s fid []
                    (fun func frameEnv resultLocs =>
                      .exec func.body frameEnv (.frame [] resultLocs [] k func.wrapper)) k choices
          | none => throw (.unsupported "unsupported call target assignee")
      | .mapRange keyVar valVar mapExpr keyTy valTy body =>
          return (.evalE mapExpr env
            (.mapRangeK keyVar valVar keyTy valTy body env k), s, choices)
      -- Channel statements (channels arc slice 1): operand-plan entry
      -- mirroring the wide-statement arm; the plans always carry ≥ 1
      -- operand (send: channel; recv: targets then channel; close:
      -- channel), so there is no nullary case.
      | .chanSend ch value elem =>
          return (.evalE ch env (.chanStK (.send elem) [] [value] env k), s, choices)
      | .closeChan ch =>
          return (.evalE ch env (.chanStK .close [] [] env k), s, choices)
      | .chanRecv targets ch elem =>
          -- Named scrutinee on purpose: the equation is what the
          -- correspondence proofs' `fun_cases` branches rewrite with.
          match _hplan : chanPlan (.chanRecv targets ch elem) with
          | some (op, e :: rest) =>
              return (.evalE e env (.chanStK op [] rest env k), s, choices)
          | some (_, []) => throw (.internal "empty channel-receive operand plan")
          | none =>
              if targets.size > 2 then
                throw (.stuck s!"channel receive with {targets.size} targets")
              else
                throw (.unsupported "unsupported channel-receive target assignee")
      | .selectStmt clauses default? =>
          match selectOperands clauses.toList with
          | e :: rest =>
              return (.evalE e env
                (.selectOpsK clauses.toList default? [] rest env k), s, choices)
          | [] =>
              -- No communication clauses: `default` runs immediately;
              -- otherwise `select {}` blocks forever (spec).
              match default? with
              | some d => return (.exec d env k, s, choices)
              | none => return (.blockedSelect [] env k, s, choices)
      | .unsupported feature => throw (.unsupported feature)
      | wide =>
          -- assignMany / newValue / makeSlice / makeMap / mapAssign /
          -- mapLookup / typeAssert / appendSlice / copySlice
          match stmtPlan wide with
          | some (op, nt, e :: rest) =>
              return (.evalE e env (.stmtOpK op nt [] rest env k), s, choices)
          | some (op, nt, []) => do
              let (s', choices') ← applyStmtOp s choices op nt []
              return (.next k, s', choices')
          | none =>
              match wide with
              | .assignMany left right =>
                  if left.size != right.size then
                    throw (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}")
                  else throw (.unsupported "unsupported multi-assignment target assignee")
              | _ => throw (.unsupported "unsupported statement target assignee")
  | .evalE e env k =>
      match e with
      | .var id =>
          match LocalEnv.lookup env id with
          | some loc => do return (.retV (← loadLoc s loc) k, s, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .intLit value kind =>
          return (.retV (.int (kind.normalize value) kind) k, s, choices)
      | .boolLit value => return (.retV (.bool value) k, s, choices)
      | .stringLit value => return (.retV (.string value) k, s, choices)
      | .ref id =>
          match LocalEnv.lookup env id with
          | some loc => return (.retV (.addr loc) k, s, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .locLit l => return (.retV (.addr l) k, s, choices)
      | .and l r => return (.evalE l env (.andK r env k), s, choices)
      | .or l r => return (.evalE l env (.orK r env k), s, choices)
      | .recoverCall =>
          let (v, k') := recoverResult k
          return (.retV v k', s, choices)
      | .unsupported feature => throw (.unsupported feature)
      | e =>
          match strictPlan e with
          | some (op, e₁ :: rest) =>
              return (.evalE e₁ env (.strictK op [] rest env k), s, choices)
          | some (op, []) =>
              match applyStrictOp s op [] with
              | .ok (v, s') => return (.retV v k, s', choices)
              | .error (.panic msg) =>
                  return (.panicking [⟨runtimeErrorValue msg, false⟩] k, s, choices)
              | .error err => throw err
          | none => throw (.internal "unclassified expression")
  | .retV v k =>
      match k with
      | .strictK op done (e :: rest) env k' =>
          return (.evalE e env (.strictK op (v :: done) rest env k'), s, choices)
      | .strictK op done [] _ k' =>
          match applyStrictOp s op (v :: done).reverse with
          | .ok (out, s') => return (.retV out k', s', choices)
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
      | .andK r env k' => do
          if ← valueAsBool v then
            return (.evalE r env (.boolK k'), s, choices)
          else
            return (.retV (.bool false) k', s, choices)
      | .orK r env k' => do
          if ← valueAsBool v then
            return (.retV (.bool true) k', s, choices)
          else
            return (.evalE r env (.boolK k'), s, choices)
      | .boolK k' => do return (.retV (.bool (← valueAsBool v)) k', s, choices)
      | .ifK t e env k' => do
          if ← valueAsBool v then
            return (.exec t env k', s, choices)
          else
            return (.exec e env k', s, choices)
      | .whileK c b env k' => do
          if ← valueAsBool v then
            return (.exec b env (.loop c b env k'), s, choices)
          else
            return (.next k', s, choices)
      | .assignTargetK rhs env k' =>
          match valueAsLoc v with
          | .ok loc => return (.evalE rhs env (.assignStoreK loc k'), s, choices)
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
      | .assignStoreK loc k' =>
          match storeLoc s loc v with
          | .ok s' => return (.next k', s', choices)
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
      | .callTargetsK fid locs pending args env k' =>
          match valueAsLoc v with
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
          | .ok loc =>
              match pending with
              | te :: rest =>
                  return (.evalE te env
                    (.callTargetsK fid (locs ++ [loc]) rest args env k'), s, choices)
              | [] =>
                  match args with
                  | a :: rest =>
                      return (.evalE a env
                        (.callArgsK fid (locs ++ [loc]) [] rest env k'), s, choices)
                  | [] =>
                      enterFrameStep s fid []
                        (fun func frameEnv resultLocs =>
                          .exec func.body frameEnv
                            (.frame (locs ++ [loc]) resultLocs [] k' func.wrapper)) k' choices
      | .callArgsK fid locs vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callArgsK fid locs (vals ++ [v]) rest env k'), s, choices)
          | [] =>
              enterFrameStep s fid (vals ++ [v])
                (fun func frameEnv resultLocs =>
                  .exec func.body frameEnv (.frame locs resultLocs [] k' func.wrapper)) k' choices
      | .stmtOpK op nt done pending env k' =>
          -- Target addresses are checked as they arrive ONLY when more
          -- operands follow (interpreter panic timing); at the apply
          -- position the same check happens inside `applyStmtOp`'s
          -- `locsOf`, so the rules need no extra guard there.
          match pending with
          | e :: rest =>
              if done.length < nt then
                match valueAsLoc v with
                | .error (.panic msg) =>
                    return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
                | .error err => throw err
                | .ok _ =>
                    return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, choices)
              else
                return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, choices)
          | [] =>
              match applyStmtOp s choices op nt (v :: done).reverse with
              | .ok (s', choices') => return (.next k', s', choices')
              | .error (.panic msg) =>
                  return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
              | .error err => throw err
      | .callValTargetsK callee locs pending args env k' =>
          match valueAsLoc v with
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
          | .ok loc =>
              match pending with
              | te :: rest =>
                  return (.evalE te env
                    (.callValTargetsK callee (locs ++ [loc]) rest args env k'), s, choices)
              | [] =>
                  return (.evalE callee env
                    (.callValCalleeK (locs ++ [loc]) args env k'), s, choices)
      | .callValCalleeK locs args env k' =>
          match v, args with
          | .funcVal fid captured, [] =>
              enterFrameStep s fid captured
                (fun func frameEnv resultLocs =>
                  .exec func.body frameEnv (.frame locs resultLocs [] k' func.wrapper)) k' choices
          | .nil, [] =>
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                k', s, choices)
          | cv, a :: rest =>
              -- Go evaluates the callee and ALL arguments before the nil
              -- check fires, so nil proceeds into the argument walk.
              if deferrableCallee cv then
                return (.evalE a env (.callValArgsK cv locs [] rest env k'), s, choices)
              else throw (.stuck s!"expected function value, got {repr cv}")
          | other, [] => throw (.stuck s!"expected function value, got {repr other}")
      | .callValArgsK cv locs vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callValArgsK cv locs (vals ++ [v]) rest env k'), s, choices)
          | [] =>
              match cv with
              | .funcVal fid captured =>
                  enterFrameStep s fid (captured ++ vals ++ [v])
                    (fun func frameEnv resultLocs =>
                      .exec func.body frameEnv (.frame locs resultLocs [] k' func.wrapper)) k' choices
              | .nil =>
                  return (.panicking [⟨runtimeErrorValue
                    "runtime error: invalid memory address or nil pointer dereference", false⟩]
                    k', s, choices)
              | other => throw (.stuck s!"expected function value, got {repr other}")
      | .deferCalleeK args env k' =>
          if deferrableCallee v then
            match args with
            | a :: rest =>
                return (.evalE a env (.deferArgsK v [] rest env k'), s, choices)
            | [] =>
                match pushDefer (v, []) k' with
                | some k'' => return (.next k'', s, choices)
                | none => throw (.stuck "defer outside a call frame")
          else throw (.stuck s!"expected function value in defer, got {repr v}")
      | .deferArgsK cv vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.deferArgsK cv (vals ++ [v]) rest env k'), s, choices)
          | [] =>
              match pushDefer (cv, vals ++ [v]) k' with
              | some k'' => return (.next k'', s, choices)
              | none => throw (.stuck "defer outside a call frame")
      | .mapRangeK keyVar valVar keyTy valTy body env k' => do
          let entries ← mapRangeSnapshotEntries s keyTy valTy v
          return (.next (.mapIterK keyVar valVar keyTy valTy body entries env k'), s, choices)
      | .panicArgK k' =>
          return (.panicking [⟨panicPayload v, false⟩] k', s, choices)
      | .chanStK op done pending env k' =>
          -- Pre-communication operands only; a receive's targets evaluate
          -- AFTER the apply step (BUG-022 — spec §Assignments phase 2,
          -- via the selectRecvK entry `applyChanOp` produces).
          match pending with
          | e :: rest =>
              return (.evalE e env (.chanStK op (v :: done) rest env k'), s, choices)
          | [] =>
              match applyChanOp s op (v :: done).reverse env k' with
              | .ok (c', s') => return (c', s', choices)
              | .error (.panic msg) =>
                  return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
              | .error err => throw err
      | .selectOpsK clauses default? done pending env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env
                (.selectOpsK clauses default? (v :: done) rest env k'), s, choices)
          | [] =>
              match applySelect s clauses default? (v :: done).reverse env k' with
              | .ok (c', s') => return (c', s', choices)
              | .error (.panic msg) =>
                  return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
              | .error err => throw err
      | .selectRecvK vals pending body env k' =>
          -- Per-target store-then-next (delta review D3): phase 2 is
          -- left-to-right, so each address stores immediately.
          match valueAsLoc v with
          | .error (.panic msg) =>
              return (.panicking [⟨runtimeErrorValue msg, false⟩] k', s, choices)
          | .error err => throw err
          | .ok loc =>
              match pending with
              | e :: rest =>
                  match vals with
                  | val :: vrest => do
                      let s' ← storeLoc s loc val
                      return (.evalE e env
                        (.selectRecvK vrest rest body env k'), s', choices)
                  | [] => throw (.internal "select receive value/target arity mismatch")
              | [] =>
                  match vals with
                  | [val] => do
                      let s' ← storeLoc s loc val
                      return (.exec body env k', s', choices)
                  | _ => throw (.internal "select receive value/target arity mismatch")
      | .stop => throw (.internal "value delivered to empty continuation")
      | _ => throw (.internal "value delivered to statement continuation")
  | .next k =>
      match k with
      | .stop => throw (.internal "step on terminal configuration")
      | .seq (t :: rest) env k' => return (.exec t env (.seq rest env k'), s, choices)
      | .seq [] _ k' => return (.next k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      | .frame targets results [] k' _ => do
          let vs ← loadMany s results
          let s' ← storeMany s targets vs
          return (.next k', s', choices)
      | .frame targets results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured =>
              -- A deferred call's results are DISCARDED (Go); only effects
              -- matter, so the inner frame reads and stores nothing. An
              -- ENTRY panic is the invocation's panic: it starts unwinding
              -- at this frame with its remaining defers (audit F1+F5,
              -- mirroring the .nil arm below).
              enterFrameStep s fid (captured ++ args)
                (fun func frameEnv _ =>
                  .exec func.body frameEnv
                    (.frame [] [] [] (.frame targets results ds k' w) func.wrapper))
                (.frame targets results ds k' w) choices
          | .nil =>
              -- Registration succeeded; the INVOCATION panics (Go), and
              -- this frame's remaining defers run on the panic path.
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                (.frame targets results ds k' w), s, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .panicResumeK chain k' =>
          if chainNewestRecovered chain then
            -- Recovered: the unwind is cancelled; the frame below resumes
            -- its normal exit path (Go: "returns normally").
            return (.next k', s, choices)
          else
            return (.panicking chain k', s, choices)
      | .breakableK k' => return (.next k', s, choices)
      | .labelK _ k' => return (.next k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body remaining env k' =>
          if remaining.isEmpty then
            return (.next k', s, choices)
          else do
            let (idx, choices') := choices.consume remaining.size
            match hidx : remaining[idx]? with
            | none => throw (.internal "mapRange choice index out of bounds")
            | some (key, value) => do
                have hlt : idx < remaining.size :=
                  (Array.getElem?_eq_some_iff.mp hidx).1
                let (env', s') ← bindIterVars env.pushScope s
                  keyVar valVar keyTy valTy key value
                return (.exec body env'
                  (.mapIterK keyVar valVar keyTy valTy body
                    (remaining.eraseIdx idx hlt) env k'), s', choices')
      | _ => throw (.internal "completion delivered to expression continuation")
  | .breaking k =>
      match k with
      | .seq _ _ k' => return (.breaking k', s, choices)
      | .loop _ _ _ k' => return (.next k', s, choices)
      | .breakableK k' => return (.next k', s, choices)
      | .labelK _ k' => return (.breaking k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ k' => return (.next k', s, choices)
      | .frame _ _ _ _ _ => throw (.stuck "function body escaped with break")
      | .stop => throw (.stuck "break outside loop")
      | _ => throw (.internal "break delivered to expression continuation")
  | .continuing k =>
      match k with
      | .seq _ _ k' => return (.continuing k', s, choices)
      | .breakableK k' => return (.continuing k', s, choices)
      | .labelK _ k' => return (.continuing k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body remaining env k' =>
          return (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k'), s, choices)
      | .frame _ _ _ _ _ => throw (.stuck "function body escaped with continue")
      | .stop => throw (.stuck "continue outside loop")
      | _ => throw (.internal "continue delivered to expression continuation")
  | .returning k =>
      match k with
      | .seq _ _ k' => return (.returning k', s, choices)
      | .breakableK k' => return (.returning k', s, choices)
      | .labelK _ k' => return (.returning k', s, choices)
      | .loop _ _ _ k' => return (.returning k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ k' => return (.returning k', s, choices)
      | .frame targets results [] k' _ => do
          let vs ← loadMany s results
          let s' ← storeMany s targets vs
          return (.next k', s', choices)
      | .frame targets results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured =>
              -- A deferred call's results are DISCARDED (Go); only effects
              -- matter, so the inner frame reads and stores nothing. An
              -- ENTRY panic is the invocation's panic: it starts unwinding
              -- at this frame with its remaining defers (audit F1+F5,
              -- mirroring the .nil arm below).
              enterFrameStep s fid (captured ++ args)
                (fun func frameEnv _ =>
                  .exec func.body frameEnv
                    (.frame [] [] [] (.frame targets results ds k' w) func.wrapper))
                (.frame targets results ds k' w) choices
          | .nil =>
              -- Registration succeeded; the INVOCATION panics (Go), and
              -- this frame's remaining defers run on the panic path.
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                (.frame targets results ds k' w), s, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .stop => throw (.internal "return unwound past the entry frame")
      | _ => throw (.internal "return delivered to expression continuation")
  | .breakingTo L k =>
      match k with
      | .seq _ _ k' => return (.breakingTo L k', s, choices)
      | .loop _ _ _ k' => return (.breakingTo L k', s, choices)
      | .breakableK k' => return (.breakingTo L k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ k' => return (.breakingTo L k', s, choices)
      | .labelK name k' =>
          if name = L then return (.next k', s, choices)
          else return (.breakingTo L k', s, choices)
      | .frame _ _ _ _ _ => throw (.stuck "function body escaped with labeled break")
      | .stop => throw (.stuck s!"labeled break escaped its label: {L}")
      | _ => throw (.internal "labeled break delivered to expression continuation")
  | .continuingTo L k =>
      match k with
      | .seq _ _ k' => return (.continuingTo L k', s, choices)
      | .breakableK k' => return (.continuingTo L k', s, choices)
      | .labelK name k' =>
          if name = L then throw (.stuck s!"continue to non-loop label {L}")
          else return (.continuingTo L k', s, choices)
      | .loop c b env k' =>
          if contHeadLabel k' = some L then
            return (.exec (.while c b) env k', s, choices)
          else return (.continuingTo L k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body remaining env k' =>
          if contHeadLabel k' = some L then
            return (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k'), s, choices)
          else return (.continuingTo L k', s, choices)
      | .frame _ _ _ _ _ => throw (.stuck "function body escaped with labeled continue")
      | .stop => throw (.stuck s!"labeled continue escaped its label: {L}")
      | _ => throw (.internal "labeled continue delivered to expression continuation")
  -- Blocked configurations (channels arc slice 1): relation-silent — no
  -- pairing partner can exist in the sequential machine, so stepping one
  -- IS the deadlocked run (Go: "all goroutines are asleep"). Classified
  -- here (not `.internal`) so every iteration driver reports the honest
  -- terminal even without its own guard; `runConfig`/`execStmtLoop`
  -- additionally classify blocked configurations before the fuel check,
  -- like the other terminals. Slice 2's pool machine steps blocked
  -- configurations at the POOL level (pairing/wake) and never calls the
  -- per-goroutine `stepFn` on them.
  | .blockedSend _ _ _ => throw .deadlock
  | .blockedRecv _ _ _ _ _ => throw .deadlock
  | .blockedSelect _ _ _ => throw .deadlock

/-- Fuel-bounded iteration of `stepFn` to a terminal configuration. Fuel
counts machine steps; the terminal check precedes the fuel check so a
finished program never reports exhaustion. `.panicked` reports as
`GoError.panic` — the same classification surface as the big-step
interpreter's. -/
def runConfig : Nat → ExecState → Config → Choices → Except GoError (ExecState × Choices)
  | fuel, s, c, choices =>
      match c with
      | .next .stop => return (s, choices)
      | .panicked msg => throw (.panic msg)
      -- Blocked = deadlocked (slice 1, zero scheduler): classified BEFORE
      -- the fuel check, like the terminals — a blocked run must never
      -- report fuel exhaustion instead of the deadlock it reached.
      | .blockedSend _ _ _ => throw .deadlock
      | .blockedRecv _ _ _ _ _ => throw .deadlock
      | .blockedSelect _ _ _ => throw .deadlock
      | c =>
          match fuel with
          | 0 => throw .fuelOut
          | fuel + 1 => do
              let (c', s', choices') ← stepFn s c choices
              runConfig fuel s' c' choices'

/-- Whole-program entry, mirroring the big-step `runFunctionWithContext`:
bind arguments (normalized at declared type), allocate named results at
defaults, pin their locations, run the body inside a targetless `frame`
over `.stop`, and read the pinned result locations at the terminal
configuration. Env-in-config throughout — `ExecState.locals` unused. -/
def runFunctionWithContextM (fuel : Nat) (types : TypeEnv) (functions : Array Func)
    (func : Func) (args : Array GoValue) (methods : Array MethodInfo := #[])
    (choices : Choices := []) : Except GoError Result := do
  let state : ExecState := { types, functions, methods }
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let (env, s₁) ← bindParams [] state func.args.toList args.toList
  let (frameEnv, s₂) ← allocDecls env s₁ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  -- The entry frame is a pure barrier (`[] []`): the big-step entry never
  -- stored results anywhere — the driver reads the pinned locations from
  -- the terminal state below.
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] .stop)
  let (sF, _) ← runConfig fuel s₂ c₀ choices
  return { values := (← loadMany sF resultLocs).toArray }

/-- **The `execStmt`-shaped wrapper** (F4 §2's decided Surface interface;
`docs/2026-07-23_reshape-r1r2-machine-design.md`): fuel-bounded iteration
of `stepFn` from a bare statement configuration, classified into the old
big-step `ExecOutcome` at the four unwound terminals. NOT a shim — no
big-step rule appears here; the name and result shape are kept so Surface
statements stay recognizable. Fuel counts machine steps. The `env`
argument replaces the old `ExecState.locals` seeding (deleted at S4 —
env-in-config is the only name-resolution story). -/
def execStmtLoop : Nat → ExecState → Config → Choices →
    Except GoError (ExecOutcome × Choices)
  | fuel, σ, c, choices =>
      match c with
      | .next .stop => return (.normal σ, choices)
      | .returning .stop => return (.returned σ, choices)
      | .breaking .stop => return (.broke σ, choices)
      | .continuing .stop => return (.continued σ, choices)
      | .panicked msg => throw (.panic msg)
      | .blockedSend _ _ _ => throw .deadlock
      | .blockedRecv _ _ _ _ _ => throw .deadlock
      | .blockedSelect _ _ _ => throw .deadlock
      | c =>
          match fuel with
          | 0 => throw .fuelOut
          | fuel + 1 => do
              let (c', σ', choices') ← stepFn σ c choices
              execStmtLoop fuel σ' c' choices'

@[inherit_doc execStmtLoop]
def execStmt (fuel : Nat) (env : LocalEnv) (σ : ExecState) (choices : Choices)
    (prog : Stmt) : Except GoError (ExecOutcome × Choices) :=
  execStmtLoop fuel σ (.exec prog env .stop) choices

/-- Raw `n`-fold iteration of `stepFn` — NO terminal check and no outcome
classification (sem-adequacy arc slice 4, 2026-08-04). `stepFn` itself
throws on every terminal configuration (`.next .stop`, the unwound
`.stop` shapes, `.panicked`), so a successful iterate is a genuine
`n`-step prefix of a run, never an over-run past a terminal. This is the
reachability carrier for the interpreter-level invariance judgment
(`Surface.ReachableExec`): "configuration reachable by the EXECUTABLE
step", with the choice stream threaded exactly as `execStmtLoop` threads
it. -/
def stepFnIter : Nat → ExecState → Config → Choices →
    Except GoError (Config × ExecState × Choices)
  | 0, σ, c, choices => .ok (c, σ, choices)
  | n + 1, σ, c, choices => do
      let (c', σ', choices') ← stepFn σ c choices
      stepFnIter n σ' c' choices'

def runFunctionWithTypesM (fuel : Nat) (types : TypeEnv) (func : Func)
    (args : Array GoValue) : Except GoError Result :=
  runFunctionWithContextM fuel types #[func] func args

def runFunctionM (fuel : Nat) (func : Func) (args : Array GoValue) :
    Except GoError Result :=
  runFunctionWithTypesM fuel [] func args

-- `runNamedFunctionM`/`runNamedFunctionIntsM` DELETED (delta-review N4,
-- 2026-08-05): the Program-level non-seeding entries had zero callers
-- left once `runProgramM` became the driver behind `native-json-run`
-- and the driver-agreement tests — and a globals-bearing program run
-- through them would NOT have gone stuck at first access (the subject's
-- allocations occupy the low base ids the frontend resolved globals
-- to — silent aliasing, audit response C1). Deleting the pair removes
-- the dead trust surface outright; `runProgramM` is THE Program-level
-- entry, and behaves identically on globals-free programs.

/-! ## Package initialization (init slice, `docs/2026-08-05_init-design.md`)

Globals are ordinary base heap cells seeded by the DRIVER as the first
`n` allocations — cell `i` at `Loc.base ⟨i⟩`, wire declaration order —
so the frontend's statically resolved `Expr.locLit` references land on
them. `$pkginit` (variable initializers in `go/types`' `InitOrder`, then
the `$initN` functions) runs to completion before the subject, in the
same state, consuming from the same choice stream. Driver-level
composition only: no new machine rule, no Surface change. -/

/-- Seed one zero-valued cell per package-level variable, checking the
allocation lands exactly on its statically resolved address (the
executable analogue of Perennial's `GlobalAlloc` address pin; can only
fire if seeding ever stops being the first allocations from a fresh
state — an internal invariant break, never Go behavior). -/
def seedGlobals (state : ExecState) (globals : Array GlobalDef) :
    Except GoError ExecState := do
  if state.nextAddr != 0 then
    throw (.internal "global seeding requires a fresh state")
  let mut s := state
  for g in globals, i in [0:globals.size] do
    let v ← defaultValue s g.typ
    let (loc, s') := s.alloc v (some g.typ)
    if loc != .base ⟨i⟩ then
      throw (.internal s!"global {g.name} seeded at {repr loc}, expected base {i}")
    s := s'
  return s

/-- Mark a DIAGNOSTIC error as originating in the `$pkginit` phase
(audit response 2026-08-05, C6): `stuck`/`unsupported`/`internal`
messages get a `package init:` prefix so fuel-out/stuck triage can tell
phases apart. `panic` is NOT marked — its message is the Go-observable
abort line the differential compares — and `fuelOut` carries no message
(an init-phase fuel exhaustion is indistinguishable by design; the
docstrings say so). -/
def markInitPhase : GoError → GoError
  | .stuck msg => .stuck s!"package init: {msg}"
  | .unsupported msg => .unsupported s!"package init: {msg}"
  | .internal msg => .internal s!"package init: {msg}"
  | e => e

/-- Run `$pkginit` if the program has one: a nullary, resultless run to
termination under a targetless barrier frame. Malformed shapes fail
closed; a panic during initialization aborts the run (Go: a panicking
initializer kills the program before `main`), surfacing through
`runConfig`'s `.panicked` terminal as `GoError.panic` (message
unmarked — it is the Go-observable abort). Diagnostic errors carry the
`package init:` marker (`markInitPhase`). -/
def runPkgInitM (fuel : Nat) (state : ExecState) (choices : Choices) :
    Except GoError (ExecState × Choices) := do
  match findFunctionIn? state.functions pkgInitFuncId with
  | none => return (state, choices)
  | some initF =>
      if initF.args.size != 0 || initF.results.size != 0 then
        throw (.stuck s!"malformed {pkgInitFuncId.key}: expected no parameters and no results")
      match runConfig fuel state (.exec initF.body [] (.frame [] [] [] .stop)) choices with
      | .ok r => pure r
      | .error e => throw (markInitPhase e)

/-- The whole-PROGRAM entry: subject lookup and arity check, seed
globals, run `$pkginit`, then the subject from the initialized state
with the leftover choice stream. The pre-init step ORDER (find → arity
→ seed → init-shape) is shared verbatim with the enumeration driver's
`CLI.enumSetup` — divergent orders gave divergent fail-closed errors on
the arity+init-failure intersection (audit response 2026-08-05, C6).
`fuel` bounds EACH phase separately — a run may take up to 2× `fuel`
machine steps total (a bound, not a budget split). After seeding, the
seeded state is asserted `StateWf` (kernel-decidable): the
defense-in-depth net behind the decoder's `globaladdr` bound check —
a dangling location in a function body or global cell refuses here
instead of aliasing a later allocation (audit response, C1). For a
program with no globals and no `$pkginit` the init phases are no-ops
and this is exactly the old named-function entry wiring
(`runFunctionWithContextM`'s, over a `Program`). -/
def runProgramM (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (choices : Choices := []) : Except GoError Result := do
  let func ←
    match findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let state : ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods }
  let s₀ ← seedGlobals state program.globals
  if StateWf s₀ then pure () else
    throw (.internal "seeded state ill-formed: a location in a global cell or function body dangles beyond the allocator bound")
  let (s₁, choices₁) ← runPkgInitM fuel s₀ choices
  let (env, s₂) ← bindParams [] s₁ func.args.toList args.toList
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] .stop)
  let (sF, _) ← runConfig fuel s₃ c₀ choices₁
  return { values := (← loadMany sF resultLocs).toArray }

def runProgramIntsM (fuel : Nat) (program : Program) (name : String)
    (args : Array Int) (choices : List Nat := []) : Except GoError Result :=
  runProgramM fuel program name (args.map GoValue.int) choices

end GoLean.GoCore.Machine
