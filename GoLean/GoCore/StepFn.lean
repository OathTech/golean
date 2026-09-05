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
`recover` — and an unrecovered chain reaching `.stop` is the ABORT
(`Config.abort?`, B4): the machine stops there with the Go `panic`
terminal, one step, no k-less successor; otherwise only out-of-model
conditions are `Except` errors. Every apply/entry arm is "apply, then deliver"
(B2): the helper's outcome is classified once (`toResult`) and
`deliverS` turns it into the step (`Machine.deliver` + the stream).

Nondeterminism: the sequential choice points (mapRange pick-next,
appendSlice spill capacity, and — slice 4 — the multi-ready select's
L2 clause pick inside `applySelect`) consume from the external
`Choices` stream, exactly as the big-step interpreter did — the
relation's corresponding rules quantify over the choice.

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

/-- The executable's delivery (B2): `deliver` with the choice stream —
a value continues as `next a` (carrying the apply's OWN post-stream);
a recoverable panic unwinds under `k` over the pre-apply state with the
PRE-apply stream `ch` (the abandoned apply consumed nothing that the
unwind keeps — today's every-site convention, now one definition). The
relation's `deliver` is this without the stream (`deliverS_deliver`). -/
def deliverS {α : Type} (s : ExecState) (k : Cont) (ch : Choices)
    (next : α → Config × ExecState × Choices) (r : Result α)
    (chain : List PanicEntry := []) : Config × ExecState × Choices :=
  match r with
  | .ok a => next a
  | .panic msg => (.panicking (chain ++ [panicEntry msg]) k, s, ch)

@[simp] theorem deliverS_ok {α : Type} {s : ExecState} {k : Cont} {ch : Choices}
    {next : α → Config × ExecState × Choices} {a : α} {chain : List PanicEntry} :
    deliverS s k ch next (.ok a) chain = next a := rfl

@[simp] theorem deliverS_panic {α : Type} {s : ExecState} {k : Cont} {ch : Choices}
    {next : α → Config × ExecState × Choices} {msg : String} {chain : List PanicEntry} :
    deliverS s k ch next (.panic msg) chain = (.panicking (chain ++ [panicEntry msg]) k, s, ch) := rfl

/-- The executable delivery projects onto the relation's. -/
theorem deliverS_deliver {α : Type} {s : ExecState} {k : Cont} {ch : Choices}
    {next : α → Config × ExecState × Choices} {r : Result α} {chain : List PanicEntry}
    {c' : Config} {s' : ExecState} {ch' : Choices}
    (h : deliverS s k ch next r chain = (c', s', ch')) :
    deliver s k (fun a => ((next a).1, (next a).2.1)) r chain = (c', s') := by
  cases r <;> simp_all [deliverS, deliver]

/-- **Frame EXIT** (B4): what a body's completion does at its call frame
— whether the body FELL OFF ITS END (`.next (.frame …)`) or RETURNED
(`.signal .ret (.frame …)`): both entries are this ONE function (a
`return` at a frame IS a fall-through at a frame; the relation's
`frameFall*`/`frameReturn*` rule pairs are its two entries). Drain the
defer chain one call per step — a deferred call's results are DISCARDED
(Go), so the inner frame reads and stores nothing; an ENTRY panic is the
invocation's panic and starts unwinding AT THIS FRAME with its remaining
defers (audit F1+F5); a nil deferred callee's INVOCATION panics the same
way (registration succeeded) — then, chain empty, read the pinned
results: a targetless, resultless frame resumes the caller in one step; a
frame with caller-target plans enters the tgtOpK spine POST-CALL (BUG-025
+ the BUG-052 order pin: the post-call point is gc's realized order — the
pin covers only the call-vs-operand axis; the spine's left-to-right
inter-target walk is our spec-legal realization of an axis left OPEN,
per the rule-site latitude block), then the per-target storeK stores. A
targetless frame WITH pinned results is stuck-closed after the same
result read (the frontend always supplies targets for result-bearing
calls; the pre-BUG-025 `storeMany [] (v::vs)` refusal). -/
def stepFrameExit (s : ExecState) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (w : Bool) (choices : Choices) :
    Except Stop (Config × ExecState × Choices) := do
  match targets, results, ds with
  | [], [], [] => return (.next k', s, choices)
  | [], rl :: rls, [] => do
      let _ ← loadMany s (rl :: rls)
      throw (.stuck "extra GoCore assignment value")
  | (sh, e :: ops) :: rest, results, [] => do
      let vs ← loadMany s results
      return (.evalE e tenv
        (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, choices)
  | (_, []) :: _, _, [] =>
      throw (.internal "malformed call target plan")
  | targets, results, (cv, args) :: ds =>
      match cv with
      | .funcVal fid captured => do
          let (r, ch') ← enterFramePick s fid (captured ++ args) choices
          return deliverS s (.frame targets tenv results ds k' w) ch'
            (fun (func, frameEnv, _, s') =>
              (.exec func.body frameEnv
                (.frame [] [] [] [] (.frame targets tenv results ds k' w) func.wrapper),
                s', ch')) r
      | .nil =>
          return (.panicking [panicEntry nilDerefPanicText]
            (.frame targets tenv results ds k' w), s, choices)
      | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")

/-- One machine step. `.ok` is a step the relation permits; `.error` is
either a Go TERMINAL the machine reached (the abort's `panic`, a sync
`fatal`, a sequential `deadlock`) or a refusal that names its cause (the
machine is stuck here). Never call on a terminal configuration (the
driver guards). -/
def stepFn (s : ExecState) (c : Config) (choices : Choices) :
    Except Stop (Config × ExecState × Choices) := do
  match c with
  | .panicking chain k =>
      match k with
      | .frame _targets _tenv _results [] k' _ => return (.panicking chain k', s, choices)
      | .frame targets tenv results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured => do
              -- Defers run on the panic path, above the suspended chain's
              -- marker (the shape `recover`'s walk detects). An ENTRY
              -- panic joins the chain (audit F1+F5; `deliverS`'s `chain`).
              -- The deferred callee's frame carries ITS wrapper flag (BUG-015).
              let (r, ch') ← enterFramePick s fid (captured ++ args) choices
              return deliverS s (.frame targets tenv results ds k' w) ch'
                (fun (func, frameEnv, _, s') =>
                  (.exec func.body frameEnv
                    (.frame [] [] [] [] (.panicResumeK chain
                      (.frame targets tenv results ds k' w)) func.wrapper), s', ch')) r chain
          | .nil =>
              -- The nil invocation's panic joins the chain; remaining
              -- defers keep draining.
              return (.panicking (chain ++ [panicEntry nilDerefPanicText])
                (.frame targets tenv results ds k' w), s, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .panicResumeK suspended k' =>
          return (.panicking (suspended ++ chain) k', s, choices)
      | .stop =>
          -- THE ABORT (B4, `Config.abort?`): an unrecovered chain at the
          -- empty continuation stops the sequential machine with the Go
          -- `panic` terminal — ONE step (the fuel the old `.panicked`
          -- step cost), no successor configuration (there is no k-less
          -- control form; the pool records a tombstone instead,
          -- `stepThread`). Rendering through `abortMsg`, shared.
          match chain with
          | first :: rest => throw (.panic (← abortMsg s first rest))
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
                let (loc, s') := s.alloc v p.typ
                return (.next (.seq rest (env.declare p.id loc) k'), s', choices)
              else throw (.internal "initialization under foreign-scope sequence")
          | _ => throw (.stuck "GoCore initialization outside a statement sequence")
      | .assign lhs rhs =>
          -- Round 4 (BUG-037): a single assignment rides the spine as a
          -- one-target multi-assign — the RHS is phase 1, the target
          -- chain's checks fire at the store (phase 2).
          match targetPlan lhs with
          | some (sh, e :: ops) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), s, choices)
          | some (_, []) => throw (.internal "malformed assignment target plan")
          | none =>
              match lhs with
              | .unsupported feature => throw (.unsupported feature)
              | _ => throw (.stuck "unclassified assignee")
      | .ifThenElse c t e => return (.evalE c env (.ifK t e env k), s, choices)
      | .while c b => return (.evalE c env (.whileK c b env k), s, choices)
      -- The five control transfers RAISE their signal (B4; rule
      -- `signalStmt` — `Stmt.signal?` is the table these five arms are).
      | .returnStmt => return (.signal .ret k, s, choices)
      | .breakStmt => return (.signal .brk k, s, choices)
      | .continueStmt => return (.signal .cont k, s, choices)
      | .inertLabel _ => return (.next k, s, choices)
      | .labeled name b => return (.exec b env (.labelK name k), s, choices)
      | .breakTo name => return (.signal (.brkTo name) k, s, choices)
      | .continueTo name => return (.signal (.contTo name) k, s, choices)
      | .breakable b => return (.exec b env (.breakableK k), s, choices)
      | .deferCall callee args =>
          return (.evalE callee env (.deferCalleeK args.toList env k), s, choices)
      | .panicStmt e =>
          return (.evalE e env (.panicArgK k), s, choices)
      | .callValue targets callee args =>
          -- BUG-052 order pin: the CALL evaluates first (callee, args,
          -- frame); the caller-target plans ride to the frame and their
          -- operands evaluate at frame EXIT (the post-call point is
          -- gc's realized order inside spec §Order of evaluation's
          -- unordered carve-out — the call-vs-operand axis only; see
          -- the relation's PINNED LATITUDE block).
          match targetsPlan targets.toList with
          | some plans =>
              return (.evalE callee env (.callValCalleeK plans args.toList env k), s, choices)
          | none => throw (.unsupported "unsupported value-call target assignee")
      | .call targets fid args =>
          match targetsPlan targets.toList with
          | some plans =>
              match args.toList with
              | a :: rest =>
                  return (.evalE a env (.callArgsK fid plans [] rest env k), s, choices)
              | [] => do
                  let (r, ch') ← enterFramePick s fid [] choices
                  return deliverS s k ch' (fun (func, frameEnv, resultLocs, s') =>
                    (.exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper),
                      s', ch')) r
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
      | .goStmt callee args =>
          -- Spawn operands evaluate NOW in the spawning goroutine (spec
          -- §Go statements — the deferCall shape); the SPAWN itself is a
          -- pool step (`stepMulti`), and `stepFn`'s spawn position below
          -- fails closed.
          return (.evalE callee env (.goCalleeK args.toList env k), s, choices)
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
      | .mapLookup t okT base index keyTy valueTy =>
          -- Round 4 (BUG-034): the comma-ok map lookup rides the spine —
          -- target operands phase 1 (checks deferred), base/key
          -- evaluated, the lookup applied (`applyRhsOp`), stores
          -- left-to-right in phase 2.
          match targetsPlan [t, okT] with
          | some ((sh, e :: ops) :: rest) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy)
                  [base, index] [] (.seqn #[]) env k), s, choices)
          | some _ => throw (.internal "malformed comma-ok target plan")
          | none => throw (.unsupported "unsupported statement target assignee")
      | .typeAssert t okT expr targetTy =>
          -- Round 4 (BUG-034): the comma-ok type assertion, same spine.
          match targetsPlan [t, okT] with
          | some ((sh, e :: ops) :: rest) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] rest (.typeAssert targetTy)
                  [expr] [] (.seqn #[]) env k), s, choices)
          | some _ => throw (.internal "malformed comma-ok target plan")
          | none => throw (.unsupported "unsupported statement target assignee")
      | .assignMany left right =>
          -- Convergence round (BUG-025): the general multi-assign rides
          -- the SAME phase-split delivery machinery as the receive —
          -- phase-1 target operands (outer checks deferred), then the
          -- RHS values (`rhsK`), then phase-2 left-to-right stores.
          if left.size = right.size then
            match targetsPlan left.toList with
            | some ((sh, e :: ops) :: rest) =>
                return (.evalE e env
                  (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), s, choices)
            | some _ => throw (.stuck "malformed multi-assignment target plan")
            | none => throw (.unsupported "unsupported multi-assignment target assignee")
          else
            throw (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}")
      | .syncStmt op args targets =>
          -- Sync statements (spec-parity slice 2): operand-plan entry
          -- mirroring the channel arm. Named scrutinee for the
          -- correspondence proofs' fun_cases rewrites.
          match _hplan : syncPlan (.syncStmt op args targets) with
          | some (sop, e :: rest) =>
              return (.evalE e env (.syncStK sop [] rest env k), s, choices)
          | some (_, []) => throw (.internal "empty sync-statement operand plan")
          | none => throw (.unsupported "malformed sync-statement shape (arity/targets)")
      | .atomicStmt op kind args targets =>
          -- sync/atomic statements (atomics arc wave 1): operand-plan
          -- entry mirroring the sync arm. Named scrutinee for the
          -- correspondence proofs' fun_cases rewrites.
          match _hplan : atomicPlan (.atomicStmt op kind args targets) with
          | some (aop, e :: rest) =>
              return (.evalE e env (.atomicStK aop [] rest env k), s, choices)
          | some (_, []) => throw (.internal "empty atomic-statement operand plan")
          | none => throw (.unsupported "malformed atomic-statement shape (arity/kind/targets)")
      | wide =>
          -- allocNew / makeSlice / makeMap / mapAssign / mapLookup /
          -- typeAssert / appendSlice / copySlice
          match stmtPlan wide with
          | some (op, nt, e :: rest) =>
              return (.evalE e env (.stmtOpK op nt [] rest env k), s, choices)
          -- A8: no `stmtPlan` arm emits an empty operand list (every plan
          -- starts with its target); the shape is refused by name, never
          -- applied (the former `Step.stmtOpNullary` rule was dead).
          | some (_, _, []) => throw (.internal "empty statement operand plan")
          | none => throw (.unsupported "unsupported statement target assignee")
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
      | .global gid =>
          -- A4: the global's cell must exist (the driver seeded the first
          -- `n` cells; the decoder bound-checked `gid < n`). The check is
          -- the wf-preserving net behind that decode-time check — a `gid`
          -- past the heap is a decoder/driver breach, refused by name.
          if gid < s.heap.size then
            return (.retV (.addr (.base ⟨gid⟩)) k, s, choices)
          else
            throw (.stuck s!"global {gid} out of range: the heap has {s.heap.size} cell(s)")
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
          | some (op, []) => do
              let r ← toResult (applyStrictOp s op [])
              return deliverS s k choices (fun (v, s') => (.retV v k, s', choices)) r
          | none => throw (.stuck "unclassified expression")
  | .retV v k =>
      match k with
      | .strictK op done (e :: rest) env k' =>
          return (.evalE e env (.strictK op (v :: done) rest env k'), s, choices)
      | .strictK op done [] _ k' => do
          let r ← toResult (applyStrictOp s op (v :: done).reverse)
          return deliverS s k' choices (fun (out, s') => (.retV out k', s', choices)) r
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
      | .callArgsK fid plans vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callArgsK fid plans (vals ++ [v]) rest env k'), s, choices)
          | [] => do
              let (r, ch') ← enterFramePick s fid (vals ++ [v]) choices
              return deliverS s k' ch' (fun (func, frameEnv, resultLocs, s') =>
                (.exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper),
                  s', ch')) r
      | .stmtOpK op nt done pending env k' =>
          -- Target addresses are checked as they arrive ONLY when more
          -- operands follow (interpreter panic timing); at the apply
          -- position the same check happens inside `applyStmtOp`'s
          -- `locsOf`, so the rules need no extra guard there.
          match pending with
          | e :: rest =>
              if done.length < nt then do
                let r ← toResult (valueAsLoc v)
                return deliverS s k' choices
                  (fun _ => (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, choices)) r
              else
                return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, choices)
          | [] => do
              let r ← toResult (applyStmtOp s choices op nt (v :: done).reverse)
              return deliverS s k' choices (fun (s', choices') => (.next k', s', choices')) r
      | .callValCalleeK plans args env k' =>
          match v, args with
          | .funcVal fid captured, [] => do
              let (r, ch') ← enterFramePick s fid captured choices
              return deliverS s k' ch' (fun (func, frameEnv, resultLocs, s') =>
                (.exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper),
                  s', ch')) r
          | .nil, [] =>
              return (.panicking [panicEntry nilDerefPanicText] k', s, choices)
          | cv, a :: rest =>
              -- Go evaluates the callee and ALL arguments before the nil
              -- check fires, so nil proceeds into the argument walk.
              if deferrableCallee cv then
                return (.evalE a env (.callValArgsK cv plans [] rest env k'), s, choices)
              else throw (.stuck s!"expected function value, got {repr cv}")
          | other, [] => throw (.stuck s!"expected function value, got {repr other}")
      | .callValArgsK cv plans vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callValArgsK cv plans (vals ++ [v]) rest env k'), s, choices)
          | [] =>
              match cv with
              | .funcVal fid captured => do
                  let (r, ch') ← enterFramePick s fid (captured ++ vals ++ [v]) choices
                  return deliverS s k' ch' (fun (func, frameEnv, resultLocs, s') =>
                    (.exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper),
                      s', ch')) r
              | .nil =>
                  return (.panicking [panicEntry nilDerefPanicText] k', s, choices)
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
          -- BUG-005 (L): record the base cell and the START-ID set;
          -- no snapshot, no validation here (per-pick, live).
          let bs ← mapRangeStartSets s v
          return (.next (.mapIterK keyVar valVar keyTy valTy body bs.1 #[] bs.2 env k'), s, choices)
      | .panicArgK k' =>
          return (.panicking [⟨panicPayload v, false⟩] k', s, choices)
      | .chanStK op done pending env k' =>
          -- Pre-communication operands only; a receive's targets evaluate
          -- AFTER the apply step (BUG-022 — spec §Assignments phase 2,
          -- via the selectRecvK entry `applyChanOp` produces).
          match pending with
          | e :: rest =>
              return (.evalE e env (.chanStK op (v :: done) rest env k'), s, choices)
          | [] => do
              let r ← toResult (applyChanOp s op (v :: done).reverse env k')
              return deliverS s k' choices (fun (c', s') => (c', s', choices)) r
      | .selectOpsK clauses default? done pending env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env
                (.selectOpsK clauses default? (v :: done) rest env k'), s, choices)
          | [] => do
              -- The stream threads through the apply: multi-ready
              -- readiness consumes the L2 clause pick (slice 4). The
              -- SEQUENTIAL step projects away the emitted commit
              -- identity (Q2) — the pool's select interception in
              -- `stepThread` is its consumer.
              let r ← toResult (applySelect s clauses default? (v :: done).reverse env k' choices)
              return deliverS s k' choices (fun (c', s', choices', _) => (c', s', choices')) r
      | .tgtOpK sh ops pending refs targets rop rhs vals body env k' =>
          -- Delivery PHASE 1 (convergence round, BUG-029): operand
          -- values accumulate; each target completes into a
          -- store-ready TargetRef (its outer nil/bounds check
          -- DEFERRED). Targets done: the receive paths (rhs = [])
          -- store their delivery values under `.next (.storeK ...)`;
          -- the general multi-assign (BUG-025) evaluates its RHS
          -- under `rhsK` first.
          match pending with
          | e :: rest =>
              return (.evalE e env
                (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), s, choices)
          | [] =>
              match completeTargetRef sh (v :: ops).reverse with
              | none => throw (.internal "malformed receive target operands")
              | some r =>
                  match targets with
                  | (sh', e :: ops') :: rest =>
                      return (.evalE e env
                        (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), s, choices)
                  | (_, []) :: _ => throw (.internal "malformed receive target plan")
                  | [] =>
                      match rhs with
                      | e :: rest =>
                          return (.evalE e env
                            (.rhsK rop (refs ++ [r]) [] rest body env k'), s, choices)
                      | [] =>
                          return (.next (.storeK (refs ++ [r]) vals body env k'), s, choices)
      | .rhsK rop refs done pending body env k' =>
          -- RHS values left-to-right; the last applies the value source
          -- (BUG-034: the comma-ok lookup/assert — its key-hash panic
          -- fires HERE, before any store) and enters phase 2.
          match pending with
          | e :: rest =>
              return (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), s, choices)
          | [] => do
              let r ← toResult (applyRhsOp s rop (v :: done).reverse)
              return deliverS s k' choices
                (fun vals => (.next (.storeK refs vals body env k'), s, choices)) r
      | .goCalleeK args env k' =>
          -- Spawn callee arrived. Nil registers into the walk like a
          -- deferred callee (gc evaluates the arguments before its
          -- nil-fatal); the zero-argument SPAWN position fails closed —
          -- spawning is a pool step (`stepMulti` intercepts this
          -- configuration before ever calling `stepFn` on it), so
          -- reaching this arm means a sequential driver ran a `go`
          -- statement (the `$pkginit` phase, `execStmt`-level runs).
          if deferrableCallee v then
            match args with
            | a :: rest =>
                return (.evalE a env (.goArgsK v [] rest env k'), s, choices)
            | [] => throw (.unsupported
                "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)")
          else throw (.stuck s!"expected function value in go statement, got {repr v}")
      | .goArgsK cv vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k'), s, choices)
          | [] => throw (.unsupported
              "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)")
      | .syncStK op done pending env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env (.syncStK op (v :: done) rest env k'), s, choices)
          | [] => do
              -- The sync apply (spec-parity slice 2): the stream is
              -- threaded through `applySyncOp` — only the TRY heads draw
              -- from it (`ChoiceSite.tryLock`, Q-TRYLOCK; the envelope
              -- statement at `applyTryLock`); every other head passes it
              -- through untouched (the acquisition-order latitude is
              -- entirely the existing L1 site's — `applySyncOpCore`'s
              -- envelope statement). `.fatal` propagates as the
              -- unrecoverable terminal it is; recoverable panics become
              -- `.panicking`.
              let r ← toResult (applySyncOp s choices op (v :: done).reverse env k')
              return deliverS s k' choices (fun (c', s', choices') => (c', s', choices')) r
      | .atomicStK op done pending env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env (.atomicStK op (v :: done) rest env k'), s, choices)
          | [] => do
              -- The atomic apply (atomics arc wave 1): ONE fused step,
              -- consuming NO choices (the envelope statement at
              -- `applyAtomicOp` — SC is the L1 interleaving of these
              -- indivisible steps). The nil-address panic is the
              -- recoverable runtime error gc realizes (SIGSEGV →
              -- `runtime.Error`); everything else propagates.
              let r ← toResult (applyAtomicOp s op (v :: done).reverse env k')
              return deliverS s k' choices (fun (c', s') => (c', s', choices)) r
      | .stop => throw (.internal "value delivered to empty continuation")
      | _ => throw (.internal "value delivered to statement continuation")
  | .next k =>
      match k with
      | .stop => throw (.internal "step on terminal configuration")
      | .seq (t :: rest) env k' => return (.exec t env (.seq rest env k'), s, choices)
      | .seq [] _ k' => return (.next k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      -- The body fell off its end at its call frame: frame EXIT
      -- (`stepFrameExit` — the same function a `return` at the frame
      -- takes, B4).
      | .frame targets tenv results ds k' w =>
          stepFrameExit s targets tenv results ds k' w choices
      | .panicResumeK chain k' =>
          if chainNewestRecovered chain then
            -- Recovered: the unwind is cancelled; the frame below resumes
            -- its normal exit path (Go: "returns normally").
            return (.next k', s, choices)
          else
            return (.panicking chain k', s, choices)
      | .breakableK k' => return (.next k', s, choices)
      | .labelK _ k' => return (.next k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' => do
          -- BUG-005 (L): LOAD the live cell (the U1-closing footprint
          -- read — every pick, including this done-check), filter by
          -- the produced-ID set (B1 stamps), validate (fail closed), then consume
          -- ONE choice of width candidates + stop, stop LAST — the
          -- zero stream IS the canonical member by definition (memo §5
          -- ruling Q3): first candidate in cell order, never stop
          -- while a candidate remains, so mutation-free ranges keep
          -- the old first-remaining pick sequence and self-inserting
          -- loops fuel-out VISIBLY. The consult at the LAST mandatory
          -- candidate has width 1 and pops nothing (the uniform rule,
          -- G-U 2026-09-04 — before it this site popped at width 1).
          let cands ← mapIterCandidates s keyTy valTy base produced
          if cands.isEmpty then
            return (.next k', s, choices)
          else do
            let mandatory := mapIterMandatoryRemains cands start
            let width := cands.size + (if mandatory then 0 else 1)
            let (idx, choices') := Choices.consumeAt .mapIter width choices
            match cands[idx]? with
            | none =>
                -- idx = cands.size: the STOP slot (only reachable when
                -- no mandatory start key remains — width excludes it
                -- otherwise).
                return (.next k', s, choices')
            | some (id, key, value) => do
                let (env', s') ← bindIterVars env.pushScope s
                  keyVar valVar keyTy valTy key value
                return (.exec body env'
                  (.mapIterK keyVar valVar keyTy valTy body
                    base (produced.push id) start env k'), s', choices')
      | .storeK refs vals body env k' =>
          -- Delivery PHASE 2 (convergence round, BUG-029): one store
          -- per step, LEFT-TO-RIGHT; a store-time panic (nil address,
          -- bounds, nil map) fires AFTER earlier stores landed.
          match refs, vals with
          | ref :: rs, val :: vrest => do
              let r ← toResult (storeTarget s ref val)
              return deliverS s k' choices
                (fun s' => (.next (.storeK rs vrest body env k'), s', choices)) r
          | [], [] => return (.exec body env k', s, choices)
          | _, _ => throw (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)")
      | _ => throw (.internal "completion delivered to expression continuation")
  | .signal sg k =>
      -- The frame×signal TABLE (B4, rule `signal`): pass, catch, or —
      -- where the table has no successor — the call frame's `ret` is the
      -- frame EXIT (the `.next` exit's twin, `stepFrameExit`) and every
      -- other shape is a refusal that names its cause.
      match signalStep sg k with
      | some c' => return (c', s, choices)
      | none =>
          match sg, k with
          | .ret, .frame targets tenv results ds k' w =>
              stepFrameExit s targets tenv results ds k' w choices
          | _, _ => throw (signalRefusal sg k)
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
  -- (The completion marker's strip left `stepFn` at C5: the post-op
  -- boundary is the POOL's per-goroutine flag and its clear a pool step,
  -- so the sequential driver takes one step fewer per completed
  -- registry op than the one-goroutine pool — `execProg_single_eq_execStmt`
  -- is stated with that count, `seqOpCount`.)
  -- A parked sync op with no sibling goroutine IS the deadlocked run
  -- (probes p06-p08: gc's detector fires on a single goroutine parked
  -- in Lock/Wait/Do) — the channel blocked shapes' classification.
  | .blockedSync _ _ _ _ => throw .deadlock

/-- Fuel-bounded iteration of `stepFn` to a terminal configuration. Fuel
counts machine steps; the terminal check precedes the fuel check so a
finished program never reports exhaustion. An unrecovered panic reports
as `Stop.panic` from the abort step itself (`stepFn` at `Config.abort?`)
— the same classification surface as the big-step interpreter's. -/
def runConfig : Nat → ExecState → Config → Choices → Except Stop (ExecState × Choices)
  | fuel, s, c, choices =>
      match c with
      | .next .stop => return (s, choices)
      -- Blocked = deadlocked (slice 1, zero scheduler): classified BEFORE
      -- the fuel check, like the terminals — a blocked run must never
      -- report fuel exhaustion instead of the deadlock it reached.
      | .blockedSend _ _ _ => throw .deadlock
      | .blockedRecv _ _ _ _ _ => throw .deadlock
      | .blockedSelect _ _ _ => throw .deadlock
      | .blockedSync _ _ _ _ => throw .deadlock
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
    (choices : Choices := []) : Except Stop Readout := do
  let state : ExecState := { types, functions, methods }
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let (env, s₁) ← bindParams [] state func.args.toList args.toList
  let (frameEnv, s₂) ← allocDecls env s₁ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  -- The entry frame is a pure barrier (`[] []`): the big-step entry never
  -- stored results anywhere — the driver reads the pinned locations from
  -- the terminal state below.
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  let (sF, _) ← runConfig fuel s₂ c₀ choices
  return { values := (← loadMany sF resultLocs).toArray }

/-- **The `execStmt`-shaped wrapper** (F4 §2's decided Surface interface;
`docs/2026-07-23_reshape-r1r2-machine-design.md`): fuel-bounded iteration
of `stepFn` from a bare statement configuration to the ONE terminal
(`.next .stop`), returning the final state. NOT a shim — no big-step rule
appears here; the name is kept so Surface statements stay recognizable.
Since B4 the former `ExecOutcome` classification is gone: a
`return`/`break`/`continue` reaching `.stop` is not a completion but the
refusal `stepFn` raises for it (`signalRefusal` — every Program driver
runs its subject under a barrier frame, so only a bare-statement run
could reach one); an unrecovered panic is the `panic` terminal raised at
the abort step. Fuel counts machine steps. The `env` argument replaces
the old `ExecState.locals` seeding (deleted at S4 — env-in-config is the
only name-resolution story). -/
def execStmtLoop : Nat → ExecState → Config → Choices →
    Except Stop (ExecState × Choices)
  | fuel, σ, c, choices =>
      match c with
      | .next .stop => return (σ, choices)
      | .blockedSend _ _ _ => throw .deadlock
      | .blockedRecv _ _ _ _ _ => throw .deadlock
      | .blockedSelect _ _ _ => throw .deadlock
      | .blockedSync _ _ _ _ => throw .deadlock
      | c =>
          match fuel with
          | 0 => throw .fuelOut
          | fuel + 1 => do
              let (c', σ', choices') ← stepFn σ c choices
              execStmtLoop fuel σ' c' choices'

@[inherit_doc execStmtLoop]
def execStmt (fuel : Nat) (env : LocalEnv) (σ : ExecState) (choices : Choices)
    (prog : Stmt) : Except Stop (ExecState × Choices) :=
  execStmtLoop fuel σ (.exec prog env .stop) choices

/-- Raw `n`-fold iteration of `stepFn` — NO terminal check and no outcome
classification (sem-adequacy arc slice 4, 2026-08-04). `stepFn` itself
throws on every terminal configuration (`.next .stop`; a signal at
`.stop`; the abort), so a successful iterate is a genuine
`n`-step prefix of a run, never an over-run past a terminal. This is the
reachability carrier for the interpreter-level invariance judgment
(`Surface.ReachableExec`): "configuration reachable by the EXECUTABLE
step", with the choice stream threaded exactly as `execStmtLoop` threads
it. -/
def stepFnIter : Nat → ExecState → Config → Choices →
    Except Stop (Config × ExecState × Choices)
  | 0, σ, c, choices => .ok (c, σ, choices)
  | n + 1, σ, c, choices => do
      let (c', σ', choices') ← stepFn σ c choices
      stepFnIter n σ' c' choices'

def runFunctionWithTypesM (fuel : Nat) (types : TypeEnv) (func : Func)
    (args : Array GoValue) : Except Stop Readout :=
  runFunctionWithContextM fuel types #[func] func args

def runFunctionM (fuel : Nat) (func : Func) (args : Array GoValue) :
    Except Stop Readout :=
  runFunctionWithTypesM fuel #[] func args

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
so the frontend's statically resolved `Expr.global` references land on
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
    Except Stop ExecState := do
  if state.nextAddr != 0 then
    throw (.internal "global seeding requires a fresh state")
  let mut s := state
  for g in globals, i in [0:globals.size] do
    let v ← defaultValue s g.typ
    let (loc, s') := s.alloc v g.typ
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
def markInitPhase : Stop → Stop
  | .stuck msg => .stuck s!"package init: {msg}"
  | .unsupported msg => .unsupported s!"package init: {msg}"
  | .internal msg => .internal s!"package init: {msg}"
  | e => e

/-- `runConfig` for the `$pkginit` phase (stdlib slice 3, 2026-09-04): the
same loop with ONE guard — a `print`/`println` apply position REFUSES by
name. The init phase runs on the sequential driver, which has no event
channel: stepping through the print would validate it and DROP its bytes
(a silent fail-open of the output observable). The pool driver folds
`StepEvent.out`; this phase does not, so it refuses instead ([AGENT]
scoping call, disclosed in the design note §3.4; rowed
`builtins/print/in-init`). The CLI's init mirrors (`enumInitRun`, the
tracer's `initLoop`, `initDFS`) carry the same guard through
`initPrintRefusal?`. -/
def initPrintRefusal? (c : Config) : Option Stop :=
  match printOut? c with
  | some _ => some (.unsupported "print/println during package initialization: the init phase runs on the sequential driver, which has no output event channel (the pool driver folds StepEvent.out) — refused rather than dropping the bytes (stdlib slice 3; row builtins/print/in-init)")
  | none => none

@[inherit_doc initPrintRefusal?]
def runInitConfig : Nat → ExecState → Config → Choices → Except Stop (ExecState × Choices)
  | fuel, s, c, choices =>
      match c with
      | .next .stop => return (s, choices)
      | .blockedSend _ _ _ => throw .deadlock
      | .blockedRecv _ _ _ _ _ => throw .deadlock
      | .blockedSelect _ _ _ => throw .deadlock
      | .blockedSync _ _ _ _ => throw .deadlock
      | c =>
          match initPrintRefusal? c with
          | some e => throw e
          | none =>
            match fuel with
            | 0 => throw .fuelOut
            | fuel + 1 => do
                let (c', s', choices') ← stepFn s c choices
                runInitConfig fuel s' c' choices'

/-- Run `$pkginit` if the program has one: a nullary, resultless run to
termination under a targetless barrier frame. Malformed shapes fail
closed; a panic during initialization aborts the run (Go: a panicking
initializer kills the program before `main`), surfacing as the abort
step's `Stop.panic` (message
unmarked — it is the Go-observable abort). Diagnostic errors carry the
`package init:` marker (`markInitPhase`). -/
def runPkgInitM (fuel : Nat) (state : ExecState) (choices : Choices) :
    Except Stop (ExecState × Choices) := do
  match findFunctionIn? state.functions pkgInitFuncId with
  | none => return (state, choices)
  | some initF =>
      if initF.args.size != 0 || initF.results.size != 0 then
        throw (.stuck s!"malformed {pkgInitFuncId.key}: expected no parameters and no results")
      match runInitConfig fuel state (.exec initF.body [] (.frame [] [] [] [] .stop)) choices with
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
def runProgramSetupM (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (choices : Choices := []) :
    Except Stop (Config × ExecState × List Loc × Choices) := do
  let func ←
    match findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  -- The reserved-prefix clause of the table's acceptance (C2 §2; audit
  -- fix R2): `runtimeErrorTypeIdx = 1` is a CONSTANT of the machine,
  -- so a table whose index 1 is not the runtime-error payload type
  -- would render a user value at that index as a runtime-error abort.
  -- The decoder constructs the prefix; a hand-built `Program` is
  -- refused here BY NAME before any step runs.
  if program.typeDefs.hasReservedPrefix then pure () else
    throw (.internal s!"program type table does not lead with the two machine-reserved entries ({emptyStructTypeId.key} at index 0, {runtimeErrorTypeId.key} at index 1): TypeEnv.hasReservedPrefix fails on a {program.typeDefs.size}-entry table — prepend TypeEnv.reserved (C2 acceptance clause)")
  let state : ExecState :=
    { types := program.typeDefs, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets
      typeDisplays := program.typeDisplays }
  let s₀ ← seedGlobals state program.globals
  if StateWf s₀ then pure () else
    throw (.internal "seeded state ill-formed: a location in a global cell or function body dangles beyond the allocator bound")
  let (s₁, choices₁) ← runPkgInitM fuel s₀ choices
  let (env, s₂) ← bindParams [] s₁ func.args.toList args.toList
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  return (c₀, s₃, resultLocs, choices₁)

@[inherit_doc runProgramSetupM]
def runProgramM (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (choices : Choices := []) : Except Stop Readout := do
  let (c₀, s₃, resultLocs, choices₁) ← runProgramSetupM fuel program name args choices
  let (sF, _) ← runConfig fuel s₃ c₀ choices₁
  return { values := (← loadMany sF resultLocs).toArray }

def runProgramIntsM (fuel : Nat) (program : Program) (name : String)
    (args : Array Int) (choices : List Nat := []) : Except Stop Readout :=
  runProgramM fuel program name (args.map GoValue.int) choices

end GoLean.GoCore.Machine
