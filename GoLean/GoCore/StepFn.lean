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
which the driver reports as `Stop.panic`; only out-of-model conditions
are `Except` errors. Every apply/entry arm is "apply, then deliver"
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

/-- One machine step. `.ok` is a step the relation permits (including
steps *to* `.panicked`); `.error` means the machine is stuck here, with
the reason. Never call on a terminal configuration (the driver guards). -/
def stepFn (s : ExecState) (c : Config) (choices : Choices) :
    Except Stop (Config × ExecState × Choices) := do
  match c with
  | .panicked _ => throw (.internal "step on terminal panicked configuration")
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
      | .returnStmt => return (.returning k, s, choices)
      | .breakStmt => return (.breaking k, s, choices)
      | .continueStmt => return (.continuing k, s, choices)
      | .inertLabel _ => return (.next k, s, choices)
      | .labeled name b => return (.exec b env (.labelK name k), s, choices)
      | .breakTo name => return (.breakingTo name k, s, choices)
      | .continueTo name => return (.continuingTo name k, s, choices)
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
      | .frame [] _ [] [] k' _ => return (.next k', s, choices)
      | .frame [] _ (rl :: rls) [] _ _ => do
          -- Targetless frame with pinned results: the frontend always
          -- supplies targets for result-bearing calls; stuck-closed as
          -- before the BUG-025 migration (the old storeMany [] (v::vs)
          -- refusal), after the same result read.
          let _ ← loadMany s (rl :: rls)
          throw (.stuck "extra GoCore assignment value")
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          -- BUG-025 + the BUG-052 order pin: read the pinned results,
          -- then evaluate the caller-target operands POST-CALL through
          -- the tgtOpK spine (the POST-CALL point is gc's realized
          -- order — the pin covers only the call-vs-operand axis; the
          -- spine's left-to-right INTER-TARGET walk is our spec-legal
          -- realization of an axis left OPEN, per the rule-site
          -- latitude block), then the per-target storeK stores.
          let vs ← loadMany s results
          return (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, choices)
      | .frame ((_, []) :: _) _ _ [] _ _ =>
          throw (.internal "malformed call target plan")
      | .frame targets tenv results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured => do
              -- A deferred call's results are DISCARDED (Go); only effects
              -- matter, so the inner frame reads and stores nothing. An
              -- ENTRY panic is the invocation's panic: it starts unwinding
              -- at this frame with its remaining defers (audit F1+F5,
              -- mirroring the .nil arm below).
              let (r, ch') ← enterFramePick s fid (captured ++ args) choices
              return deliverS s (.frame targets tenv results ds k' w) ch'
                (fun (func, frameEnv, _, s') =>
                  (.exec func.body frameEnv
                    (.frame [] [] [] [] (.frame targets tenv results ds k' w) func.wrapper),
                    s', ch')) r
          | .nil =>
              -- Registration succeeded; the INVOCATION panics (Go), and
              -- this frame's remaining defers run on the panic path.
              return (.panicking [panicEntry nilDerefPanicText]
                (.frame targets tenv results ds k' w), s, choices)
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
  | .breaking k =>
      match k with
      | .seq _ _ k' => return (.breaking k', s, choices)
      | .loop _ _ _ k' => return (.next k', s, choices)
      | .breakableK k' => return (.next k', s, choices)
      | .labelK _ k' => return (.breaking k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.next k', s, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with break")
      | .stop => throw (.stuck "break outside loop")
      | _ => throw (.internal "break delivered to expression continuation")
  | .continuing k =>
      match k with
      | .seq _ _ k' => return (.continuing k', s, choices)
      | .breakableK k' => return (.continuing k', s, choices)
      | .labelK _ k' => return (.continuing k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          return (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), s, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with continue")
      | .stop => throw (.stuck "continue outside loop")
      | _ => throw (.internal "continue delivered to expression continuation")
  | .returning k =>
      match k with
      | .seq _ _ k' => return (.returning k', s, choices)
      | .breakableK k' => return (.returning k', s, choices)
      | .labelK _ k' => return (.returning k', s, choices)
      | .loop _ _ _ k' => return (.returning k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.returning k', s, choices)
      | .frame [] _ [] [] k' _ => return (.next k', s, choices)
      | .frame [] _ (rl :: rls) [] _ _ => do
          -- Targetless frame with pinned results: the frontend always
          -- supplies targets for result-bearing calls; stuck-closed as
          -- before the BUG-025 migration (the old storeMany [] (v::vs)
          -- refusal), after the same result read.
          let _ ← loadMany s (rl :: rls)
          throw (.stuck "extra GoCore assignment value")
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          -- BUG-025 + the BUG-052 order pin: read the pinned results,
          -- then evaluate the caller-target operands POST-CALL through
          -- the tgtOpK spine (the POST-CALL point is gc's realized
          -- order — the pin covers only the call-vs-operand axis; the
          -- spine's left-to-right INTER-TARGET walk is our spec-legal
          -- realization of an axis left OPEN, per the rule-site
          -- latitude block), then the per-target storeK stores.
          let vs ← loadMany s results
          return (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, choices)
      | .frame ((_, []) :: _) _ _ [] _ _ =>
          throw (.internal "malformed call target plan")
      | .frame targets tenv results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured => do
              -- A deferred call's results are DISCARDED (Go); only effects
              -- matter, so the inner frame reads and stores nothing. An
              -- ENTRY panic is the invocation's panic: it starts unwinding
              -- at this frame with its remaining defers (audit F1+F5,
              -- mirroring the .nil arm below).
              let (r, ch') ← enterFramePick s fid (captured ++ args) choices
              return deliverS s (.frame targets tenv results ds k' w) ch'
                (fun (func, frameEnv, _, s') =>
                  (.exec func.body frameEnv
                    (.frame [] [] [] [] (.frame targets tenv results ds k' w) func.wrapper),
                    s', ch')) r
          | .nil =>
              -- Registration succeeded; the INVOCATION panics (Go), and
              -- this frame's remaining defers run on the panic path.
              return (.panicking [panicEntry nilDerefPanicText]
                (.frame targets tenv results ds k' w), s, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .stop => throw (.internal "return unwound past the entry frame")
      | _ => throw (.internal "return delivered to expression continuation")
  | .breakingTo L k =>
      match k with
      | .seq _ _ k' => return (.breakingTo L k', s, choices)
      | .loop _ _ _ k' => return (.breakingTo L k', s, choices)
      | .breakableK k' => return (.breakingTo L k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.breakingTo L k', s, choices)
      | .labelK name k' =>
          if name = L then return (.next k', s, choices)
          else return (.breakingTo L k', s, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with labeled break")
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
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          if contHeadLabel k' = some L then
            return (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), s, choices)
          else return (.continuingTo L k', s, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with labeled continue")
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
  -- The registry-op completion marker's STRIP (W3.2 slice 1 stage C,
  -- B1; rule `Step.opDoneStrip`): one pure control step to the wrapped
  -- successor. It runs on BOTH drivers identically — sequential runs
  -- of completing chan/sync/select ops carry the marker too (emitted
  -- by the applies in Machine.lean), which is what keeps
  -- `execProg_single_eq_execStmt` step-for-step at shifted-but-equal
  -- fuel. The marker's boundary/scheduling meaning is pool-only
  -- (`Config.atBoundary`; envelope statement at `Config.opDone`).
  | .opDone _ c => return (c, s, choices)
  -- A parked sync op with no sibling goroutine IS the deadlocked run
  -- (probes p06-p08: gc's detector fires on a single goroutine parked
  -- in Lock/Wait/Do) — the channel blocked shapes' classification.
  | .blockedSync _ _ _ _ => throw .deadlock

/-- Fuel-bounded iteration of `stepFn` to a terminal configuration. Fuel
counts machine steps; the terminal check precedes the fuel check so a
finished program never reports exhaustion. `.panicked` reports as
`Stop.panic` — the same classification surface as the big-step
interpreter's. -/
def runConfig : Nat → ExecState → Config → Choices → Except Stop (ExecState × Choices)
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
of `stepFn` from a bare statement configuration, classified into the old
big-step `ExecOutcome` at the four unwound terminals. NOT a shim — no
big-step rule appears here; the name and result shape are kept so Surface
statements stay recognizable. Fuel counts machine steps. The `env`
argument replaces the old `ExecState.locals` seeding (deleted at S4 —
env-in-config is the only name-resolution story). -/
def execStmtLoop : Nat → ExecState → Config → Choices →
    Except Stop (ExecOutcome × Choices)
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
      | .blockedSync _ _ _ _ => throw .deadlock
      | c =>
          match fuel with
          | 0 => throw .fuelOut
          | fuel + 1 => do
              let (c', σ', choices') ← stepFn σ c choices
              execStmtLoop fuel σ' c' choices'

@[inherit_doc execStmtLoop]
def execStmt (fuel : Nat) (env : LocalEnv) (σ : ExecState) (choices : Choices)
    (prog : Stmt) : Except Stop (ExecOutcome × Choices) :=
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
      | .panicked msg => throw (.panic msg)
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
initializer kills the program before `main`), surfacing through
`runConfig`'s `.panicked` terminal as `Stop.panic` (message
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
  let state : ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets }
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
