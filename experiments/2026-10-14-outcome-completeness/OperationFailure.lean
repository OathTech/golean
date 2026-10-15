import OperationCheck

namespace GoLean.GoCore.Relational.C1
open Machine
open OperationCheck

namespace FailureChecks

/-- The common statement operations use their existing validate/commit
contracts. Choiceful operations expose their consult between the checks
that precede and follow it, rather than consulting a projection in advance. -/
def statementOperation (ctx : ProgramCtx) (s : Store) (op : StmtOp)
    (vs : List GoValue) : OperationCheck :=
  match op with
  | .appendSlice elem =>
    match vs with
    | [tv, sliceV, elemsV] =>
      afterDelivered (valueAsSlice sliceV) fun slice =>
      afterDelivered (valueAsSlice elemsV) fun elems =>
      afterDelivered (validateSlice slice) fun _ =>
      afterDelivered (validateSlice elems) fun _ =>
      afterDelivered (Mem.loadSlice ctx s elems) fun (elemValues, trE) =>
      let newLen := slice.len + elemValues.size
      afterDelivered (valueAsLoc tv) fun tloc =>
      if newLen ≤ slice.cap then
        committed s (.ok fun current => do
          let (current, trW) ← Mem.storeRun ctx current slice slice.len elemValues.toList
          let (current, trT) ← Mem.store ctx current tloc (.slice { slice with len := newLen })
          return (current, trE ++ trW ++ trT))
      else
        afterDelivered (tySizeBytes ctx.types elem) fun elemSize =>
        if newLen ≥ intExclusiveUpperBound || newLen * elemSize > maxAllocBytes then .passed
        else afterDelivered (Mem.loadSlice ctx s slice) fun (oldValues, trO) =>
          let width := appendSpillWidth slice.cap newLen
          .consult .appendSpill width fun extra =>
            let newCap := newLen + ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            afterDelivered (buildAppendBackingValue ctx elem oldValues elemValues newCap) fun backing =>
              committed s (.ok fun current => do
                let (base, current) ← Store.alloc ctx current backing (.array newCap elem)
                let (current, trT) ← Mem.store ctx current tloc
                  (.slice { base := some base, offset := 0, len := newLen, cap := newCap })
                return (current, trE ++ trO ++ trT))
    | _ => .failed (.stuck "malformed appendSlice operands")
  | .randIntn =>
    match vs with
    | [tv, .int n .int] =>
      afterDelivered (valueAsLoc tv) fun tloc =>
      if n < 1 then .failed (.stuck s!"rand-intn: bound {n} ≤ 0 reached the draw (the lowering's guard was bypassed — forged wire)")
      else .consult .intn n.toNat fun pick =>
        committed s (.ok fun current => do
          let (current, trace) ← Mem.store ctx current tloc (.int pick .int)
          return (current, trace))
    | [.int n .int] =>
      if n < 1 then .failed (.stuck s!"rand-intn: bound {n} ≤ 0 reached the draw (the lowering's guard was bypassed — forged wire)")
      else .consult .intn n.toNat fun _ => .passed
    | _ => .failed (.stuck "malformed rand-intn operands (expected [target address,] an int bound)")
  | op => committed s (applyStmtOpCore.plan ctx s op vs)

/-- Conversion validation consults capacity only after the operand check. -/
def strict (ctx : ProgramCtx) (s : Store) (leaf : Loc → Loc)
    (op : StrictOp) (vs : List GoValue) : OperationCheck :=
  match op.convKind? with
  | none => delivered (applyStrictOp ctx s leaf op vs)
  | some (kind, literal) =>
    match convOperand? vs with
    | none => delivered (convRefuse kind vs)
    | some value => .consult .convCap (convCapWidth kind literal value) fun pick =>
        delivered (convCapApplyAt ctx s kind literal value pick)

/-- Frame activation failures precede the optional nil-method panic-text
consultation. A recovered activation panic has no ordinary failure. -/
def activation (ctx : ProgramCtx) (s : Store) (fid : FuncId) (args : List GoValue) :
    OperationCheck := committed s (enterFrame.plan ctx s fid args)

/-- Try-lock validates the address and synchronization cell before selecting;
the selected operation can still fail on arbitrary supplied stores. -/
def synchronization (ctx : ProgramCtx) (s : Store) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : OperationCheck :=
  match op.tryTargets?, vs with
  | some targets, [av] =>
    afterDelivered (valueAsLoc av) fun loc =>
    afterDelivered (syncCell ctx s loc) fun pre =>
    .consult .tryLock (tryLockWidth op pre) fun pick =>
      delivered (applyTryLock ctx s op loc pre (pick == 1) targets env k)
  | some _, vs => .failed (.stuck s!"malformed try-lock application: {repr op} on {vs.length} operand(s)")
  | none, _ => delivered (applySyncOpCore ctx s op vs env k)

def select (ctx : ProgramCtx) (s : Store) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (vs : List GoValue) (env : LocalEnv) (k : Cont) : OperationCheck :=
  afterDelivered (applySelectCore ctx s clauses default? vs env k) fun result =>
  match result with
  | .done .. => .passed
  | .picks _ commits => .consult .l2Entry commits.length fun pick =>
    match commits[pick]? with
    | some _ => .passed
    | none => .failed (.internal "select ready-clause pick out of range")

/-- Validation of a live map traversal and the selected binding. In particular,
the stop alternative does not validate a binding that it never performs. -/
def mapIteration (ctx : ProgramCtx) (s : Store) (keyVar valVar : Option VarId)
    (keyTy valTy : Ty) (base : Option Loc) (produced : Array Nat) (start : Array Nat)
    (env : LocalEnv) : OperationCheck :=
  after (mapIterCandidates ctx s keyTy valTy base produced) fun (cands, _) =>
  if cands.isEmpty then .passed
  else
    let width := cands.size + (if mapIterMandatoryRemains cands start then 0 else 1)
    .consult .mapIter width fun pick =>
      match cands[pick]? with
      | none => .passed
      | some (_, key, value) => validate
          (bindIterVars ctx env.pushScope s keyVar valVar keyTy valTy key value)

def frameExit (ctx : ProgramCtx) (s : Store) (targets : List (TargetShape × List Expr))
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k : Cont) : OperationCheck :=
  match targets, results, ds with
  | [], [], [] => .passed
  | [], loc :: locs, [] =>
    match k, locs with
    | .preprintK .., [] => validate (Mem.loadBinding ctx s loc)
    | _, _ => after (loadResults ctx s (loc :: locs)) fun _ =>
        .failed (.stuck "extra GoCore assignment value")
  | (_, _ :: _) :: _, _, [] => validate (loadResults ctx s results)
  | (_, []) :: _, _, [] => .failed (.internal "malformed call target plan")
  | _, _, (cv, args) :: _ =>
    match cv with
    | .funcVal fid captured => activation ctx s fid (captured ++ args)
    | .nil => .passed
    | other => .failed (.stuck s!"deferred callee is not a function value: {repr other}")

def unseqEntry (ctx : ProgramCtx) (s : Store) (g : UnseqGraph)
    (env : LocalEnv) (k : Cont) : OperationCheck :=
  match k with
  | .seq _ kenv _ =>
    if kenv = env then
      match g.wellFormed? with
      | some msg => .failed (.stuck s!"unseq: malformed graph — {msg}")
      | none => match unseqEntryCheck? g env with
        | some msg => .failed (.stuck s!"unseq: malformed graph at entry — {msg}")
        | none => validate (allocDecls ctx env.pushScope s g.cells)
    else .failed (.internal "unseq under foreign-scope sequence")
  | _ => .failed (.stuck "GoCore unseq outside a statement sequence")

def unseqNext (ctx : ProgramCtx) (s : Store) (g : UnseqGraph) (thenB : Stmt)
    (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv)
    (phase : UnseqPhase) : OperationCheck :=
  match phase with
  | .pick =>
    match g.skippedDep? st with
    | some msg => .failed (.stuck msg)
    | none =>
      if g.allSettled st then
        match g.unproducedConsumer? st thenB with
        | some msg => .failed (.stuck msg)
        | none => validate (unseqStorePlan ctx s env tg g.stores)
      else .consult .unseqNext (g.ready st).length fun pick =>
        match (g.ready st)[pick]? with
        | some _ => .passed
        | none => .failed (.stuck "unseq: malformed graph — pending active work with no ready occurrence")
  | .run i =>
    match g.occs[i]? with
    | none => .failed (.internal s!"unseq: running occurrence {i} outside the graph")
    | some o => match o.body with
      | .eval .. | .invoke .. | .recv .. | .allocate .. | .wide .. => .passed
      | .load bind tgt => committed s (unseqLoad.plan ctx s env tg bind tgt)
      | .target _ lhs => validate (unseqTargetPlan ctx s env lhs)
      | .guard test w out => validate (unseqGuard ctx s g env st i test w out)
  | .wait i =>
    match g.occs[i]? with
    | none => .failed (.internal s!"unseq: awaited occurrence {i} outside the graph")
    | some o => match o.body with
      | .invoke .. | .recv .. | .allocate .. | .wide .. => .passed
      | _ => .failed (.internal "unseq: statement completion delivered for a value-producing occurrence")

def unseqValue (ctx : ProgramCtx) (s : Store) (v : GoValue) (g : UnseqGraph)
    (env : LocalEnv) (phase : UnseqPhase) : OperationCheck :=
  match phase with
  | .wait i =>
    match g.occs[i]? with
    | none => .failed (.internal s!"unseq: awaited occurrence {i} outside the graph")
    | some o => match o.body with
      | .eval bind _ => after (unseqCellLoc env bind) fun loc => validate (Mem.store ctx s loc v)
      | _ => .failed (.internal "unseq: value delivered for an occurrence whose body is not a value head")
  | _ => .failed (.internal "unseq: value delivered to the sweep frame outside a running occurrence")

def preprintValue (v : GoValue) (k : Cont) : OperationCheck :=
  match k with
  | .preprintK .. => match v with
    | .string _ => .passed
    | other => .failed (.stuck s!"preprint: the payload method returned a non-string result {repr other}")
  | _ => .failed (.internal "value delivered to statement continuation")

def preprintNext (ctx : ProgramCtx) (s : Store) (k : Cont) : OperationCheck :=
  match k with
  | .preprintK _ entry _ _ => delivered (preprintDispatch ctx s entry)
  | _ => .failed (.internal "completion delivered to expression continuation")

def statement (ctx : ProgramCtx) (s : Store) (stmt : Stmt) (env : LocalEnv)
    (k : Cont) : OperationCheck :=
  match stmt with
  | .seqn .. | .ifThenElse .. | .while .. | .returnStmt | .breakStmt | .continueStmt
    | .inertLabel .. | .labeled .. | .breakTo .. | .continueTo .. | .breakable ..
    | .deferCall .. | .panicStmt .. | .callValue .. | .mapRange ..
    | .chanSend .. | .closeChan .. | .goStmt .. | .selectStmt .. | .unseqProbe .. =>
    -- Value calls validate their target plans before evaluating the callee.
    match stmt with
    | .callValue targets _ _ => match targetsPlan targets.toList with
      | some _ => .passed
      | none => .failed (.unsupported "unsupported value-call target assignee")
    | _ => .passed
  | .block decls _ => validate (allocDecls ctx env.pushScope s decls.toList)
  | .assign lhs _ => match targetPlan lhs with
    | some (_, _ :: _) => .passed
    | some (_, []) => .failed (.internal "malformed assignment target plan")
    | none => match lhs with
      | .unsupported feature => .failed (.unsupported feature)
      | _ => .failed (.stuck "unclassified assignee")
  | .call targets fid args => match targetsPlan targets.toList with
    | none => .failed (.unsupported "unsupported call target assignee")
    | some _ => match args.toList with
      | [] => activation ctx s fid []
      | _ :: _ => .passed
  | .chanRecv targets ch elem => match chanPlan (.chanRecv targets ch elem) with
    | some (_, _ :: _) => .passed
    | some (_, []) => .failed (.internal "empty channel-receive operand plan")
    | none => if targets.size > 2 then .failed (.stuck s!"channel receive with {targets.size} targets")
      else .failed (.unsupported "unsupported channel-receive target assignee")
  | .unsupported feature => .failed (.unsupported feature)
  | .mapLookup t okT _ _ _ _ =>
    match targetsPlan [t, okT] with
    | some ((_, _ :: _) :: _) => .passed
    | some _ => .failed (.internal "malformed comma-ok target plan")
    | none => .failed (.unsupported "unsupported statement target assignee")
  | .typeAssert t okT _ _ =>
    match targetsPlan [t, okT] with
    | some ((_, _ :: _) :: _) => .passed
    | some _ => .failed (.internal "malformed comma-ok target plan")
    | none => .failed (.unsupported "unsupported statement target assignee")
  | .assignMany left right =>
    if left.size = right.size then match targetsPlan left.toList with
      | some ((_, _ :: _) :: _) => .passed
      | some _ => .failed (.stuck "malformed multi-assignment target plan")
      | none => .failed (.unsupported "unsupported multi-assignment target assignee")
    else .failed (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}")
  | .syncStmt op args targets => match syncPlan (.syncStmt op args targets) with
    | some (_, _ :: _) => .passed
    | some (_, []) => .failed (.internal "empty sync-statement operand plan")
    | none => .failed (.unsupported "malformed sync-statement shape (arity/targets)")
  | .atomicStmt op kind args targets => match atomicPlan (.atomicStmt op kind args targets) with
    | some (_, _ :: _) => .passed
    | some (_, []) => .failed (.internal "empty atomic-statement operand plan")
    | none => .failed (.unsupported "malformed atomic-statement shape (arity/kind/targets)")
  | .unseq g _ => unseqEntry ctx s g env k
  | wide => match stmtPlan wide with
    | some (_, _, _ :: _) => .passed
    | some (_, _, []) => .failed (.internal "empty statement operand plan")
    | none => .failed (.unsupported "unsupported statement target assignee")

def expression (ctx : ProgramCtx) (s : Store) (e : Expr) (env : LocalEnv)
    (k : Cont) : OperationCheck :=
  match e with
  | .var id => match LocalEnv.lookup env id with
    | none => .failed (.stuck s!"unbound GoCore variable address: {id}")
    | some loc => validate (Mem.loadBindingFor ctx s loc (projChainTarget ctx s k loc))
  | .ref id => match LocalEnv.lookup env id with
    | none => .failed (.stuck s!"unbound GoCore variable address: {id}")
    | some _ => .passed
  | .global gid => if gid < s.heap.size then .passed
    else .failed (.stuck s!"global {gid} out of range: the heap has {s.heap.size} cell(s)")
  | .intLit .. | .boolLit .. | .stringLit .. | .and .. | .or .. | .recoverCall => .passed
  | .unsupported feature => .failed (.unsupported feature)
  | e => match strictPlan e with
    | some (_, _ :: _) => .passed
    | some (op, []) => delivered (applyStrictOp ctx s (projChainTarget ctx s k) op [])
    | none => .failed (.stuck "unclassified expression")

def returned (ctx : ProgramCtx) (s : Store) (v : GoValue) (k : Cont) : OperationCheck :=
  match k with
  | .strictK op done pending _ k' => match pending with
    | [] => strict ctx s (projChainTarget ctx s k') op (v :: done).reverse
    | _ :: _ => .passed
  | .andK .. | .orK .. | .boolK .. | .ifK .. | .whileK .. => validate (valueAsBool v)
  | .callArgsK fid _ vals pending _ _ => match pending with
    | [] => activation ctx s fid (vals ++ [v])
    | _ :: _ => .passed
  | .stmtOpK op nt done pending _ _ => match pending with
    | [] => statementOperation ctx s op (v :: done).reverse
    | _ :: _ => if done.length < nt then delivered (valueAsLoc v) else .passed
  | .callValCalleeK _ args _ _ => match v, args with
    | .funcVal fid captured, [] => activation ctx s fid captured
    | .nil, [] => .passed
    | cv, _ :: _ => if deferrableCallee cv then .passed
      else .failed (.stuck s!"expected function value, got {repr cv}")
    | other, [] => .failed (.stuck s!"expected function value, got {repr other}")
  | .callValArgsK cv _ vals pending _ _ => match pending with
    | _ :: _ => .passed
    | [] => match cv with
      | .funcVal fid captured => activation ctx s fid (captured ++ vals ++ [v])
      | .nil => .passed
      | other => .failed (.stuck s!"expected function value, got {repr other}")
  | .deferCalleeK args _ k' =>
    if deferrableCallee v then match args with
      | _ :: _ => .passed
      | [] => match pushDefer (v, []) k' with
        | some _ => .passed
        | none => .failed (.stuck "defer outside a call frame")
    else .failed (.stuck s!"expected function value in defer, got {repr v}")
  | .deferArgsK cv vals pending _ k' => match pending with
    | _ :: _ => .passed
    | [] => match pushDefer (cv, vals ++ [v]) k' with
      | some _ => .passed
      | none => .failed (.stuck "defer outside a call frame")
  | .mapRangeK .. => validate (mapRangeStartSets s v)
  | .panicArgK .. | .probeK .. => .passed
  | .chanStK op done pending env k' => match pending with
    | _ :: _ => .passed
    | [] => delivered (applyChanOp ctx s op (v :: done).reverse env k')
  | .selectOpsK clauses default? done pending env k' => match pending with
    | _ :: _ => .passed
    | [] => select ctx s clauses default? (v :: done).reverse env k'
  | .tgtOpK sh ops pending _ targets _ _ _ _ _ _ => match pending with
    | _ :: _ => .passed
    | [] => match completeTargetRef sh (v :: ops).reverse with
      | none => .failed (.internal "malformed receive target operands")
      | some _ => match targets with
        | (_, []) :: _ => .failed (.internal "malformed receive target plan")
        | _ => .passed
  | .rhsK op _ done pending _ _ _ => match pending with
    | _ :: _ => .passed
    | [] => delivered (applyRhsOp ctx s op (v :: done).reverse)
  | .goCalleeK args _ _ =>
    if deferrableCallee v then match args with
      | _ :: _ => .passed
      | [] => .failed (.unsupported "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)")
    else .failed (.stuck s!"expected function value in go statement, got {repr v}")
  | .goArgsK _ _ pending _ _ => match pending with
    | _ :: _ => .passed
    | [] => .failed (.unsupported "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)")
  | .syncStK op done pending env k' => match pending with
    | _ :: _ => .passed
    | [] => synchronization ctx s op (v :: done).reverse env k'
  | .atomicStK op done pending env k' => match pending with
    | _ :: _ => .passed
    | [] => delivered (applyAtomicOp ctx s op (v :: done).reverse env k')
  | .unseqK g _ _ _ env phase _ => unseqValue ctx s v g env phase
  | .stop => .failed (.internal "value delivered to empty continuation")
  | k => preprintValue v k

def next (ctx : ProgramCtx) (s : Store) (k : Cont) : OperationCheck :=
  match k with
  | .stop => .failed (.internal "step on terminal configuration")
  | .seq .. | .loop .. | .panicResumeK .. | .breakableK .. | .labelK .. => .passed
  | .frame targets _ results ds k' _ => frameExit ctx s targets results ds k'
  | .mapIterK kv vv kt vt _ base produced start env _ =>
      mapIteration ctx s kv vv kt vt base produced start env
  | .storeK refs vals _ _ _ => match refs, vals with
    | ref :: _, val :: _ => committed s (storeTarget.plan ctx s ref val)
    | [], [] => .passed
    | _, _ => .failed (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)")
  | .unseqK g thenB st tg env phase _ => unseqNext ctx s g thenB st tg env phase
  | k => preprintNext ctx s k

/-- Panic rendering is a separate terminal boundary. This check has no
ordinary alternative at a settled abort; its bridge excludes those states. -/
def panicking (ctx : ProgramCtx) (s : Store) (chain : List PanicEntry)
    (k : Cont) : OperationCheck :=
  match k with
  | .frame _ _ _ [] _ _ => .passed
  | .frame _ _ _ ((cv, args) :: _) _ _ => match cv with
    | .funcVal fid captured => activation ctx s fid (captured ++ args)
    | .nil => .passed
    | other => .failed (.stuck s!"deferred callee is not a function value: {repr other}")
  | .panicResumeK .. | .probeK .. => .passed
  | .stop => match chain with
    | [] => .failed (.internal "empty panic chain at stop")
    | _ :: _ => .passed
  | k => match panicPassthrough k with
    | some _ => .passed
    | none => .failed (panicUnwindStop ctx chain k)

def atState (ctx : ProgramCtx) (a : State) : OperationCheck :=
  match a.control with
  | .exec stmt env k => statement ctx a.store stmt env k
  | .evalE e env k => expression ctx a.store e env k
  | .retV v k => returned ctx a.store v k
  | .next k => next ctx a.store k
  | .panicking chain k => panicking ctx a.store chain k
  | .signal sg k => match signalStep sg k with
    | some _ => .passed
    | none => match sg, k with
      | .ret, .frame targets _ results ds k' _ => frameExit ctx a.store targets results ds k'
      | _, _ => .failed (signalRefusal sg k)
  | .blockedSend .. | .blockedRecv .. | .blockedSelect .. | .blockedSync .. => .passed

end FailureChecks
end GoLean.GoCore.Relational.C1
