import GoLeanProofs.FastEval.Shared
import GoLeanProofs.FastEval.Iter

/-!
# FastEval — `stepFast` (campaign Arc 2, U4): the per-step mirror

The arm-for-arm mirror of `stepFn` (`GoLean/GoCore/StepFn.lean`),
UNTRUSTED METHOD — never in any statement closure. Two stub classes,
both fail-closed:

- `fastEval-stub:` — arms the witness run does not exercise (probe D
  census, `docs/campaign-arc2-probes/records/probeD-armcensus.out`):
  the whole `.panicking` head, panic/chan/select/go machinery. These
  are PERMANENT for this route (one-directional refinement — their
  sim cases are vacuous).
- `fastEval-WIRE:` — arms awaiting the wave modules
  (Values/Stores/Frames); each names the helper it will call. A WIRE
  stub that survives integration is a defect, not a narrowing — the
  mid-build gate's compiled pre-check would hit it loudly.

The sim `stepFast_ok` is the per-step one-directional refinement that
`iterF_ok` (Iter.lean) lifts to runs.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- `enterFrameStep`, fast (wired at integration to `enterFrameF`). -/
def enterFrameStepF (σF : ExecStateF) (_fid : FuncId) (_args : List GoValue)
    (_mk : Func → LocalEnv → List Loc → Config) (_k : Cont)
    (_choices : Choices) : Except GoError (Config × ExecStateF × Choices) :=
  let _ := σF
  stuck "fastEval-WIRE: enterFrameStep/enterFrameF"

/-- One fast machine step — `stepFn`'s mirror. -/
def stepFast (σF : ExecStateF) (c : Config) (choices : Choices) :
    Except GoError (Config × ExecStateF × Choices) := do
  match c with
  | .panicked _ => throw (.internal "step on terminal panicked configuration")
  | .panicking _ _ => stuck "fastEval-stub: panicking head"
  | .exec stmt env k =>
      match stmt with
      | .seqn ss => return (.next (seqCont ss.toList env k), σF, choices)
      | .block decls ss =>
          stuck "fastEval-WIRE: allocDecls (block)"
      | .initialization p =>
          match k with
          | .seq rest kenv k' =>
              if kenv = env then do
                let v ← defaultValue (γF σF) p.typ
                let (loc, σF') := allocF σF v (some p.typ)
                return (.next (.seq rest (env.declare p.id loc) k'), σF', choices)
              else throw (.internal "initialization under foreign-scope sequence")
          | _ => throw (.stuck "GoCore initialization outside a statement sequence")
      | .assign lhs rhs =>
          match targetPlan lhs with
          | some (sh, e :: ops) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), σF, choices)
          | some (_, []) => throw (.internal "malformed assignment target plan")
          | none =>
              match lhs with
              | .unsupported feature => throw (.unsupported feature)
              | _ => throw (.internal "unclassified assignee")
      | .ifThenElse c t e => return (.evalE c env (.ifK t e env k), σF, choices)
      | .while c b => return (.evalE c env (.whileK c b env k), σF, choices)
      | .returnStmt => return (.returning k, σF, choices)
      | .breakStmt => return (.breaking k, σF, choices)
      | .continueStmt => return (.continuing k, σF, choices)
      | .label _ => return (.next k, σF, choices)
      | .labeled name b => return (.exec b env (.labelK name k), σF, choices)
      | .breakTo name => return (.breakingTo name k, σF, choices)
      | .continueTo name => return (.continuingTo name k, σF, choices)
      | .breakable b => return (.exec b env (.breakableK k), σF, choices)
      | .deferCall callee args =>
          return (.evalE callee env (.deferCalleeK args.toList env k), σF, choices)
      | .panicStmt _ => stuck "fastEval-stub: panicStmt"
      | .callValue targets callee args =>
          match targetsPlan targets.toList with
          | some plans =>
              return (.evalE callee env (.callValCalleeK plans args.toList env k), σF, choices)
          | none => throw (.unsupported "unsupported value-call target assignee")
      | .call targets fid args =>
          match targetsPlan targets.toList with
          | some plans =>
              match args.toList with
              | a :: rest =>
                  return (.evalE a env (.callArgsK fid plans [] rest env k), σF, choices)
              | [] =>
                  enterFrameStepF σF fid []
                    (fun func frameEnv resultLocs =>
                      .exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper)) k choices
          | none => throw (.unsupported "unsupported call target assignee")
      | .mapRange keyVar valVar mapExpr keyTy valTy body =>
          return (.evalE mapExpr env
            (.mapRangeK keyVar valVar keyTy valTy body env k), σF, choices)
      | .chanSend _ _ _ => stuck "fastEval-stub: chanSend"
      | .closeChan _ => stuck "fastEval-stub: closeChan"
      | .chanRecv _ _ _ => stuck "fastEval-stub: chanRecv"
      | .goStmt _ _ => stuck "fastEval-stub: goStmt"
      | .selectStmt _ _ => stuck "fastEval-stub: selectStmt"
      | .unsupported feature => throw (.unsupported feature)
      | .mapLookup t okT base index keyTy valueTy =>
          match targetsPlan [t, okT] with
          | some ((sh, e :: ops) :: rest) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy)
                  [base, index] [] (.seqn #[]) env k), σF, choices)
          | some _ => throw (.internal "malformed comma-ok target plan")
          | none => throw (.unsupported "unsupported statement target assignee")
      | .typeAssert t okT expr targetTy =>
          match targetsPlan [t, okT] with
          | some ((sh, e :: ops) :: rest) =>
              return (.evalE e env
                (.tgtOpK sh [] ops [] rest (.typeAssert targetTy)
                  [expr] [] (.seqn #[]) env k), σF, choices)
          | some _ => throw (.internal "malformed comma-ok target plan")
          | none => throw (.unsupported "unsupported statement target assignee")
      | .assignMany left right =>
          if left.size = right.size then
            match targetsPlan left.toList with
            | some ((sh, e :: ops) :: rest) =>
                return (.evalE e env
                  (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), σF, choices)
            | some _ => throw (.stuck "malformed multi-assignment target plan")
            | none => throw (.unsupported "unsupported multi-assignment target assignee")
          else
            throw (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}")
      | .syncStmt op args targets =>
          match syncPlan (.syncStmt op args targets) with
          | some (sop, e :: rest) =>
              return (.evalE e env (.syncStK sop [] rest env k), σF, choices)
          | some (_, []) => throw (.internal "empty sync-statement operand plan")
          | none => throw (.unsupported "malformed sync-statement shape (arity/targets)")
      | wide =>
          match stmtPlan wide with
          | some (op, nt, e :: rest) =>
              return (.evalE e env (.stmtOpK op nt [] rest env k), σF, choices)
          | some (_, _, []) =>
              stuck "fastEval-WIRE: applyStmtOp (nullary wide statement)"
          | none => throw (.unsupported "unsupported statement target assignee")
  | .evalE e env k =>
      match e with
      | .var id =>
          match LocalEnv.lookup env id with
          | some loc => do return (.retV (← loadLocF σF loc) k, σF, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .intLit value kind =>
          return (.retV (.int (kind.normalize value) kind) k, σF, choices)
      | .boolLit value => return (.retV (.bool value) k, σF, choices)
      | .stringLit value => return (.retV (.string value) k, σF, choices)
      | .ref id =>
          match LocalEnv.lookup env id with
          | some loc => return (.retV (.addr loc) k, σF, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .locLit l => return (.retV (.addr l) k, σF, choices)
      | .and l r => return (.evalE l env (.andK r env k), σF, choices)
      | .or l r => return (.evalE l env (.orK r env k), σF, choices)
      | .recoverCall =>
          let (v, k') := recoverResult k
          return (.retV v k', σF, choices)
      | .unsupported feature => throw (.unsupported feature)
      | e =>
          match strictPlan e with
          | some (op, e₁ :: rest) =>
              return (.evalE e₁ env (.strictK op [] rest env k), σF, choices)
          | some (_, []) =>
              stuck "fastEval-WIRE: applyStrictOp (nullary)"
          | none => throw (.internal "unclassified expression")
  | .retV v k =>
      match k with
      | .strictK op done (e :: rest) env k' =>
          return (.evalE e env (.strictK op (v :: done) rest env k'), σF, choices)
      | .strictK _ _ [] _ _ =>
          stuck "fastEval-WIRE: applyStrictOp (apply)"
      | .andK r env k' => do
          if ← valueAsBool v then
            return (.evalE r env (.boolK k'), σF, choices)
          else
            return (.retV (.bool false) k', σF, choices)
      | .orK r env k' => do
          if ← valueAsBool v then
            return (.retV (.bool true) k', σF, choices)
          else
            return (.evalE r env (.boolK k'), σF, choices)
      | .boolK k' => do return (.retV (.bool (← valueAsBool v)) k', σF, choices)
      | .ifK t e env k' => do
          if ← valueAsBool v then
            return (.exec t env k', σF, choices)
          else
            return (.exec e env k', σF, choices)
      | .whileK c b env k' => do
          if ← valueAsBool v then
            return (.exec b env (.loop c b env k'), σF, choices)
          else
            return (.next k', σF, choices)
      | .callArgsK fid plans vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callArgsK fid plans (vals ++ [v]) rest env k'), σF, choices)
          | [] =>
              enterFrameStepF σF fid (vals ++ [v])
                (fun func frameEnv resultLocs =>
                  .exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper)) k' choices
      | .stmtOpK op nt done pending env k' =>
          match pending with
          | e :: rest =>
              if done.length < nt then
                match valueAsLoc v with
                | .error (.panic msg) =>
                    return (.panicking [⟨runtimeErrorValue msg, false⟩] k', σF, choices)
                | .error err => throw err
                | .ok _ =>
                    return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), σF, choices)
              else
                return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), σF, choices)
          | [] =>
              stuck "fastEval-WIRE: applyStmtOp + contAfterStmtOp"
      | .callValCalleeK plans args env k' =>
          match v, args with
          | .funcVal fid captured, [] =>
              enterFrameStepF σF fid captured
                (fun func frameEnv resultLocs =>
                  .exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper)) k' choices
          | .nil, [] =>
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                k', σF, choices)
          | cv, a :: rest =>
              if deferrableCallee cv then
                return (.evalE a env (.callValArgsK cv plans [] rest env k'), σF, choices)
              else throw (.stuck s!"expected function value, got {repr cv}")
          | other, [] => throw (.stuck s!"expected function value, got {repr other}")
      | .callValArgsK cv plans vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callValArgsK cv plans (vals ++ [v]) rest env k'), σF, choices)
          | [] =>
              match cv with
              | .funcVal fid captured =>
                  enterFrameStepF σF fid (captured ++ vals ++ [v])
                    (fun func frameEnv resultLocs =>
                      .exec func.body frameEnv (.frame plans env resultLocs [] k' func.wrapper)) k' choices
              | .nil =>
                  return (.panicking [⟨runtimeErrorValue
                    "runtime error: invalid memory address or nil pointer dereference", false⟩]
                    k', σF, choices)
              | other => throw (.stuck s!"expected function value, got {repr other}")
      | .deferCalleeK args env k' =>
          if deferrableCallee v then
            match args with
            | a :: rest =>
                return (.evalE a env (.deferArgsK v [] rest env k'), σF, choices)
            | [] =>
                match pushDefer (v, []) k' with
                | some k'' => return (.next k'', σF, choices)
                | none => throw (.stuck "defer outside a call frame")
          else throw (.stuck s!"expected function value in defer, got {repr v}")
      | .deferArgsK cv vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.deferArgsK cv (vals ++ [v]) rest env k'), σF, choices)
          | [] =>
              match pushDefer (cv, vals ++ [v]) k' with
              | some k'' => return (.next k'', σF, choices)
              | none => throw (.stuck "defer outside a call frame")
      | .mapRangeK _ _ _ _ _ _ _ =>
          stuck "fastEval-WIRE: mapRangeStartSets"
      | .panicArgK _ => stuck "fastEval-stub: panicArgK"
      | .chanStK _ _ _ _ _ => stuck "fastEval-stub: chanStK"
      | .selectOpsK _ _ _ _ _ _ => stuck "fastEval-stub: selectOpsK"
      | .tgtOpK sh ops pending refs targets rop rhs vals body env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env
                (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), σF, choices)
          | [] =>
              match completeTargetRef sh (v :: ops).reverse with
              | none => throw (.internal "malformed receive target operands")
              | some r =>
                  match targets with
                  | (sh', e :: ops') :: rest =>
                      return (.evalE e env
                        (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), σF, choices)
                  | (_, []) :: _ => throw (.internal "malformed receive target plan")
                  | [] =>
                      match rhs with
                      | e :: rest =>
                          return (.evalE e env
                            (.rhsK rop (refs ++ [r]) [] rest body env k'), σF, choices)
                      | [] =>
                          return (.next (.storeK (refs ++ [r]) vals body env k'), σF, choices)
      | .rhsK rop refs done pending body env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), σF, choices)
          | [] =>
              stuck "fastEval-WIRE: applyRhsOp"
      | .goCalleeK _ _ _ => stuck "fastEval-stub: goCalleeK"
      | .goArgsK _ _ _ _ _ => stuck "fastEval-stub: goArgsK"
      | .syncStK op done pending env k' =>
          match pending with
          | e :: rest =>
              return (.evalE e env (.syncStK op (v :: done) rest env k'), σF, choices)
          | [] =>
              stuck "fastEval-WIRE: applySyncOp"
      | .stop => throw (.internal "value delivered to empty continuation")
      | _ => throw (.internal "value delivered to statement continuation")
  | .next k =>
      match k with
      | .stop => throw (.internal "step on terminal configuration")
      | .seq (t :: rest) env k' => return (.exec t env (.seq rest env k'), σF, choices)
      | .seq [] _ k' => return (.next k', σF, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', σF, choices)
      | .frame [] _ [] [] k' _ => return (.next k', σF, choices)
      | .frame [] _ (rl :: rls) [] _ _ => do
          let _ ← loadManyF σF (rl :: rls)
          throw (.stuck "extra GoCore assignment value")
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          let vs ← loadManyF σF results
          return (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), σF, choices)
      | .frame ((_, []) :: _) _ _ [] _ _ =>
          throw (.internal "malformed call target plan")
      | .frame targets tenv results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured =>
              enterFrameStepF σF fid (captured ++ args)
                (fun func frameEnv _ =>
                  .exec func.body frameEnv
                    (.frame [] [] [] [] (.frame targets tenv results ds k' w) func.wrapper))
                (.frame targets tenv results ds k' w) choices
          | .nil =>
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                (.frame targets tenv results ds k' w), σF, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .panicResumeK chain k' =>
          if chainNewestRecovered chain then
            return (.next k', σF, choices)
          else
            return (.panicking chain k', σF, choices)
      | .breakableK k' => return (.next k', σF, choices)
      | .labelK _ k' => return (.next k', σF, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ _ =>
          stuck "fastEval-WIRE: mapIter tower"
      | .storeK refs vals body env k' =>
          match refs, vals with
          | _ :: _, _ :: _ =>
              stuck "fastEval-WIRE: storeTarget (storeK)"
          | [], [] => return (.exec body env k', σF, choices)
          | _, _ => throw (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)")
      | _ => throw (.internal "completion delivered to expression continuation")
  | .breaking k =>
      match k with
      | .seq _ _ k' => return (.breaking k', σF, choices)
      | .loop _ _ _ k' => return (.next k', σF, choices)
      | .breakableK k' => return (.next k', σF, choices)
      | .labelK _ k' => return (.breaking k', σF, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.next k', σF, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with break")
      | .stop => throw (.stuck "break outside loop")
      | _ => throw (.internal "break delivered to expression continuation")
  | .continuing k =>
      match k with
      | .seq _ _ k' => return (.continuing k', σF, choices)
      | .breakableK k' => return (.continuing k', σF, choices)
      | .labelK _ k' => return (.continuing k', σF, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', σF, choices)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          return (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), σF, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with continue")
      | .stop => throw (.stuck "continue outside loop")
      | _ => throw (.internal "continue delivered to expression continuation")
  | .returning k =>
      match k with
      | .seq _ _ k' => return (.returning k', σF, choices)
      | .breakableK k' => return (.returning k', σF, choices)
      | .labelK _ k' => return (.returning k', σF, choices)
      | .loop _ _ _ k' => return (.returning k', σF, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.returning k', σF, choices)
      | .frame [] _ [] [] k' _ => return (.next k', σF, choices)
      | .frame [] _ (rl :: rls) [] _ _ => do
          let _ ← loadManyF σF (rl :: rls)
          throw (.stuck "extra GoCore assignment value")
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          let vs ← loadManyF σF results
          return (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), σF, choices)
      | .frame ((_, []) :: _) _ _ [] _ _ =>
          throw (.internal "malformed call target plan")
      | .frame targets tenv results ((cv, args) :: ds) k' w =>
          match cv with
          | .funcVal fid captured =>
              enterFrameStepF σF fid (captured ++ args)
                (fun func frameEnv _ =>
                  .exec func.body frameEnv
                    (.frame [] [] [] [] (.frame targets tenv results ds k' w) func.wrapper))
                (.frame targets tenv results ds k' w) choices
          | .nil =>
              return (.panicking [⟨runtimeErrorValue
                "runtime error: invalid memory address or nil pointer dereference", false⟩]
                (.frame targets tenv results ds k' w), σF, choices)
          | other => throw (.stuck s!"deferred callee is not a function value: {repr other}")
      | .stop => throw (.internal "return unwound past the entry frame")
      | _ => throw (.internal "return delivered to expression continuation")
  | .breakingTo L k =>
      match k with
      | .seq _ _ k' => return (.breakingTo L k', σF, choices)
      | .loop _ _ _ k' => return (.breakingTo L k', σF, choices)
      | .breakableK k' => return (.breakingTo L k', σF, choices)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => return (.breakingTo L k', σF, choices)
      | .labelK name k' =>
          if name = L then return (.next k', σF, choices)
          else return (.breakingTo L k', σF, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with labeled break")
      | .stop => throw (.stuck s!"labeled break escaped its label: {L}")
      | _ => throw (.internal "labeled break delivered to expression continuation")
  | .continuingTo L k =>
      match k with
      | .seq _ _ k' => return (.continuingTo L k', σF, choices)
      | .breakableK k' => return (.continuingTo L k', σF, choices)
      | .labelK name k' =>
          if name = L then throw (.stuck s!"continue to non-loop label {L}")
          else return (.continuingTo L k', σF, choices)
      | .loop c b env k' =>
          if contHeadLabel k' = some L then
            return (.exec (.while c b) env k', σF, choices)
          else return (.continuingTo L k', σF, choices)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          if contHeadLabel k' = some L then
            return (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), σF, choices)
          else return (.continuingTo L k', σF, choices)
      | .frame _ _ _ _ _ _ => throw (.stuck "function body escaped with labeled continue")
      | .stop => throw (.stuck s!"labeled continue escaped its label: {L}")
      | _ => throw (.internal "labeled continue delivered to expression continuation")
  | .blockedSend _ _ _ => throw .deadlock
  | .blockedRecv _ _ _ _ _ => throw .deadlock
  | .blockedSelect _ _ _ => throw .deadlock
  | .opDone _ c => return (c, σF, choices)
  | .blockedSync _ _ _ _ => throw .deadlock

/-- Conditioned arm equation for the named-scrutinee `syncStmt` arm
(the named `match _hplan :` blocks ordinary simp/split reduction). -/
theorem stepFn_syncStmt_eq {σ : ExecState} {op : SyncStmtOp}
    {args : Array Expr} {targets : Array Assignee} {env : LocalEnv}
    {k : Cont} {ch : Choices} {sop : SyncOp} {e : Expr} {rest : List Expr}
    (hplan : syncPlan (Stmt.syncStmt op args targets) = some (sop, e :: rest)) :
    stepFn σ (.exec (.syncStmt op args targets) env k) ch =
      .ok (.evalE e env (.syncStK sop [] rest env k), σ, ch) := by
  simp only [stepFn]
  split <;> rename_i hp
  · rw [hplan] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := hp
    cases h2
    subst h1
    rfl
  · rw [hplan] at hp; simp at hp
  · rw [hplan] at hp; simp at hp

/-- **THE PER-STEP REFINEMENT** (one-directional): a fast step's `.ok`
is the slow step's `.ok` at the γ-image. Stub and WIRE arms are
vacuous (`.error` hypotheses). -/
theorem stepFast_ok {σF : ExecStateF} {c : Config} {ch : Choices}
    {c' : Config} {σF' : ExecStateF} {ch' : Choices}
    (h : stepFast σF c ch = .ok (c', σF', ch')) :
    stepFn (γF σF) c ch = .ok (c', γF σF', ch') := by
  fun_cases stepFast σF c ch
  all_goals first
    | (simp_all [stepFast, stuck]; done)
    | (simp_all [stepFast, stepFn, Except.ok.injEq, Prod.mk.injEq,
        pure, Except.pure]
       try obtain ⟨rfl, rfl, rfl⟩ := h
       try rfl
       done)
    | skip
  case case5 =>
    rename_i p rest kenv k'
    simp_all only [stepFast, stepFn]
    cases hd : defaultValue (γF σF) p.typ with
    | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
    | ok v =>
        rw [hd] at h
        simp only [Bind.bind, Except.bind, if_true] at h ⊢
        rcases hA : allocF σF v (some p.typ) with ⟨loc, σF₁⟩
        rw [hA] at h
        have hloc := allocF_loc σF v (some p.typ)
        have hst := allocF_state σF v (some p.typ)
        rw [hA] at hloc hst
        rcases hB : ExecState.alloc (γF σF) v (some p.typ) with ⟨loc', s'⟩
        rw [hB] at hloc hst
        simp only at hloc hst
        subst hloc
        simp only [Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨h1, h2, h3⟩ := h
        exact ⟨h1, by rw [← h2, hst], h3⟩
  case case46 =>
    simp only [stepFast] at h
    split at h <;> rename_i hplan
    · rename_i sop e rest
      rw [stepFn_syncStmt_eq hplan]
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · simp at h
    · simp at h
  case case52 =>
    rename_i env k id loc hl
    simp_all only [stepFast, stepFn]
    cases hv : loadLocF σF loc with
    | error e => rw [hv] at h; simp [Bind.bind, Except.bind] at h
    | ok v =>
        rw [hv] at h
        rw [loadLocF_ok hv]
        simp only [Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl⟩
  case case69 =>
    rename_i v r env k'
    simp_all only [stepFast, stepFn]
    cases hb : valueAsBool v with
    | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok b =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases b <;> simp_all [pure, Except.pure]
  case case70 =>
    rename_i v r env k'
    simp_all only [stepFast, stepFn]
    cases hb : valueAsBool v with
    | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok b =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases b <;> simp_all [pure, Except.pure]
  case case71 =>
    rename_i v k'
    simp_all only [stepFast, stepFn]
    cases hb : valueAsBool v with
    | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok b =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        simp_all [pure, Except.pure]
  case case72 =>
    rename_i v t e env k'
    simp_all only [stepFast, stepFn]
    cases hb : valueAsBool v with
    | error er => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok b =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases b <;> simp_all [pure, Except.pure]
  case case73 =>
    rename_i v cnd b env k'
    simp_all only [stepFast, stepFn]
    cases hb : valueAsBool v with
    | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok bb =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases bb <;> simp_all [pure, Except.pure]
  case case79 =>
    rename_i v op nt done a rest env k'
    simp_all only [stepFast, stepFn]
    split at h <;> rename_i hlt
    · split at h <;> rename_i hloc
      · rename_i msg
        simp only [hloc]  -- goal's valueAsLoc match: rewrite scrutinee
        simp_all [pure, Except.pure]
      · simp_all
      · rename_i lv
        simp only [hloc]
        simp_all [pure, Except.pure]
    · simp_all [pure, Except.pure]
  case case120 =>
    rename_i tenv rl rls k w
    simp_all only [stepFast, stepFn]
    cases hl : loadManyF σF (rl :: rls) with
    | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok vs =>
        rw [hl] at h
        simp [Bind.bind, Except.bind] at h
  case case121 =>
    rename_i sh e ops rest tenv results k' w
    simp_all only [stepFast, stepFn]
    cases hl : loadManyF σF results with
    | error er => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok vs =>
        rw [hl] at h
        rw [loadManyF_ok hl]
        simp only [Bind.bind, Except.bind] at h ⊢
        simp_all [pure, Except.pure]
  case case157 =>
    rename_i tenv rl rls k w
    simp_all only [stepFast, stepFn]
    cases hl : loadManyF σF (rl :: rls) with
    | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok vs =>
        rw [hl] at h
        simp [Bind.bind, Except.bind] at h
  case case158 =>
    rename_i sh e ops rest tenv results k' w
    simp_all only [stepFast, stepFn]
    cases hl : loadManyF σF results with
    | error er => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok vs =>
        rw [hl] at h
        rw [loadManyF_ok hl]
        simp only [Bind.bind, Except.bind] at h ⊢
        simp_all [pure, Except.pure]

end GoLean.FastEval
