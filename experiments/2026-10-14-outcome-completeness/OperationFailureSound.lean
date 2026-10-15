import OperationFailure

namespace GoLean.GoCore.Relational.C1
open Machine OperationCheck OperationCheck.Correspondence

namespace FailureChecks.Correspondence

def error? {α : Type} : Except Stop α → Option Stop
  | .ok _ => none
  | .error e => some e

@[simp] theorem error_ok {α : Type} (a : α) : error? (.ok a) = none := rfl
@[simp] theorem error_error {α : Type} (e : Stop) : error? (.error e : Except Stop α) = some e := rfl

@[simp] theorem error_map {α β : Type} (f : α → β) (x : Except Stop α) :
    error? (f <$> x) = error? x := by cases x <;> rfl

@[simp] theorem error_bind {α β : Type} (x : Except Stop α) (f : α → Except Stop β) :
    error? (x >>= f) =
      (match x with | .ok v => error? (f v) | .error e => some e) := by
  cases x <;> rfl

@[simp] theorem run_validate {α : Type} (x : Except Stop α) (ch : Choices) :
    (run (validate x) ch).1 = error? x := by cases x <;> rfl

@[simp] theorem run_delivered {α : Type} (x : Except Stop α) (ch : Choices) :
    (run (delivered x) ch).1 = error? (toResult x) := run_validate _ _

@[simp] theorem run_after {α : Type} (x : Except Stop α) (next : α → OperationCheck)
    (ch : Choices) :
    (run (after x next) ch).1 =
      (match x with | .error e => some e | .ok v => (run (next v) ch).1) := by
  cases x <;> rfl

@[simp] theorem run_afterDelivered {α : Type} (x : Except Stop α)
    (next : α → OperationCheck) (ch : Choices) :
    (run (afterDelivered x next) ch).1 =
      (match toResult x with
       | .error e => some e | .ok (.panic _) => none | .ok (.ok v) => (run (next v) ch).1) := by
  unfold afterDelivered
  rw [run_after]
  cases toResult x with
  | error => rfl
  | ok r => cases r <;> rfl

@[simp] theorem error_deliverV {α : Type} (s : Store) (k : Cont) (ch : Choices)
    (next : α → Config × Store × Choices × StepLabel) (r : Result (Commit α))
    (chain : List PanicEntry) (picks : List PickRecord) :
    error? (deliverV s k ch next r chain picks) =
      (match r with | .ok c => error? (runCommit c s) | .panic _ => none) := by
  cases r with
  | panic => rfl
  | ok c => exact error_map _ _

@[simp] theorem run_committed {α : Type} (s : Store) (p : Except Stop (Commit α))
    (ch : Choices) :
    (run (committed s p) ch).1 =
      (match toResult p with
       | .error e => some e | .ok (.panic _) => none | .ok (.ok c) => error? (runCommit c s)) := by
  unfold committed
  rw [run_after]
  cases toResult p with
  | error => rfl
  | ok r => cases r <;> simp only [run_validate, run]

@[simp] theorem toResult_map_error {α β : Type} (x : Except Stop α) (f : α → β) :
    error? (toResult (Except.map f x)) = error? (toResult x) := by
  cases x with
  | ok => rfl
  | error e => cases e with
    | terminal t => cases t <;> rfl
    | refusal => rfl
    | fuelOut => rfl

theorem toResult_bind_error {α β : Type} (x : Except Stop α) (f : α → Except Stop β) :
    error? (toResult (x >>= f)) =
      (match toResult x with
       | .error e => some e | .ok (.panic _) => none
       | .ok (.ok v) => error? (toResult (f v))) := by
  cases x with
  | ok => rfl
  | error e => cases e with
    | terminal t => cases t <;> rfl
    | refusal => rfl
    | fuelOut => rfl

theorem synchronization_errors (ctx : ProgramCtx) (s : Store) (op : SyncOp)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) (ch : Choices) :
    (run (synchronization ctx s op vs env k) ch).1 =
      error? (toResult (applySyncOp ctx s ch op vs env k)) := by
  unfold synchronization applySyncOp
  split <;> simp_all only [run_afterDelivered, toResult_bind_error, run, run_delivered]
  · simp only [error?]
    repeat' (split <;> try simp_all only)
    all_goals simp_all [pure, Except.pure, toResult]
  · rfl
  · cases h : applySyncOpCore ctx s op _ env k with
    | ok => rfl
    | error e => cases e with
      | terminal t => cases t <;> rfl
      | refusal => rfl
      | fuelOut => rfl

theorem select_errors (ctx : ProgramCtx) (s : Store)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) (ch : Choices) :
    (run (select ctx s clauses default? vs env k) ch).1 =
      error? (toResult (applySelect ctx s clauses default? vs env k ch)) := by
  unfold select applySelect
  rw [run_afterDelivered, toResult_bind_error]
  cases hr : toResult (applySelectCore ctx s clauses default? vs env k) with
  | error => rfl
  | ok result => cases result with
    | panic => rfl
    | ok out => cases out with
      | done => rfl
      | picks poll commits =>
        simp only [run]
        split
        · rename_i pair hp
          obtain ⟨cl, result⟩ := pair
          cases result <;> simp [hp, run, toResult, error?]
        · simp_all [run, toResult, error?, throw, throwThe, MonadExceptOf.throw]

theorem mapIteration_errors (ctx : ProgramCtx) (s : Store) (kv vv : Option VarId)
    (kt vt : Ty) (body : Stmt) (base : Option Loc) (produced start : Array Nat)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    (run (mapIteration ctx s kv vv kt vt base produced start env) ch).1 =
      error? (stepFn ctx s (.next (.mapIterK kv vv kt vt body base produced start env k)) ch) := by
  simp only [mapIteration, stepFn, run_after, error_bind]
  cases hc : mapIterCandidates ctx s kt vt base produced with
  | error => rfl
  | ok pair =>
    obtain ⟨cands, tr⟩ := pair
    dsimp only
    split
    · rfl
    · simp only [run]
      split <;> simp_all only [run, run_validate, error_bind]
      · rfl
      · split <;> simp_all [error?]

theorem strict_errors (ctx : ProgramCtx) (s : Store) (leaf : Loc → Loc)
    (op : StrictOp) (vs : List GoValue) (ch : Choices) :
    (run (strict ctx s leaf op vs) ch).1 =
      error? (toResult (applyStrictOpPick ctx s leaf op vs ch)) := by
  cases hk : op.convKind? with
  | none => simpa only [strict, applyStrictOpPick, hk, run_delivered] using
      (toResult_map_error (applyStrictOp ctx s leaf op vs) (fun r => (r, ch, ([] : List PickRecord)))).symm
  | some pair =>
    obtain ⟨kind, literal⟩ := pair
    cases hv : convOperand? vs with
    | none => simpa only [strict, applyStrictOpPick, hk, hv, convCapApply, run_delivered] using
        (toResult_map_error (convRefuse kind vs) (fun r => (r, ch, ([] : List PickRecord)))).symm
    | some value =>
      simp only [strict, applyStrictOpPick, hk, hv, convCapApply, run, run_delivered]
      exact (toResult_map_error _ _).symm

theorem activation_errors (ctx : ProgramCtx) (s : Store) (fid : FuncId)
    (args : List GoValue) (k : Cont) (ch : Choices)
    (next : Choices → Entry × Store × AccessTrace → Config × Store × Choices × StepLabel)
    (chain : List PanicEntry) :
    (run (activation ctx s fid args) ch).1 = error? (do
      let (r, tail, picks) ← enterFramePickV ctx s fid args ch
      deliverV s k tail (next tail) r chain picks) := by
  unfold activation committed after enterFramePickV
  cases h : toResult (enterFrame.plan ctx s fid args) with
  | error e => rfl
  | ok r => cases r with
    | panic => rfl
    | ok commit => cases hc : runCommit commit s <;>
        simp [run, validate, after, deliverV, hc, error?, Except.bind, Bind.bind,
          Functor.map, Except.map]

theorem unseqEntry_errors (ctx : ProgramCtx) (s : Store) (g : UnseqGraph)
    (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    (run (unseqEntry ctx s g env k) ch).1 =
      error? (stepUnseqEnter ctx s g body env k ch) := by
  fun_cases stepUnseqEnter ctx s g body env k ch
  all_goals simp_all [unseqEntry,
    run, error?, throw, throwThe, MonadExceptOf.throw]
  split <;> simp_all [Bind.bind, Except.bind]

theorem unseqValue_errors (ctx : ProgramCtx) (s : Store) (v : GoValue) (g : UnseqGraph)
    (body : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef))
    (env : LocalEnv) (phase : UnseqPhase) (k : Cont) (ch : Choices) :
    (run (unseqValue ctx s v g env phase) ch).1 =
      error? (stepUnseqValue ctx s v g body st tg env phase k ch) := by
  fun_cases stepUnseqValue ctx s v g body st tg env phase k ch
  all_goals simp_all [unseqValue,
    run, error?, throw, throwThe, MonadExceptOf.throw]
  repeat' (split <;> try simp_all [Bind.bind, Except.bind])

theorem preprintValue_errors (s : Store) (v : GoValue) (k : Cont) (ch : Choices) :
    (run (preprintValue v k) ch).1 = error? (stepRetOther s v k ch) := by
  fun_cases stepRetOther s v k ch
  all_goals simp_all [preprintValue, run, error?,
    throw, throwThe, MonadExceptOf.throw]

theorem frameExit_errors (ctx : ProgramCtx) (s : Store)
    (targets : List (TargetShape × List Expr)) (env : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k : Cont) (fr : FuncId) (ch : Choices) :
    (run (frameExit ctx s targets results ds k) ch).1 =
      error? (stepFrameExit ctx s targets env results ds k fr ch) := by
  fun_cases stepFrameExit ctx s targets env results ds k fr ch
  all_goals simp_all only [frameExit]
  all_goals first
    | exact activation_errors _ _ _ _ _ _ _ _
    | rfl
    | skip
  all_goals simp_all only [run_validate, run_after, activation, run_committed,
    enterFramePickV, error_bind, error_deliverV]
  all_goals repeat' (split <;> try simp_all [run, error?,  
        throw, throwThe, MonadExceptOf.throw])

theorem unseqNext_errors (ctx : ProgramCtx) (s : Store) (g : UnseqGraph)
    (body : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef))
    (env : LocalEnv) (phase : UnseqPhase) (k : Cont) (ch : Choices) :
    (run (unseqNext ctx s g body st tg env phase) ch).1 =
      error? (stepUnseqNext ctx s g body st tg env phase k ch) := by
  fun_cases stepUnseqNext ctx s g body st tg env phase k ch
  all_goals simp_all only [unseqNext,  run_validate, error_bind]
  all_goals first
    | rfl
    | (simp_all [run, error?,   throw, throwThe, MonadExceptOf.throw])
  all_goals repeat' (split <;> try simp_all [Functor.map, Except.map])

theorem preprintNext_errors (ctx : ProgramCtx) (s : Store) (k : Cont) (ch : Choices) :
    (run (preprintNext ctx s k) ch).1 = error? (stepNextOther ctx s k ch) := by
  fun_cases stepNextOther ctx s k ch
  all_goals simp_all only [preprintNext, run_delivered, error_bind]
  · split <;> simp_all [error?]
  · rfl

theorem committed_bind {α β : Type} (s : Store) (x : Except Stop α)
    (f : α → Except Stop (Commit β)) (ch : Choices) :
    (run (committed s (x >>= f)) ch).1 =
      (run (afterDelivered x (fun v => committed s (f v))) ch).1 := by
  cases x with
  | ok => rfl
  | error e => cases e with
    | terminal t => cases t <;> rfl
    | refusal => rfl
    | fuelOut => rfl

theorem committed_stream (s : Store) (c : Commit (Store × AccessTrace))
    (ch tail : Choices) (ps : List PickRecord) :
    (run (committed s (.ok (Commit.withStream tail ps c))) ch).1 =
      (run (committed s (.ok c)) ch).1 := by
  simp only [run_committed, toResult_ok, runCommit_withStream]
  cases runCommit c s <;> rfl

theorem error_commit_delivery {α : Type} (s : Store) (plan : Except Stop (Commit α))
    (k : Cont) (ch : Choices) (next : α → Config × Store × Choices × StepLabel) :
    error? (do let r ← toResult plan; deliverV s k ch next r) =
      (run (committed s plan) ch).1 := by
  simp only [error_bind, run_committed, error_deliverV]
  cases toResult plan with
  | error => rfl
  | ok r => cases r <;> rfl

theorem statementOperation_errors (ctx : ProgramCtx) (s : Store) (op : StmtOp)
    (nt : Nat) (vs : List GoValue) (ch : Choices) :
    (run (statementOperation ctx s op vs) ch).1 =
      (run (committed s (applyStmtOp.plan ctx s ch op nt vs)) ch).1 := by
  fun_cases applyStmtOp.plan ctx s ch op nt vs
  all_goals simp_all only [statementOperation, committed_bind, run_afterDelivered, run,
    pure, Except.pure, committed_stream, panic]
  all_goals repeat' (split <;> try simp_all only [committed_bind, run_afterDelivered,
      committed_stream, run])
  all_goals try simp_all [   run_committed,
    toResult,  stuck, error?, runCommit,  Bind.bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

theorem error_bind_pure {α β : Type} (x : Except Stop α) (f : α → β) :
    error? (x >>= fun v => pure (f v)) = error? x := by cases x <;> rfl

theorem statementPlan_nt (ctx : ProgramCtx) (s : Store) (ch : Choices)
    (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    applyStmtOp.plan ctx s ch op nt vs = applyStmtOp.plan ctx s ch op 0 vs := rfl

theorem statementOperation_errors_zero (ctx : ProgramCtx) (s : Store) (op : StmtOp)
    (vs : List GoValue) (ch : Choices) :
    (run (statementOperation ctx s op vs) ch).1 =
      (run (committed s (applyStmtOp.plan ctx s ch op 0 vs)) ch).1 :=
  statementOperation_errors ctx s op 0 vs ch

set_option maxHeartbeats 1600000 in
theorem atState_errors (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices)
    (ha : c.abort? = none) (hb : c.blockedB = false) :
    (run (atState ctx ⟨c, s⟩) ch).1 = error? (stepFn ctx s c ch) := by
  fun_cases stepFn ctx s c ch
  all_goals try simp_all only [atState, statement, expression, returned, next, panicking]
  all_goals first
    | exact activation_errors _ _ _ _ _ _ _ _
    | exact frameExit_errors _ _ _ _ _ _ _ _ _
    | exact unseqEntry_errors _ _ _ _ _ _ _
    | exact unseqValue_errors _ _ _ _ _ _ _ _ _ _ _
    | exact unseqNext_errors _ _ _ _ _ _ _ _ _ _
    | exact preprintValue_errors _ _ _ _
    | exact preprintNext_errors _ _ _ _
    | exact mapIteration_errors _ _ _ _ _ _ _ _ _ _ _ _ _
    | rfl
    | skip
  all_goals try simp_all only [ 
    strict_errors, synchronization_errors, select_errors,
    activation, run_committed, enterFramePickV, error_deliverV,
    run_validate, run_delivered,  error_bind]
  all_goals try simp_all [run, error?, Config.abort?, Config.blockedB]
  all_goals repeat' (split <;> try simp_all [run, error?])
  all_goals try (exfalso; apply_assumption <;> rfl)
  all_goals try simp_all only [statementPlan_nt, statementOperation_errors_zero,
    run_committed, error?]
  all_goals try simp_all [   error?,
      preprintValue_errors s, preprintNext_errors]
  all_goals try (split at * <;> simp_all [stepPanicStop])
  all_goals try (exfalso; solve_by_elim (maxDepth := 20))
  all_goals
    rename_i _ rest _ _ _ _ _ _ _
    cases rest <;> simp_all

end FailureChecks.Correspondence
end GoLean.GoCore.Relational.C1
