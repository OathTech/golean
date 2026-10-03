import GoLean.GoCore.EquationsAttr
import GoLean.GoCore.MachineSound

/-!
# The semantic EQUATIONS — per-arm `stepFn` lemmas, the `stepFn_eqns` rewrite set (window packet D)

[AGENT packet D worker] 2026-10-03, under the re-pin offer's charter row 7 (three separate checks:
STATEMENTS — `BridgeSet.lean`; EQUATIONS — this file, proved, catching a definition changed under
the same type; the toy CLIENT — `Tests/EquationClient.lean`, which USES these and never
re-unfolds `stepFn`); brief `docs/codex-briefs/2026-09-24_packet-D-equations.md` as amended
2026-09-28/30; the logic team's requests 1, 2 and 7 of 2026-09-28 (relayed).

ONE lemma per `stepFn` arm, over a SYMBOLIC store `s`, environment `env`, continuation `k` and
tape `ch`, with the arm's operation premises EXPLICIT — each of the shape
`stepFn ctx s (<configuration pattern>) ch = .ok (<successor>, s', ch', <label>)` or
`= .error <stop>`. Nothing here unfolds `stepFn` in a STATEMENT (proofs do). The premises bottom
out in the memory module's primitives where the arm's helper is a thin wrapper over one —
`loadRoot` (a variable read, a pinned result read), `storeLoc` (the plain-variable store),
`Store.alloc` through `allocDecls`/`bindParams` (block entry, frame entry — the C4/B6 slot laws
`blockEntry_*`/`frameEntry_*`/`enterFrame_declared` take it from there) — and in the COMPOSED
applies otherwise (`applyStrictOp`, `applyStmtOp`, `applyChanOp`, `applySelect`, `applySyncOp`,
`applyAtomicOp`, `applyRhsOp`, `storeTarget`, `enterFrame`): the logic team's request 1, with its
filing correction (`callArgsK`, `callValCalleeK`, `callValArgsK`, `deferCalleeK`, `deferArgsK`,
`stmtOpK` are `.retV v` arms). Every lemma carries `@[stepFn_eqns]` (`EquationsAttr.lean`);
`simp only [stepFn_eqns, <the premises>]` is the intended use.

Sections, in the charter's §3 priority: (1) control, calls, defer, return, panic/recover, the
signal table, FRAME EXIT (`stepFrameExit` with named results, defers pending, result readback —
continuations audit F4) and the UNWINDING equations (request 7, stated over the preprint phase's
arms); (2) memory — variable/address/global reads, the store spine, block entry, the root cell
read/write laws; (3) the rest — branches, loops, Booleans, the strict operators, the wide
statements, channels/select/go/sync/atomic, `unseq`; then the PINNED SETUP EQUATION (request 2:
no globals, no package initializer — the entry configuration, the argument/result layout, the
residual tape).

Not expressible as stated and therefore NOT here (reported, per the brief): the `.evalE`
catch-all's `"unclassified expression"` refusal is UNREACHABLE — every `Expr` constructor is either
an explicit arm or has a `strictPlan` — so no equation states it; the `.retV` catch-all's
`"expected function value"` refusals over an arbitrary non-function value are stated only for the
shapes the frontend emits (`nil`, a function value) — the general form would enumerate `GoValue`.
-/

namespace GoLean.GoCore.Equations

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {ctx : ProgramCtx}

/-! ## Small helper facts the equations rest on (not arms; no attribute) -/

/-- A composed apply that panics did so in its VALIDATE phase (the commit cannot). -/
theorem storeTarget_inv_panic {s : Store} {r : TargetRef} {v : GoValue} {msg : String}
    (h : storeTarget ctx s r v = .error (.panic msg)) :
    storeTarget.plan ctx s r v = .error (.panic msg) := by
  unfold storeTarget at h
  rcases plan_run_error h with hp | ⟨c, hc, hcs⟩
  · exact hp
  · exact absurd hcs (storeTarget_commit_noPanic _ _ _ c hc s msg)

theorem applyStmtOp_inv_panic {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {msg : String}
    (h : applyStmtOp ctx s ch op nt vs = .error (.panic msg)) :
    applyStmtOp.plan ctx s ch op nt vs = .error (.panic msg) := by
  unfold applyStmtOp at h
  rcases plan_run_error h with hp | ⟨c, hc, hcs⟩
  · exact hp
  · exact absurd hcs (applyStmtOp_commit_noPanic _ _ _ _ _ c hc s msg)

/-- A composed apply that stops on a non-panic `Stop` stopped in its validate phase or its
commit; either way the composed result is that stop (what `toResult` passes through). -/
theorem toResult_of_error {α : Type} {x : Except Stop α} {e : Stop}
    (h : x = .error e) (hne : ∀ msg, e ≠ .panic msg) : toResult x = .error e := by
  subst h; exact toResult_error hne

/-- `valueAsBool` on a Boolean value is the value. -/
theorem valueAsBool_bool (b : Bool) : valueAsBool (.bool b) = .ok b := rfl

/-- `valueAsLoc` on an address is the address; on `nil` it is the nil-dereference panic. -/
theorem valueAsLoc_addr (loc : Loc) : valueAsLoc (.addr loc) = .ok loc := rfl
theorem valueAsLoc_nil : valueAsLoc .nil = .error (.panic nilDerefPanicText) := rfl

/-- A plain-variable target (`Assignee.var`): its phase-1 plan and its completed reference. -/
theorem targetPlan_var (id : VarId) : targetPlan (.var id) = some (.chain [], [.ref id]) := rfl
theorem completeTargetRef_var (a : GoValue) : completeTargetRef (.chain []) [a] = some (.chain a [] []) := rfl
theorem resolveChain_nil (s : Store) (a : GoValue) : resolveChain ctx s a [] [] = .ok a := rfl
theorem applyRhsOp_vals (s : Store) (vs : List GoValue) : applyRhsOp ctx s .vals vs = .ok (vs, []) := rfl

/-! ## The root-cell read/write laws (request 1: the arm premises' floor) -/

/-- The read of a root cell IS the heap lookup. -/
theorem loadRoot_base {s : Store} {a : Addr} {ty : Ty} {v : GoValue}
    (hl : Heap.lookup s.heap (.base a) = some (.value ty v)) : loadRoot ctx s (.base a) = .ok v := by
  simp [loadRoot, loadLoc, hl]

/-- The write of a root cell: the incoming value NORMALIZED at the cell's declared type replaces
the cell in place; nothing else moves. -/
theorem storeLoc_root {s : Store} {a : Addr} {ty : Ty} {old v v' : GoValue}
    (hl : Heap.lookup s.heap (.base a) = some (.value ty old))
    (hn : normalizeValueForTy ctx ty v = .ok v') :
    storeLoc ctx s (.base a) v = .ok { heap := s.heap.set a.id (.value ty v') (Heap.lookup_lt hl) } := by
  have hi := Heap.lookup_lt hl
  have hcell : s.heap[a.id] = .value ty old := by
    obtain ⟨i⟩ := a
    simp only [Heap.lookup] at hl
    exact (Array.getElem?_eq_some_iff.mp hl).2
  unfold storeLoc Store.updateCell
  simp only [Loc.rootPath, hi, ↓reduceDIte, hcell, writeAt]
  have : normalizeValueForTyTy (normalizeValueForTyAt ctx.types ctx.types.size) ty v = .ok v' := hn
  simp [this, Bind.bind, Except.bind, Functor.map, Except.map]

/-- Reading back the cell just written. -/
theorem Heap.lookup_set_self {h : Heap} {i : Nat} {c : HeapCell} {hi : i < h.size} :
    Heap.lookup (h.set i c hi) (.base ⟨i⟩) = some c := by
  simp [Heap.lookup]

/-- Reading back the cell just allocated (`Store.alloc` pushes at `.base ⟨h.size⟩`,
`Store.alloc_shape`/`Store.alloc_cell`). -/
theorem Heap.lookup_push_self {h : Heap} {c : HeapCell} :
    Heap.lookup (h.push c) (.base ⟨h.size⟩) = some c := by
  simp [Heap.lookup]

/-! ## (1) Control: sequencing, branches, loops, labels, the five control transfers -/

@[stepFn_eqns] theorem exec_seqn (s : Store) (ss : Array Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.seqn ss) env k) ch = .ok (.next (seqCont ss.toList env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_ifThenElse (s : Store) (c : Expr) (t e : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.ifThenElse c t e) env k) ch = .ok (.evalE c env (.ifK t e env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_while (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.while c b) env k) ch = .ok (.evalE c env (.whileK c b env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_returnStmt (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec .returnStmt env k) ch = .ok (.signal .ret k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_breakStmt (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec .breakStmt env k) ch = .ok (.signal .brk k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_continueStmt (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec .continueStmt env k) ch = .ok (.signal .cont k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_inertLabel (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.inertLabel name) env k) ch = .ok (.next k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_labeled (s : Store) (name : String) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.labeled name b) env k) ch = .ok (.exec b env (.labelK name k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_breakTo (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.breakTo name) env k) ch = .ok (.signal (.brkTo name) k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_continueTo (s : Store) (name : String) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.continueTo name) env k) ch = .ok (.signal (.contTo name) k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_breakable (s : Store) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.breakable b) env k) ch = .ok (.exec b env (.breakableK k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_unsupported (s : Store) (feature : String) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.unsupported feature) env k) ch = .error (.unsupported feature) := rfl

/-! ## (1) Calls: the declared call, the value call, the argument walks, frame ENTRY -/

/-- A declared call with arguments: the first argument evaluates under `callArgsK`. -/
@[stepFn_eqns] theorem exec_call_args {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {a : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hp : targetsPlan targets.toList = some plans) (hargs : args.toList = a :: rest) :
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.evalE a env (.callArgsK fid plans [] rest env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hp, hargs]

/-- A nullary declared call ENTERS its frame in the same step (`enterFrame`, the composed entry:
`enterFrame_declared` states its binding/allocation phases). -/
@[stepFn_eqns] theorem exec_call_nullary {s s' : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hp : targetsPlan targets.toList = some plans) (hargs : args.toList = [])
    (he : enterFrame ctx s fid [] = .ok (e, s', tr)) :
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .ok (e.callConfig plans env k, s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFn, hp, hargs, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc,
    Functor.map, Except.map]

/-- A nullary declared call whose entry PANICS (a nil receiver): the panic unwinds under `k`, with
the `nilValueMethodText` consult's pick, residual and record. -/
@[stepFn_eqns] theorem exec_call_nullary_panic {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hp : targetsPlan targets.toList = some plans) (hargs : args.toList = [])
    (he : enterFrame ctx s fid [] = .error (.panic msg)) :
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid [] msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1)] k, s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid [])
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1, []⟩) := by
  simp [stepFn, hp, hargs, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

@[stepFn_eqns] theorem exec_call_unsupported {s : Store} {targets : Array Assignee} {fid : FuncId} {args : Array Expr}
    (env : LocalEnv) (k : Cont) (ch : Choices) (hp : targetsPlan targets.toList = none) :
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .error (.unsupported "unsupported call target assignee") := by
  simp [stepFn, hp, throw, throwThe, MonadExceptOf.throw]

@[stepFn_eqns] theorem exec_callValue {s : Store} {targets : Array Assignee} {callee : Expr} {args : Array Expr}
    {plans : List (TargetShape × List Expr)} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hp : targetsPlan targets.toList = some plans) :
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .ok (.evalE callee env (.callValCalleeK plans args.toList env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hp]

@[stepFn_eqns] theorem exec_callValue_unsupported {s : Store} {targets : Array Assignee} {callee : Expr}
    {args : Array Expr} (env : LocalEnv) (k : Cont) (ch : Choices) (hp : targetsPlan targets.toList = none) :
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .error (.unsupported "unsupported value-call target assignee") := by
  simp [stepFn, hp, throw, throwThe, MonadExceptOf.throw]

/-- The declared call's argument walk: another argument pending. -/
@[stepFn_eqns] theorem retV_callArgsK_more (s : Store) (v : GoValue) (fid : FuncId) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.callArgsK fid plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The last argument arrived: frame ENTRY (request 1's filing correction — a `.retV` arm). -/
@[stepFn_eqns] theorem retV_callArgsK_enter {s s' : Store} {v : GoValue} {fid : FuncId} {plans : List (TargetShape × List Expr)}
    {vals : List GoValue} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid (vals ++ [v]) = .ok (e, s', tr)) :
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFn, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

@[stepFn_eqns] theorem retV_callArgsK_enter_panic {s : Store} {v : GoValue} {fid : FuncId} {plans : List (TargetShape × List Expr)}
    {vals : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid (vals ++ [v]) = .error (.panic msg)) :
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1, []⟩) := by
  simp [stepFn, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

/-- The value call's callee arrived, no arguments: ENTRY of the function value's target with its
captures (request 1's filing correction — a `.retV` arm). -/
@[stepFn_eqns] theorem retV_callValCalleeK_enter {s s' : Store} {fid : FuncId} {captured : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid captured = .ok (e, s', tr)) :
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFn, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

@[stepFn_eqns] theorem retV_callValCalleeK_enter_panic {s : Store} {fid : FuncId} {captured : List GoValue}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid captured = .error (.panic msg)) :
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid captured msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid captured)
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1, []⟩) := by
  simp [stepFn, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

/-- A nil callee with no arguments: the nil-dereference panic at INVOCATION. -/
@[stepFn_eqns] theorem retV_callValCalleeK_nil (s : Store) (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV .nil (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) := rfl

/-- The value call's callee arrived with arguments pending: a deferrable callee (a function value
or nil — Go evaluates every argument before the nil check) starts the argument walk. -/
@[stepFn_eqns] theorem retV_callValCalleeK_args {s : Store} {cv : GoValue} (plans : List (TargetShape × List Expr))
    (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (hd : deferrableCallee cv = true) :
    stepFn ctx s (.retV cv (.callValCalleeK plans (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans [] rest env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hd]

@[stepFn_eqns] theorem retV_callValArgsK_more (s : Store) (v cv : GoValue) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.callValArgsK cv plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem retV_callValArgsK_enter {s s' : Store} {v : GoValue} {fid : FuncId} {captured vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .ok (e, s', tr)) :
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) := by
  rw [List.append_assoc] at he
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFn, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

@[stepFn_eqns] theorem retV_callValArgsK_enter_panic {s : Store} {v : GoValue} {fid : FuncId} {captured vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .error (.panic msg)) :
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1, []⟩) := by
  rw [List.append_assoc] at he
  simp [stepFn, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_callValArgsK_nil (s : Store) (v : GoValue) (plans : List (TargetShape × List Expr))
    (vals : List GoValue) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.callValArgsK .nil plans vals [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) := rfl

/-! ## (1) Defer: registration (`pushDefer`) -/

@[stepFn_eqns] theorem exec_deferCall (s : Store) (callee : Expr) (args : Array Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.deferCall callee args) env k) ch
      = .ok (.evalE callee env (.deferCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem retV_deferCalleeK_args {s : Store} {v : GoValue} (a : Expr) (rest : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (hd : deferrableCallee v = true) :
    stepFn ctx s (.retV v (.deferCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hd]

/-- A nullary deferred callee is REGISTERED on the innermost call frame (`pushDefer`). -/
@[stepFn_eqns] theorem retV_deferCalleeK_push {s : Store} {v : GoValue} {k' k'' : Cont} (env : LocalEnv) (ch : Choices)
    (hd : deferrableCallee v = true) (hp : pushDefer (v, []) k' = some k'') :
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hd, hp]

/-- The registration at a call frame directly below, written out (`pushDefer_frame`). -/
@[stepFn_eqns] theorem retV_deferCalleeK_push_frame {s : Store} {v : GoValue} (env : LocalEnv) (ch : Choices)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k'' : Cont) (fr : FuncId) (hd : deferrableCallee v = true) :
    stepFn ctx s (.retV v (.deferCalleeK [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((v, []) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hd, pushDefer_frame]

@[stepFn_eqns] theorem retV_deferCalleeK_outside {s : Store} {v : GoValue} {k' : Cont} (env : LocalEnv) (ch : Choices)
    (hd : deferrableCallee v = true) (hp : pushDefer (v, []) k' = none) :
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .error (.stuck "defer outside a call frame") := by
  simp [stepFn, hd, hp, throw, throwThe, MonadExceptOf.throw]

@[stepFn_eqns] theorem retV_deferArgsK_more (s : Store) (v cv : GoValue) (vals : List GoValue) (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.deferArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The last deferred argument arrived: the call is registered with its argument VALUES
(`pushDefer_saves_values`). -/
@[stepFn_eqns] theorem retV_deferArgsK_push {s : Store} {v cv : GoValue} {vals : List GoValue} {k' k'' : Cont}
    (env : LocalEnv) (ch : Choices) (hp : pushDefer (cv, vals ++ [v]) k' = some k'') :
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hp]

@[stepFn_eqns] theorem retV_deferArgsK_push_frame (s : Store) (v cv : GoValue) (vals : List GoValue) (env : LocalEnv)
    (ch : Choices) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k'' : Cont) (fr : FuncId) :
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((cv, vals ++ [v]) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, pushDefer_frame]

@[stepFn_eqns] theorem retV_deferArgsK_outside {s : Store} {v cv : GoValue} {vals : List GoValue} {k' : Cont}
    (env : LocalEnv) (ch : Choices) (hp : pushDefer (cv, vals ++ [v]) k' = none) :
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .error (.stuck "defer outside a call frame") := by
  simp [stepFn, hp, throw, throwThe, MonadExceptOf.throw]

/-! ## (1) Panic and recover: the raise, `recover()` -/

@[stepFn_eqns] theorem exec_panicStmt (s : Store) (e : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.panicStmt e) env k) ch = .ok (.evalE e env (.panicArgK k), s, ch, ⟨[], [], []⟩) := rfl

/-- THE RAISE: the payload's entry (its rewrite mark decided by its dynamic type) starts
unwinding under `k'`. -/
@[stepFn_eqns] theorem retV_panicArgK (s : Store) (v : GoValue) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.panicArgK k')) ch
      = .ok (.panicking [panicEntryOf ctx (panicPayload v)] k', s, ch, ⟨[], [], []⟩) := rfl

/-- `recover()`: the walk's answer and the continuation with the entry marked
(`recoverResult_eq`/`_frame`/`_glue` state the walk). -/
@[stepFn_eqns] theorem evalE_recoverCall (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE .recoverCall env k) ch
      = .ok (.retV (recoverResult k).1 (recoverResult k).2, s, ch, ⟨[], [], []⟩) := rfl

/-! ## (1) The UNWINDING equations (request 7; stated over the preprint phase's arms) -/

/-- Stripping a call frame with an EMPTY defer list: the chain moves below it. -/
@[stepFn_eqns] theorem panicking_frame_empty (s : Store) (chain : List PanicEntry) (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFn ctx s (.panicking chain (.frame t te r [] k' fr)) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) := rfl

/-- A deferred call runs ON THE PANIC PATH: entered above the suspended chain's marker
(`panicResumeK chain`) on the draining frame — the `deferPanic` entry. -/
@[stepFn_eqns] theorem panicking_frame_defer {s s' : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {e : Entry} {tr : AccessTrace} (t : List (TargetShape × List Expr)) (te : LocalEnv)
    (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)) :
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (e.drainConfig (.panicResumeK chain (.frame t te r ds k' fr))
              (fun cv => .panicking chain (.frame t te r ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFn, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

/-- The same, on a RUN entry (the declared target's body under a barrier frame on the marker). -/
@[stepFn_eqns] theorem panicking_frame_defer_run {s s' : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {func : Func} {fenv : LocalEnv} {rl : List Loc} {tr : AccessTrace}
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)) :
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.panicResumeK chain (.frame t te r ds k' fr)) func.id),
            s', ch, ⟨tr, [], []⟩) :=
  panicking_frame_defer t te r ds k' fr ch he

/-- A deferred call whose ENTRY panics joins the chain; the remaining defers keep draining. -/
@[stepFn_eqns] theorem panicking_frame_defer_panic {s : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {msg : String} (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)) :
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)])
              (.frame t te r ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) := by
  simp [stepFn, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

/-- A nil deferred callee's invocation panics into the chain. -/
@[stepFn_eqns] theorem panicking_frame_defer_nil (s : Store) (chain : List PanicEntry) (args : List GoValue)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue))
    (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFn ctx s (.panicking chain (.frame t te r ((.nil, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry nilDerefPanicText]) (.frame t te r ds k' fr), s, ch, ⟨[], [], []⟩) := rfl

/-- A panic reaching the suspended chain's marker JOINS it (the newer entries after the older). -/
@[stepFn_eqns] theorem panicking_panicResumeK (s : Store) (chain suspended : List PanicEntry) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.panicResumeK suspended k')) ch
      = .ok (.panicking (suspended ++ chain) k', s, ch, ⟨[], [], []⟩) := rfl

/-- `panicResumeK` RESUMING: the drain completed with the newest entry UNRECOVERED — the unwind
continues below the marker. -/
@[stepFn_eqns] theorem next_panicResumeK_unrecovered {s : Store} {chain : List PanicEntry} (k' : Cont) (ch : Choices)
    (h : chainNewestRecovered chain = false) :
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

/-- `panicResumeK` with the newest entry RECOVERED: the unwind is cancelled; the frame below resumes
its normal exit. -/
@[stepFn_eqns] theorem next_panicResumeK_recovered {s : Store} {chain : List PanicEntry} (k' : Cont) (ch : Choices)
    (h : chainNewestRecovered chain = true) :
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

/-- `panicPassthrough` over GLUE of either kind: the head is stripped, the chain unchanged
(the general law; the sequence/block glue `.seq` and the loop/label/breakable/expression frames
are its instances below). -/
@[stepFn_eqns] theorem panicking_glue {s : Store} {chain : List PanicEntry} {g : Frame} (k : Cont) (ch : Choices)
    (hg : g.class = .stmtGlue ∨ g.class = .exprGlue) :
    stepFn ctx s (.panicking chain (g :: k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := by
  cases g <;> simp [Frame.class] at hg <;> rfl

/-- Sequence and block glue (a block's body runs under a `.seq` frame, C4). -/
@[stepFn_eqns] theorem panicking_seq (s : Store) (chain : List PanicEntry) (rest : List Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.seq rest env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem panicking_loop (s : Store) (chain : List PanicEntry) (c : Expr) (b : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.loop c b env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem panicking_breakableK (s : Store) (chain : List PanicEntry) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.breakableK k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem panicking_labelK (s : Store) (chain : List PanicEntry) (name : String) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.labelK name k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem panicking_strictK (s : Store) (chain : List PanicEntry) (op : StrictOp) (done : List GoValue)
    (pending : List Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.strictK op done pending env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem panicking_storeK (s : Store) (chain : List PanicEntry) (refs : List TargetRef) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.storeK refs vals body env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) := rfl

/-- The probe frame's `unseqPanic` consult (E13 option (b)): slot 0 DEFERS the operand's panic
(re-evaluated at its residual position), any other slot RAISES it now. -/
@[stepFn_eqns] theorem panicking_probeK (s : Store) (chain : List PanicEntry) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.probeK k')) ch
      = .ok (if (Choices.consumeAtE .unseqPanic 2 ch).1 = 0 then .next k' else .panicking chain k', s,
            (Choices.consumeAtE .unseqPanic 2 ch).2.1, ⟨[], (Choices.consumeAtE .unseqPanic 2 ch).2.2, []⟩) := by
  simp only [stepFn]
  rfl

/-- THE ABORT: a SETTLED chain at the empty continuation is the Go `panic` terminal after the
`repanicCollapse` consult — `stepFn` raises, no successor (`Prefix.stepFn_abort` under
`Config.abort?`; here over the split). -/
@[stepFn_eqns] theorem panicking_stop_settled {s : Store} {first : PanicEntry} {rest : List PanicEntry} (ch : Choices)
    (hs : splitNewestPending? (first :: rest) = none) :
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = (do let msg ← abortMsg ctx first rest (abortConsult first rest ch).1; throw (.panic msg)) := by
  simp only [stepFn, stepPanicStop, hs]

/-- THE PREPRINT PHASE (unit 6b): an UNSETTLED chain at `.stop` takes the phase step at its newest
pending entry — the `repanicCollapse` consult at `preprintWidth`: slot 0 at a collision marks the
older entry repanicked and drops the newer (`preprintDrop`); otherwise the entry is selected and
the preprint frame built. -/
@[stepFn_eqns] theorem panicking_stop_pending {s : Store} {first : PanicEntry} {rest older : List PanicEntry}
    {entry : PanicEntry} {newer : List PanicEntry} (ch : Choices)
    (hs : splitNewestPending? (first :: rest) = some (older, entry, newer)) :
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = .ok (if preprintCollide older entry && (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).1 = 0
              then .panicking (preprintDrop older newer) .stop
              else .next (.preprintK older entry newer .stop), s,
            (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.1,
            ⟨[], (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.2, []⟩) := by
  simp only [stepFn, stepPanicStop, hs]
  rfl

@[stepFn_eqns] theorem panicking_nil_stop (s : Store) (ch : Choices) :
    stepFn ctx s (.panicking [] .stop) ch = .error (.internal "empty panic chain at stop") := rfl

/-- The preprint frame RESOLVES its pending call (`preprintDispatch`: the member on the payload's
dynamic type, the receiver adjusted) and re-queues it as the nullary value call the
`callValCalleeK` position enters next step. -/
@[stepFn_eqns] theorem next_preprintK {s : Store} {older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry}
    {fid : FuncId} {recv : GoValue} {tr : AccessTrace} (k' : Cont) (ch : Choices)
    (h : preprintDispatch ctx s entry = .ok (fid, recv, tr)) :
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.retV (.funcVal fid [recv]) (.callValCalleeK [] [] [] (.preprintK older entry newer k')), s, ch,
            ⟨tr, [], []⟩) := by
  simp [stepFn, stepNextOther, h, Bind.bind, Except.bind]

/-- The resolution's own panic (a nil `*T` under a value method) is delivered as a fresh chain on the
preprint frame — the fatal follows at the next step. -/
@[stepFn_eqns] theorem next_preprintK_panic {s : Store} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {msg : String} (k' : Cont) (ch : Choices)
    (h : preprintDispatch ctx s entry = .error (.panic msg)) :
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.panicking [panicEntry msg] (.preprintK older entry newer k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stepNextOther, h, Bind.bind, Except.bind]

/-- The payload method RETURNED its string: stored beside the payload (`Rewrite.done`), the chain
resumes at the frame's tail. -/
@[stepFn_eqns] theorem retV_preprintK_string (s : Store) (text : GoString) (older : List PanicEntry) (entry : PanicEntry)
    (newer : List PanicEntry) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV (.string text) (.preprintK older entry newer k')) ch
      = .ok (.panicking (older ++ { entry with rewrite := .done text } :: newer) k', s, ch, ⟨[], [], []⟩) := rfl

/-- The payload method's own panic unwound onto the preprint frame: gc's unrecoverable fatal
«panic while printing panic value» (`preprintFatalStop`). -/
@[stepFn_eqns] theorem panicking_preprintK (s : Store) (chain older : List PanicEntry) (entry : PanicEntry)
    (newer : List PanicEntry) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.panicking chain (.preprintK older entry newer k')) ch = .error (preprintFatalStop ctx chain) := rfl

/-! ## (1) FRAME EXIT (`stepFrameExit`; continuations audit F4): the two entries and every arm -/

/-- A body that fell off its end at its call frame takes `stepFrameExit` (the `.next` entry). -/
@[stepFn_eqns] theorem next_frame (s : Store) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFn ctx s (.next (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch := rfl

/-- `return` at a call frame IS the frame exit (the `.signal .ret` entry). -/
@[stepFn_eqns] theorem signal_ret_frame (s : Store) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFn ctx s (.signal .ret (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch := rfl

/-- An empty frame (no targets, no results, no defers) pops itself. -/
@[stepFn_eqns] theorem frameExit_nil (s : Store) (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFrameExit ctx s [] tenv [] [] k' fr ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := rfl

/-- Defers drained, caller targets pending: the pinned RESULT CELLS are read (`loadResults` — one
emitting `loadRoot` each) and the first target's operand evaluates on the `tgtOpK` spine with the
values in hand. -/
@[stepFn_eqns] theorem frameExit_targets {s : Store} {results : List Loc} {vs : List GoValue} {tr : AccessTrace}
    (sh : TargetShape) (e : Expr) (ops : List Expr) (rest : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (k' : Cont) (fr : FuncId) (ch : Choices) (hl : loadResults ctx s results = .ok (vs, tr)) :
    stepFrameExit ctx s ((sh, e :: ops) :: rest) tenv results [] k' fr ch
      = .ok (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, ch, ⟨tr, [], []⟩) := by
  simp [stepFrameExit, hl, Bind.bind, Except.bind]

/-- A DEFER pending at exit: the deferred call is entered on the frame (results discarded) —
the drain's successor is `Entry.drainConfig` over the frame with the chain shortened. -/
@[stepFn_eqns] theorem frameExit_defer {s s' : Store} {fid : FuncId} {captured args : List GoValue} {e : Entry}
    {tr : AccessTrace} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)) :
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (e.drainConfig (.frame targets tenv results ds k' fr)
              (fun cv => .next (.frame targets tenv results ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := enterFrame_inv_ok he
  simp [stepFrameExit, enterFramePickV_of_plan_ok hpl, Bind.bind, Except.bind, runCommit_eq_ok.mpr hc,
    Functor.map, Except.map]

/-- The drain on a RUN entry, written out: the target's body under a barrier frame on the exiting
frame. -/
@[stepFn_eqns] theorem frameExit_defer_run {s s' : Store} {fid : FuncId} {captured args : List GoValue} {func : Func}
    {fenv : LocalEnv} {rl : List Loc} {tr : AccessTrace} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)) :
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.frame targets tenv results ds k' fr) func.id), s', ch,
            ⟨tr, [], []⟩) :=
  frameExit_defer targets tenv results ds k' fr ch he

/-- A deferred call whose entry panics at exit: the invocation's panic starts unwinding AT THIS
FRAME with its remaining defers. -/
@[stepFn_eqns] theorem frameExit_defer_panic {s : Store} {fid : FuncId} {captured args : List GoValue} {msg : String}
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)) :
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)]
              (.frame targets tenv results ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) := by
  simp [stepFrameExit, enterFramePickV_of_plan_panic (enterFrame_inv_panic he), Bind.bind, Except.bind]

@[stepFn_eqns] theorem frameExit_defer_nil (s : Store) (args : List GoValue) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFrameExit ctx s targets tenv results ((.nil, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry nilDerefPanicText] (.frame targets tenv results ds k' fr), s, ch, ⟨[], [], []⟩) := by
  simp [stepFrameExit]

/-- The payload method's frame on the PREPRINT frame: its one pinned result is read and delivered to
the preprint frame as a value (unit 6b). -/
@[stepFn_eqns] theorem frameExit_preprint {s : Store} {rl : Loc} {v : GoValue} (tenv : LocalEnv) (older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k'' : Cont) (fr : FuncId) (ch : Choices)
    (hl : loadRoot ctx s rl = .ok v) :
    stepFrameExit ctx s [] tenv [rl] [] (.preprintK older entry newer k'') fr ch
      = .ok (.retV v (.preprintK older entry newer k''), s, ch, ⟨[.access .read (.data rl.canon)], [], []⟩) := by
  simp [stepFrameExit, Mem.loadBinding, hl, Bind.bind, Except.bind]

/-- A targetless frame WITH pinned results, under any continuation but the preprint frame's one-result
shape, reads them and is stuck-closed (the frontend always supplies targets). -/
@[stepFn_eqns] theorem frameExit_extra_results {s : Store} {rl : Loc} {rls : List Loc} {vs : List GoValue} {tr : AccessTrace}
    (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices)
    (hl : loadResults ctx s (rl :: rls) = .ok (vs, tr))
    (hk : ∀ older entry newer k'', k' = .preprintK older entry newer k'' → rls ≠ []) :
    stepFrameExit ctx s [] tenv (rl :: rls) [] k' fr ch = .error (.stuck "extra GoCore assignment value") := by
  match k', rls with
  | [], _ => simp [stepFrameExit, hl, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | g :: k'', [] =>
      cases g <;> first
        | exact absurd rfl (hk _ _ _ _ rfl)
        | simp [stepFrameExit, hl, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | g :: k'', r :: rs =>
      cases g <;> simp [stepFrameExit, hl, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

@[stepFn_eqns] theorem frameExit_malformed (s : Store) (sh : TargetShape) (rest : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFrameExit ctx s ((sh, []) :: rest) tenv results [] k' fr ch = .error (.internal "malformed call target plan") := rfl

/-- The result readback, bottomed out: `loadResults` is one `loadRoot` per pinned cell, one read event each. -/
theorem loadResults_nil (s : Store) : loadResults ctx s [] = .ok ([], []) := rfl
theorem loadResults_cons {s : Store} {l : Loc} {ls : List Loc} {v : GoValue} {vs : List GoValue} {tr : AccessTrace}
    (hl : loadRoot ctx s l = .ok v) (hs : loadResults ctx s ls = .ok (vs, tr)) :
    loadResults ctx s (l :: ls) = .ok (v :: vs, [.access .read (.data l.canon)] ++ tr) := by
  simp [loadResults, Mem.loadBinding, hl, hs, Bind.bind, Except.bind]

/-! ## (1) The signal table (`signalStep`) -/

/-- A signal the table resolves: pass, catch or re-test — the table's successor, no store change. -/
@[stepFn_eqns] theorem signal_table {s : Store} {sg : Signal} {k : Cont} {c' : Config} (ch : Choices)
    (h : signalStep sg k = some c') : stepFn ctx s (.signal sg k) ch = .ok (c', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

/-- A signal at the empty continuation is a refusal that names its cause (B4: every driver runs its
subject under a barrier frame). -/
@[stepFn_eqns] theorem signal_stop (s : Store) (sg : Signal) (ch : Choices) :
    stepFn ctx s (.signal sg .stop) ch = .error (signalRefusal sg .stop) := by
  cases sg <;> rfl

/-- A non-`ret` signal escaping a function body refuses by name. -/
@[stepFn_eqns] theorem signal_frame_escape {s : Store} {sg : Signal} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) (hsg : sg ≠ .ret) :
    stepFn ctx s (.signal sg (.frame targets tenv results ds k' fr)) ch
      = .error (signalRefusal sg (.frame targets tenv results ds k' fr)) := by
  cases sg <;> first | exact absurd rfl hsg | rfl

/-- The table's rows, as equations. -/
theorem signalStep_seq (sg : Signal) (rest : List Stmt) (env : LocalEnv) (k' : Cont) :
    signalStep sg (.seq rest env k') = some (.signal sg k') := rfl
theorem signalStep_breakableK_brk (k' : Cont) : signalStep .brk (.breakableK k') = some (.next k') := rfl
theorem signalStep_breakableK_ret (k' : Cont) : signalStep .ret (.breakableK k') = some (.signal .ret k') := rfl
theorem signalStep_breakableK_cont (k' : Cont) : signalStep .cont (.breakableK k') = some (.signal .cont k') := rfl
theorem signalStep_loop_brk (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) :
    signalStep .brk (.loop c b env k') = some (.next k') := rfl
theorem signalStep_loop_cont (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) :
    signalStep .cont (.loop c b env k') = some (.exec (.while c b) env k') := rfl
theorem signalStep_loop_ret (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) :
    signalStep .ret (.loop c b env k') = some (.signal .ret k') := rfl
theorem signalStep_labelK_ret (name : String) (k' : Cont) : signalStep .ret (.labelK name k') = some (.signal .ret k') := rfl
theorem signalStep_labelK_brkTo_self (name : String) (k' : Cont) :
    signalStep (.brkTo name) (.labelK name k') = some (.next k') := by simp [signalStep]

/-! ## (1) The `.next` control arms: sequences, loops, labels, the terminal -/

@[stepFn_eqns] theorem next_stop (s : Store) (ch : Choices) :
    stepFn ctx s (.next .stop) ch = .error (.internal "step on terminal configuration") := rfl

@[stepFn_eqns] theorem next_seq_cons (s : Store) (t : Stmt) (rest : List Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.seq (t :: rest) env k')) ch = .ok (.exec t env (.seq rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- Block/sequence EXIT is store-neutral (`blockExit_store_eq`, C4 D8). -/
@[stepFn_eqns] theorem next_seq_nil (s : Store) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.seq [] env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem next_loop (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.loop c b env k')) ch = .ok (.exec (.while c b) env k', s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem next_breakableK (s : Store) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.breakableK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem next_labelK (s : Store) (name : String) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.labelK name k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := rfl

/-- A statement completion delivered to an expression frame is a machine-internal breach, named
(three representative instances). -/
@[stepFn_eqns] theorem next_strictK (s : Store) (op : StrictOp) (done : List GoValue) (pending : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.strictK op done pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") := rfl
@[stepFn_eqns] theorem next_ifK (s : Store) (t e : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.ifK t e env k')) ch = .error (.internal "completion delivered to expression continuation") := rfl
@[stepFn_eqns] theorem next_callArgsK (s : Store) (fid : FuncId) (plans : List (TargetShape × List Expr)) (vals : List GoValue)
    (pending : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.callArgsK fid plans vals pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") := rfl

/-- A VALUE delivered to a statement frame is a machine-internal breach, named (the `.retV`
catch-all's statement half; instances for the statement frames). -/
@[stepFn_eqns] theorem retV_seq (s : Store) (v : GoValue) (rest : List Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.seq rest env k')) ch = .error (.internal "value delivered to statement continuation") := rfl
@[stepFn_eqns] theorem retV_frame (s : Store) (v : GoValue) (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) :
    stepFn ctx s (.retV v (.frame targets tenv results ds k' fr)) ch
      = .error (.internal "value delivered to statement continuation") := rfl
@[stepFn_eqns] theorem retV_storeK (s : Store) (v : GoValue) (refs : List TargetRef) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.storeK refs vals body env k')) ch
      = .error (.internal "value delivered to statement continuation") := rfl
@[stepFn_eqns] theorem retV_stop (s : Store) (v : GoValue) (ch : Choices) :
    stepFn ctx s (.retV v .stop) ch = .error (.internal "value delivered to empty continuation") := rfl

/-! ## (2) MEMORY: reads, addresses, the store spine, block entry -/

/-- THE VARIABLE READ: the binding cell's root read (`loadRoot`), the access recorded at the leaf
the continuation projects (`projChainTarget` — the cell itself under a non-projecting frame). -/
@[stepFn_eqns] theorem evalE_var {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = some loc) (hv : loadRoot ctx s loc = .ok v) :
    stepFn ctx s (.evalE (.var id) env k) ch
      = .ok (.retV v k, s, ch, ⟨[.access .read (.data (projChainTarget ctx s k loc).canon)], [], []⟩) := by
  simp [stepFn, hl, Mem.loadBindingFor, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem evalE_var_unbound {s : Store} {id : VarId} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = none) :
    stepFn ctx s (.evalE (.var id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") := by
  simp [stepFn, hl, throw, throwThe, MonadExceptOf.throw]

/-- The ADDRESS of a local: the binding's cell, no read. -/
@[stepFn_eqns] theorem evalE_ref {s : Store} {id : VarId} {loc : Loc} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = some loc) :
    stepFn ctx s (.evalE (.ref id) env k) ch = .ok (.retV (.addr loc) k, s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hl]

@[stepFn_eqns] theorem evalE_ref_unbound {s : Store} {id : VarId} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = none) :
    stepFn ctx s (.evalE (.ref id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") := by
  simp [stepFn, hl, throw, throwThe, MonadExceptOf.throw]

/-- A global's address: its statically resolved base cell, which must exist. -/
@[stepFn_eqns] theorem evalE_global {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont) (ch : Choices) (h : gid < s.heap.size) :
    stepFn ctx s (.evalE (.global gid) env k) ch = .ok (.retV (.addr (.base ⟨gid⟩)) k, s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem evalE_global_oob {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont) (ch : Choices) (h : ¬ gid < s.heap.size) :
    stepFn ctx s (.evalE (.global gid) env k) ch
      = .error (.stuck s!"global {gid} out of range: the heap has {s.heap.size} cell(s)") := by
  simp [stepFn, h, throw, throwThe, MonadExceptOf.throw]

/-- A single assignment rides the spine as a one-target multi-assign: the target's phase-1
operands first. -/
@[stepFn_eqns] theorem exec_assign {s : Store} {lhs : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr} (rhs : Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices) (h : targetPlan lhs = some (sh, e :: ops)) :
    stepFn ctx s (.exec (.assign lhs rhs) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) := by
  cases lhs <;> simp_all [stepFn, targetPlan]

/-- The plain-variable assignment, written out: the target's address first. -/
@[stepFn_eqns] theorem exec_assign_var (s : Store) (id : VarId) (rhs : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.assign (.var id) rhs) env k) ch
      = .ok (.evalE (.ref id) env (.tgtOpK (.chain []) [] [] [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_assign_unsupported (s : Store) (feature : String) (rhs : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.assign (.unsupported feature) rhs) env k) ch = .error (.unsupported feature) := rfl

/-- Phase 1 of the spine: another operand of the current target. -/
@[stepFn_eqns] theorem retV_tgtOpK_more (s : Store) (v : GoValue) (sh : TargetShape) (ops : List GoValue) (e : Expr) (rest : List Expr)
    (refs : List TargetRef) (targets : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.tgtOpK sh ops (e :: rest) refs targets rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The current target completes (`completeTargetRef`); the next target's first operand evaluates. -/
@[stepFn_eqns] theorem retV_tgtOpK_next_target {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (sh' : TargetShape) (e : Expr) (ops' : List Expr) (rest : List (TargetShape × List Expr))
    (rop : RhsOp) (rhs : List Expr) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hc : completeTargetRef sh (v :: ops).reverse = some r) :
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: rest) rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, hc, pure_eq_ok]

/-- Every target complete, right-hand sides pending: the first evaluates under `rhsK`. -/
@[stepFn_eqns] theorem retV_tgtOpK_rhs {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (rop : RhsOp) (e : Expr) (rest : List Expr) (vals : List GoValue) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (hc : completeTargetRef sh (v :: ops).reverse = some r) :
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals body env k')) ch
      = .ok (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k'), s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, hc, pure_eq_ok]

/-- Every target complete, no right-hand sides (a receive's delivery): phase 2, the stores. -/
@[stepFn_eqns] theorem retV_tgtOpK_store {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} {r : TargetRef}
    (refs : List TargetRef) (rop : RhsOp) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hc : completeTargetRef sh (v :: ops).reverse = some r) :
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop [] vals body env k')) ch
      = .ok (.next (.storeK (refs ++ [r]) vals body env k'), s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, hc, pure_eq_ok]

@[stepFn_eqns] theorem retV_tgtOpK_malformed {s : Store} {v : GoValue} {sh : TargetShape} {ops : List GoValue} (refs : List TargetRef)
    (targets : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr) (vals : List GoValue) (body : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (hc : completeTargetRef sh (v :: ops).reverse = none) :
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs targets rop rhs vals body env k')) ch
      = .error (.internal "malformed receive target operands") := by
  simp only [stepFn, hc]
  rfl

@[stepFn_eqns] theorem retV_rhsK_more (s : Store) (v : GoValue) (rop : RhsOp) (refs : List TargetRef) (done : List GoValue) (e : Expr)
    (rest : List Expr) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.rhsK rop refs done (e :: rest) body env k')) ch
      = .ok (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The last right-hand side arrived: the value source applies (`applyRhsOp` — the identity for
`.vals`, `applyRhsOp_vals`) and phase 2 begins. -/
@[stepFn_eqns] theorem retV_rhsK_apply {s : Store} {v : GoValue} {rop : RhsOp} {done vals : List GoValue} {tr : AccessTrace}
    (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : applyRhsOp ctx s rop (v :: done).reverse = .ok (vals, tr)) :
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.next (.storeK refs vals body env k'), s, ch, ⟨tr, [], []⟩) := by
  simp only [stepFn, h, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

@[stepFn_eqns] theorem retV_rhsK_apply_panic {s : Store} {v : GoValue} {rop : RhsOp} {done : List GoValue} {msg : String}
    (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : applyRhsOp ctx s rop (v :: done).reverse = .error (.panic msg)) :
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, h, toResult_panic, Bind.bind, Except.bind, deliverS_panic, pure_eq_ok, List.nil_append]

/-- PHASE 2, one store per step, left to right: the composed `storeTarget` (its own checks fire here). -/
@[stepFn_eqns] theorem next_storeK_store {s s' : Store} {ref : TargetRef} {val : GoValue} {tr : AccessTrace} (rs : List TargetRef)
    (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : storeTarget ctx s ref val = .ok (s', tr)) :
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨tr, [], []⟩) := by
  obtain ⟨c, hpl, hc⟩ := storeTarget_inv_ok h
  simp only [stepFn, hpl, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

/-- The store through an address CHAIN, bottomed out: the chain resolves to an address
(`resolveChain`/`valueAsLoc` — the deferred nil/bounds checks), then ONE `storeLoc`, one write event. -/
@[stepFn_eqns] theorem next_storeK_chain {s s' : Store} {anchor : GoValue} {idxs : List GoValue} {steps : List TargetStep}
    {val av : GoValue} {loc : Loc} (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (hres : resolveChain ctx s anchor steps idxs = .ok av) (hloc : valueAsLoc av = .ok loc)
    (hst : storeLoc ctx s loc val = .ok s') :
    stepFn ctx s (.next (.storeK (.chain anchor idxs steps :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) := by
  simp [stepFn, storeTarget.plan, hres, hloc, Bind.bind, Except.bind, runCommit, Mem.store, hst, Functor.map, Except.map]

/-- The PLAIN-VARIABLE store (`x = v`: the anchor is the cell's address, no steps): one `storeLoc`. -/
@[stepFn_eqns] theorem next_storeK_var {s s' : Store} {loc : Loc} {val : GoValue} (rs : List TargetRef) (vrest : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) (hst : storeLoc ctx s loc val = .ok s') :
    stepFn ctx s (.next (.storeK (.chain (.addr loc) [] [] :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  next_storeK_chain rs vrest body env k' ch rfl rfl hst

/-- A store-time panic (nil address, bounds, nil map) fires AFTER the earlier stores landed. -/
@[stepFn_eqns] theorem next_storeK_panic {s : Store} {ref : TargetRef} {val : GoValue} {msg : String} (rs : List TargetRef)
    (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : storeTarget ctx s ref val = .error (.panic msg)) :
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, storeTarget_inv_panic h, toResult_panic, Bind.bind, Except.bind, deliverV_panic, List.nil_append]

/-- Phase 2 done: the statement's body (the assignment's `(.seqn #[])`, a receive's clause body). -/
@[stepFn_eqns] theorem next_storeK_done (s : Store) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.storeK [] [] body env k')) ch = .ok (.exec body env k', s, ch, ⟨[], [], []⟩) := rfl

/-- BLOCK ENTRY (C4): the declarations' cells are allocated in a fresh scope — `allocDecls` over
`env.pushScope`, one `Store.alloc` per declaration at its zero value (`blockEntry_shift`/`_lookup`/
`_zero`/`_fresh` state the layout); the body runs as a sequence under the new scope. -/
@[stepFn_eqns] theorem exec_block {s s' : Store} {decls : Array Param} {env env' : LocalEnv} (ss : Array Stmt) (k : Cont) (ch : Choices)
    (h : allocDecls ctx env.pushScope s decls.toList = .ok (env', s')) :
    stepFn ctx s (.exec (.block decls ss) env k) ch = .ok (.next (.seq ss.toList env' k), s', ch, ⟨[], [], []⟩) := by
  simp [stepFn, h, Bind.bind, Except.bind]

/-- `allocDecls` and `bindParams`, one declaration at a time (their defining equations: the floor of
block and frame entry is `Store.alloc`). -/
theorem allocDecls_nil (env : LocalEnv) (s : Store) : allocDecls ctx env s [] = .ok (env, s) := rfl
theorem allocDecls_cons {env : LocalEnv} {s s₁ : Store} {p : Param} {v : GoValue} {loc : Loc} (rest : List Param)
    (hd : defaultValue ctx p.typ = .ok v) (ha : Store.alloc ctx s v p.typ = .ok (loc, s₁)) :
    allocDecls ctx env s (p :: rest) = allocDecls ctx (env.declare p.id loc) s₁ rest := by
  simp [allocDecls, hd, ha, Bind.bind, Except.bind]
theorem bindParams_nil (env : LocalEnv) (s : Store) : bindParams ctx env s [] [] = .ok (env, s) := rfl
theorem bindParams_cons {env : LocalEnv} {s s₁ : Store} {p : Param} {v v' : GoValue} {loc : Loc} (ps : List Param)
    (vs : List GoValue) (hn : normalizeValueForTy ctx p.typ v = .ok v') (ha : Store.alloc ctx s v' p.typ = .ok (loc, s₁)) :
    bindParams ctx env s (p :: ps) (v :: vs) = bindParams ctx (env.declare p.id loc) s₁ ps vs := by
  simp [bindParams, hn, ha, Bind.bind, Except.bind]

/-! ## (3) The rest: branches, loops, Booleans -/

@[stepFn_eqns] theorem retV_ifK_true {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok true) :
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec t env k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_ifK_false {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok false) :
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec e env k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_whileK_true {s : Store} {v : GoValue} (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok true) :
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.exec b env (.loop c b env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_whileK_false {s : Store} {v : GoValue} (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok false) :
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem evalE_and (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.and l r) env k) ch = .ok (.evalE l env (.andK r env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem evalE_or (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.or l r) env k) ch = .ok (.evalE l env (.orK r env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem retV_andK_true {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok true) :
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_andK_false {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok false) :
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.retV (.bool false) k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_orK_true {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok true) :
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.retV (.bool true) k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_orK_false {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : valueAsBool v = .ok false) :
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_boolK {s : Store} {v : GoValue} {b : Bool} (k' : Cont) (ch : Choices) (hv : valueAsBool v = .ok b) :
    stepFn ctx s (.retV v (.boolK k')) ch = .ok (.retV (.bool b) k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hv, Bind.bind, Except.bind]

/-! ## (3) Literals and the strict operators -/

@[stepFn_eqns] theorem evalE_intLit (s : Store) (value : Int) (kind : IntKind) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.intLit value kind) env k) ch = .ok (.retV (.int (kind.normalize value) kind) k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem evalE_boolLit (s : Store) (value : Bool) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.boolLit value) env k) ch = .ok (.retV (.bool value) k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem evalE_stringLit (s : Store) (value : GoString) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.stringLit value) env k) ch = .ok (.retV (.string value) k, s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem evalE_unsupported (s : Store) (feature : String) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE (.unsupported feature) env k) ch = .error (.unsupported feature) := rfl

/-- A strict form with operands (`strictPlan e = some (op, e₁ :: rest)`): the first operand evaluates
under `strictK`. -/
@[stepFn_eqns] theorem evalE_strict_more {s : Store} {e e₁ : Expr} {op : StrictOp} {rest : List Expr} (env : LocalEnv) (k : Cont)
    (ch : Choices) (h : strictPlan e = some (op, e₁ :: rest)) :
    stepFn ctx s (.evalE e env k) ch = .ok (.evalE e₁ env (.strictK op [] rest env k), s, ch, ⟨[], [], []⟩) := by
  cases e <;> simp [strictPlan] at h <;> simp [stepFn, strictPlan, h]

/-- A nullary strict form (a `nil`, a float literal, a zero value, a capture-free closure): the apply
in the same step (`applyStrictOp`, read-only — `deliverS`). -/
@[stepFn_eqns] theorem evalE_strict_nullary {s s' : Store} {e : Expr} {op : StrictOp} {v : GoValue} {tr : AccessTrace} (env : LocalEnv)
    (k : Cont) (ch : Choices) (h : strictPlan e = some (op, []))
    (ha : applyStrictOp ctx s (projChainTarget ctx s k) op [] = .ok (v, s', tr)) :
    stepFn ctx s (.evalE e env k) ch = .ok (.retV v k, s', ch, ⟨tr, [], []⟩) := by
  cases e
  case slice b lo hi m => cases m <;> simp [strictPlan] at h
  all_goals simp [strictPlan] at h
  all_goals first | (obtain ⟨rfl, rfl⟩ := h) | (subst h)
  all_goals (try simp at ha)
  all_goals simp [stepFn, strictPlan, ha, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_strictK_more (s : Store) (v : GoValue) (op : StrictOp) (done : List GoValue) (e : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.strictK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.strictK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The last operand arrived: the strict APPLY (`applyStrictOp`, the leaf narrowed by the
continuation's projection chain) delivers its value. -/
@[stepFn_eqns] theorem retV_strictK_apply {s s' : Store} {v out : GoValue} {op : StrictOp} {done : List GoValue} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .ok (out, s', tr)) :
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.retV out k', s', ch, ⟨tr, [], []⟩) := by
  simp only [stepFn, ha, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

@[stepFn_eqns] theorem retV_strictK_apply_panic {s : Store} {v : GoValue} {op : StrictOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error (.panic msg)) :
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, ha, toResult_panic, Bind.bind, Except.bind, deliverS_panic, pure_eq_ok, List.nil_append]

/-- A strict apply's refusal or fatal propagates as the step's `Stop`. -/
@[stepFn_eqns] theorem retV_strictK_apply_error {s : Store} {v : GoValue} {op : StrictOp} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error e) (hne : ∀ msg, e ≠ .panic msg) :
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .error e := by
  simp only [stepFn, toResult_of_error ha hne, Bind.bind, Except.bind]

/-! ## (3) The wide statements (`stmtPlan` → `stmtOpK` → `applyStmtOp`) -/

/-- A wide statement's plan (`stmtPlan`): its target's address first, then its operands. -/
@[stepFn_eqns] theorem exec_wide {s : Store} {stmt : Stmt} {op : StmtOp} {nt : Nat} {e : Expr} {rest : List Expr} (env : LocalEnv)
    (k : Cont) (ch : Choices) (h : stmtPlan stmt = some (op, nt, e :: rest)) :
    stepFn ctx s (.exec stmt env k) ch = .ok (.evalE e env (.stmtOpK op nt [] rest env k), s, ch, ⟨[], [], []⟩) := by
  cases stmt <;> simp [stmtPlan] at h <;> simp [stepFn, stmtPlan, h]

/-- The common wide statements, written out. -/
@[stepFn_eqns] theorem exec_allocNew {s : Store} {target : Assignee} {te : Expr} (value : Expr) (typ : Ty) (env : LocalEnv) (k : Cont)
    (ch : Choices) (ht : assigneeExpr target = some te) :
    stepFn ctx s (.exec (.allocNew target value typ) env k) ch
      = .ok (.evalE te env (.stmtOpK (.allocNew typ) 1 [] [value] env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stmtPlan, ht, Bind.bind, Option.bind]

@[stepFn_eqns] theorem exec_mapAssign (s : Store) (base index value : Expr) (keyTy valueTy : Ty) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.mapAssign base index value keyTy valueTy) env k) ch
      = .ok (.evalE base env (.stmtOpK (.mapAssign keyTy valueTy) 0 [] [index, value] env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_appendSlice {s : Store} {target : Assignee} {te : Expr} (elem : Ty) (slice elems : Expr) (env : LocalEnv)
    (k : Cont) (ch : Choices) (ht : assigneeExpr target = some te) :
    stepFn ctx s (.exec (.appendSlice target elem slice elems) env k) ch
      = .ok (.evalE te env (.stmtOpK (.appendSlice elem) 1 [] [slice, elems] env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stmtPlan, ht, Bind.bind, Option.bind]

@[stepFn_eqns] theorem exec_print {s : Store} {args : Array Expr} {e : Expr} {rest : List Expr} (newline : Bool) (env : LocalEnv) (k : Cont)
    (ch : Choices) (hargs : args.toList = e :: rest) :
    stepFn ctx s (.exec (.print newline args) env k) ch
      = .ok (.evalE e env (.stmtOpK (.print newline) 0 [] rest env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stmtPlan, hargs]

/-- The wide operand walk: a TARGET address is checked as it arrives when more operands follow
(interpreter panic timing). -/
@[stepFn_eqns] theorem retV_stmtOpK_more_target {s : Store} {v : GoValue} {loc : Loc} {nt : Nat} {done : List GoValue} (op : StmtOp) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (hlt : done.length < nt) (hloc : valueAsLoc v = .ok loc) :
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hlt, hloc, Bind.bind, Except.bind]

/-- A nil target address panics at its arrival. -/
@[stepFn_eqns] theorem retV_stmtOpK_more_target_nil {s : Store} {nt : Nat} {done : List GoValue} (op : StmtOp) (e : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (hlt : done.length < nt) :
    stepFn ctx s (.retV .nil (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hlt, valueAsLoc, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_stmtOpK_more_operand {s : Store} {v : GoValue} {nt : Nat} {done : List GoValue} (op : StmtOp) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (hge : ¬ done.length < nt) :
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hge]

/-- The last operand arrived: the wide APPLY (`applyStmtOp` — validate, then commit; the tape
threads through it: the `appendSpill`/`intn` consults) — one step, the statement completes, its
output on the label (`stmtOpOut`: the `print` bytes). -/
@[stepFn_eqns] theorem retV_stmtOpK_apply {s s' : Store} {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue} {ch' : Choices}
    {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : applyStmtOp ctx s ch op nt (v :: done).reverse = .ok (s', ch', ps, tr)) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch
      = .ok (.next k', s', ch', ⟨tr, ps, stmtOpOut op (v :: done).reverse⟩) := by
  obtain ⟨c, hpl, hc⟩ := applyStmtOp_inv_ok h
  simp only [stepFn, hpl, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_eq_ok.mpr hc, Functor.map, Except.map]

@[stepFn_eqns] theorem retV_stmtOpK_apply_panic {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (h : applyStmtOp ctx s ch op nt (v :: done).reverse = .error (.panic msg)) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, applyStmtOp_inv_panic h, toResult_panic, Bind.bind, Except.bind, deliverV_panic, List.nil_append]

/-! ## (3) Ranges over maps -/

@[stepFn_eqns] theorem exec_mapRange (s : Store) (keyVar valVar : Option VarId) (mapExpr : Expr) (keyTy valTy : Ty) (body : Stmt)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) ch
      = .ok (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k), s, ch, ⟨[], [], []⟩) := rfl

/-- The range STARTS: the base cell and the start-id set are recorded (one map read). -/
@[stepFn_eqns] theorem retV_mapRangeK {s : Store} {v : GoValue} {base : Option Loc} {start : Array Nat} {tr : AccessTrace}
    (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : mapRangeStartSets s v = .ok (base, start, tr)) :
    stepFn ctx s (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k')) ch
      = .ok (.next (.mapIterK keyVar valVar keyTy valTy body base #[] start env k'), s, ch, ⟨tr, [], []⟩) := by
  simp [stepFn, h, Bind.bind, Except.bind]

/-- A range pick with NO candidate left: the range ends (the live read still happens). -/
@[stepFn_eqns] theorem next_mapIterK_done {s : Store} {keyTy valTy : Ty} {base : Option Loc} {produced : Array Nat} {tr : AccessTrace}
    (keyVar valVar : Option VarId) (body : Stmt) (start : Array Nat) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : mapIterCandidates ctx s keyTy valTy base produced = .ok (#[], tr)) :
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch, ⟨tr, [], []⟩) := by
  simp [stepFn, h, Bind.bind, Except.bind]

/-- A range pick with candidates: THE `mapIter` consult at `width` (the candidates plus the STOP slot
when no mandatory start key remains); a candidate slot binds the iteration variables in a fresh
scope and runs the body, the stop slot ends the range. -/
@[stepFn_eqns] theorem next_mapIterK_pick {s s' : Store} {keyTy valTy : Ty} {base : Option Loc} {produced start : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat} {ch' : Choices} {ps : List PickRecord}
    {id : Nat} {key value : GoValue} {env env' : LocalEnv} (keyVar valVar : Option VarId) (body : Stmt) (k' : Cont) (ch : Choices)
    (h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr)) (hne : cands.isEmpty = false)
    (hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (hget : cands[idx]? = some (id, key, value))
    (hb : bindIterVars ctx env.pushScope s keyVar valVar keyTy valTy key value = .ok (env', s')) :
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.exec body env' (.mapIterK keyVar valVar keyTy valTy body base (produced.push id) start env k'), s', ch',
            ⟨tr, ps, []⟩) := by
  subst hw
  simp [stepFn, h, hne, hc, hget, hb, Bind.bind, Except.bind]

@[stepFn_eqns] theorem next_mapIterK_stop {s : Store} {keyTy valTy : Ty} {base : Option Loc} {produced start : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat} {ch' : Choices} {ps : List PickRecord}
    (keyVar valVar : Option VarId) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr)) (hne : cands.isEmpty = false)
    (hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (hget : cands[idx]? = none) :
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch', ⟨tr, ps, []⟩) := by
  subst hw
  simp [stepFn, h, hne, hc, hget, Bind.bind, Except.bind]

/-! ## (3) Comma-ok forms, multi-assignment -/

@[stepFn_eqns] theorem exec_mapLookup {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} (base index : Expr) (keyTy valueTy : Ty) (env : LocalEnv) (k : Cont) (ch : Choices)
    (h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)) :
    stepFn ctx s (.exec (.mapLookup t okT base index keyTy valueTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy) [base, index] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem exec_typeAssert {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} (expr : Expr) (targetTy : Ty) (env : LocalEnv) (k : Cont) (ch : Choices)
    (h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)) :
    stepFn ctx s (.exec (.typeAssert t okT expr targetTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.typeAssert targetTy) [expr] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem exec_assignMany {s : Store} {left : Array Assignee} {right : Array Expr} {sh : TargetShape} {e : Expr}
    {ops : List Expr} {rest : List (TargetShape × List Expr)} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hsz : left.size = right.size) (h : targetsPlan left.toList = some ((sh, e :: ops) :: rest)) :
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hsz, h]

@[stepFn_eqns] theorem exec_assignMany_arity {s : Store} {left : Array Assignee} {right : Array Expr} (env : LocalEnv) (k : Cont)
    (ch : Choices) (hsz : left.size ≠ right.size) :
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .error (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}") := by
  simp [stepFn, hsz, throw, throwThe, MonadExceptOf.throw]

/-! ## (3) Channels, select, go, sync, atomic -/

@[stepFn_eqns] theorem exec_chanSend (s : Store) (chE value : Expr) (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.chanSend chE value elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.send elem) [] [value] env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem exec_closeChan (s : Store) (chE : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.closeChan chE) env k) ch = .ok (.evalE chE env (.chanStK .close [] [] env k), s, ch, ⟨[], [], []⟩) := rfl

/-- A receive with admitted targets (at most two, each with a plan): the channel operand first; the
targets evaluate AFTER the communication (phase 2). -/
@[stepFn_eqns] theorem exec_chanRecv {s : Store} {targets : Array Assignee} {plans : List (TargetShape × List Expr)} (chE : Expr) (elem : Ty)
    (env : LocalEnv) (k : Cont) (ch : Choices) (hsz : ¬ targets.size > 2) (hp : targetsPlan targets.toList = some plans) :
    stepFn ctx s (.exec (.chanRecv targets chE elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.recv targets.toList elem) [] [] env k), s, ch, ⟨[], [], []⟩) := by
  have hplan : chanPlan (.chanRecv targets chE elem) = some (.recv targets.toList elem, [chE]) := by
    simp [chanPlan, hsz, hp, Bind.bind, Option.bind]
  simp only [stepFn]
  split
  · rename_i heq; rw [hplan] at heq; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq; rfl
  · rename_i heq; rw [hplan] at heq; simp at heq
  · rename_i heq; rw [hplan] at heq; simp at heq

@[stepFn_eqns] theorem retV_chanStK_more (s : Store) (v : GoValue) (op : ChanStOp) (done : List GoValue) (e : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.chanStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.chanStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The channel APPLY (`applyChanOp`): a completed op's successor, or the parked shape. -/
@[stepFn_eqns] theorem retV_chanStK_apply {s s' : Store} {v : GoValue} {op : ChanStOp} {done : List GoValue} {c' : Config} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (h : applyChanOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)) :
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) := by
  simp only [stepFn, h, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

@[stepFn_eqns] theorem retV_chanStK_apply_panic {s : Store} {v : GoValue} {op : ChanStOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (h : applyChanOp ctx s op (v :: done).reverse env k' = .error (.panic msg)) :
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, h, toResult_panic, Bind.bind, Except.bind, deliverS_panic, pure_eq_ok, List.nil_append]

@[stepFn_eqns] theorem exec_selectStmt {s : Store} {clauses : Array (SelectClauseHead × Stmt)} {e : Expr} {rest : List Expr}
    (default? : Option Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) (h : selectOperands clauses.toList = e :: rest) :
    stepFn ctx s (.exec (.selectStmt clauses default?) env k) ch
      = .ok (.evalE e env (.selectOpsK clauses.toList default? [] rest env k), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem exec_selectStmt_default {s : Store} {clauses : Array (SelectClauseHead × Stmt)} (d : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices) (h : selectOperands clauses.toList = []) :
    stepFn ctx s (.exec (.selectStmt clauses (some d)) env k) ch = .ok (.exec d env k, s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem exec_selectStmt_block {s : Store} {clauses : Array (SelectClauseHead × Stmt)} (env : LocalEnv) (k : Cont) (ch : Choices)
    (h : selectOperands clauses.toList = []) :
    stepFn ctx s (.exec (.selectStmt clauses none) env k) ch = .ok (.blockedSelect [] env k, s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, h]

@[stepFn_eqns] theorem retV_selectOpsK_more (s : Store) (v : GoValue) (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.selectOpsK clauses default? done (e :: rest) env k')) ch
      = .ok (.evalE e env (.selectOpsK clauses default? (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The select APPLY (`applySelect`): the tape threads through it (the multi-ready `l2Entry` consult);
the sequential step projects the emitted commit identity away. -/
@[stepFn_eqns] theorem retV_selectOpsK_apply {s s' : Store} {v : GoValue} {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {c' : Config} {ch' : Choices} {ps : List PickRecord} {cl? : Option EvClause} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .ok (c', s', ch', ps, cl?, tr)) :
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) := by
  simp only [stepFn, h, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

@[stepFn_eqns] theorem exec_goStmt (s : Store) (callee : Expr) (args : Array Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.goStmt callee args) env k) ch
      = .ok (.evalE callee env (.goCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem retV_goCalleeK_args {s : Store} {v : GoValue} (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hd : deferrableCallee v = true) :
    stepFn ctx s (.retV v (.goCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, hd]

/-- The completed SPAWN position fails closed sequentially: spawning is a pool step (`stepMulti`). -/
@[stepFn_eqns] theorem retV_goCalleeK_spawn {s : Store} {v : GoValue} (env : LocalEnv) (k' : Cont) (ch : Choices) (hd : deferrableCallee v = true) :
    stepFn ctx s (.retV v (.goCalleeK [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") := by
  simp [stepFn, hd, throw, throwThe, MonadExceptOf.throw]

@[stepFn_eqns] theorem retV_goArgsK_more (s : Store) (v cv : GoValue) (vals : List GoValue) (a : Expr) (rest : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.goArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

@[stepFn_eqns] theorem retV_goArgsK_spawn (s : Store) (v cv : GoValue) (vals : List GoValue) (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.goArgsK cv vals [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") := rfl

@[stepFn_eqns] theorem exec_syncStmt {s : Store} {op : SyncStmtOp} {args : Array Expr} {targets : Array Assignee} {sop : SyncOp} {e : Expr}
    {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices) (h : syncPlan (.syncStmt op args targets) = some (sop, e :: rest)) :
    stepFn ctx s (.exec (.syncStmt op args targets) env k) ch
      = .ok (.evalE e env (.syncStK sop [] rest env k), s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn]
  split
  · rename_i heq; rw [h] at heq; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq; rfl
  · rename_i heq; rw [h] at heq; simp at heq
  · rename_i heq; rw [h] at heq; simp at heq

@[stepFn_eqns] theorem exec_atomicStmt {s : Store} {op : AtomicStmtOp} {kind : IntKind} {args : Array Expr} {targets : Array Assignee}
    {aop : AtomicOp} {e : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices)
    (h : atomicPlan (.atomicStmt op kind args targets) = some (aop, e :: rest)) :
    stepFn ctx s (.exec (.atomicStmt op kind args targets) env k) ch
      = .ok (.evalE e env (.atomicStK aop [] rest env k), s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn]
  split
  · rename_i heq; rw [h] at heq; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq; rfl
  · rename_i heq; rw [h] at heq; simp at heq
  · rename_i heq; rw [h] at heq; simp at heq

@[stepFn_eqns] theorem retV_syncStK_more (s : Store) (v : GoValue) (op : SyncOp) (done : List GoValue) (e : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.syncStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.syncStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The sync APPLY (`applySyncOp`; only the TRY heads draw from the tape). -/
@[stepFn_eqns] theorem retV_syncStK_apply {s s' : Store} {v : GoValue} {op : SyncOp} {done : List GoValue} {c' : Config} {ch' : Choices}
    {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (h : applySyncOp ctx s ch op (v :: done).reverse env k' = .ok (c', s', ch', ps, tr)) :
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) := by
  simp only [stepFn, h, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

/-- A sync misuse is the UNRECOVERABLE `fatal` terminal — it propagates as the step's `Stop`
(the shape `Finish.fatal` classifies). -/
@[stepFn_eqns] theorem retV_syncStK_apply_error {s : Store} {v : GoValue} {op : SyncOp} {done : List GoValue} {e : Stop} (env : LocalEnv)
    (k' : Cont) (ch : Choices) (h : applySyncOp ctx s ch op (v :: done).reverse env k' = .error e) (hne : ∀ msg, e ≠ .panic msg) :
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .error e := by
  simp only [stepFn, toResult_of_error h hne, Bind.bind, Except.bind]

@[stepFn_eqns] theorem retV_atomicStK_more (s : Store) (v : GoValue) (op : AtomicOp) (done : List GoValue) (e : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.atomicStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.atomicStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) := rfl

/-- The atomic APPLY (`applyAtomicOp`): one fused step, no consult. -/
@[stepFn_eqns] theorem retV_atomicStK_apply {s s' : Store} {v : GoValue} {op : AtomicOp} {done : List GoValue} {c' : Config} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (h : applyAtomicOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)) :
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) := by
  simp only [stepFn, h, toResult_ok, Bind.bind, Except.bind, deliverS_ok, pure_eq_ok]

@[stepFn_eqns] theorem retV_atomicStK_apply_panic {s : Store} {v : GoValue} {op : AtomicOp} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (h : applyAtomicOp ctx s op (v :: done).reverse env k' = .error (.panic msg)) :
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  simp only [stepFn, h, toResult_panic, Bind.bind, Except.bind, deliverS_panic, pure_eq_ok, List.nil_append]

/-- The four blocked shapes: relation-silent, the sequential DEADLOCK terminal. -/
@[stepFn_eqns] theorem blockedSend (s : Store) (chl : Option Loc) (v : GoValue) (k : Cont) (ch : Choices) :
    stepFn ctx s (.blockedSend chl v k) ch = .error .deadlock := rfl
@[stepFn_eqns] theorem blockedRecv (s : Store) (chl : Option Loc) (targets : List Assignee) (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.blockedRecv chl targets elem env k) ch = .error .deadlock := rfl
@[stepFn_eqns] theorem blockedSelect (s : Store) (clauses : List EvClause) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.blockedSelect clauses env k) ch = .error .deadlock := rfl
@[stepFn_eqns] theorem blockedSync (s : Store) (op : SyncOp) (loc : Loc) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.blockedSync op loc env k) ch = .error .deadlock := rfl

/-! ## (3) The probe and the `unseq` sweep -/

@[stepFn_eqns] theorem exec_unseqProbe (s : Store) (e : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.unseqProbe e) env k) ch = .ok (.evalE e env (.probeK k), s, ch, ⟨[], [], []⟩) := rfl

/-- A probed operand that yields a VALUE is re-evaluated at its residual position; nothing consumed. -/
@[stepFn_eqns] theorem retV_probeK (s : Store) (v : GoValue) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.probeK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) := rfl

/-- The `unseq` sweep's three positions reduce to their helpers (each stated against its rules in
`MachineSound`). -/
@[stepFn_eqns] theorem exec_unseq (s : Store) (g : UnseqGraph) (thenB : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec (.unseq g thenB) env k) ch = stepUnseqEnter ctx s g thenB env k ch := rfl
@[stepFn_eqns] theorem next_unseqK (s : Store) (g : UnseqGraph) (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef))
    (env : LocalEnv) (ph : UnseqPhase) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.next (.unseqK g thenB st tg env ph k')) ch = stepUnseqNext ctx s g thenB st tg env ph k' ch := rfl
@[stepFn_eqns] theorem retV_unseqK (s : Store) (v : GoValue) (g : UnseqGraph) (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (ph : UnseqPhase) (k' : Cont) (ch : Choices) :
    stepFn ctx s (.retV v (.unseqK g thenB st tg env ph k')) ch = stepUnseqValue ctx s v g thenB st tg env ph k' ch := rfl

/-- `unseq` ENTER at a statement-sequence position: the shape and the id-level checks pass, the
binder cells are allocated in a sweep-private scope (`allocDecls` over `env.pushScope`, C4 D3 (b)). -/
@[stepFn_eqns] theorem unseqEnter {s s' : Store} {g : UnseqGraph} {env env' : LocalEnv} (thenB : Stmt) (rest : List Stmt) (k' : Cont)
    (ch : Choices) (hwf : g.wellFormed? = none) (hen : unseqEntryCheck? g env = none)
    (ha : allocDecls ctx env.pushScope s g.cells = .ok (env', s')) :
    stepFn ctx s (.exec (.unseq g thenB) env (.seq rest env k')) ch
      = .ok (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env k')), s', ch, ⟨[], [], []⟩) := by
  simp [stepFn, stepUnseqEnter, hwf, hen, ha, Bind.bind, Except.bind]

/-- A value head's result is WRITTEN into its predeclared binder cell (a root cell: one `storeLoc`)
and the occurrence is done. -/
@[stepFn_eqns] theorem unseqValue {s s' : Store} {v : GoValue} {g : UnseqGraph} {i : Nat} {o : UnseqOcc} {bind : VarId} {head : Expr}
    {loc : Loc} (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hget : g.occs[i]? = some o) (hbody : o.body = .eval bind head) (hloc : unseqCellLoc env bind = .ok loc)
    (hst : storeLoc ctx s loc v = .ok s') :
    stepFn ctx s (.retV v (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) := by
  simp [stepFn, stepUnseqValue, hget, hbody, hloc, Mem.store, hst, Bind.bind, Except.bind]

/-- The scheduler at `.run i` on a value head: the head evaluates under the waiting frame. -/
@[stepFn_eqns] theorem unseqRun_eval {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc} {bind : VarId} {head : Expr} (thenB : Stmt)
    (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hget : g.occs[i]? = some o) (hbody : o.body = .eval bind head) :
    stepFn ctx s (.next (.unseqK g thenB st tg env (.run i) k')) ch
      = .ok (.evalE head env (.unseqK g thenB st tg env (.wait i) k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stepUnseqNext, hget, hbody]

/-- The scheduler at `.wait i` on an invocation: its statement completion marks it done. -/
@[stepFn_eqns] theorem unseqWait_invoke {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc} {binds : List VarId} {callee : Expr}
    {args : List Expr} (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hget : g.occs[i]? = some o) (hbody : o.body = .invoke binds callee args) :
    stepFn ctx s (.next (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s, ch, ⟨[], [], []⟩) := by
  simp [stepFn, stepUnseqNext, hget, hbody]

/-! ## The pinned SETUP EQUATION (request 2): no globals, no package initializer -/

/-- The empty store is well-formed. -/
theorem stateWf_empty : StateWf ctx ({} : Store) := by
  refine ⟨?_, ?_⟩
  · simp [Store.locSup, Heap.locSup, heapCellsSup, Store.nextAddr]
  · simp [HeapNormal, Heap.normalB]

/-- Seeding no globals from the fresh store is the identity. -/
theorem seedGlobals_nil : seedGlobals ctx ({} : Store) #[] = .ok {} := by
  simp [seedGlobals, Store.nextAddr, Bind.bind, Except.bind]

/-- A program with no `$pkginit` has no initialization phase. -/
theorem runPkgInitM_none {fuel : Nat} {s : Store} {ch : Choices} (h : findFunctionIn? ctx.functions pkgInitFuncId = none) :
    runPkgInitM ctx fuel s ch = .ok (s, ch) := by
  simp [runPkgInitM, h]

/-- **The setup equation.** For a program with NO globals and NO package initializer, successful
setup is: the subject found by name, its arity matched, the type table's reserved prefix in
place, the arguments BOUND (normalized at their declared types — `bindParams`, one `Store.alloc`
each from the EMPTY store) and the results declared at their zero values (`allocDecls`) and PINNED
(`pinResultLocs`); the entry configuration runs the body in the frame environment under a
targetless barrier frame naming the subject, over the store after binding, with the residual tape
EQUAL to the input tape (no phase consumed). The layout is `setup_lookup_arg`/`_result`,
`setup_resultLocs` and `setup_heap_size` below. -/
theorem runProgramSetup_noInit {fuel : Nat} {program : Program} {name : String} {args : Array GoValue} {choices : Choices}
    {func : Func} {env frameEnv : LocalEnv} {s₂ s₃ : Store} {resultLocs : List Loc}
    (hf : findFunctionIn? program.funcs ⟨name⟩ = some func) (harity : func.args.size = args.size)
    (hres : program.typeDefs.hasReservedPrefix = true) (hglob : program.globals = #[])
    (hinit : findFunctionIn? program.funcs pkgInitFuncId = none)
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs) :
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, choices) := by
  have hinit' : findFunctionIn? (ProgramCtx.functions ⟨program⟩) pkgInitFuncId = none := hinit
  simp [runProgramSetupM, hf, harity, hres, hglob, seedGlobals_nil, stateWf_empty, runPkgInitM_none hinit', hb, ha, hp,
    Bind.bind, Except.bind]

/-- `pinResultLocs` reads the declared bindings back, in order. -/
theorem pinResultLocs_eq_of_lookup :
    ∀ (env : LocalEnv) (ps : List Param) (f : Nat → Loc),
      (∀ (j : Nat) (hj : j < ps.length), LocalEnv.lookup env ps[j].id = some (f j)) →
      pinResultLocs env ps = .ok ((List.range ps.length).map f)
  | _, [], _, _ => rfl
  | env, p :: ps, f, h => by
      have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      have hrest := pinResultLocs_eq_of_lookup env ps (fun j => f (j + 1)) (fun j hj => by
        have := h (j + 1) (by simpa using Nat.succ_lt_succ hj)
        simpa using this)
      simp [pinResultLocs, h0, hrest, Bind.bind, Except.bind, List.range_succ_eq_map, Function.comp_def]

/-- The argument layout at setup: parameter `i` is bound to cell `i` of the fresh store
(`entrySlot {} i = .base ⟨i⟩`), under the signature's ids pairwise distinct. -/
theorem setup_lookup_arg {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (i : Nat) (hi : i < func.args.size) :
    LocalEnv.lookup frameEnv func.args[i].id = some (.base ⟨i⟩) := by
  have hd : namesDistinct (func.args.toList.map (·.id) ++ func.results.toList.map (·.id)) = true := by
    simpa [Array.toList_append, List.map_append] using hdistinct
  obtain ⟨hda, -, hdisj⟩ := namesDistinct_append hd
  have hi' : i < func.args.toList.length := by simpa using hi
  have hmem : func.args.toList[i].id ∈ func.args.toList.map (·.id) := List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩
  rw [← Array.getElem_toList (h := hi'), allocDecls_lookup_preserve _ _ _ ha (hdisj _ hmem)]
  have := bindParams_lookup _ _ _ _ hb hda i hi'
  simpa using this

/-- The result layout at setup: result `j` is bound to the cell after all the parameters. -/
theorem setup_lookup_result {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (j : Nat) (hj : j < func.results.size) :
    LocalEnv.lookup frameEnv func.results[j].id = some (.base ⟨func.args.size + j⟩) := by
  have hd : namesDistinct (func.args.toList.map (·.id) ++ func.results.toList.map (·.id)) = true := by
    simpa [Array.toList_append, List.map_append] using hdistinct
  obtain ⟨-, hdr, -⟩ := namesDistinct_append hd
  have hj' : j < func.results.toList.length := by simpa using hj
  have hsize := bindParams_heap_size _ _ _ _ hb
  rw [← Array.getElem_toList (h := hj'), allocDecls_lookup _ _ _ ha hdr j hj', hsize]
  simp

/-- The pinned result locations at setup are exactly the result cells, in order. -/
theorem setup_resultLocs {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs) :
    resultLocs = (List.range func.results.size).map (fun j => Loc.base ⟨func.args.size + j⟩) := by
  have := pinResultLocs_eq_of_lookup frameEnv func.results.toList (fun j => Loc.base ⟨func.args.size + j⟩) (fun j hj => by
    have hj' : j < func.results.size := by simpa using hj
    have := setup_lookup_result hb ha hdistinct j hj'
    simpa [Array.getElem_toList] using this)
  rw [this] at hp
  simp only [Except.ok.injEq] at hp
  simpa using hp.symm

/-- The store after setup holds exactly the parameter and result cells. -/
theorem setup_heap_size {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃)) :
    s₃.heap.size = func.args.size + func.results.size := by
  have h1 := bindParams_heap_size _ _ _ _ hb
  have h2 := allocDecls_heap_size _ _ _ ha
  simp at h1 h2
  omega

end GoLean.GoCore.Equations
