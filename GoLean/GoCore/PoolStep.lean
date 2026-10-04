import GoLean.GoCore.Multi

/-!
# The LABELLED pool relation — FROZEN DEFINITIONS (the pool/registry half, spec packet)

[AGENT design worker, lane `design/pool-relation-spec-1004`] 2026-10-04. Authority: [USER] Mike
2026-10-04 «Great, launch it» (relayed by the [AGENT] coordinator — cite as relayed), approving the
plan: a spec packet (frozen definitions + exact statements + a `sorry`'d skeleton outside the build +
a design note) as a NAMED DESIGN GATE, then a Codex grind under a tight brief. Design note:
`docs/2026-10-04_pool-relation-spec.md`; the statements: `GoLean/GoCore/PoolStatement.lean`; the
skeleton: `docs/specs/pool-relation/Skeleton.lean` (outside every build target and gate scan).
Every decision below is [AGENT], PENDING [USER] ratification at the gate.

THIS FILE IS DEFINITIONS ONLY — no theorem of substance, no `sorry`, total, no `partial`.

What is owed (`CLAUDE.md` item (2); the window plan `docs/2026-09-24_window-plan.md` §2): «the
labelled pool relation over `StepLabel` with attribution, registry boundaries and the pool
deadlock's own condition». What exists (`Multi.lean`): `StepM : MultiConfig → MultiConfig →
AccessTrace → Prop`, labelled by the memory TRACE only, with `stepMulti_sound`/`stepM_complete`
(`MultiSound.lean`) relating it to the executable `stepMulti`, whose event `StepEvent := { who,
action, label : StepLabel }` carries the full label and the attribution the relation drops.

THE SHAPE, in one breath. `StepML ctx m m' ev` is `StepM` RE-LABELLED BY THE FULL EXECUTABLE
EVENT: the same `StepEvent` the executable returns — `who` (attribution), `action` (the pool's
classification of the step, incl. the spawned child's and the pairing partner's index) and the
full `StepLabel` (trace, picks, out). ONE event type at both layers (the step-label reshape's
discipline, `docs/2026-09-28_step-label.md` §3). Scheduling is LATITUDE, reified as a PICK: the
rule premise `SchedSlot` names the SLOT of the boundary's menu the picked goroutine occupies, and
the event's `picks` channel begins with that consultation's RECORD (`schedRecord` — `[]` at a
singleton menu, the uniform bound-≤-1 rule; `[⟨site, |menu|, slot⟩]` otherwise), exactly as
`stepMulti` prepends it. Nothing is baked into evaluator recursion: every consultation the pool
makes (`l1Sched`/`postOp`/`backEdge`, `l2Arrival`, `l4Waiter`, `repanicCollapse`, and the
sequential step's own) is a RECORD in the event, stated with `PickRecord.ofPick` like the
sequential rules do. The existing trace-labelled `StepM` is the PROJECTION of this relation
(`stepML_erase_stmt`); nothing of it is restated or weakened.

Registry BOUNDARIES are `Thread.atBoundary` on the running goroutine (the definition of record
since C5), surfaced here as `MultiConfig.schedMenu?` (the site and slot menu a boundary
consults, `none` off a boundary); a context switch happens ONLY at one (`stepML_switch_boundary_stmt`).

The pool DEADLOCK gets its OWN predicate, `PoolDeadlock` — the driver's third classification
(no tombstone, main not at its terminal, nobody runnable) over a non-empty pool — stated once,
apart from the sequential `Blocked` (the two differ by the wake condition:
`singleton_deadlock_stmt`). The relation stays deadlock-SILENT (no rule; `asleep_silent_stmt`).

The DRIVER's own structure is a second carrier: `PoolPrefix` is the counted, choice-threaded
closure of the driver loop's iterations (`Continue` — the pre-step gate incl. the main-exit
window's draw, RECORDED — then `stepMulti`, then the detector fold), the pool twin of
`ExecutionStatement.Prefix`; `PoolFinish` the driver's classification with TERMINAL PRIORITY
(tombstone, then main's exit, then deadlock, all at cost 0; a fatal step or a detected race at
cost 1), carrying the window's record, the racing step's event and the residual tape.
-/

namespace GoLean.GoCore.Machine

variable (ctx : ProgramCtx)

open GoLean

/-! ## Registry boundaries and the scheduling consultation -/

/-- **The scheduling consultation a pool configuration makes**: at a registry boundary
(`Thread.atBoundary` on the running goroutine), the SITE the boundary consults
(`Thread.boundarySite`) and its SLOT MENU (`schedSlots`); `none` when the running goroutine is
inside a registry-free segment (it continues privately) or the running index is out of range. -/
def MultiConfig.schedMenu? (m : MultiConfig) : Option (ChoiceSite × List Nat) :=
  match m.threads[m.cur]? with
  | some t =>
      if t.atBoundary then
        some (t.boundarySite, schedSlots ctx m.shared m.threads m.cur t.boundarySite)
      else none
  | none => none

/-- **The scheduling pick, as a slot** (the relation's premise): at a boundary, slot `slot` of the
menu names goroutine `i`; off a boundary the running goroutine continues (`i = m.cur`, slot 0 —
no menu, no record). The slot formulation refines `schedPick` (membership in `runnableIdxs`):
`schedSlot_iff_stmt`. -/
def SchedSlot (m : MultiConfig) (i slot : Nat) : Prop :=
  match m.threads[m.cur]? with
  | some t =>
      if t.atBoundary then (schedSlots ctx m.shared m.threads m.cur t.boundarySite)[slot]? = some i
      else i = m.cur ∧ slot = 0
  | none => False

/-- **The scheduling consultation's RECORD** — what `stepMulti` prepends to the picked goroutine's
event picks: `PickRecord.ofPick site |menu| slot` at a boundary (`[]` at a singleton menu — the
uniform bound-≤-1 rule, sequential conservation's hinge), `[]` off a boundary. -/
def schedRecord (m : MultiConfig) (slot : Nat) : List PickRecord :=
  match m.threads[m.cur]? with
  | some t =>
      if t.atBoundary then
        PickRecord.ofPick t.boundarySite (schedSlots ctx m.shared m.threads m.cur t.boundarySite).length slot
      else []
  | none => []

/-- The select interception's action from the apply's emitted commit identity (`stepThread`'s
match, named): a committed clause, or a pass (default taken / parked / the apply's panic). -/
def selectAction : Option EvClause → StepAction
  | some cl => .selectCommit cl
  | none => .selectPass

/-! ## The labelled pool relation -/

/-- **THE LABELLED POOL RELATION** (`StepM` re-labelled by the full executable event; `stepMulti`
is its executable instantiation — `stepMulti_sound_stmt`/`stepML_complete_stmt`). Ten rule
classes, one per arm of `stepMulti ∘ stepThread`, every premise `StepM`'s or `stepThread`'s own:

* `strip` — the boundary CLEAR (C5): the flagged goroutine clears its flag; `.opDoneStrip`.
* `abort` — the ABORT (B4): a settled unrecovered chain at `.stop` renders into the tombstone
  under the `repanicCollapse` pick (quantified below its width); `.aborted`, the pick recorded.
* `spawn` — the completed `go` position forks: the parent's successor is flagged `l1Sched`
  (`Thread.afterStep`), the child is appended at index `|threads|`; `.spawned |threads|`; the
  label is the `go` edge, then the child's entry reads ATTRIBUTED to it, the entry's records.
* `thread` — a partnerless goroutine step by the sequential `Step` at a non-select position (the
  arrival analysis found no waiter involvement); `.privateStep`; the label is the step's, its
  picks after the scheduling record.
* `selectApply` / `selectApplyPanic` — the select INTERCEPTION (the cell-path select apply, run
  at the pool so the emitted commit identity reaches the event): `applySelect`'s success with
  `selectAction cl?`, or its recoverable panic delivered as the unwinding configuration
  (`.selectPass`, no trace, no output — `deliver`'s convention).
* `pair` / `pickPair` — the arrival pairing with a parked partner (gc's waiter-queue priority):
  the L4 waiter pick, after the L2 clause pick on the multi-ready select arrival; `.paired j`
  for the partner `j`; the label is `applyPairing`'s (entry emission, both goroutines' actions,
  the partner's attributed).
* `pickCommit` — the multi-ready select arrival whose L2-picked clause is cell-only ready,
  committed at the pool; `.selectCommit cl`; the label is the poll over all clauses then the
  commit's action, the L2 record.
* `wake` — a wake-ready parked goroutine resumes (head-commit, no re-randomization); `.woke`.

Every rule's successor has `cur := i`. The scheduling pick (`SchedSlot`) and its record
(`schedRecord`) are the only pool-layer additions to each arm's own label. Deadlock is
relation-SILENT: an all-asleep pool has no rule (`asleep_silent_stmt`). -/
inductive StepML : MultiConfig → MultiConfig → StepEvent → Prop where
  | strip {m : MultiConfig} {i slot : Nat} {c : Config} {site : ChoiceSite} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c (some site)) →
      StepML m ⟨m.threads.setIfInBounds i (.running c none), m.shared, i⟩
        ⟨i, .opDoneStrip, ⟨[], schedRecord ctx m slot, []⟩⟩
  | abort {m : MultiConfig} {i slot : Nat} {c : Config} {first : PanicEntry}
      {rest : List PanicEntry} {pick : Nat} {msg : String} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      c.abort? = some (first, rest) →
      pick < repanicCollapseWidth first rest →
      abortMsg ctx first rest pick = .ok msg →
      StepML m ⟨m.threads.setIfInBounds i (.aborted msg), m.shared, i⟩
        ⟨i, .aborted,
          ⟨[], schedRecord ctx m slot
                ++ PickRecord.ofPick .repanicCollapse (repanicCollapseWidth first rest) pick, []⟩⟩
  | spawn {m : MultiConfig} {i slot : Nat} {c : Config} {cv : GoValue} {args : List GoValue}
      {k : Cont} {parent' child : Config} {σ' : Store} {ch ch' : Choices}
      {ps : List PickRecord} {tr : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      spawnPlan c = some (cv, args, k) →
      spawnStep ctx m.shared cv args k ch = .ok (parent', child, σ', ch', ps, tr) →
      StepML m ⟨(m.threads.setIfInBounds i (Thread.afterStep m.shared c parent')).push
          (.running child none), σ', i⟩
        ⟨i, .spawned m.threads.size,
          ⟨.hb (.spawn m.threads.size) :: tr.map (.attributed m.threads.size),
            schedRecord ctx m slot ++ ps, []⟩⟩
  | thread {m : MultiConfig} {i slot : Nat} {c c' : Config} {σ' : Store} {l : StepLabel} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok .cellPath →
      selectApplyPlan c = none →
      Step ctx c m.shared c' σ' l →
      StepML m ⟨m.threads.setIfInBounds i (Thread.afterStep m.shared c c'), σ', i⟩
        ⟨i, .privateStep, ⟨l.trace, schedRecord ctx m slot ++ l.picks, l.out⟩⟩
  | selectApply {m : MultiConfig} {i slot : Nat} {c : Config} {v : GoValue}
      {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt} {done : List GoValue}
      {env : LocalEnv} {k : Cont} {ch ch' : Choices} {c' : Config} {σ' : Store}
      {ps : List PickRecord} {cl? : Option EvClause} {tr : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      selectApplyPlan c = some (v, clauses, default?, done, env, k) →
      arrivalCases ctx m.shared m.threads i c = .ok .cellPath →
      applySelect ctx m.shared clauses default? (v :: done).reverse env k ch
        = .ok (c', σ', ch', ps, cl?, tr) →
      StepML m ⟨m.threads.setIfInBounds i (Thread.afterStep m.shared c c'), σ', i⟩
        ⟨i, selectAction cl?, ⟨tr, schedRecord ctx m slot ++ ps, []⟩⟩
  | selectApplyPanic {m : MultiConfig} {i slot : Nat} {c : Config} {v : GoValue}
      {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt} {done : List GoValue}
      {env : LocalEnv} {k : Cont} {ch : Choices} {msg : String} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      selectApplyPlan c = some (v, clauses, default?, done, env, k) →
      arrivalCases ctx m.shared m.threads i c = .ok .cellPath →
      applySelect ctx m.shared clauses default? (v :: done).reverse env k ch
        = .error (.panic msg) →
      StepML m ⟨m.threads.setIfInBounds i
          (Thread.afterStep m.shared c (.panicking [panicEntry msg] k)), m.shared, i⟩
        ⟨i, .selectPass, ⟨[], schedRecord ctx m slot, []⟩⟩
  | pair {m : MultiConfig} {i slot : Nat} {c bc : Config} {σ'' : Store}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Thread} {tr : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.single bc cs) →
      (hidx : idx < cs.length) →
      applyPairing ctx m.shared m.threads i bc cs[idx] = .ok (ts', σ'', tr) →
      StepML m ⟨ts', σ'', i⟩
        ⟨i, .paired cs[idx].2.partnerIdx,
          ⟨tr, schedRecord ctx m slot ++ PickRecord.ofPick .l4Waiter cs.length idx, []⟩⟩
  | pickPair {m : MultiConfig} {i slot : Nat} {c bc : Config} {σ'' : Store}
      {os : List ArrivalOutcome} {sel : Nat}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Thread} {tr : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.pair bc cs) →
      (hidx : idx < cs.length) →
      applyPairing ctx m.shared m.threads i bc cs[idx] = .ok (ts', σ'', tr) →
      StepML m ⟨ts', σ'', i⟩
        ⟨i, .paired cs[idx].2.partnerIdx,
          ⟨tr, schedRecord ctx m slot
                ++ (PickRecord.ofPick .l2Arrival os.length sel
                    ++ PickRecord.ofPick .l4Waiter cs.length idx), []⟩⟩
  | pickCommit {m : MultiConfig} {i slot : Nat} {c : Config} {evs : List EvClause} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {os : List ArrivalOutcome} {sel : Nat}
      {c' : Config} {σ' : Store} {trc : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.commit evs cl env k) →
      commitClause ctx m.shared env k cl = .ok (c', σ', trc) →
      StepML m ⟨m.threads.setIfInBounds i (Thread.afterStep m.shared c c'), σ', i⟩
        ⟨i, .selectCommit cl,
          ⟨selectPoll evs ++ trc,
            schedRecord ctx m slot ++ PickRecord.ofPick .l2Arrival os.length sel, []⟩⟩
  | wake {m : MultiConfig} {i slot : Nat} {c c' : Config} {σ' : Store} {tr : AccessTrace} :
      SchedSlot ctx m i slot →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = true →
      resumeThread ctx m.shared c = .ok (c', σ', tr) →
      StepML m ⟨m.threads.setIfInBounds i (Thread.completed c'), σ', i⟩
        ⟨i, .woke, ⟨tr, schedRecord ctx m slot, []⟩⟩

/-- The labelled reflexive-transitive closure: the events of a pool run, in order. (`PoolSteps`,
`PoolTrace.lean`, is its erasure — `stepsML_erase_stmt`.) -/
inductive StepsML : MultiConfig → MultiConfig → List StepEvent → Prop where
  | refl (m : MultiConfig) : StepsML m m []
  | head {m m' mf : MultiConfig} {ev : StepEvent} {evs : List StepEvent} :
      StepML ctx m m' ev → StepsML m' mf evs → StepsML m mf (ev :: evs)

/-! ## The pool deadlock -/

/-- **THE POOL DEADLOCK'S OWN CONDITION** — the driver's third classification (`execProgLoop`:
after the tombstone check and main's terminal, before the fuel): a NON-EMPTY pool (an empty pool is
the driver's internal refusal, not a deadlock) with no aborted goroutine, main not at its
terminal, and NO RUNNABLE GOROUTINE — every goroutine done, or parked and not wake-ready
(`threadRunnable`/`wakeReady`: Go's detector state, «all goroutines are asleep»). The pool wakes a
wake-ready parked goroutine instead of stopping — which is exactly where this differs from the
sequential `Blocked` classification (`singleton_deadlock_stmt`). -/
def PoolDeadlock (m : MultiConfig) : Prop :=
  m.threads.isEmpty = false ∧ m.panicMsg? = none ∧ m.mainOutcome? = none ∧
    runnableIdxs ctx m.shared m.threads = []

/-! ## The driver's own carriers: the gate, the prefix, the finish -/

/-- **The driver's pre-step GATE** — `front … = .ok (.inr ch₁)` with the main-exit window's draw
RECORDED (`front_continue_stmt`): the step is taken when the pool holds no tombstone and either
(`running`) main is not at its terminal and somebody is runnable, or (`window`) main IS at its
terminal, somebody else is runnable, and the `l5ExitWindow` draw (bound 2 — the L5 envelope: 0 =
exit now, 1 = one more pool step) picked CONTINUE. `ch₁` is the tape handed to `stepMulti`; `rec`
the window's record (`[]` for `running`). -/
inductive Continue (m : MultiConfig) : Choices → Choices → List PickRecord → Prop where
  | running {ch : Choices} :
      m.panicMsg? = none → m.mainOutcome? = none →
      runnableIdxs ctx m.shared m.threads ≠ [] →
      Continue m ch ch []
  | window {ch ch₁ : Choices} {rec : List PickRecord} {σ : Store} :
      m.panicMsg? = none → m.mainOutcome? = some σ →
      runnableIdxs ctx m.shared m.threads ≠ [] →
      Choices.consumeAtE .l5ExitWindow 2 ch = (1, ch₁, rec) →
      Continue m ch ch₁ rec

/-- One iteration of the driver loop, as a label: the main-exit window's record (`[]` when no draw
was made) and the pool step's event. The window draw belongs to the DRIVER, not to any step —
kept apart so the step's event stays the executable's `StepEvent` verbatim. -/
structure DriverEvent where
  window : List PickRecord
  event : StepEvent

/-- **The pool PREFIX** — the counted, choice-threaded, labelled closure of the driver loop's
ITERATIONS, with arbitrary endpoints: each step passes the gate (`Continue`, the window draw
recorded), takes the executable pool step (`stepMulti`), and folds the detector (`raceUpdate`)
without a race. The detector state rides along (a race ENDS the run — `PoolFinish.raced`). The
pool twin of `ExecutionStatement.Prefix` (defined by executable steps, erased to the relations:
`poolPrefix_labelled_stmt`, `poolPrefix_erase_stmt`). -/
inductive PoolPrefix :
    Nat → MultiConfig → RaceState → Choices → List DriverEvent →
      MultiConfig → RaceState → Choices → Prop where
  | done {m : MultiConfig} {r : RaceState} {ch : Choices} : PoolPrefix 0 m r ch [] m r ch
  | step {n : Nat} {m m' mf : MultiConfig} {r r' rf : RaceState} {ch ch₁ ch' chf : Choices}
      {rec : List PickRecord} {ev : StepEvent} {des : List DriverEvent} :
      Continue ctx m ch ch₁ rec →
      stepMulti ctx m ch₁ = .ok (m', ch', ev) →
      raceUpdate ev m' r = .ok r' →
      PoolPrefix n m' r' ch' des mf rf chf →
      PoolPrefix (n + 1) m r ch (⟨rec, ev⟩ :: des) mf rf chf

/-- What a finished pool run reports (the driver's result, with its evidence): main's normal exit
with the final shared store, the deadlock, the abort (the rendered first `panic: ` line, read from
the tombstone), the unrecoverable `fatal`, or a detected race carrying the RACING STEP's event.
Every outcome carries the residual tape. -/
inductive PoolOutcome where
  | normal (σ : Store) (ch : Choices)
  | deadlock (ch : Choices)
  | aborted (msg : String) (ch : Choices)
  | fatal (msg : String) (ch : Choices)
  | raced (ev : StepEvent) (ch : Choices)

/-- The Go terminal a pool outcome reports (`none` for normal completion): links a `PoolFinish`
to the driver's `.error (.terminal t)`. -/
def PoolOutcome.terminal? : PoolOutcome → Option Terminal
  | .normal _ _ => none
  | .deadlock _ => some .deadlock
  | .aborted msg _ => some (.panic msg)
  | .fatal msg _ => some (.fatal msg)
  | .raced _ _ => some .raceDetected

/-- **The driver's CLASSIFICATION at an endpoint, with TERMINAL PRIORITY** (`execProgLoop`'s
order, made a relation): the TOMBSTONE first (`aborted` — an unrecovered panic in ANY goroutine
ends the program, cost 0: the abort STEP already happened), then MAIN'S TERMINAL (`normal` when
nobody else is runnable; `exitWindow` when others are runnable and the L5 draw picked EXIT —
recorded), then the DEADLOCK (`PoolDeadlock`, cost 0), all BEFORE the fuel check; then the two
step-level ends at cost 1 — a `fatal` raised by the pool step itself after the gate (`Continue`;
the tape after the gate, the gate's record), and a RACE detected on the step's event
(`raced`, the event kept). The classification is a FUNCTION of `(m, r, ch)`
(`poolFinish_functional_stmt`) — which is what the priority order buys. -/
inductive PoolFinish (m : MultiConfig) (r : RaceState) :
    Choices → List PickRecord → PoolOutcome → Nat → Prop where
  | aborted {ch : Choices} {msg : String} :
      m.panicMsg? = some msg → PoolFinish m r ch [] (.aborted msg ch) 0
  | normal {ch : Choices} {σ : Store} :
      m.panicMsg? = none → m.mainOutcome? = some σ →
      runnableIdxs ctx m.shared m.threads = [] →
      PoolFinish m r ch [] (.normal σ ch) 0
  | exitWindow {ch ch₁ : Choices} {rec : List PickRecord} {σ : Store} :
      m.panicMsg? = none → m.mainOutcome? = some σ →
      runnableIdxs ctx m.shared m.threads ≠ [] →
      Choices.consumeAtE .l5ExitWindow 2 ch = (0, ch₁, rec) →
      PoolFinish m r ch rec (.normal σ ch₁) 0
  | deadlock {ch : Choices} :
      PoolDeadlock ctx m → PoolFinish m r ch [] (.deadlock ch) 0
  | fatal {ch ch₁ : Choices} {rec : List PickRecord} {msg : String} :
      Continue ctx m ch ch₁ rec →
      stepMulti ctx m ch₁ = .error (.fatal msg) →
      PoolFinish m r ch rec (.fatal msg ch₁) 1
  | raced {ch ch₁ ch' : Choices} {rec : List PickRecord} {m' : MultiConfig} {ev : StepEvent} :
      Continue ctx m ch ch₁ rec →
      stepMulti ctx m ch₁ = .ok (m', ch', ev) →
      raceUpdate ev m' r = .error .raceDetected →
      PoolFinish m r ch rec (.raced ev ch') 1

end GoLean.GoCore.Machine
