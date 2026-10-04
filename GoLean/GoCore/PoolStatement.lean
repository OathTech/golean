import GoLean.GoCore.PoolStep
import GoLean.GoCore.PoolProjection

/-!
# The pool/registry half — STATEMENTS ONLY (the spec packet's frozen surface)

[AGENT design worker, lane `design/pool-relation-spec-1004`] 2026-10-04; authority and the design
note as in `PoolStep.lean`'s header. Every theorem owed by the pool/registry half is a `def
<name>_stmt : Prop` here — it elaborates with no proof. The grind (a Codex worker under
`docs/2026-10-04_pool-relation-grind-brief.md`) PROVES each `<name>_stmt` as `theorem <name> :
<name>_stmt` in a new `GoLean/GoCore/PoolSound.lean`, the statements UNCHANGED — the packet-A/B
device (`ExecutionStatement.lean` / `Prefix.lean`), re-used verbatim. The `sorry`'d skeleton
`docs/specs/pool-relation/Skeleton.lean` (outside every build target and gate scan) lists the same
names and elaborates against this file.

The only proofs in this file are the CONTROLS at the end, each closed by `rfl` on a tiny pool
(`#eval`-checked first — never `decide` on a possibly-false `Bool`).

Groups: (A) the step correspondence and the projection to `StepM`; (B) attribution and registry
boundaries; (C) the pool deadlock; (D) the step's error classes (the pool twin of «no stray
panic»); (E) the driver carriers — `Continue`/`PoolFinish` vs `front`, terminal priority; (F) the
run lifts — the `PoolPrefix` algebra, erasure, the exact fuel bridges and the four-way
classification; (G) the program seam; (H) the single-goroutine reduction — step level (to `Step`),
finish level (to `Finish`), prefix level (to `Prefix`, the labels fold-equal, attribution 0), and
the pin that `PoolProjection`'s result is the special case.
-/

namespace GoLean.GoCore.PoolStatement

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics GoLean.Semantics.Pool
open GoLean.GoCore.ExecutionStatement (Prefix Finish FinishOutcome Blocked)

/-! ## Glue definitions (proof-layer; beside `seqOut`/`outFold`) -/

/-- The OUTPUT of a pool prefix: the fold of its events' `out` channels onto `acc`, in step order
— `execProgLoopOut`'s fold (`outFold`, `PoolProjection.lean`) over the driver events' labels. -/
def poolOut (des : List DriverEvent) (acc : GoString) : GoString :=
  outFold (des.map fun d => d.event.label) acc

/-- The events of a prefix (its window records dropped). -/
def DriverEvent.events (des : List DriverEvent) : List StepEvent := des.map (·.event)

/-! ## (A) The step correspondence -/

/-- **Soundness of the executable pool step**: every `stepMulti` step is a `StepML` step with the
SAME event — attribution, action and full label (the analogue of `stepFn_sound`, over the pool).
Refines `stepMulti_sound` (`MultiSound.lean:1192`), whose conclusion is this one's trace. -/
def stepMulti_sound_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ch ch' : Choices) (ev : StepEvent),
    stepMulti ctx m ch = .ok (m', ch', ev) → StepML ctx m m' ev

/-- **Completeness**: every `StepML` step is realized by `stepMulti` under some tape, with the SAME
event (the analogue of `step_complete`; refines `stepM_complete`, `MultiSound.lean:1338`, whose
witness agreed on the trace only). -/
def stepML_complete_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ∃ ch ch' : Choices, stepMulti ctx m ch = .ok (m', ch', ev)

/-- **The projection**: the trace-labelled `StepM` is `StepML` with the event erased to its trace
— nothing of the existing relation is restated or weakened. -/
def stepML_erase_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → StepM ctx m m' ev.trace

/-- The converse projection: every `StepM` step is some `StepML` step's trace. -/
def stepM_lift_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (tr : AccessTrace),
    StepM ctx m m' tr → ∃ ev : StepEvent, StepML ctx m m' ev ∧ ev.trace = tr

/-- The labelled closure erases to `PoolSteps` (`PoolTrace.lean`). -/
def stepsML_erase_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m mf : MultiConfig) (evs : List StepEvent),
    StepsML ctx m mf evs → PoolSteps ctx m mf

/-! ## (B) Attribution and registry boundaries -/

/-- **Attribution is runnable**: the goroutine a step is attributed to is runnable in the
pre-state (the stepping goroutine of EVERY rule). -/
def stepML_who_runnable_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ev.who ∈ runnableIdxs ctx m.shared m.threads

/-- The stepping goroutine is a legal scheduler pick (`schedPick`, the existing premise, as a
consequence) and becomes the running one. -/
def stepML_sched_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → schedPick ctx m ev.who ∧ m'.cur = ev.who

/-- **Context switches happen only at registry boundaries**: a step attributed to a goroutine
other than the running one starts at a boundary of the running goroutine. -/
def stepML_switch_boundary_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev → ev.who ≠ m.cur →
      ∃ t : Thread, m.threads[m.cur]? = some t ∧ t.atBoundary = true

/-- **The scheduling record leads the picks**: at a boundary whose menu offers a choice (≥ 2
slots), the event's first pick record is the scheduling consultation — the site, the menu's
length, and a slot naming the stepping goroutine. -/
def stepML_sched_record_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent) (site : ChoiceSite) (menu : List Nat),
    StepML ctx m m' ev → m.schedMenu? ctx = some (site, menu) → 1 < menu.length →
      ∃ slot : Nat, menu[slot]? = some ev.who ∧ ev.picks.head? = some ⟨site, menu.length, slot⟩

/-- The slot formulation refines the membership one: a legal pick IS some slot of the menu. -/
def schedSlot_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (i : Nat),
    schedPick ctx m i ↔ ∃ slot : Nat, SchedSlot ctx m i slot

/-- **The attribution FRAME LAW**: a step rewrites the stepping goroutine, and — on a pairing — its
partner (`ev.action = .paired j`); every other pre-existing goroutine is untouched. The pool never
shrinks. -/
def stepML_frame_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev →
      m.threads.size ≤ m'.threads.size ∧
      ∀ j : Nat, j < m.threads.size → j ≠ ev.who →
        m'.threads[j]? = m.threads[j]? ∨ ev.action = .paired j

/-- A pairing's partner is NAMED IN THE TRACE: the rendezvous with it, or an action attributed to
it (the handoff's slot transit) — attribution reaches the memory-model label. -/
def stepML_paired_trace_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent) (j : Nat),
    StepML ctx m m' ev → ev.action = .paired j →
      (∃ e : MemEvent, MemEvent.attributed j e ∈ ev.trace) ∨ MemEvent.hb (.rendezvous j) ∈ ev.trace

/-- A spawn appends exactly one goroutine at the pool's size and names it in the trace by the
`go` edge; every other step keeps the size. -/
def stepML_spawn_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m m' : MultiConfig) (ev : StepEvent),
    StepML ctx m m' ev →
      ((∀ n : Nat, ev.action ≠ .spawned n) → m'.threads.size = m.threads.size) ∧
      (∀ n : Nat, ev.action = .spawned n →
        n = m.threads.size ∧ m'.threads.size = m.threads.size + 1 ∧
          MemEvent.hb (.spawn n) ∈ ev.trace)

/-! ## (C) The pool deadlock -/

/-- **An all-asleep pool is relation-silent**: no runnable goroutine, no step (so a `PoolDeadlock`
pool has no successor). -/
def asleep_silent_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig),
    runnableIdxs ctx m.shared m.threads = [] → ∀ (m' : MultiConfig) (ev : StepEvent), ¬ StepML ctx m m' ev

/-- **Sequential blocking vs the pool deadlock — the different environmental conditions, made
exact**: a blocked goroutine alone in a pool is the pool deadlock IFF its blocked operation is not
wake-ready against the cells (the pool otherwise WAKES it — the `transferableWide` exclusion's
reason, `MultiSound.lean`/`PoolProjection.lean`). -/
def singleton_deadlock_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (σ : Store) (c : Config),
    Blocked c → (PoolDeadlock ctx ⟨#[.running c none], σ, 0⟩ ↔ wakeReady ctx σ c = false)

/-- Main at its terminal never deadlocks (the priority: main's exit is classified first). -/
def mainOutcome_not_deadlock_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (σ : Store),
    m.mainOutcome? = some σ → ¬ PoolDeadlock ctx m

/-! ## (D) The pool step's error classes -/

/-- **No stray panic at the pool** (the pool twin of `stepFn_no_stray_panic`): `stepMulti`'s error
is a REFUSAL, the unrecoverable `fatal`, or the empty-menu deadlock throw — never the Go `panic`
terminal (every goroutine panic is DELIVERED into its configuration and rendered by the abort
step), never a race (the detector is the driver's fold), never fuel-out. -/
def stepMulti_error_cases_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch : Choices) (e : Stop),
    stepMulti ctx m ch = .error e →
      (∃ r : Refusal, e = .refusal r) ∨ (∃ msg : String, e = .fatal msg) ∨ e = .deadlock

/-- The empty-menu deadlock throw is UNREACHABLE after the gate: a continuing pool has a runnable
goroutine, and every runnable goroutine is in the menu (`mem_schedSlots_of_runnable`). -/
def stepMulti_deadlock_elim_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch ch₁ : Choices) (rec : List PickRecord),
    Continue ctx m ch ch₁ rec → stepMulti ctx m ch₁ ≠ .error .deadlock

/-- The detector's only error is the race terminal. -/
def raceUpdate_error_stmt : Prop :=
  ∀ (ev : StepEvent) (m' : MultiConfig) (r : RaceState) (e : Stop),
    raceUpdate ev m' r = .error e → e = .raceDetected

/-! ## (E) The driver carriers vs `front`; terminal priority -/

/-- **The gate IS `front`'s continue arm**: `front … = .ok (.inr ch₁)` exactly when `Continue`
holds for some record (the window draw, recorded). -/
def front_continue_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch ch₁ : Choices),
    front ctx m ch = .ok (.inr ch₁) ↔ ∃ rec : List PickRecord, Continue ctx m ch ch₁ rec

/-- **The cost-0 finishes ARE `front`'s classifications**: normal completion, the tombstone's
panic terminal, the deadlock — each exactly the matching `PoolFinish` at cost 0. -/
def front_finish_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch : Choices),
    (∀ (σ : Store) (ch' : Choices),
      front ctx m ch = .ok (.inl (σ, ch')) ↔ ∃ rec, PoolFinish ctx m r ch rec (.normal σ ch') 0) ∧
    (∀ msg : String,
      front ctx m ch = .error (.panic msg) ↔ PoolFinish ctx m r ch [] (.aborted msg ch) 0) ∧
    (front ctx m ch = .error .deadlock ↔ PoolFinish ctx m r ch [] (.deadlock ch) 0)

/-- `front`'s only refusal is the empty pool. -/
def front_refusal_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (ch : Choices) (rr : Refusal),
    front ctx m ch = .error (.refusal rr) ↔
      m.threads.isEmpty = true ∧ rr = .internal "thread pool without a main goroutine"

/-- **Terminal priority, as functionality**: at a fixed pool, detector state and tape the
classification is UNIQUE — record, outcome and cost. (The tombstone excludes every other finish;
main's terminal excludes the deadlock; the window draw separates exit from the cost-1 ends; the
gate's tape is determined; `stepMulti` is a function.) -/
def poolFinish_functional_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (rec rec' : List PickRecord) (o o' : PoolOutcome) (cost cost' : Nat),
    PoolFinish ctx m r ch rec o cost → PoolFinish ctx m r ch rec' o' cost' →
      rec = rec' ∧ o = o' ∧ cost = cost'

/-- A finish and a gate exclude each other: a classified pool does not step, and a stepping pool is
not classified at cost 0 (the cost-1 finishes pass the gate by construction). -/
def poolFinish_zero_not_continue_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (m : MultiConfig) (r : RaceState) (ch ch₁ : Choices)
    (rec rec' : List PickRecord) (o : PoolOutcome),
    PoolFinish ctx m r ch rec o 0 → ¬ Continue ctx m ch ch₁ rec'

/-! ## (F) The run lifts -/

/-- `PoolPrefix` composes: lengths add, events append. -/
def poolPrefix_comp_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n k : Nat) (m m₁ mf : MultiConfig) (r r₁ rf : RaceState)
    (ch ch₁ chf : Choices) (des des' : List DriverEvent),
    PoolPrefix ctx n m r ch des m₁ r₁ ch₁ → PoolPrefix ctx k m₁ r₁ ch₁ des' mf rf chf →
    PoolPrefix ctx (n + k) m r ch (des ++ des') mf rf chf

/-- `PoolPrefix` splits at every intermediate length. -/
def poolPrefix_split_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n k : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx (n + k) m r ch des mf rf chf →
    ∃ (des₁ des₂ : List DriverEvent) (m₁ : MultiConfig) (r₁ : RaceState) (ch₁ : Choices),
      des = des₁ ++ des₂ ∧ PoolPrefix ctx n m r ch des₁ m₁ r₁ ch₁ ∧
        PoolPrefix ctx k m₁ r₁ ch₁ des₂ mf rf chf

/-- Erasure to the labelled relational closure: the prefix's events ARE a `StepsML` run. -/
def poolPrefix_labelled_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx n m r ch des mf rf chf → StepsML ctx m mf (DriverEvent.events des)

/-- Erasure to pool reachability (`PoolSteps`). -/
def poolPrefix_erase_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent),
    PoolPrefix ctx n m r ch des mf rf chf → PoolSteps ctx m mf

/-- **The driver runs a prefix exactly**: `n` units of fuel carry the output-folding driver to the
prefix's endpoint, the prefix's output folded. -/
def poolPrefix_run_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n k : Nat) (m mf : MultiConfig) (r rf : RaceState) (ch chf : Choices)
    (des : List DriverEvent) (acc : GoString),
    PoolPrefix ctx n m r ch des mf rf chf →
    execProgLoopOut ctx (n + k) m r ch acc = execProgLoopOut ctx k mf rf chf (poolOut des acc)

/-- **Normal completion**: a prefix of length `n ≤ fuel` to a pool whose cost-0 finish is main's
exit; the output is the prefix's fold. -/
def pool_run_ok_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (σ : Store) (chf : Choices),
    execProgLoopOut ctx fuel m r ch acc = (out, .ok (σ, chf)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ : Choices)
        (rec : List PickRecord),
        n ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf₀ ∧
          PoolFinish ctx mf rf chf₀ rec (.normal σ chf) 0 ∧ out = poolOut des acc

/-- **The Go terminals**: the panic (a tombstone), the deadlock, the fatal and the detected race —
a prefix plus a finish reporting `t`, the finish's cost within the fuel; the output is the prefix's
fold (a fatal or racing step prints nothing — the driver folds output AFTER the detector). -/
def pool_run_terminal_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (t : Terminal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.terminal t)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices)
        (rec : List PickRecord) (o : PoolOutcome) (cost : Nat),
        n + cost ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf ∧
          PoolFinish ctx mf rf chf rec o cost ∧ o.terminal? = some t ∧ out = poolOut des acc

/-- **Fuel-out**: the fixed tape's ACTUAL prefix of length exactly `fuel`, ending at a pool that
passes the gate (not classified at cost 0). -/
def pool_run_fuelOut_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString),
    execProgLoopOut ctx fuel m r ch acc = (out, .error .fuelOut) ↔
      ∃ (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf ch₁ : Choices)
        (rec : List PickRecord),
        PoolPrefix ctx fuel m r ch des mf rf chf ∧ Continue ctx mf chf ch₁ rec ∧
          out = poolOut des acc

/-- **Refusals, REPORTED**: a prefix to a pool whose gate refuses (the empty pool, cost 0) or whose
pool step refuses after the gate (cost 1). -/
def pool_run_refusal_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (rr : Refusal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.refusal rr)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices),
        PoolPrefix ctx n m r ch des mf rf chf ∧ out = poolOut des acc ∧
          ((n ≤ fuel ∧ front ctx mf chf = .error (.refusal rr)) ∨
           (n + 1 ≤ fuel ∧ ∃ (ch₁ : Choices) (rec : List PickRecord),
              Continue ctx mf chf ch₁ rec ∧ stepMulti ctx mf ch₁ = .error (.refusal rr)))

/-- Case 1 — normal completion, with `pool_run_ok_iff_stmt`'s witness. -/
def PoolClassOk (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc : GoString) : Prop :=
  ∃ (out : GoString) (σ : Store) (chf : Choices),
    execProgLoopOut ctx fuel m r ch acc = (out, .ok (σ, chf)) ∧
    ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ : Choices)
      (rec : List PickRecord),
      n ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf₀ ∧
        PoolFinish ctx mf rf chf₀ rec (.normal σ chf) 0 ∧ out = poolOut des acc

/-- Case 2 — a Go terminal, with `pool_run_terminal_iff_stmt`'s witness. -/
def PoolClassTerminal (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) : Prop :=
  ∃ (out : GoString) (t : Terminal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.terminal t)) ∧
    ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices)
      (rec : List PickRecord) (o : PoolOutcome) (cost : Nat),
      n + cost ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf ∧
        PoolFinish ctx mf rf chf rec o cost ∧ o.terminal? = some t ∧ out = poolOut des acc

/-- Case 3 — fuel-out, with `pool_run_fuelOut_iff_stmt`'s witness. -/
def PoolClassFuelOut (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) : Prop :=
  ∃ (out : GoString),
    execProgLoopOut ctx fuel m r ch acc = (out, .error .fuelOut) ∧
    ∃ (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf ch₁ : Choices)
      (rec : List PickRecord),
      PoolPrefix ctx fuel m r ch des mf rf chf ∧ Continue ctx mf chf ch₁ rec ∧
        out = poolOut des acc

/-- Case 4 — a refusal, REPORTED, with `pool_run_refusal_iff_stmt`'s witness. -/
def PoolClassRefusal (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) : Prop :=
  ∃ (out : GoString) (rr : Refusal),
    execProgLoopOut ctx fuel m r ch acc = (out, .error (.refusal rr)) ∧
    ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf : Choices),
      PoolPrefix ctx n m r ch des mf rf chf ∧ out = poolOut des acc ∧
        ((n ≤ fuel ∧ front ctx mf chf = .error (.refusal rr)) ∨
         (n + 1 ≤ fuel ∧ ∃ (ch₁ : Choices) (rec : List PickRecord),
            Continue ctx mf chf ch₁ rec ∧ stepMulti ctx mf ch₁ = .error (.refusal rr)))

/-- **UNCONDITIONAL classification of the pool driver**: every run is exactly one of the four
cases — no «all executions succeed» premise, refusal a REPORTED case. Exclusivity is by
construction (the four fix pairwise-distinct result shapes). -/
def pool_classification_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc : GoString),
    PoolClassOk ctx fuel m r ch acc ∨ PoolClassTerminal ctx fuel m r ch acc ∨
      PoolClassFuelOut ctx fuel m r ch acc ∨ PoolClassRefusal ctx fuel m r ch acc

/-- `Run` (`PoolTrace.lean`) over the labelled carrier: a successful run IS a prefix and a normal
finish — the relabelling of `run_iff`'s success case. -/
def run_ok_prefix_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices)
    (acc out : GoString) (σ : Store) (chf : Choices),
    Run ctx fuel m r ch acc (out, .ok (σ, chf)) ↔
      ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ : Choices)
        (rec : List PickRecord),
        n ≤ fuel ∧ PoolPrefix ctx n m r ch des mf rf chf₀ ∧
          PoolFinish ctx mf rf chf₀ rec (.normal σ chf) 0 ∧ out = poolOut des acc

/-! ## (G) The program seam -/

/-- **The program bridge over the labelled pool carrier** (under successful setup — setup stays a
premise, `program_bridge`'s limit RETAINED): a program's normal readout is a pool prefix from the
seeded one-goroutine pool to a pool finishing by main's exit, the program's output the prefix's
fold, the values `loadMany`'s readout at the final shared store. -/
def program_prefix_stmt : Prop :=
  ∀ (fuel : Nat) (p : Program) (name : String) (args : Array GoValue) (ch : Choices)
    (pctx : ProgramCtx) (c₀ : Config) (s₀ : Store) (locs : List Loc) (ch₁ : Choices)
    (ro : Readout),
    runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁) →
    runProgramPoolOutM fuel p name args ch = .ok ro →
    ∃ (n : Nat) (des : List DriverEvent) (mf : MultiConfig) (rf : RaceState) (chf₀ chf : Choices)
      (rec : List PickRecord) (sf : Store),
      n ≤ fuel ∧ PoolPrefix pctx n ⟨#[Thread.running c₀ none], s₀, 0⟩ {} ch₁ des mf rf chf₀ ∧
        PoolFinish pctx mf rf chf₀ rec (.normal sf chf) 0 ∧
        ro.output = poolOut des GoString.empty ∧ loadMany pctx sf locs = .ok ro.values.toList

/-! ## (H) The single-goroutine reduction -/

/-- **Step level, sound**: a step of a lone, live, unparked, non-spawn, non-abort goroutine IS a
sequential `Step` of it — the successor flagged by the boundary rule, attribution 0, the label the
step's (the select interception's label is the apply's; its panic path `deliver`'s). -/
def stepML_single_sound_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (σ : Store) (c : Config) (m' : MultiConfig) (ev : StepEvent),
    isBlockedConfig c = false → spawnPlan c = none → c.abort? = none →
    StepML ctx ⟨#[.running c none], σ, 0⟩ m' ev →
      ∃ (c' : Config) (σ' : Store) (l : StepLabel),
        Step ctx c σ c' σ' l ∧ m' = ⟨#[Thread.afterStep σ c c'], σ', 0⟩ ∧
          ev.who = 0 ∧ ev.label = l

/-- **Step level, complete**: every sequential `Step` of a lone goroutine is a pool step of the
singleton pool, attribution 0, the label the step's. -/
def stepML_single_complete_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (σ σ' : Store) (c c' : Config) (l : StepLabel),
    Step ctx c σ c' σ' l →
      ∃ ev : StepEvent,
        StepML ctx ⟨#[.running c none], σ, 0⟩ ⟨#[Thread.afterStep σ c c'], σ', 0⟩ ev ∧
          ev.who = 0 ∧ ev.label = l

/-- **Prefix level — THE SINGLETON EMBEDDING OVER LABELS**: a sequential prefix of `n` steps is a
pool prefix of the singleton pool of `n + seqOpCount …` iterations (one boundary clear per
completed registry op — the proved cost relation, never «equal fuel»), to the lone goroutine at
the prefix's endpoint with its flag cleared, the detector state untouched, NO window draw, every
event attributed to goroutine 0, and the events' labels FOLD-EQUAL to the prefix's (the clears are
silent). -/
def singleton_prefix_embedding_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (σ sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel) (rs : RaceState),
    Prefix ctx n σ c ch ls sf cf chf →
      ∃ des : List DriverEvent,
        PoolPrefix ctx (n + seqOpCount ctx n σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch des
          ⟨#[.running cf none], sf, 0⟩ rs chf ∧
        (∀ d ∈ des, d.window = [] ∧ d.event.who = 0) ∧
        StepLabel.fold ((DriverEvent.events des).map StepEvent.label) = StepLabel.fold ls

/-- **Finish level — normal**: the lone goroutine's normal terminal is the pool's normal finish. -/
def singleton_finish_normal_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (sf : Store) (chf : Choices) (rs : RaceState),
    PoolFinish ctx ⟨#[.running (.next .stop) none], sf, 0⟩ rs chf [] (.normal sf chf) 0

/-- **Finish level — the abort**: the sequential `Finish.aborted` (cost 1: the `stepFn` abort) is
ONE pool step — the tombstone, the same record — then the cost-0 `aborted` finish. -/
def singleton_finish_aborted_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf ch'' : Choices) (rec : List PickRecord)
    (t : String) (rs : RaceState),
    Finish ctx sf cf chf rec (.aborted t sf ch'') 1 →
      stepMulti ctx ⟨#[.running cf none], sf, 0⟩ chf
          = .ok (⟨#[.aborted t], sf, 0⟩, ch'', ⟨0, .aborted, ⟨[], rec, []⟩⟩) ∧
        PoolFinish ctx ⟨#[.aborted t], sf, 0⟩ rs ch'' [] (.aborted t ch'') 0

/-- **Finish level — the renderer's refusal**: the sequential `Finish.abortRefused` is the pool
step's refusal with the same text. -/
def singleton_finish_refused_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf ch'' : Choices) (rec : List PickRecord)
    (rr : Refusal),
    Finish ctx sf cf chf rec (.refused rr sf ch'') 1 →
      stepMulti ctx ⟨#[.running cf none], sf, 0⟩ chf = .error (.refusal rr)

/-- **Finish level — the fatal**: the sequential `Finish.fatal` is the pool's `fatal` finish (the
gate passes with no draw; the pool step raises the same terminal). -/
def singleton_finish_fatal_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf : Choices) (msg : String) (rs : RaceState),
    Finish ctx sf cf chf [] (.fatal msg sf chf) 1 →
      PoolFinish ctx ⟨#[.running cf none], sf, 0⟩ rs chf [] (.fatal msg chf) 1

/-- **Finish level — the deadlock**: the sequential `Finish.blocked` is the pool's deadlock finish
exactly when the blocked operation is not wake-ready (`singleton_deadlock_stmt`'s condition). -/
def singleton_finish_deadlock_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (sf : Store) (cf : Config) (chf : Choices) (rs : RaceState),
    Finish ctx sf cf chf [] (.deadlock sf chf) 0 → wakeReady ctx sf cf = false →
      PoolFinish ctx ⟨#[.running cf none], sf, 0⟩ rs chf [] (.deadlock chf) 0

/-- **The pin to `PoolProjection`**: the single-goroutine run bridge over `transferableWide` as a
`Run` — DEFINITIONAL from `execProgLoopOut_single_wide` through `run_iff` (pinned here so the
reduction's base case is a named member of this set, not a re-derivation). -/
def singleton_run_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (rs : RaceState)
    (acc : GoString) (r : Except Stop (Store × Choices)),
    execStmtLoop ctx fuel σ c ch = r → transferableWide r →
    Run ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch acc
      (seqOut ctx fuel σ c ch acc, r)

/-! ## Controls (`#eval`-checked, then `rfl`; tiny pools) -/

section Controls

/-- A control context with no functions and no types. -/
def controlCtx : ProgramCtx := ProgramCtx.ofTables #[] #[]

-- (1) A lone parked select with no clauses over the empty store: nobody runnable — the deadlock
-- condition's runnable conjunct holds; main's terminal does not; no tombstone.
example : runnableIdxs controlCtx {} #[.running (.blockedSelect [] [] .stop) none] = [] := rfl
example : MultiConfig.mainOutcome? ⟨#[.running (.blockedSelect [] [] .stop) none], {}, 0⟩ = none := rfl
example : MultiConfig.panicMsg? ⟨#[.running (.blockedSelect [] [] .stop) none], {}, 0⟩ = none := rfl
example : wakeReady controlCtx {} (.blockedSelect [] [] .stop) = false := rfl

-- (2) Main alone at its terminal: not runnable, main's outcome is the shared store.
example : runnableIdxs controlCtx {} #[.running (.next .stop) none] = [] := rfl
example (σ : Store) : MultiConfig.mainOutcome? ⟨#[.running (.next .stop) none], σ, 0⟩ = some σ := rfl

-- (3) A tombstone is the first classification, whatever main is doing.
example (σ : Store) : MultiConfig.panicMsg? ⟨#[.running (.next .stop) none, .aborted "boom"], σ, 0⟩
    = some "boom" := rfl

-- (4) The scheduling record: a flagged running goroutine (its `postOp` boundary open) beside one
-- other runnable goroutine — the menu is issuer-first `[0, 1]`, so slot 1 is recorded at bound 2.
example : schedRecord controlCtx
    ⟨#[.running (.next .stop) (some .postOp), .running (.next (.seq [] [] .stop)) none], {}, 0⟩ 1
    = [⟨.postOp, 2, 1⟩] := rfl
example : MultiConfig.schedMenu? controlCtx
    ⟨#[.running (.next .stop) (some .postOp), .running (.next (.seq [] [] .stop)) none], {}, 0⟩
    = some (.postOp, [0, 1]) := rfl

-- (5) Off a boundary (a plain sequence head), no consultation and no record.
example : MultiConfig.schedMenu? controlCtx ⟨#[.running (.next (.seq [] [] .stop)) none], {}, 0⟩
    = none := rfl
example : schedRecord controlCtx ⟨#[.running (.next (.seq [] [] .stop)) none], {}, 0⟩ 0 = [] := rfl

-- (6) A singleton menu records nothing (the uniform bound-≤-1 rule): main's terminal boundary with
-- one other runnable goroutine — the menu is that goroutine alone.
example : MultiConfig.schedMenu? controlCtx
    ⟨#[.running (.next .stop) none, .running (.next (.seq [] [] .stop)) none], {}, 0⟩
    = some (.l1Sched, [1]) := rfl
example : schedRecord controlCtx
    ⟨#[.running (.next .stop) none, .running (.next (.seq [] [] .stop)) none], {}, 0⟩ 0 = [] := rfl

end Controls

end GoLean.GoCore.PoolStatement
