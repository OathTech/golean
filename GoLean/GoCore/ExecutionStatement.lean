import GoLean.GoCore.Trace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.MultiSound

/-!
# The execution statement — STATEMENTS ONLY (window charter row 0, §2)

[AGENT packet A worker] 2026-09-27, under «The window charter (rev. 2) and the Codex
packaging — RULED (2026-09-24)» and the execution-model ruling of 2026-09-27
(`docs/2026-08-31_qrow-rulings.md`). The design note is
`docs/2026-09-24_execution-statement.md`; every name below is charter §2's.

THE DEVICE. The relations were first stated (packet A, 2026-09-27) over the 5-ary `Step`
and the 4-tuple `stepFn` whose per-step label was an `AccessTrace`. The row-2 label
reshape ([AGENT worker, lane core/step-label-0928], 2026-09-28; design note
`docs/2026-09-28_step-label.md`) RE-STATED this file over the full event label
`StepLabel := { trace, picks, out }` (`Ops.lean`): `Prefix`/`LRun`/the classification
carry `List StepLabel`; `replays` is now replay BY RECORD over a label's `picks`; the
silent projection is the per-field fold `StepLabel.fold`. Still statements only — packet B
then PROVES each `<name>_stmt` as `<name>`. Every theorem here is a `def <name>_stmt :
Prop` — it elaborates with no proof. The only proofs in this file are the boundary
CONTROLS, each closed by `rfl`: three copied from the review witness
(`docs/evidence/2026-09-23_batched-window-review/FuelBoundary.lean`) and two for the fatal;
plus one `NoRefusal` positive control (a short case analysis, audit F2).

Coordinator dispositions ([AGENT] coordinator, 2026-09-27; disclosed at the merge ask):
(1) Reading A for the classification — `Finish` gains a FIFTH constructor `fatal` for the
UNRECOVERABLE terminal `.terminal (.fatal m)` that `stepFn` raises at a non-zero-cost
configuration (`Machine.lean:4392`, `:4416`, `:4443`; propagated by `toResult`,
`Value.lean:394`), finishing cost 1; `classification_stmt` / `classification_wf_stmt` are
stated over the five constructors. (2) Reading A for `program_bridge_stmt` — stated; its
`loadMany` mention is recorded in `scripts/mem-callsites.tsv` («NO EXECUTION»).

Audit F1 (2026-09-27, `docs/2026-09-27_packet-a-audit.md` on branch
`review/packet-a-contract-0927`) — RESOLVED by `core/stray-panic-refusal-0927` (disposition
(b), [AGENT] coordinator, disclosed at the merge ask): `stepFn` raised the Go PANIC terminal
at a NON-abort configuration (a binding cell read through `Mem.loadFor` → `loadLoc` →
`arrayGet`), which no `Finish` constructor classifies, refuting `finish_abort_step_stmt`,
`run_panic_iff_stmt`, `classification_stmt` and `classification_wf_stmt` as stated. The core
lane's root-only reader `loadRoot` makes a non-root binding location refuse as `.internal
"binding cell is not a root location: …"`; the statements are UNCHANGED, and the auditor's
witness is now a `ClassRefusal` (not a `ClassTerminal`) —
`docs/evidence/2026-09-24_packet-a/F1Witness.lean`.
-/

namespace GoLean.GoCore.ExecutionStatement

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics

/-! ## Zero-cost classification (the F2 predicate) -/

/-- The four blocked forms: single goroutine, no partner — the sequential deadlock. -/
def Blocked (c : Config) : Prop :=
  (∃ ch v k, c = .blockedSend ch v k) ∨
  (∃ ch targets elem env k, c = .blockedRecv ch targets elem env k) ∨
  (∃ clauses env k, c = .blockedSelect clauses env k) ∨
  (∃ op loc env k, c = .blockedSync op loc env k)

/-- The five arms `execStmtLoop` (`StepFn.lean:1012`) matches BEFORE its `fuel` match:
classified at cost 0. The fuel-out statement uses the NEGATION of this predicate (F2),
not the negation of `Finish` — an abort configuration has a `Finish` but costs 1. -/
def ZeroCost (c : Config) : Prop :=
  c = .next .stop ∨ Blocked c

/-! ## The labelled prefix closure (primary carrier) -/

/-- `n` executable steps from `(s, c, ch)` to `(sf, cf, chf)`, one label per step, the
tape threaded exactly as `stepFn` threads it. The labelled twin of `Trace`
(`Trace.lean:15`); arbitrary endpoints, independent of termination. -/
inductive Prefix (ctx : ProgramCtx) :
    Nat → Store → Config → Choices → List StepLabel → Store → Config → Choices → Prop where
  | done {s : Store} {c : Config} {ch : Choices} : Prefix ctx 0 s c ch [] s c ch
  | step {n : Nat} {s s₁ sf : Store} {c c₁ cf : Config} {ch ch₁ chf : Choices}
      {l : StepLabel} {ls : List StepLabel} :
      stepFn ctx s c ch = .ok (c₁, s₁, ch₁, l) →
      Prefix ctx n s₁ c₁ ch₁ ls sf cf chf →
      Prefix ctx (n + 1) s c ch (l :: ls) sf cf chf

/-! ## The classified finish -/

/-- What a finished run reports: every outcome carries the endpoint store and the
residual tape (correction (1)). -/
inductive FinishOutcome where
  | normal (s : Store) (ch : Choices)
  | deadlock (s : Store) (ch : Choices)
  | aborted (t : String) (s : Store) (ch : Choices)
  | refused (r : Refusal) (s : Store) (ch : Choices)
  | fatal (m : String) (s : Store) (ch : Choices)

/-- The Go terminal a finish outcome reports (`none` for normal completion and for a
refusal): links a `Finish` to `execStmtLoop`'s `.error (.terminal t)`. -/
def FinishOutcome.terminal? : FinishOutcome → Option Terminal
  | .normal _ _ => none
  | .deadlock _ _ => some .deadlock
  | .aborted t _ _ => some (.panic t)
  | .refused _ _ _ => none
  | .fatal m _ _ => some (.fatal m)

/-- The driver's classification at an endpoint, with the finishing picks and the
FINISHING COST (F2): 0 for the zero-cost arms, 1 for the abort and the fatal (each a
`stepFn` call, so each needs positive fuel).

`fatal` ([AGENT] coordinator disposition 2026-09-27, Reading A): a `stepFn` call at the
endpoint raises the unrecoverable terminal `.terminal (.fatal m)` (the sync misuse throws,
`Machine.lean:4392`, `:4416`, `:4443`, passed through by `toResult`, `Value.lean:394`); the
outcome carries the endpoint store and tape (correction (1)) and NO pick record — the
executable raises without returning a tape, and no consultation precedes those throws
(an [AGENT packet A worker] reading, flagged for packet B).

`aborted` / `abortRefused` do exactly what `stepFn`'s `.panicking chain .stop` arm does
(`StepFn.lean:368`–`387`): the `repanicCollapse` consult, then the fallible renderer
`abortMsg` (`Machine.lean:3908`). The executable arm draws through `abortConsult first rest
ch = Choices.consumeAt .repanicCollapse (repanicCollapseWidth first rest) ch`
(`Machine.lean:3203`); `Choices.consumeAtE_fst_snd` (`State.lean:475`) links it to the
record-emitting `consumeAtE` used here — cited, not proved in this file. `abortMsg`'s
error is a refusal by construction (`.unsupported`, `Machine.lean:3912`), hence the
`.refusal r` pattern. -/
inductive Finish (ctx : ProgramCtx) :
    Store → Config → Choices → List PickRecord → FinishOutcome → Nat → Prop where
  | normal {s : Store} {ch : Choices} :
      Finish ctx s (.next .stop) ch [] (.normal s ch) 0
  | blocked {s : Store} {c : Config} {ch : Choices} :
      Blocked c → Finish ctx s c ch [] (.deadlock s ch) 0
  | aborted {s : Store} {c : Config} {ch ch'' : Choices} {first : PanicEntry}
      {rest : List PanicEntry} {pick : Nat} {rec : List PickRecord} {t : String} :
      c.abort? = some (first, rest) →
      Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch
        = (pick, ch'', rec) →
      abortMsg ctx first rest pick = .ok t →
      Finish ctx s c ch rec (.aborted t s ch'') 1
  | abortRefused {s : Store} {c : Config} {ch ch'' : Choices} {first : PanicEntry}
      {rest : List PanicEntry} {pick : Nat} {rec : List PickRecord} {r : Refusal} :
      c.abort? = some (first, rest) →
      Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch
        = (pick, ch'', rec) →
      abortMsg ctx first rest pick = .error (.refusal r) →
      Finish ctx s c ch rec (.refused r s ch'') 1
  | fatal {s : Store} {c : Config} {ch : Choices} {m : String} :
      stepFn ctx s c ch = .error (.terminal (.fatal m)) →
      Finish ctx s c ch [] (.fatal m s ch) 1

/-- A completed labelled run — DERIVED from `Prefix` and `Finish`, not the carrier. -/
def LRun (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices)
    (ls : List StepLabel) (rec : List PickRecord) (o : FinishOutcome) : Prop :=
  ∃ n sf cf chf cost, Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf rec o cost

/-! ## Replay by record (correction (4)) and the domain premise (correction (5)) -/

/-- `ch₂` REPLAYS the pick records `ps` (a step's `StepLabel.picks`, in consultation order),
leaving `ch₂'` — replay BY RECORD (correction (4); re-stated by the row-2 label reshape,
2026-09-28): each record `⟨site, bound, pick⟩` is re-drawn on the remaining tape by the
SAME record-emitting consultation `Choices.consumeAtE site bound`, which must return the
recorded pick and emit exactly that record (so `bound > 1`: a bound-≤-1 consultation is
never recorded and pops nothing); no records — the tape is untouched. The previous form
(packet A) read the site and bound off `seqConsumption`; the label now carries them. -/
def replays : List PickRecord → Choices → Choices → Prop
  | [], ch₂, ch₂' => ch₂' = ch₂
  | r :: rs, ch₂, ch₂' =>
      ∃ mid, Choices.consumeAtE r.site r.bound ch₂ = (r.pick, mid, [r]) ∧ replays rs mid ch₂'

/-- No `Prefix`-reachable NON-zero-cost configuration, on any initial tape, has a refusing
`stepFn` call, and no reachable abort has a refusing renderer under the pick its consult
draws. The zero-cost endpoints are excluded (audit F2, 2026-09-27; [AGENT] coordinator
disposition): the driver never calls `stepFn` there, and `stepFn` REFUSES at `.next .stop`
(`StepFn.lean:850`, `.internal "step on terminal configuration"`), so without the exclusion
this premise failed on every normally completing run (the positive control below). -/
def NoRefusal (ctx : ProgramCtx) (s : Store) (c : Config) : Prop :=
  ∀ n ch ls sf cf chf, Prefix ctx n s c ch ls sf cf chf →
    (¬ ZeroCost cf → ∀ r, stepFn ctx sf cf chf ≠ .error (.refusal r)) ∧
    (∀ first rest, cf.abort? = some (first, rest) →
      ∀ e, abortMsg ctx first rest
        (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) chf).1
          ≠ .error e)

/-! ## The owed theorems, as statements (packet B proves each `_stmt` as `<name>`) -/

/-- `Prefix` is reflexive at length 0 with no labels. -/
def prefix_refl_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices), Prefix ctx 0 s c ch [] s c ch

/-- `Prefix` composes: lengths add, labels append. -/
def prefix_comp_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n m : Nat) (s s₁ sf : Store) (c c₁ cf : Config)
    (ch ch₁ chf : Choices) (ls ls' : List StepLabel),
    Prefix ctx n s c ch ls s₁ c₁ ch₁ → Prefix ctx m s₁ c₁ ch₁ ls' sf cf chf →
    Prefix ctx (n + m) s c ch (ls ++ ls') sf cf chf

/-- `Prefix` splits at every intermediate length. -/
def prefix_split_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n m : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx (n + m) s c ch ls sf cf chf →
    ∃ (ls₁ ls₂ : List StepLabel) (s₁ : Store) (c₁ : Config) (ch₁ : Choices),
      ls = ls₁ ++ ls₂ ∧ Prefix ctx n s c ch ls₁ s₁ c₁ ch₁ ∧ Prefix ctx m s₁ c₁ ch₁ ls₂ sf cf chf

/-- Erasure to relational reachability `Steps` (`Machine.lean:6157`). -/
def prefix_erase_steps_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx n s c ch ls sf cf chf → Steps ctx c s cf sf

/-- Erasure to the unlabelled counted `Trace` (`Trace.lean:15`). -/
def prefix_erase_trace_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices)
    (ls : List StepLabel),
    Prefix ctx n s c ch ls sf cf chf → Trace ctx n s c ch sf cf chf

/-- Exact agreement with the executable iterate `stepFnIter` (`StepFn.lean:1042`). -/
def prefix_iter_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (n : Nat) (s sf : Store) (c cf : Config) (ch chf : Choices),
    stepFnIter ctx n s c ch = .ok (cf, sf, chf) ↔ ∃ ls, Prefix ctx n s c ch ls sf cf chf

/-- `Finish.aborted` at `(s, c, ch)` with text `t` is exactly `stepFn`'s panic terminal
there (correction (2)). -/
def finish_abort_step_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (t : String),
    (∃ (rec : List PickRecord) (ch'' : Choices), Finish ctx s c ch rec (.aborted t s ch'') 1) ↔
      stepFn ctx s c ch = .error (.terminal (.panic t))

/-- At an abort configuration, `Finish.abortRefused` with `r` is exactly `stepFn`'s
refusal `r` there. -/
def finish_refused_step_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    ((∃ (rec : List PickRecord) (ch'' : Choices), Finish ctx s c ch rec (.refused r s ch'') 1) ↔
      stepFn ctx s c ch = .error (.refusal r))

/-- TERMINAL-draw replay (audit F3, 2026-09-27; [AGENT] coordinator disposition; response
§2 (4) / §6 «terminal consultation coverage»): a second tape `ch₂` whose `repanicCollapse`
consult emits the SAME record replays the abort's finish — same text (or refusal), `ch₂`'s
own residual. -/
def finish_replay_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch ch₂ : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (rec : List PickRecord),
    c.abort? = some (first, rest) →
    (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.2 = rec →
    (∀ (t : String) (ch'' : Choices), Finish ctx s c ch rec (.aborted t s ch'') 1 →
      Finish ctx s c ch₂ rec
        (.aborted t s (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1)
        1) ∧
    (∀ (r : Refusal) (ch'' : Choices), Finish ctx s c ch rec (.refused r s ch'') 1 →
      Finish ctx s c ch₂ rec
        (.refused r s (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1)
        1)

/-- Normal completion: a prefix of length `n ≤ fuel` to `.next .stop` (cost 0). -/
def run_ok_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf

/-- The panic terminal: prefix length plus the abort's cost 1 within the fuel. -/
def run_panic_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) (t : String),
    execStmtLoop ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1

/-- The sequential deadlock: a blocked endpoint at `n ≤ fuel` (cost 0). -/
def run_deadlock_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    execStmtLoop ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0

/-- Fuel-out: the fixed tape's ACTUAL prefix of length exactly `fuel`, ending at a
configuration that is NOT zero-cost (F2; an abort configuration is such a case). -/
def run_fuelOut_iff_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    execStmtLoop ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf

/-- Consultation COVERAGE: no unrecorded consultation affects a step — a second tape that
replays the step's recorded picks (`replays`, by record) takes the same step with the same
label, leaving its own residual. Stated WITHOUT the `c.appendTargetLocal` premise
`stepFn_consumption_some` carries (`MachineSound.lean`; its `none` twin): the proof already
drops it — «`hloc` is no longer needed here (kept in the statement for its callers)»
(audit F4) — so the premise-free statement is expected TRUE (unproven here). Row-2 note
([AGENT worker, lane core/step-label-0928]): a delivered panic that RESTORES the pre-apply
tape drops its consultation's record with the stream advance (the `appendSpill` arm's
post-pop panic path, if reachable), so coverage there rests on the same fact — packet B's
first question, flagged in `docs/2026-09-28_step-label-handoff.md`. -/
def replay_coverage_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s s' : Store) (c c' : Config) (ch ch' : Choices) (l : StepLabel),
    stepFn ctx s c ch = .ok (c', s', ch', l) →
    ∀ ch₂ ch₂', replays l.picks ch₂ ch₂' → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l)

/-- A silent step (label `⟨[], [], []⟩`) contributes nothing to the observation — the
per-field fold `StepLabel.fold` (`Ops.lean`; proved there as `StepLabel.fold_silent`, the
statement kept here under its packet-A name). No `[emptyLabel]` element ever appears. -/
def silent_projection_stmt : Prop :=
  ∀ (ls₁ ls₂ : List StepLabel),
    StepLabel.fold (ls₁ ++ ⟨[], [], []⟩ :: ls₂) = StepLabel.fold (ls₁ ++ ls₂)

/-- The single-goroutine embedding: `execProgLoop_single` (`MultiSound.lean:666`) restated;
the cost relation IS `seqOpCount` (`MultiSound.lean:640`), never «equal fuel». DEFINITIONAL
(audit F5): it is literally `execProgLoop_single` — pinned, NOT counted as a new bridge. -/
def single_embedding_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (σ : Store) (c : Config) (ch : Choices) (rs : RaceState)
    (r : Except Stop (Store × Choices)),
    execStmtLoop ctx fuel σ c ch = r → transferable r →
    execProgLoop ctx (fuel + seqOpCount ctx fuel σ c ch) ⟨#[.running c none], σ, 0⟩ rs ch = r

/-- The program bridge under successful setup (setup's tape `ch → ch₁` INCLUDED): the
driver is the pool fold from the setup seam's context, configuration, store and residual
tape, with the `loadMany` readout. Init OUTPUT is empty BY REFUSAL (`initPrintRefusal?`,
`StepFn.lean:1118`) — the named limitation is RETAINED. DEFINITIONAL (audit F5): it is
`runProgramPoolOutM`'s own equation unfolded under the setup premise; it pins the setup →
pool-fold → readout seam and does NOT connect to `Prefix`/`LRun` — NOT counted as a bridge
(the pool half waits, charter §2). -/
def program_bridge_stmt : Prop :=
  ∀ (fuel : Nat) (p : Program) (name : String) (args : Array GoValue) (ch : Choices)
    (pctx : ProgramCtx) (c₀ : Config) (s₀ : Store) (locs : List Loc) (ch₁ : Choices),
    runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁) →
    runProgramPoolOutM fuel p name args ch =
      (match execProgLoopOut pctx fuel ⟨#[Thread.running c₀ none], s₀, 0⟩ {} ch₁
          GoString.empty with
        | (out, .error e) => .error (e, out)
        | (out, .ok (sf, _)) =>
            match loadMany pctx sf locs with
            | .ok vs => .ok { values := vs.toArray, output := out }
            | .error e => .error (e, out))

/-! ## The four-way classification (correction (5); [AGENT] coordinator disposition
2026-09-27, Reading A: the terminal case ranges over the FIVE `Finish` constructors) -/

/-- Case 1 — normal completion, with `run_ok_iff_stmt`'s witness. -/
def ClassOk (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) : Prop :=
  ∃ sf chf, execStmtLoop ctx fuel s c ch = .ok (sf, chf) ∧
    ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf

/-- Case 2 — a Go terminal, with a `Finish` reporting it at prefix length plus finishing
cost within the fuel. -/
def ClassTerminal (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
    Prop :=
  ∃ t, execStmtLoop ctx fuel s c ch = .error (.terminal t) ∧
    ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices)
      (rec : List PickRecord) (o : FinishOutcome) (cost : Nat),
      n + cost ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf rec o cost ∧
        o.terminal? = some t

/-- Case 3 — fuel-out, with `run_fuelOut_iff_stmt`'s witness. -/
def ClassFuelOut (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
    Prop :=
  execStmtLoop ctx fuel s c ch = .error .fuelOut ∧
    ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
      Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf

/-- Case 4 — a refusal, REPORTED: a prefix to a configuration whose `stepFn` call refuses
(the call costs 1, hence `n + 1 ≤ fuel`), or a `Finish.abortRefused`. -/
def ClassRefusal (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
    Prop :=
  ∃ r, execStmtLoop ctx fuel s c ch = .error (.refusal r) ∧
    ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
      n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
        (stepFn ctx sf cf chf = .error (.refusal r) ∨
          ∃ (rec : List PickRecord) (ch'' : Choices), Finish ctx sf cf chf rec (.refused r sf ch'') 1)

/-- UNCONDITIONAL classification: every run is exactly one of the four cases — no «all
executions succeed» premise. Exclusivity is by construction: the four cases fix
`execStmtLoop …` to the pairwise-distinct result shapes `.ok`, `.error (.terminal _)`,
`.error .fuelOut`, `.error (.refusal _)`. -/
def classification_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    ClassOk ctx fuel s c ch ∨ ClassTerminal ctx fuel s c ch ∨ ClassFuelOut ctx fuel s c ch ∨
      ClassRefusal ctx fuel s c ch

/-- The corollary under the domain premises: a well-formed store and no reachable refusal
leave the first three cases only. `step_preserves_wf` (`StateWf.lean:8106`) is the
preservation fact to cite; it is stated over `MachineWf ctx σ c`, not `StateWf ctx σ` (an
[AGENT packet A worker] flag for packet B). -/
def classification_wf_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    StateWf ctx s → NoRefusal ctx s c →
      ClassOk ctx fuel s c ch ∨ ClassTerminal ctx fuel s c ch ∨ ClassFuelOut ctx fuel s c ch

/-! ## Boundary controls (the fuel convention KEPT, F2)

Three proved controls copied from the review witness, two FATAL controls (below)
(`docs/evidence/2026-09-23_batched-window-review/FuelBoundary.lean`), then the other four
boundary facts as statements. The witness's `ctx` (`ProgramCtx.ofTables #[] #[]`) and
`abortConfig` (`.panicking [panicEntry "review"] .stop`) are inlined. -/

example : (Config.panicking [panicEntry "review"] .stop).abort? = some (panicEntry "review", []) :=
  rfl

example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.panicking [panicEntry "review"] .stop) ch
      = .error .fuelOut := rfl

example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.next .stop) ch = .ok (s, ch) := rfl

/- The FATAL boundary ([AGENT] coordinator disposition 2026-09-27; witness [AGENT packet A
worker]): an `Unlock` of an unlocked mutex at its apply position — the store holds one
unlocked mutex cell at `base 0`, the configuration delivers its address to the
`syncStK .unlock` frame. The fatal is raised by the `stepFn` call: fuel-out at 0, the
terminal at 1 (cost 1, like the abort). -/

example (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0
      { heap := #[.value (.sync .mutex) (.syncData (.mutex false))] }
      (.retV (.addr (.base ⟨0⟩)) (.syncStK .unlock [] [] [] .stop)) ch = .error .fuelOut := rfl

example (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 1
      { heap := #[.value (.sync .mutex) (.syncData (.mutex false))] }
      (.retV (.addr (.base ⟨0⟩)) (.syncStK .unlock [] [] [] .stop)) ch
      = .error (.terminal (.fatal "sync: unlock of unlocked mutex")) := rfl

/- `NoRefusal` POSITIVE CONTROL (audit F2; the auditor's `not_noRefusal_of_completes` shape,
`docs/evidence/2026-09-27_packet-a-audit/NoRefusalVacuous.lean`, now reversed): a run that
completes normally — one step from `.next (.seq [] [] .stop)` to `.next .stop` (checked by
`#eval` first) — SATISFIES the corrected `NoRefusal`, for every context and store. -/
example (ctx : ProgramCtx) (s : Store) : NoRefusal ctx s (.next (.seq [] [] .stop)) := by
  intro n ch ls sf cf chf hp
  cases hp with
  | done => exact ⟨(fun _ r h => nomatch h), (fun _ _ h => nomatch h)⟩
  | step h hp' =>
    injection h with h'
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    cases hp' with
    | done => exact ⟨(fun hz => absurd (Or.inl rfl) hz), (fun _ _ h => nomatch h)⟩
    | step h2 _ => exact nomatch h2

/-- An abort whose renderer succeeds is the panic terminal at fuel 1. -/
def boundary_abort_one_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (t : String),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 = .ok t →
    execStmtLoop ctx 1 s c ch = .error (.terminal (.panic t))

/-- A blocked configuration is the deadlock terminal at fuel 0. -/
def boundary_blocked_zero_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices),
    Blocked c → execStmtLoop ctx 0 s c ch = .error (.terminal .deadlock)

/-- A renderer refusal at an abort is the refusal at fuel 1. -/
def boundary_refused_one_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
        = .error (.refusal r) →
    execStmtLoop ctx 1 s c ch = .error (.refusal r)

/-- The same abort configuration at fuel 0 is fuel-out (the abort costs 1). -/
def boundary_refused_zero_stmt : Prop :=
  ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) (first : PanicEntry)
    (rest : List PanicEntry) (r : Refusal),
    c.abort? = some (first, rest) →
    abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
        = .error (.refusal r) →
    execStmtLoop ctx 0 s c ch = .error .fuelOut

end GoLean.GoCore.ExecutionStatement
