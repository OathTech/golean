# The sem() adequacy arc — plan of record (2026-08-03)

Decided in the 2026-08-03 baselining conversation (user + agent, recorded
here per the capture-decisions rule). This arc realizes the project's
statement idiom in its final intended form and supersedes older framings —
see §Supersessions, which edits the living docs in the same commit so no
remnant of the old framing survives as guidance.

## THE GOAL (the user's formulation, verbatim in substance)

We are building a **semantic evaluation function `sem()` over GoCore
programs**: more or less an interpreter — it can terminate or keep going —
with type roughly `GoState → GoState` over configurations of memory and
variables. Specifications are stated ENTIRELY in interpreter-level notions:

    ⟨P terminates⟩ ∧ ⟨state satisfies pre⟩ → sem(P, state) satisfies post

with variants for reasoning about nontermination, and (future) concurrency
handled by an outer fork/join scope — single-threaded pre-state in, forked
execution, join, results read off — so even concurrent specs are pre/post
state statements over `sem`. **Iris is proof machinery, never a
specification idiom.** We build the semantics for fidelity (differential
testing) and use Iris internally. The agent's stronger rendering (below) is
adopted so long as the user's form above is a supported case.

## The decisions

1. **One trusted semantic artifact.** `sem` is `stepFn` iterated under fuel
   (`execStmt` is exactly that wrapper — post-reshape there is no second
   interpreter). This is the differentially validated artifact and the ONLY
   semantics allowed in headline statements.
2. **The Prop-level relation (`Step`/`Steps`, defined inside `Machine.lean` since the reshape deleted `Rel.lean`) is proof
   infrastructure**, exactly like Iris: required because WP needs a
   transition relation, verified against `stepFn` (two-sided at step level:
   `stepFn_sound`/`step_complete`), and — after this arc — absent from
   every headline statement's closure. The deletion test extends to it:
   deleting the relation (`Step`/`Steps` and everything about them) must not change what any headline theorem *says* — enforced at CONSTANT level by the statement-TCB gate, since the relation shares `Machine.lean` with the interpreter and module-level deletion is not the operative test.
   (This INVERTS the pre-reshape framing "relational semantics = the proof
   authority, interpreter = its test implementation"; see §Supersessions.)
3. **Termination is a first-class interpreter-level notion.**
   `Terminates P s := ∃ N, ∀ fuel ≥ N, ∀ choices, execStmt … = .ok …`
   (uniform bound is right: branching is finite). The headline default is
   the PROVEN-termination (total-correctness) form
   `pre → Terminates ∧ post`; the user's assumed-termination form and the
   nontermination dual (`∀ fuel, fuel-out`) are supported cases. Rationale
   for the default: assumed termination re-admits the vacuity class
   (a diverging wrong program satisfies the assumed form), and proving the
   stronger thing has repeatedly forced honest side conditions out of the
   machine (the `< 2^63` representability bound).
4. **Safety restates interpreter-side.** `Progress` becomes "for all fuel
   and choices, `execStmt` returns only `.ok` or fuel-exhaustion — never
   stuck, never unrecovered panic". Requires splitting fuel-exhaustion
   from genuine stuckness in `GoError` (today both are `.stuck`,
   distinguished only by message text). Invariance (`GoInvariant`)
   restates over `stepFn` iterates. Honesty note kept from the
   conversation: intermediate-state properties are beyond ANY differential
   oracle (Go does not expose our configurations); stating them over
   `stepFn` means they rest on the *tested* presentation of the model.
5. **Concurrency posture (forward decision, not this arc).** The `Choices`
   stream in `sem`'s signature is the scheduler hook; "∀ schedules" is the
   ∀-choices quantifier statements already carry. Fork/join specs stay
   pre/post over `sem`. The differential oracle weakens from equality to
   MEMBERSHIP (Go exhibits one schedule per run; we admit a set) — the
   concurrent corpus must be designed around that from day one.

## Slices

0. **This document + the living-doc scrub** (same commit): AGENTS.md trust
   chain, roadmap.md strategy bullets, CLAUDE.md audit-dimension wording,
   doctrine doc extension. Dated pre-reshape notes stay as historical
   record — they are records, not guidance.
1. **The termination-discharge SPIKE (front-loaded — the arc's main
   risk).** Kernel-evaluate `execStmt` to `.ok` on the pinned lowerings
   (no `native_decide` — banned in proof-facing code; this is honest
   kernel reduction, `rfl`-class). Measure cost golden → recover → quorum
   → committed-index-real. If tractable: `Terminates` discharges by
   computation. If not: fallback is a steps-bounded variant of the walk
   machinery (symbolic, constructive fuel bound) — and knowing which world
   we are in reshapes slices 3–5, hence spike first.
2. **`fuelOut` refinement.** Distinct fuel-exhaustion error (or outcome) in
   the core; differential-neutral by intent; corpus classification cases
   FIRST (guardrails-first), then `--diff`.
3. **The named notions.** `Terminates`, the total `GoSpec` variant, the
   assumed-termination derived form, interpreter-side `Progress`, the
   error-direction correspondence lemma (execStmt stuck/panic error ⇔
   reachable stuck/panicked config) proving old-Progress ↔ new-Progress.
4. **Relation eviction.** Invariance over `stepFn` iterates; every headline
   statement relation-free; statement-TCB gate extended to enforce
   RELATION-freedom exactly as it enforces Iris-freedom (module-of-origin
   check on `Rel`/`Correspondence` proof modules … precise module list
   fixed during the slice).
5. **Retrofit + re-certify.** The designated family upgraded to total form
   where the slice-1 answer makes it payable; unconditional negative twins
   landed; Audit gates updated; **Comparator landmark run mandatory**
   (designated statements change) before the merge ask.

## Build log

- **Slice 1 spike — VERDICT (2026-08-03): tractable after a bounded core
  restructure.** Phase A (compiled): all four pinned programs terminate
  with correct readouts (recover→7, oneKnown→12, threeAll→6, allConfig→6)
  at fuel ≤ 4000, milliseconds. Phase B (kernel `rfl`): stuck — `#reduce`
  tracing found `Acc.rec`, i.e. well-founded recursion, which never
  reduces definitionally. Environment scan of every `GoLean.*` constant
  for `WellFounded.fix`/`Acc.rec`/`._unary` found the COMPLETE
  kernel-irreducible set is four definition families:
  `Ty.mentionsUnsupported`, `defaultValueFuel` (mutual),
  `normalizeValueForTyFuel` (mutual), `valueEqFuel` (mutual) — every one a
  bounded type/value helper, none of them `stepFn`'s spine. Fix: uniform
  depth-structural recursion (`| d+1 => … d` on an explicit Nat), which
  the kernel reduces; signatures preserved via the existing fuel-constant
  wrappers; behavior change confined to how fast internal resolution
  depth is consumed (differential validates neutrality). This is the
  CLAUDE.md "prefer structural recursion so the proof direction stays
  reachable" principle cashing out, three weeks after it was written.

- **Slice 1 executed (sub-branch `sem-adequacy-dewf`) — the de-WF
  restructure + spike completion, 2026-08-03.** Chronicle, including two
  design corrections the process forced:
  1. **Node-count fuel rejected (soundness catch).** The first structural
     recipe charged fuel per element; threading its side condition into the
     sort walk showed it would make `Progress` — and hence
     `committedIndexAllConfigs` — FALSE for configs past the budget (the
     statement quantifies `c.length < 2^63`). Shipped shape: parameterized
     list/field helpers (`normalizeListWith` etc.) taking the
     already-decremented recursive function — structural, kernel-reducible,
     and DEPTH-only accounting. (Precision, from the sub-branch audit's
     measured old-vs-new differential: depth-ONLY holds — elements and
     fields never charge — but not "exactly as before", as an earlier
     draft of this entry claimed: array LEVELS and the leaf now cost one
     unit each where they were free, a pure `.defined` chain supports
     1023 links instead of 1024, and `Ty.mentionsUnsupported`, previously
     budget-free total recursion, now shares the budget failing CLOSED.
     Every divergence is old-ok→new-fail-closed at nesting depth ≥ 1023,
     unreachable from Go source; the audit's ~180k-case probe found ZERO
     divergences at the real 1024 seed. Normative statement:
     `typeResolutionFuel`'s docstring in `Ops.lean`.)
  2. **Elaborator sealing.** Reducible fuel towers made `whnf`/`isDefEq`
     dive 1024 literals deep (heartbeat blowups; one uncapped reduction ate
     system RAM in seconds — twice took the whole session stack down via
     the OOM killer; containment convention now in
     `docs/agent-sandbox.md`). Sealing the FUEL functions is unworkable
     (equation generation is per-module and blocked by irreducibility —
     found empirically); the WRAPPERS are sealed instead, restoring the
     old equations-only proof discipline; kernel unaffected.
  3. **`List.mergeSort` is kernel-irreducible** (WF-compiled in core Lean;
     the elaborator's smart unfolding had hidden this). The machine's
     `sortSlice` now uses the structural `sortLe` (insertion sort), with
     the `Laws/Values` lemma surface mirrored (`sortLe_perm`,
     `pairwise_sortLe`, `sortLe_pairs_eq_of_perm`); output provably
     agrees (sorted-permutation uniqueness) and the mergeSort lemmas stay
     for the math layer (`sortAsc`).
  4. **The derived `BEq GoValue` is WF-compiled too** (nested `Array`) —
     it stuck the first end-to-end kernel probes and cost a fuel-bisect to
     localize; kernel-side checks must project to primitive types (the
     readout statements' `loadLoc … = .ok (.int v k)` form is already
     right; only Bool-level probes need care).
  **RESULT: all four pinned programs kernel-evaluate end to end** —
  recover→7 (296-step quorum: oneKnown→12; threeAll→6; the real
  `main.MajorityConfig.CommittedIndex` on the heap-encoded 3-voter
  config→6) — in ≈4 s total under a 16 GiB cap, `decide +kernel`, no
  `native_decide`. `Terminates` discharge is VIABLE for the whole summit
  family. Differential: 873/873 no-drift after the de-WF families
  (fresh full run) AND again after the sort swap (fresh full run,
  873/873, `scripts/ci --diff` PASS at 4dddf7b).

- **Slice 2 (`fuelOut` refinement) — DONE 2026-08-03.** `GoError.fuelOut`
  is its own constructor (status `"fuel-out"`), thrown at the two
  fuel-exhaustion sites (`runConfig`, `execStmtLoop`); `.stuck` no longer
  doubles as the fuel marker (the old shape distinguished them only by
  message text — unusable as the basis of interpreter-side `Progress`).
  Guardrails-first honored: the two eval-tests were authored FIRST and
  shown red against the old core ("expected fuel-out, got stuck"), then
  the refinement landed them green. CLI observation schema extended with
  the new status (fail-closed unknown-status handling unchanged). Proofs
  layer: zero fallout (no proof matched GoError exhaustively). Gate:
  `scripts/ci --diff` PASS, fresh 873/873, zero drift — corpus cases never
  exhaust fuel, by construction.

- **Slice 3 (sub-branch `sem-adequacy-notions`) — IN PROGRESS, paused at a
  design choice point (2026-08-03).** Landed: the choices-discipline
  refactor (`applyStmtOpCore` — the stream now syntactically touches
  exactly two machine sites, both total); Surface's `Terminates` /
  `ProgressExec` / `GoSpecT` / `goSpecT_assumed_form`; `execStmt_mono`;
  `step_panicked_elim`. **BLOCKED, honestly:** the worker's ∀-choices kit
  proof hit a machine-checked obstruction — `appendSlice`'s spill path
  allocates fresh backing at `s.nextAddr` sized by the consumed capacity
  choice, so a DANGLING target loc aliasing into the fresh cell makes
  step success depend on the choice stream (witness: same state, target
  `.index (.base nextAddr) 8` — `.ok` at stream `[1]`, index-panic at
  `[0]`; a nested variant gives panic-vs-STUCK). No machine-reachable
  well-formed state contains a dangling loc (allocator freshness; real Go
  has no dangling addresses — fidelity unaffected, differential can never
  see it), but `InitialSplit.HeapBounded` bounds heap KEYS only, so the
  ∀-state notions (`ProgressExec` from relation-`Progress`, the transport
  chain) are FALSE at these pathological unreachable states. The candidate
  resolutions (user decision pending): (a) a `StateWf` invariant — every
  loc occurring in heap values / env / config is below `nextAddr` —
  proved preserved by `Step` and threaded into admissibility
  (`InitialSplit`), strengthening every surface statement's premise; or
  (b) reshape the spill arm to decouple ok-ness from the capacity choice.
  **DECIDED (user, 2026-08-04): (a) — well-formedness.** The judgments
  should capture reasoning about LEGITIMATE Go states: `{P ∧ wf} prog
  {Q ∧ wf}` with per-step preservation `{wf} cmd {wf}`; the post-side wf
  is a corollary of preservation, never a per-spec obligation. Recorded
  rationale from the design discussion: Goose/Perennial obtain the same
  discipline IMPLICITLY (opaque locations + iProp-only statements +
  state-interpretation invariants); our explicit conjunct is that
  discipline made visible, and the price of the two deliberate choices
  that surface it — a DETERMINISTIC allocator (the semantics must
  EXECUTE: the differential's trust root, "the absolutely most important"
  property per the user) and faithful quantification over Go's
  append-capacity latitude (observable via `cap()`; Goose hardcodes one
  policy). One-time preservation induction, then a single premise
  conjunct forever; also the invariant concurrency will need.

- **Slice 3, StateWf preservation (2026-08-04, in progress on
  `sem-adequacy-notions`).** The decided (a)-resolution implemented:
  `GoLean/GoCore/StateWf.lean` — kernel-reducible `locSup` checker family
  (strict sup of location root-bases; structural recursion incl. nested
  inductives, verified no `WellFounded.fix`/`Acc.rec`), Prop wrappers
  `StateWf`/`ConfigWf`/`MachineWf` (decidable, so concrete seeds discharge
  by `decide`), the helper-preservation layer (load/store/alloc/enterFrame/
  bind-iter/op tables), and `step_preserves_wf` over every `Step` rule.
  TWO carrier findings beyond the plan: `Expr.locLit` means program TEXT
  carries locations (so `Stmt`/`Expr`/`Func`-body checkers exist and
  `StateWf` covers `σ.functions` bodies — `enterFrame` moves them into the
  configuration). `InitialSplit` gained `(funcs env₀ prog)` parameters and
  a `wf : MachineWf …` field; all Golden* readout seeds discharge it by
  kernel `decide`.
- **Slice 3 — SECOND ∀-choices obstruction, machine-checked (2026-08-04):
  `mapIterNext` resists ∀-streams even under StateWf.** Witness
  (`.tmp/probe_mapiter.lean`): a loc-free (hence trivially wf) state with a
  `mapIterK` snapshot holding HETEROGENEOUS entries `#[(int 1, _),
  (bool true, _)]` at `keyTy = int`: the relation steps (pick 0 binds), but
  `stepFn` at stream `[1]` picks entry 1 and `bindIterVars`'s
  `normalizeValueForTy` rejects the bool key — `.error .stuck`. Since
  snapshots come from heap `mapData` cells and neither cells nor the
  `mapRange` statement's `keyTy` are constrained by loc-wf, `step_complete_any_wf`
  as specified is FALSE; and with a diverging loop body the bad `.next
  (.mapIterK …)` re-entry is unreachable, so relation-`Progress` holds
  while a bad stream still errors — `execStmtLoop_ok_or_fuelOut` and the
  unconditional `Progress → ProgressExec` transport are FALSE as
  specified too. This is a VALUE-SHAPE (typing) condition, not a
  loc-boundedness one: candidate resolutions are (a) an explicit
  per-snapshot bindability side condition on the reachable set (honest but
  reachability-quantified), or (b) reshaping `mapRangeSnapshot` to
  normalize entries at snapshot time (stream-independent fail-closed
  point; a semantics change needing its own differential run) — user
  decision pending, recorded here per the fail-closed/no-silent-weakening
  contract. `appendSlice`, by contrast, resolves exactly as the wf design
  predicted (the spill target provably addresses an existing cell).

- **mapIter obstruction — RESOLVED BY DESIGN (2026-08-04, recorded):
  snapshot-time validation (the worker's option (b)), chosen because (i)
  the refuting state — an ill-typed key in a map snapshot — is not a
  legitimate Go state any more than a dangling loc is (`mapAssign` only
  ever stores normalized keys), and (ii) it is the choices-discipline
  principle again: moving the per-pick typing check to the pick-FREE
  snapshot step makes stream-independence of iteration success
  structural, not proven. Shape: the `mapRange` snapshot step (stepFn AND
  the relation rule) fails CLOSED unless every snapshot key is
  self-normalized at the range key type (`normalizeValueForTy σ keyTy k =
  .ok k` — the self-normalized CHECK, not a re-normalization, so no
  idempotency metatheory is needed and `bindIterVars`' per-pick normalize
  then provably succeeds unchanged). Legitimate states pass the check
  identically → differential-neutral by intent, `--diff` mandatory.
  `MachineWf` gains the matching typing component for in-flight
  `mapIterK` continuations, established by the snapshot rule and
  preserved by shrinkage.

- **Slice 3 — the ∀-choices kit COMPLETED (2026-08-04, on
  `sem-adequacy-notions`).** The recorded snapshot-time-validation design
  implemented end to end; every piece landed, differential-neutral
  (fresh full run 873/873, zero drift vs `baselines/native-full.tsv`).
  1. **Semantics**: `mapRangeSnapshotEntries` (Machine.lean) — the
     snapshot premise function shared verbatim by `stepFn`'s `mapRangeK`
     arm and rule `Step.mapRangeSnapshot` — fails closed unless every
     snapshot entry is self-normalized at the range key/value types
     (`snapshotEntriesSelfNormalized`, over the kernel-reducible
     `isNormalForTy` checker family in Ops.lean, which decides
     `normalizeValueForTy σ ty v = .ok v` without a generic `GoValue`
     equality — the derived `BEq GoValue` is WF-compiled/opaque and must
     stay off kernel-evaluation paths). **Deviation from the recorded
     shape, forced by a machine-checked gap:** the design named only the
     KEYS, but `bindIterVars` also normalizes the VALUE at `valTy`
     whenever a value variable is bound, so key-only validation leaves a
     values-variant of the same probe refuting `step_complete_any_wf`
     (heterogeneous VALUES, `valVar = some`). The check therefore covers
     keys AND values — same legitimacy argument (`mapAssign` stores both
     normalized), differential-confirmed neutral.
  2. **Wf extension**: `MachineWf` gains a third conjunct —
     `Config.itersNormalized σ.types c` (StateWf.lean), the per-`mapIterK`
     snapshot check over the whole continuation. Parameterized by the
     `TypeEnv` directly so types-invariance is a rewrite; the old
     preservation theorem became `step_preserves_wf_loc` (now also
     concluding `σ'.types = σ.types` — no rule mutates `types`),
     `step_preserves_iters` proves the typing half (snapshot rule
     establishes, `eraseIdx` shrinkage preserves, everything else is
     structural; `seqCont`/`pushDefer`/`panicPassthrough`/`recoverResult`
     mirror lemmas), and `step_preserves_wf` recombines under the old
     name/statement. Concrete seeds still `decide` (initial configs carry
     no `mapIterK`); all six `InitialSplit` sites unchanged.
  3. **The kit (MachineSound.lean)**: the appendSlice spill half closed
     via the three recorded lemmas —
     `defaultValueFuel_ok_of_normalize_ok` (padding defaults from any
     element's normalize success), `Heap.lookup_set_ne` +
     `loadLoc_root_congr` under new `LawfulBEq Addr/Loc` instances
     (load/store agreement below `nextAddr`), and a `capCong`
     (values-equal-up-to-slice-`cap`) congruence family through
     `normalizeValueForTyFuel`/`coerceStoredValue`/`StructFields.set`/
     `arraySet`/`storeLoc` (`storeLoc_congr`: outcome CLASS — ok / panic
     / neither — independent of the fresh backing and the stored cap).
     Headliners: `applyStmtOp_ok_any_ch_wf` (+ `_panic_` twin, via
     `applyStmtOp_congr_any_ch`), `step_complete_any_wf`,
     `execStmtLoop_ok_or_fuelOut`, and Surface's
     `progressExec_of_progress` (InitialSplit's wf field supplies the
     premise; `execStmt` unfolds to `execStmtLoop` definitionally).
  4. **Law fallout**: `wp_map_range_snapshot` gained the matching
     `hnorm` premise (ghost-pinned via `GoCoreGS.types GF`, like
     `wp_map_iter_next_key`'s); `wp_map_range_snapshot_nil` unchanged in
     statement (empty snapshot passes trivially). Repaired sites:
     `GoldenQuorumPin.wp_map_range_snapshot_committed` (gains the
     hypothesis — its entries are symbolic), `GoldenQuorumWP` (discharged
     `by rw [htypes]; decide +kernel` at the pinned snapshot),
     `GoldenQuorumThree`/`GoldenQuorumAll` (symbolic voter lists:
     per-entry via `snapshotEntriesSelfNormalizedList_of_mem` + the
     walks' existing `hnormk`, constant value part by `decide +kernel`).
     `wp_map_iter_next_key`'s `hnorm` premise is now REDUNDANT for
     machine-produced snapshots (subsumed by the snapshot-time check) but
     its statement is left untouched (statement stability); simplification
     opportunity recorded, not taken.
  5. **Probe**: `.tmp/probe_mapiter2.lean` — the old witness state now
     fails `MachineWf` (`decide +kernel`), the snapshot step rejects the
     ill-typed cell at every stream, and a well-typed snapshot still
     steps with a well-formed result. `.tmp/probe_mapiter.lean`'s raw
     `mapIterK` `#eval`s behave as before BY DESIGN (the per-pick path is
     untouched; the state is simply illegitimate now).

- **Sub-branch audit + response (`sem-adequacy-notions`, 2026-08-04).**
  2 Opus reviewers + refute-by-default verifiers over the 7-commit diff:
  13 findings, 9 confirmed. Fixed: [major] MachineSound's module doc
  still declared the kit theorems FALSE/open (stale as of the very
  commit that closed them) — rewritten to the resolved status with
  history; [major] `goSpecT_assumed_form` was an eta-expansion of
  `GoSpecT.1` that never used `Terminates` — replaced by the honest
  `goSpecT_terminates_and_post` (termination + normal-run post,
  completion outcome deliberately quantified); [minor] the Audit ledger
  gained the slice-3 section (axiom pins for `step_preserves_wf`,
  `step_complete_any_wf`, `execStmtLoop_ok_or_fuelOut`,
  `progressExec_of_progress`, `goSpecT_terminates_and_post` +
  deletion-guard references) and the `wp_map_range_snapshot` witness
  ledger prose was updated (premise propagated by the symbolic witness,
  discharged at both shapes by its callers); [note] the unused `StateWf`
  hypothesis on `applyStmtOp_appendSlice_congr` dropped with corrected
  credit; [note] `applyStmtOpCore`'s docstring now names its fail-closed
  internal appendSlice arm; [note] BUG-005 coupling recorded in BUGS.md
  (the live-iteration fix must replay the stream-obliviousness
  analysis); [note] NEW pre-existing fidelity bug found by audit
  probing, filed as **BUG-011** (anonymous `struct{}{}` stuck at named
  empty-struct types — Go assignability vs our identity check;
  fail-closed, corpus case owed first per the standing rule). Recorded
  decisions: values-unconditional snapshot checking kept (legit states
  pass identically — `mapAssign` normalizes both; conditioning on
  `valVar` rejected as complexity without fidelity gain);
  `InitialSplit.bounded` is now provably redundant under `wf` — its
  REMOVAL is bundled into slice 5's statement re-land (one statement
  churn, one Comparator re-landmark); the notions' real witnesses ARE
  the slice-5 retrofits (deferral recorded, not a toy witness); the
  **Comparator landmark trigger is armed**: `InitialSplit`'s reshape
  changed every designated statement's closure, so slice 5's judge run
  is mandatory before the arc's merge ask.

- **Slices 4+5 (branch `sem-adequacy-eviction`) — the statement re-land,
  DONE 2026-08-04.** Three commits (stage A eviction, stage A gate, stage
  B totals+twins); `scripts/ci` PASS end to end.
  1. **Relation eviction (slice 4).** `GoSpec := GoTriple ∧ ProgressExec`
     — the safety half is interpreter-side; the relation-quantified
     progress survives as the PROOF-layer `ProgressRel` (the WP adequacy
     pipe's output shape) and `goSpec_of_triple_progressRel` is the
     assembly pipe (`goSpec_of_wp`'s last step — the predicted one-line
     change; every existing discharge went through untouched).
     `GoInvariant` restates over EXECUTABLE reachability: new core
     `stepFnIter` (raw n-fold `stepFn`; terminals throw, so a successful
     iterate is a genuine run prefix), `Surface.ReachableExec`, transport
     `stepFnIter_sound`/`steps_of_reachableExec` (`stepFn_sound` chained
     — the containment direction discharges need; `goldenInvariant`'s
     proof text unchanged). **Recorded as NOT built:** the converse
     realization (`Steps`-reachable ⇒ reachable at some stream) is true
     on paper via `step_complete` but chaining per-step witness streams
     into one `stepFnIter` stream needs a stream-stitching lemma no
     current discharge needs; the executable-reachable set is the honest
     statement carrier regardless (the tested presentation).
     `InitialSplit.bounded` REMOVED as bundled: heap KEYS count into
     `StateWf`'s sup, so `Heap.lookup_key_locSup` + `wf` derive
     `HeapBounded` (`InitialSplit.heapBounded`); the six seed sites
     dropped the field, the adequacy pipe consumes the derivation.
  2. **Gate (slice 4).** The statement-TCB walk now forbids the relation
     from designated statement closures exactly as it forbids Iris — by
     explicit forbidden NAMES (`…Machine.Step`/`…Machine.Steps` + their
     namespaces; module-of-origin cannot discriminate — the relation
     lives in Machine.lean). All 25 designated closures pass with ZERO
     eviction debt after stage A; a negative test confirmed the walk DOES
     reach `Steps` from a `ProgressRel`-shaped statement (the check is
     live, not vacuous).
  3. **∀-streams termination (slice 5).** The checker `allStreamsOk`
     (MachineSound) + soundness `execStmtLoop_ok_of_allStreamsOk`:
     `Terminates` quantifies every stream, a kernel run exhibits one; the
     bridge is the choices discipline made a proof — `stepFn_oblivious`
     (a `fun_cases` sweep: every arm that is not the `mapIterK` pick or
     an `appendSlice` apply is stream-oblivious with the SAME successor;
     a future consuming arm breaks the sweep loudly, never unsounds the
     checker), the pick BRANCHED over every index (`stepFn_mapIter_pick`
     — the successor is a function of the index alone), `appendSlice`
     apply positions failing closed. The whole chain is CONSTRUCTIVE
     (`[propext, Quot.sound]`). Landed: `goldenTerminates`,
     `recoverTerminates`, `quorumOneKnownTerminates`,
     `quorumThreeAllTerminates` (all 3! = 6 pick orders explored) —
     measured ≈ 6 s total kernel time for all four under the 16 GiB cap
     — plus the per-seed `<pin>TotalReadout` forms (originally
     Terminates ∧ the proven readout; STRENGTHENED to normal-pinned
     completion at the 2026-08-04 audit response — see the entry below).
     **Recorded as OWED, not attempted:** full per-pin
     `GoSpecT` — symbolic termination over ALL admissible initial states
     — the ∀-config statements stay at (new) `GoSpec` strength.
  4. **Unconditional negative twins (slice 5).**
     `quorumOneKnownNotEleven_statement` / `quorumThreeAllNotTwelve_statement`
     — targets since phase 4, honestly out of reach until a terminating
     run existed — DISCHARGED (`Specs/TotalPins.lean`): the
     kernel-exhibited `.normal` run + the run-conditioned readout at the
     true value (12/6) contradict the wrong spec's triple. The
     run-conditioned twins were renamed `*Run` (statements unchanged,
     still designated); the clean names now carry the unconditional
     claims. Designated list 23 → 25; Challenge/Solution/judge-config
     updated in lockstep. **The armed Comparator landmark is now due**:
     designated statements changed shape (`GoSpec`/`GoInvariant`
     redefinition, `InitialSplit` field removal) and grew by two — the
     judge run precedes the arc's merge ask (coordinator runs it).
  5. **Pre-merge audit response (2026-08-04).** Confirmed findings,
     fixed on the branch:
     - **`.normal` pin (MAJOR, claim strength).** Slice 4's
       `ProgressExec` left the completion outcome existential, silently
       accepting top-level `.returned`/`.broke`/`.continued` completions
       the old relation-Progress rejected (no relation rule steps from
       an unwound-`.stop` configuration — new lemmas
       `step_returning_stop_elim`/`step_breaking_stop_elim`/
       `step_continuing_stop_elim`, so `GoSpec … prog False` had become
       satisfiable for such programs). `ProgressExec`'s and
       `execStmtLoop_ok_or_fuelOut`'s success disjuncts are now
       `.ok (.normal …)`; every consumer compiled unchanged.
     - **TotalReadout terminal pin.** `allStreamsOk` deliberately
       certifies completion at ANY of the four terminals (`Terminates`
       stays the outcome-agnostic primitive), so "per-seed total
       correctness" needed the pin from elsewhere: new
       `TerminatesNormally` (= `Terminates` × `.normal`-pinned
       `ProgressExec` at the seeded frameless split,
       `terminatesNormally_of_progressExec` / `InitialSplit.noFrame`);
       the four `<pin>TotalReadout` statements are now
       `∃ N, ∀ fuel ≥ N, ∀ ch, ∃ σf ch', run = .ok (.normal σf, ch') ∧
       readout σf`.
     - **Reachability wording.** Three docstrings (incl.
       `goldenInvariant_statement`, inside the Challenge's trusted
       closure) still said "relation-reachable" where the statements
       quantify `ReachableExec`; fixed to the honest
       executable-reachability wording (`ReachableExec ⊆
       Steps`-reachable proven; converse owed). Stale "NOT PROVEN"
       honesty blocks for the unconditional twins updated to
       discharged-with-history.
     - **Designation.** The eight slice-5 headline deliverables (four
       `<pin>Terminates`, four `<pin>TotalReadout`) added to the
       designated list, Challenge/Solution, judge-config: 25 → 33; gate
       green (Iris-free, relation-free).

- **Owed-list addition (arc-final audit, 2026-08-04):** the unconditional
  ∀-config-instance twin (the `¬ GoSpec`-at-`12` form at the 3-voter
  encoding, `GoldenQuorumAll`'s readout seed) is now PAYABLE by the
  TotalPins recipe and deliberately deferred. Also recorded from the
  final audit: the slice-1 spike's "complete kernel-irreducible set is
  four families" verdict was WRONG as a completeness claim — the scan
  (WellFounded.fix/Acc.rec) structurally cannot see `partial`-class
  OPAQUE stubs, and the derived `BEq GoValue` was exactly that: logically
  `fun _ _ => default`, compiled as real structural equality — the
  differential-vs-logic divergence class at its purest, live at ONE
  semantic site (`renderPanicHead`'s recovered-collapse check). FIXED at
  the audit response: hand-written fuel-structural `GoValue.eqb`
  installed as THE `BEq GoValue` instance (the `Ty.eqb` recipe;
  compiled behavior identical, logical behavior now defined,
  kernel-reducible; differential re-certified). The promised post-side
  wf corollary also landed (`execStmt_preserves_wf`). Future scans for
  kernel-irreducibility must ALSO flag opaque constants.

## Exit criteria

- `Terminates` and the total-correctness form exist, with the user's
  assumed-termination form derivable as a special case.
- At least the summit family (`quorumOneKnown*`, `quorumThreeAll*`,
  `committedIndexAll*`, recover, golden) is total-correctness or has a
  recorded reason why not; unconditional negative twins proven for
  whatever the spike makes payable.
- Zero headline statements reference `Rel.*` modules; the statement-TCB
  gate enforces it; the relation (`Step`/`Steps`) is deletable-without-meaning-change, mechanically (constant-level gate; `Rel.lean` itself was deleted at the reshape).
- `scripts/ci` green throughout; differential 873/873 (plus new fuelOut
  cases); Comparator fresh-clone PASS on the upgraded Challenge.
- The spike's cost numbers and the tractability verdict are recorded here.

## Supersessions (the old framings, edited out in this commit)

| doc | old framing | new |
|---|---|---|
| AGENTS.md trust chain | "relational semantics (the proof authority)"; interpreter as the differentially-validated feeder | interpreter (`stepFn`/`execStmt`) is the semantic authority AND the statement language; relation is proof infrastructure proven equivalent |
| roadmap.md strategy | "proof-facing semantics should be relational, with the executable interpreter treated as a differential-testing implementation of that relation"; "keep the relation broader than the interpreter" | inverted: statements over the interpreter; relation tracks the interpreter exactly (two-sided step correspondence); implementation latitude lives in the `Choices` stream |
| CLAUDE.md audit dimension | "GoCore's machine and relation are the trust surface" | the interpreter is the trust surface; the relation is proof infra whose divergence from the interpreter is a proof-layer bug (still audited — but as correspondence, not as authority) |
| tcb-doctrine doc | deletion test named Iris only; statement ladder had a "relation-quantified" rung | deletion test covers Iris AND the relation; the relation-quantified rung is deprecated, eliminated by this arc |

Dated notes (2026-07-19/20/22 pipeline/end-state/invariant notes, BUGS.md
prose) retain the old framing as historical record of what we believed
then; they are superseded by this document and say nothing normative.
