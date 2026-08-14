# The Gallery Campaign — a long-cycle, high-autonomy sprint (2026-08-15)

Status: CHARTERED (user-directed). This is the `<file>` referenced by
the long-running-agency goal. **Everything in this document is
mandatory.** There are four goals, G1–G4; the campaign is DONE when the
conjunction below holds — nothing in it is optional, a stretch, or a
continuation. The experiment is in the *path*: judgment calls are the
agent's to make, inside the boundaries, resolved by the project's
recorded principles, with the material ones logged.

**EMERGENCY EXIT CONDITION.** The agent may declare an EMERGENCY EARLY
EXIT from the goal. This is ALWAYS permitted without question, no matter
the reason given. Exercise judgment: use it only when truly stuck —
spinning on a goal that cannot be completed, or facing a dire threat to
project success. On exit: leave the lane committed-clean, write a park
record in the campaign log (state, blocker, pickup plan), and report.

## DEFINITION OF DONE (all of the following, at the lane tip)

0. **G0 met**: the brick-wp review recorded and the named preemptive
   kit builds landed per G0's own checklist.
1. **G1 met**: `docs/verified-examples.md` has ≥ 20 COMPLETE entries.
2. **G2 met**: ≥ 3 of the named extensions E1–E4 landed, each
   guardrails-first, fail-closed, with ≥ 1 COMPLETE consuming entry.
3. **G3 met**: every item in the dossier register (fixed at campaign
   start) has an evidence dossier with a proposed disposition.
4. **G4 met**: all four named infrastructure-debt items cleared with
   their acceptance measures.
5. `scripts/ci` PASS with a FULL differential record at the tip;
   `scripts/render-gallery` exit 0.
6. The campaign log is complete (per-unit entries, checkpoint summaries
   at least every 5 units of work).
7. The arc-end protocol is INITIATED, not finished: the pre-merge audit
   ask prepared and POSED to the user (scope + scale proposal),
   designation candidates for new headlines listed, the merge request
   drafted. THE AUDIT SIGN-OFF AND THE MERGE ARE THE USER'S — never
   part of the goal.

## G0 — the opening kit phase (FIRST; user-directed 2026-08-15)

Review the brick-wp promotion wave (deps/brick-wp @ `52f8a6e`, commits
`944c555..52f8a6e` — READ-ONLY, trust-tools rule) and build the
forecastable-leverage kit PREEMPTIVELY. The consumer-driven rule is not
suspended — it is satisfied differently: at campaign start the
consumers are SCHEDULED (G1's enumerated candidate list), so every
preemptive lift must name its ≥ 2 chartered consumers, and its fixture
obligation is discharged by retrofitting ≥ 2 EXISTING examples where
the pattern already occurs (real consumers today). A lift with neither
landed nor chartered consumers stays forbidden.

G0 is done when:

1. **The review mapping is recorded** (a dated docs/ note): each
   promotion-wave pattern mapped to exists / build-now / not-applicable
   with reasons, in the slice-2 mapping's format.
2. **The named preemptive builds are landed**, each with chartered
   consumers listed + existing-consumer retrofits as fixtures:
   - **P5 setup-loop induction schema** (reopened: the ledger closed it
     "reopenable on the repeated-instantiation grind signal" — a
     13-example campaign IS that signal, in advance): the
     family-backing setup induction stated once, generically;
     chartered consumers = every array-setup candidate; retrofit ≥ 2
     shipped examples.
   - **MapMem promotion**: the WordCount map executable-fact family
     into a shared module (histogram + fibonacci-memo are chartered
     consumers; wordcount is a landed one — that is 3).
   - **Entry-equation macro completion**: retrofit the 5 remaining
     manual flat-state modules; extend to the program-generic shape
     via the recorded show-bridge (slice-2 record §3). 10 total
     consumers, all landed.
   - Judgment call for anything further the review surfaces, under the
     same chartered-consumer test.
   - **The rollback half of every lift** (the P6 pattern): after each
     lift, example-local copies it covers are DELETED or reduced to
     delegations in the same commit series — a lift is not done while
     its duplicates survive.
3. **The kit surface gains axiom pins** (the promotion wave's audit
   wiring, adapted): every public StepKit/SliceMem/MapMem/FuelMeasure
   lemma and the macro's emitted-theorem fixtures get `#print axioms`
   `#guard_msgs` pins in an Audit shard — the kit becomes an audited
   surface like the examples.
4. **The flagship rule is adopted** (discharged inside G1): the FIRST
   new G1 example is the kit's integration exercise — proven
   end-to-end using kit + macro only, no hand-rolled segment where a
   kit form exists; deviations recorded as kit gaps and fed back.

G0 measures: line/elaboration deltas per retrofit (the §12 standard),
recorded in the campaign log.

## G1 — the gallery grows to twenty

≥ 13 new COMPLETE entries (7 shipped + these ≥ 13 = ≥ 20). COMPLETE is
this checklist, every item machine-checkable:

1. `Corpus/coverage/exec/examples/<name>/main.go` — subject + harness
   (settled style triad; ghost rung 0 — no annotations, everything
   real Go) + `main`; `cases.tsv` rows incl. edge cases, all
   differentially green against the real oracle.
2. Golden pin + Program term + named harness `rfl` pin —
   `scripts/check-golden` green on both links. NOTE the standing gate
   rule: a new `*Program` module in Challenge's trusted closure costs
   one reviewable allowlist line + one import pin in `scripts/ci`
   (the 2026-08-15 audit fix made this deliberate; follow the
   existing seven-entry pattern exactly).
3. Headline theorem over the machine's native entry: termination +
   returned values only (∃N-∀fuel-∀ch); no heap/cell/seed vocabulary;
   axioms ≤ `[propext, Classical.choice, Quot.sound]`,
   `#guard_msgs`-pinned in the example's Audit shard.
4. Explicit fuel bound in the proof's witness, quoted in the gallery
   AS A BOUND (never a "measured law" — the 2026-08-15 audit precedent;
   record measured-vs-shipped separately when they differ).
5. Deletion test RUN (minimal-hypotheses or closure walk), not
   asserted.
6. Gallery entry per the audited honesty rules: full harness verbatim
   (render-gallery-pinned); claim never stronger than the theorem;
   domain bounds attributed (mathematics / Go's domain / the program's
   own arithmetic / machine idealization); input-family, bounded-cap,
   and ∃-witness family-determination disclosures where they apply.
7. `scripts/proof-costs`: no new module above ~2.5 GiB peak
   (program-generic discipline; long concrete runs are a retired
   class — E-form / conditioned-lemma shapes).
8. Full `scripts/ci` PASS at the commit (with `--diff` re-pin,
   same-commit with reason, whenever corpus changed).

Candidates (pick ≥ 13; substitution is a judgment call, recorded):
bubble sort · selection sort · two-sum · run-length encoding · binary
GCD (Stein) · exponentiation by squaring · palindrome check (array) ·
dedup adjacent · Kadane max-subarray · dot product · histogram (map) ·
sieve of Eratosthenes (bounded) · matrix multiply (fixed arrays) ·
stack via slice · queue via slice · fibonacci-memo (map).
Reserve (probe machine support first — guardrails doctrine): string
reverse · string palindrome · word frequency over a string · caesar
cipher · struct-heavy geometry examples.

An attempted example that resists may end as a RECORDED HONEST GAP
(guardrails landed if landable, precise blocker, pickup plan, log
entry). Gaps are legitimate outcomes of an attempt, but G1 counts only
COMPLETE entries — substitute from the lists and finish twenty.

## G2 — three extensions, pulled not pushed

≥ 3 of E1–E4, each built only when an example pulls it, guardrail
corpus cases committed BEFORE implementation, fail-closed remainder,
full differential at every step:

- **E1 — differential driver `--arg` past int64**: unlocks oracle rows
  in the uint64 wrap region; includes renaming the `harness-wrapping`
  row id with its re-pin.
- **E2 — `fmt` subset in the frontend** (≥ `fmt.Sprint` of integers /
  slices); unsupported remainder stays quarantined.
- **E3 — calls in short-circuit operands**: frontend normalization
  (hoisting), evaluation-order fidelity argued against the spec and
  pinned by corpus cases before landing.
- **E4 — string-construct coverage** as pulled by reserve-list
  examples; fail-closed remainder.

Frontend changes are trust surface: the standing discipline has no
autonomy exception.

## G3 — the evidence dossiers, all of them

At campaign start, enumerate THE DOSSIER REGISTER into the campaign
log: every sequential item in `docs/2026-08-11_latitude-inventory.md`
not yet enveloped or quotiented — the "unknown" class plus sequential
pins carrying re-envelope obligations. That register is then FIXED (the
denominator does not move), and G3 = a dossier for every item. Each
dossier, a dated docs/ file:

- Evidence per the doctrine's classes: spec text (quoted, cited); gc
  probes (programs + verbatim outputs committed under
  `docs/evidence/`); corpus / de-facto-spec observations;
  cross-implementation data where obtainable; proposal archaeology
  where relevant.
- A PROPOSED disposition — envelope (with argued width), pin with
  recorded obligation, or quotient candidate — with the argument, the
  counter-argument, and what evidence would change the answer.
- NO machine change, no baseline change beyond added probe evidence.
  Proposals are BATCHED FOR USER RULING — fidelity is the user's
  lever, absolutely.

The campaign log's dossier table (item → dossier → proposed
disposition) must be ready for a single user ruling session.

## G4 — infrastructure debt cleared

The four recorded post-merge follow-ups from
`docs/2026-08-15_phase2-premerge-audit.md`, each with its acceptance
measure:

1. **Shard import pruning** (audit C-H3): the copy-pasted Iris-heavy
   import headers pruned across the 25 example shards to what each
   uses. Measure: builds green; per-shard import lists minimal;
   scheduling-path improvement measured and recorded.
2. **Import-DAG repair** (C-H4, subsumes C-H5's structural half): the
   linear shard chains re-pointed to true dependencies (recorded
   targets: WordCount 14→~7 deep; the five no-dependency links; the
   roots' headline-reachability decision executed properly now that
   restructuring is in scope). Measure: builds green; chain depths
   recorded before/after; the "thin headline module" docstrings true.
3. **Re-privatization** (C-M1): the ~152 split-exposed declarations
   with zero cross-shard consumers returned to `private` (re-count
   first; keep what gained consumers since). Measure: builds green;
   public-surface count recorded before/after; C-M5's stale
   byte-identity docstrings corrected in the same pass.
4. **The comparator-judge worktree fix**: exactly the recorded
   one-line path-substitution defect (`f="${f//.//}"` substituting
   over the whole path). Constraint: the fix must change nothing else;
   demonstrate fail-closed behavior before AND working behavior after
   from a worktree; the trust tools themselves stay untouched. This is
   a gate edit — smallest possible diff, flagged prominently in the
   report for the arc-end audit's gate-honesty dimension.

## Judgment calls DELEGATED to the agent (the experiment)

Selection, substitution, and ordering across ALL FOUR goals
(interleaving is expected — dossiers are good work while a heavy build
runs); style choice per example within the triad; proof route and
segment layout; bound tightness (measured vs simpler honest witness —
record which); lift/promotion decisions per the active abstraction
loop (§12: ≥2 consumers, fixtures, measured deltas); when a G2
extension is pulled vs an example substituted; module/shard layout;
wall-clock tradeoffs. Resolve by the recorded principles — the
two-bounds doctrine, the harness ruling, fail-closed, guardrails-first,
honest-gaps-over-grinds. Where principles tension: **honesty beats
velocity beats elegance.** Record every material call in the campaign
log (one line: the call, the principle applied).

## HARD BOUNDARIES (never in scope; no judgment call reaches them)

- **No ghost rungs**: no annotation vocabulary of any kind (rungs 1/2
  are user-ruled deferrals).
- **No GoCore semantics changes**: a suspected machine bug or latitude
  question is RECORDED (corpus case if expressible + log entry + the
  example parked as a gap; G3 dossier if it is a latitude item) —
  never fixed autonomously.
- **No gate weakening, no re-pin laundering**: baselines re-pinned only
  for explained coverage changes, same-commit, with reason; new checks
  at speedbump standard (DO-NOT-HARDEN); G4.4 is the sole sanctioned
  gate edit and is constrained above; G1's per-example gate lines
  follow the existing pattern verbatim.
- **No merge, no push, no new designation**: done-state 7 prepares the
  asks; `main` is untouched. (Designation CANDIDATES are listed for
  the user; the designation itself, with its hoist-and-wire recipe and
  comparator landmark, is arc-end work under user sign-off.)
- **Trust tools and `deps/` are read-only** (G4.4's wrapper script is
  `scripts/`, not a trust tool; the tools it drives stay pristine).
- Worktree discipline (own lane only); memory-budget rules (capped
  builds, one heavy build at a time); the validation gate is NEVER
  skipped.

## Process

- Lane: `.claude/worktrees/gallery-campaign`, branch
  `gallery-campaign`. First action: `scripts/setup-deps --from
  /home/dev/projects/golean` (fresh worktrees bootstrap their own
  `deps/`; fail-closed without it).
- Campaign log: `docs/gallery-campaign-log.md` — per-unit entries
  (example / extension / dossier / debt item: status, judgment calls,
  findings, costs), checkpoint summaries at least every 5 units with
  honest totals per goal (complete / gap / remaining).
- Commit cadence: at minimum one commit per unit of work; the log
  updates in the same commit as the work it describes.
- Findings outside the four goals (fidelity gaps beyond the register,
  kit needs beyond §12's bar, envelope questions) are recorded as
  INPUTS in the log's findings section — the byproduct stream, not
  scope creep.
