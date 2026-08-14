# The Gallery Campaign — tiers for a long-running autonomous build-out (2026-08-15)

Status: DRAFT for user review — the `<file>` referenced by the
long-running-agency goal. Commits with the campaign kickoff.

This is an experiment in long-cycle autonomy (user-directed,
2026-08-14): the success state is deliberately UNAMBIGUOUS — counted,
mechanically checkable — while the path there is deliberately open: the
agent makes its own judgment calls inside the boundaries below, resolves
them by the project's recorded principles, and records the material
ones. Do not stop or set aside the work until Tiers 1 & 2 are COMPLETE
as defined here.

**EMERGENCY EXIT CONDITION.** The agent may declare an EMERGENCY EARLY
EXIT from the goal. This is ALWAYS permitted without question, no matter
the reason given. Exercise judgment: use it only when truly stuck —
spinning on a goal that cannot be completed, or facing a dire threat to
project success. On exit: leave the lane committed-clean, write a park
record in the campaign log (state, blocker, pickup plan), and report.

## Success state (the unambiguous part)

**Tier 1 is COMPLETE when all of the following hold at the lane tip:**
- `docs/verified-examples.md` contains **≥ 20 COMPLETE entries**
  (the 7 shipped + ≥ 13 new), where COMPLETE is the per-example
  checklist below — recorded honest gaps do NOT count toward the 13;
  substitute from the reserve list instead.
- `scripts/ci` PASS **with a FULL differential record at the tip**
  (`baseline diff FULL, no regression`).
- `scripts/render-gallery` exit 0.
- The campaign log (`docs/gallery-campaign-log.md`) has one entry per
  attempted example (complete or gap) and a checkpoint summary at least
  every 5 examples.

**Tier 2 is COMPLETE when additionally:**
- **≥ 3 of the named extensions (E1–E4)** are landed, each with (a) its
  guardrail corpus cases committed BEFORE the implementation, (b)
  fail-closed boundaries for everything not implemented, and (c) at
  least one COMPLETE gallery example that consumes it.
- Same gate conditions as Tier 1 at the final tip.

**The end state of the whole goal** is the lane branch complete as
above, plus the arc-end protocol INITIATED, not finished: the audit ask
prepared and posed to the user (scope + scale proposal), designation
candidates listed, and the merge request drafted. THE MERGE ITSELF AND
THE AUDIT SIGN-OFF ARE THE USER'S — the goal never includes them.

**Tier 3 (below) is a continuation mandate, not part of the completion
bar**: with Tiers 1 & 2 complete and the session still running, proceed
into Tier 3 dossier work without further instruction.

## The per-example COMPLETE checklist (every item machine-checkable)

1. `Corpus/coverage/exec/examples/<name>/main.go` — subject + harness
   (settled style triad, §11/§11a-era rulings) + `main`, ordinary
   compilable Go, ghost rung 0 (no annotations); `cases.tsv` rows
   including edge cases, all differentially green via the real oracle.
2. Golden pin (`baselines/golden/<name>-lowered.repr`), Program term
   (`…/Examples/<Name>Program.lean`), named harness `rfl` pin —
   `scripts/check-golden` green on both links.
3. Headline theorem over `runFunctionWithContextM` (or `runProgramM`):
   termination + returned values only (∃N-∀fuel-∀ch); NO heap/cell/seed
   vocabulary in the statement; axioms at most
   `[propext, Classical.choice, Quot.sound]`, `#guard_msgs`-pinned in
   the example's Audit shard.
4. Explicit fuel bound in the proof's witness, quoted in the gallery.
5. Deletion test RUN (minimal-hypotheses or closure walk), not asserted.
6. Gallery entry per the audited honesty rules: full harness verbatim
   (render-gallery-pinned), claim never stronger than the theorem,
   domain bounds attributed (mathematics / Go's domain / program's own
   arithmetic / machine idealization), input-family and bounded-cap
   disclosures, machine-idealization clause.
7. `scripts/proof-costs`: no new module above ~2.5 GiB peak (the
   program-generic discipline — long concrete runs are a retired class;
   use the E-form / conditioned-lemma shapes).
8. Full `scripts/ci` PASS at the commit (with `--diff` re-pin,
   same-commit with reason, whenever corpus changed).

An attempted example that resists may end as a **RECORDED HONEST GAP**:
green guardrails if landable, the precise blocker, a pickup plan, a log
entry. Gaps are legitimate outcomes but do not count toward the totals.

## Tier 1 — candidate list (pick 13+; substitution is a judgment call)

Primary: bubble sort · selection sort · two-sum · run-length encoding ·
binary GCD (Stein) · exponentiation by squaring · palindrome check
(array) · dedup adjacent · Kadane max-subarray · dot product ·
histogram (map) · sieve of Eratosthenes (bounded) · matrix multiply
(fixed arrays) · stack via slice (push/pop/peek) · queue via slice ·
fibonacci-memo (map).

Reserve (probe support first — guardrails doctrine; substitute freely,
record why): string reverse · string palindrome · word frequency over a
string · caesar cipher · struct-heavy examples (point/rect geometry).

Rules of thumb: probe machine support with a corpus case BEFORE
investing in proofs (a case the machine can't run must classify
visibly frontend/feature-blocked, never false-pass); prefer breadth of
Go-construct coverage over algorithmic novelty; every example should
teach either a Go boundary (domain conditions) or a kit gap (lifts).

## Tier 2 — the named extensions (each pulled BY an example, never built
speculatively)

- **E1 — differential driver `--arg` past int64**: unlocks oracle rows
  in the uint64 wrap region; includes properly renaming the
  `harness-wrapping` row id with its re-pin. (Recorded audit input.)
- **E2 — `fmt` subset in the frontend** (at minimum `fmt.Sprint` of
  integers/slices): currently fail-closed quarantined; guardrails
  first; keep the unsupported remainder fail-closed.
- **E3 — short-circuit operand calls**: frontend normalization
  (hoisting) for calls in `&&`/`||` operands, currently quarantined;
  evaluation-order fidelity argued against the spec and pinned by
  corpus cases before landing.
- **E4 — string-construct coverage** as pulled by reserve-list
  examples (indexing, iteration, comparison — whatever the example
  needs, fail-closed remainder).

Frontend changes are trust surface: guardrail cases first, fail-closed
always, full differential at every step — the standing discipline, no
exceptions under autonomy.

## Tier 3 — the width-arc evidence dossiers (CONTINUATION tier)

Tier 3 is NOT required for goal completion — the completion bar is
Tiers 1 & 2. It is the SANCTIONED CONTINUATION: if Tiers 1 & 2 are
complete and the session continues, proceed directly into Tier 3
without waiting for instruction. It exists so the runner never idles
and so the sequential-width arc (its charter:
`docs/2026-08-12_sequential-width-arc-charter.md`) starts with its
decisions pre-researched.

**The unit: one EVIDENCE DOSSIER per sequential latitude-inventory item
not yet enveloped or quotiented** (enumerate from
`docs/2026-08-11_latitude-inventory.md` at campaign start — the
"unknown" class plus sequential pins carrying re-envelope obligations;
list them in the campaign log so the denominator is fixed). Each
dossier, as a dated docs/ file:
- Evidence per the doctrine's classes: spec text (quoted, cited),
  gc probes (programs + verbatim outputs, committed under
  `docs/evidence/`), corpus/de-facto-spec observations,
  cross-implementation data where obtainable, proposal archaeology
  where relevant.
- A PROPOSED disposition — envelope (with the argued width), pin with
  recorded obligation, or quotient candidate — with the argument, the
  counter-argument, and what evidence would change the answer.
- NO machine change, no corpus-baseline change beyond added probe
  evidence. The proposals are BATCHED FOR USER RULING — that boundary
  is absolute (fidelity is the user's lever).

**Tier 3 completeness** (for the record, not for goal completion):
every enumerated item has a dossier; the campaign log's Tier-3 table
maps item → dossier → proposed disposition, ready for a single user
ruling session.

## Judgment calls DELEGATED to the agent (the experiment)

Selection, substitution, and ordering of examples; style choice per
example within the triad; proof route and segment layout; bound
tightness (measured vs simpler honest witness — record which);
lift/promotion decisions per the active abstraction loop (§12:
≥2 consumers, fixtures, measured deltas); when Tier 2 extensions are
pulled vs an example substituted; module/shard layout; wall-clock
tradeoffs. Resolve by the recorded principles — the doctrine
(two bounds), the harness ruling, fail-closed, guardrails-first,
honest-gaps-over-grinds. Where principles tension: **honesty beats
velocity beats elegance.** Record every material call in the campaign
log (one line each: the call, the principle applied).

## HARD BOUNDARIES (never in scope; no judgment call reaches them)

- **No ghost rungs**: no annotation vocabulary of any kind (rung 1/2
  are user-ruled deferrals).
- **No GoCore semantics changes**: a suspected machine bug or latitude
  question is RECORDED (corpus case if expressible + log entry + the
  example parked as a gap) — never fixed autonomously. Fidelity is the
  user's lever.
- **No gate weakening, no re-pin laundering**: baselines re-pinned only
  for explained coverage changes, same-commit, with reason; new checks
  at speedbump standard only (DO-NOT-HARDEN).
- **No merge, no push, no designation**: the goal ends at
  branch-complete + prepared arc-end asks. `main` is untouched.
- **Trust tools and `deps/` are read-only.** Worktree discipline holds
  (own lane only); memory-budget rules hold (capped builds, one heavy
  build at a time).
- The validation gate is NEVER skipped: every commit that touches
  runtime/corpus follows the CLAUDE.md gate, including the focused
  differential and baseline diff.

## Process

- Lane: a fresh worktree/branch off merged `main` (opened at kickoff,
  after the phase-2 arc lands — the campaign builds on the swapped
  spec styles and the scaling infrastructure).
- Campaign log: `docs/gallery-campaign-log.md` — per-example entries
  (status, judgment calls, findings, costs), checkpoint summaries every
  5 examples with honest totals (complete / gap / remaining).
- Commit cadence: at minimum one commit per example (guardrails and
  proofs may be separate coherent commits); log updated in the same
  commit as the work it describes.
- Findings that belong to other levers (fidelity gaps, envelope
  questions, kit needs beyond §12's bar) are recorded as INPUTS in the
  log's findings section — the campaign's byproduct stream, not its
  scope.
