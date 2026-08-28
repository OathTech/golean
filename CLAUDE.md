# CLAUDE.md — the working charter

This file is the charter: what we build, what is trusted, how proof
is done, and the gates. It is deliberately short; details live in
the pointed-to documents. Amend only when a practice proves its
worth or its cost.

## The stack and the plan of record (top of mind)

The plan of record is **`docs/2026-08-28_iris-corpus-plan.md`** —
the corpus-first Iris era ([USER]-approved 2026-08-28; it replaced
`docs/2026-08-27_clean-proof-plan.md`). The architecture:

```
executable GoCore       ← the TCB; statements live here; oracle-tested
  ⇧ adequacy (proofs travel down; statements stay first-order)
relational semantics    ← the per-step relation + language instance
  ⇧
Iris reasoning          ← heap RA, WP, FnSpec contracts, per-construct
                          rules, assertion layer, automation: THE BUILD
  ⇩ proves
target programs         ← the pattern corpus (canonical properties
                          incl. NEGATIVE TWINS); raft is the FINAL
                          corpus member, not the next milestone
```

The delivery unit is a corpus case closed cleanly THROUGH the WP
calculus. A proof that states WP but grinds machine spans underneath
— the VENEER — is a named forbidden pattern: tier-3 proofs reach the
machine only through the Laws/lifting/adequacy layer (the A-TRIP
gate enforces this mechanically — `scripts/wp-veneer-lint` + the
proof-closure check `scripts/WpVeneerClosure.lean` in `scripts/ci`,
scope `scripts/wp-lint-scope.txt`; cost profiles and negative twins
do not catch it, so the closure check is the tripwire).

## What we are building

A fast, careful Go-to-Lean verifier, demonstrated by verifying
etcd-io/raft (`docs/roadmap.md`) — reached corpus-first per the plan
of record above. Two products, strictly separated:

- **A trustworthy, portable Go semantics** — the weakest machine Go
  permits, all latitude included. Differential testing is the lower
  bound (observed ∈ modeled); spec/docs/corpus argue the upper.
  Doctrine: `docs/2026-08-11_essence-of-go-doctrine.md`; latitude
  census: `docs/2026-08-11_latitude-inventory.md`.
- **A reusable, agent-operable reasoning stack** over that
  semantics: Hoare-style specs, symbolic execution, frames, loop
  rules — general machinery with target instances, never the
  reverse. Index: `docs/2026-08-26_mechanism-registry.md`.

Every verification result ships in one shape: **a theorem about a
concrete harness (or a parameterized family of harnesses)** —
`∀ ch (fuel), the interpreter runs the pinned program to a result
satisfying its spec` — proved by reasoning, with the program
entering only through reflection.

## The trusted surface (and nothing else)

1. The interpreter (`GoLean/GoCore/` — `stepFn` and its drivers),
   validated by the differential corpus against `go run`.
2. The reflection pair: `goldenWire%` (on-disk program → Lean term
   via the same fail-closed decoder every run uses) + shape pins
   (kernel certificates that proof-mentioned syntax = the pinned
   term). `scripts/check-golden` ties bytes to source.
3. The designated harness sentences (first-order over the
   interpreter; the statement-TCB gate enforces their closure) and
   the audit/judge apparatus. The EXTERNAL trust tools (comparator,
   lean4export, landrun) are never modified — version pins are
   chosen with the user; our own apparatus (`Audit.lean`,
   Challenge/Solution, the wrapper scripts) evolves only under the
   gates, with trust-adjacent edits delta-flagged.

Everything else — judgments, specs, invariants, symbolic
evaluators, quotients, accelerators — is untrusted machinery,
verified against the semantics, useful-not-complete, replaceable.

## Proof doctrine

- **Bounded techniques are not proof.** Enumeration, fixed vectors,
  unrolling, fixture-anchored statements: totally forbidden as
  proof technique — they do not generalize. A statement anchored to
  a SUBJECT RUN — a measured span length, a censused prefix, a
  fixture identity, an enumerated case list over states — is scaffolding at best, labeled so at birth,
  never cited by — or composed into — a proof. (Not banned: shape constants of the
  frontend's fixed desugars in ∀-quantified rules, and bounds that
  appear in the reflected program text itself.)
  The subject's identity enters only via the reflection pair.
  (The 2026-08 fixed-trajectory era is the recorded cautionary
  instance: `docs/ARCHIVE.md`.)
- **Reason; never dumbly walk the execution.** Proofs are
  Hoare/O'Hearn-style: function specs (continuation-parametric,
  call-span shaped), loop rules with invariants (variants for
  totality), frame and congruence rules. Symbolic execution —
  execution over symbolic paths, covering a state family per step —
  is a first-class valid technique and the working engine; what is
  banned is CONCRETE walking as proof (grinding one literal state
  down one trajectory). Nondeterminism is the reified choice tape,
  quantified demonically. Concrete evaluation appears only in
  declared reflection certificates, in the discharge of ∃-shaped
  statements (exhibiting a run is how existentials are proved), and
  — until superseded — the retained interface witnesses. In the
  Iris era this includes the VENEER ban (the stack section above):
  a WP-stated theorem whose proof term reaches the machine outside
  the Laws/lifting/adequacy layer is concrete walking in costume.
- **The quantifier audit.** Before work starts, write down the end
  theorem's quantifiers (∀ streams, ∀ states, ∀ iterations, ∃ fuel,
  …) and, for each, the RULE that discharges it — a loop rule, a
  congruence, a spec, a case analysis over an invariant-constrained
  set. Every unit charter opens with its line of this table: which
  quantifier it advances, by what rule. "By instances" is never an
  answer — no volume of proved instances discharges a ∀ (the
  2026-08 enumeration mistake: weeks of green units advancing no
  quantifier). A unit that cannot name its rule is scaffolding
  before it starts, and must be labeled so.
- **Classics first, with lineage.** Before building a proof
  mechanism, identify the literature ancestor it instantiates —
  separation logic and frames, simulation/refinement, symbolic
  execution, loop invariants and variants, certificate replay,
  computational reflection — and write a LINEAGE line in its design
  note naming the classic and where the construction diverges. Why:
  a classic arrives with obligation shapes the community has
  stress-tested for decades; a novel trick repeats that evolution
  at our expense, with failure modes discovered late. When two
  classics compete, measurement referees (a probe each, compare).
  A mechanism that maps to no classic is suspicious and takes extra
  scrutiny — a named reason, a design review — before shipping.
- **The middle path.** The build-decision test is two-axis: COST ×
  CONSUMER COUNT. Cheap and disposable → a concrete slice is
  correct; expensive OR repeatedly consumed → the general form is
  mandatory. "Demonstrated demand" means an existing second
  consumer (the promotion ledger's ≥2 rule: when a pattern bites
  twice, lift it) or a MEASURED fragility/cost — never a
  hypothetical future user. Speculative interfaces are as banned as
  grind: an interface with one inhabitant is a chain in costume,
  and every interface carries a named vacuity check (≥2 genuinely
  different instances). Deletion bias: nothing is kept because
  tests are green; scaffolding carries a retirement condition or a
  deletion date.
- **Proof-facing code is total.** No `partial`, no `sorry`, no
  `native_decide` in the semantic core or the reasoning layer;
  structural/well-founded recursion so the proof direction stays
  reachable. The in-build Audit gate enforces the axiom envelope.
- **Fail closed, always.** Unknown wire node, unsupported feature,
  unclassified case, exhausted budget → an explicit refusal that
  NAMES ITS CAUSE at the point of failure (the sealed-payload
  pattern: semantically False, payload identifies the site), never
  a silent default, never an absorbing fallback. Refusals are
  load-bearing signals: an `unsupported`/`stuck`/refused outcome
  never counts as a pass, a gate that cannot run FAILS rather than
  skips, and partial machinery advertises its boundary (coverage
  grown consume-on-demand, each extension proved on admission).
  The smell of fail-open is a default that makes an error
  disappear; a visible red beats a hidden wrong answer.

## The gates

- `scripts/ci` before any commit that touches runtime code —
  always via `scripts/capped` (cgroup-capped; never bare lake/lean;
  see `docs/operational-lessons.md` for the measured build
  discipline: warm/threads/build-lock). Runtime changes add the
  differential (`--diff`); baseline re-pins only with a full run
  and a written reason.
- `scripts/comparator-judge` at landmarks: designated-statement
  changes, trusted-closure movement, or a ci staleness/scope note.
- The pre-merge adversarial audit: the ask is unconditional; scope
  and waiver are the user's. Reviewers Opus, workers Fable.

## The merge protocol (exact, every time)

1. All work on branches off `main`, in worktrees
   (`.claude/worktrees/<lane>`, one writer per worktree; primary
   checkout parked on `main`).
2. Arc complete → gate green (+ judge if triggered).
3. The audit ask — never skipped; the user may trim or waive.
4. Pause; merge only on explicit at-that-moment sign-off.
5. `git checkout main && git merge --ff-only <branch>` (if refused:
   rebase or sanctioned main-merge-into-branch, re-gate, re-ask).
6. End parked on `main`, clean, green. Push is a separate sign-off.

## Working practices

- Capture decisions in tracked files, not chat; [AGENT]/[USER]
  provenance on every logged decision; snapshot refs before risky
  git ops; honest reporting (failures with output, bounds as
  bounds, numbers derivation-anchored).
- Autonomous arcs: judgment delegated inside written boundaries; no
  gate weakening, no trust-surface changes, no merge/push/
  designation; branch-complete + audit-ask posed is the end state.
  **Named design gates are HARD STOPS**: no autonomous directive,
  goal monitor, or completion pressure overrides one — a run that
  cannot stop EXITS (the emergency path) rather than
  self-adjudicating the gate; a self-adjudicated gate is a protocol
  breach even when its substance survives review. A design gate's
  review object includes the FIRST IMPLEMENTATION built against the
  design, not the note alone. Autonomous-goal prompts enumerate the
  named gates up front so a stop-at-gate reads as goal-compliant.
  (The 2026-08 instance and rationale:
  `docs/2026-08-28_w25-gate-postmortem.md`.)
- Reference checkouts in gitignored `deps/` (goose, perennial,
  iris-lean, raft, verdi(+raft), BRiCk, refinedc, brick-wp, …) —
  consult before inventing.

## Pointers

Plan of record: `docs/2026-08-28_iris-corpus-plan.md` (superseded
predecessors, banners in place: `docs/2026-08-27_clean-proof-plan.md`)
· The triage that opened this era: `docs/2026-08-27_triage-plan.md` ·
Proof structure (pre-pivot, still the seam reference):
`docs/2026-08-27_proof-structure-explained.md` · The archives of the
killed eras: `docs/ARCHIVE.md` (+ branches
`archive/fixed-trajectory-era`, `archive/callspec-era`) · The W2.5
gate post-mortem: `docs/2026-08-28_w25-gate-postmortem.md` ·
Mechanism index: `docs/2026-08-26_mechanism-registry.md` ·
Operational lessons (build/OOM/tool incidents, measured remedies):
`docs/operational-lessons.md` · Architecture rules: `AGENTS.md` ·
Constitution (campaign governance):
`docs/2026-08-21_raft-proof-constitution.md`.
