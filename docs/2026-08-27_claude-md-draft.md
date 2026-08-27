# DRAFT: CLAUDE.md v2 — the working charter (for [USER] sign-off)

Replaces the accreted CLAUDE.md at the W0 landing. Incident
narratives move to `docs/operational-lessons.md` (created in the
same commit, content lifted verbatim from today's CLAUDE.md).
Everything below IS the proposed file content.

---

# CLAUDE.md — the working charter

This file is the charter: what we build, what is trusted, how proof
is done, and the gates. It is deliberately short; details live in
the pointed-to documents. Amend only when a practice proves its
worth or its cost.

## What we are building

A fast, careful Go-to-Lean verifier, demonstrated by verifying
etcd-io/raft (`docs/roadmap.md`; the campaign plan of record is
`docs/2026-08-27_clean-proof-plan.md`). Two products, strictly
separated:

- **A trustworthy, portable Go semantics** — the weakest machine Go
  permits, all latitude included. Differential testing is the lower
  bound (observed ∈ modeled); spec/docs/corpus argue the upper.
  Doctrine: `docs/2026-08-11_essence-of-go-doctrine.md`; latitude
  census: `docs/2026-08-11_latitude-inventory.md`.
- **A reusable, agent-operable reasoning stack** over that
  semantics: Hoare-style specs, symbolic execution, frames, loop
  rules — general machinery with target instances, never the
  reverse. Index: `docs/mechanism-registry.md`.

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
  fixture identity — is scaffolding at best, labeled so at birth,
  never cited by a proof. (Not banned: shape constants of the
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
  — until superseded — the retained interface witnesses.
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
- Reference checkouts in gitignored `deps/` (goose, perennial,
  iris-lean, raft, verdi(+raft), BRiCk, refinedc, brick-wp, …) —
  consult before inventing.

## Pointers

Plan of record: `docs/2026-08-27_clean-proof-plan.md` · Proof
structure: `docs/2026-08-27_proof-structure-explained.md` · The
archive of the killed era: `docs/ARCHIVE.md` · Mechanism index:
`docs/mechanism-registry.md` · Operational lessons (build/OOM/tool
incidents, measured remedies): `docs/operational-lessons.md` ·
Constitution (campaign governance): 
`docs/2026-08-21_raft-proof-constitution.md`.
