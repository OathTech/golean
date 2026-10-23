# CLAUDE.md — the working charter

`AGENTS.md` is a git-tracked symlink alias of this file so that agents
looking for `AGENTS.md` find the working charter; edit `CLAUDE.md` only —
the architecture rules formerly in `AGENTS.md` are
`docs/architecture-rules.md`. ([USER] 2026-09-07, relayed; the alias
shape is checked by `scripts/check-agents-alias`, a `scripts/ci` speedbump.)

This file is the charter: what we build, what is trusted, and the
gates. It is deliberately short; details live in the pointed-to
documents. Amend only when a practice proves its worth or its cost.

## What this repo is (top of mind)

**The GoLean semantics: a trustworthy, portable, executable Go
semantics, validated by differential testing.** One product, one
claim.

Since the repo split (2026-08-31, [USER]-directed —
`docs/2026-08-31_repo-split-plan.md`), the Iris proof layer (the
designated theorem set, the judge/audit apparatus, program proofs)
is NOT here: the parked era is on branch `park/reasoning-2026-08-31`,
and the live program logic is the separate repository
`golean-logic` (a sibling checkout), which consumes this one at a pinned
commit. This repo makes
NO verification claims about Go programs.

The boundary, ruled 2026-09-05 ([USER], Mike, verbatim, relayed by
the [AGENT] coordinator — cite as relayed; review F10, `docs/
2026-09-05_master-plan.md` §7.5): «I agree btw, that it makes sense
for the relational semantics to live in this repo. In the case of
cerberus-lean, we didn't do this because cerberus is fixed (we are
just porting it) and the relational semantics is downstream. But
here we are co-designing the semantics to support both execution
and proof. So we should build both in this repo, with a thin enough
customer layer that we can feel confident we are building the right
thing». SUPERSEDED 2026-10-20 ([USER] ruling, relayed by the [AGENT]
coordinator): the relational layer is retired from the build — tag
`relational/last-main-2026-10-20` is the last main carrying it, `docs/ARCHIVE.md`
has the archive entry — so the statement above no longer governs and the
consequence that followed it (next sentence, kept as written) no longer
holds. So: the semantic transition relation, its observations, the
invariants stating its domain, and the executable↔relation coherence
proofs LIVE HERE, co-designed with the executable core (the merge
invariant in `docs/architecture-rules.md`). Iris resources, WP rules,
program proofs, tactics, and consumer ghost state are the customer's,
downstream. A thin customer adapter (an iris-lean `Language` instance
+ toy facts) may be built in-repo as a SPIKE, outside the default
build and the gate's dependency graph, to validate the interface.

Top-level goal ([USER], Mike, verbatim, relayed by the [AGENT]
coordinator — cite as relayed), 2026-09-11: «Our job is to make the Go
seantics as good as we can make it. […] We *can* provide a relational
definition along with it too» (`docs/2026-09-11_review-dispositions.md`);
2026-09-22: «Our ultimate aim here is to support the GoLean logic that
we're building in a different repo. That's our upstream customer.»
The customer's review shaped the current plan
(`docs/2026-09-23_batched-window-charter.md`).

**What this repo provides, and does not** ([USER], Mike, 2026-09-16,
verbatim, relayed; the qualifications are [AGENT], ratified by the
[USER] the same day): «(1) we provide a Go semantics defined via the core
GoCore language, (2) we ship a relational, i.e fuel-free semantics
which is provably equivalent to the operational semantics, (3) we DO
NOT ship any higher level reasoning. The aim is for the relational
semantics to be useful for reasoning but this isn't something we
ourselves supply». Qualifications: (1) includes the native lowering
Go → GoCore, differentially validated and carrying NO correctness
theorem — a consumer of a GoCore program inherits that trust
assumption and the wire's provenance record. (2) is WITHDRAWN by the
[USER] ruling of 2026-10-20 (relayed): the relational semantics and its
coherence proofs — the per-step soundness/completeness, the pool half
(`StepML`), the pinned statement set `BridgeSet`, the setup/multi
soundness modules — are retired from the build; the last main carrying
them is tag `relational/last-main-2026-10-20`, the archive entry is
`docs/ARCHIVE.md`. What stays on main as a supported surface for the
raft-proofs customer (owner input, 2026-10-20, relayed): `Prefix`/`Finish`
(`GoLean/GoCore/ExecutionStatement.lean`, proofs in `Prefix.lean` — the
counted, choice-threaded prefix closure over `stepFn`, the finishing
classification with its five endings, the fuel bridges, choice replay by
record, the refusal-separate classification; the domain premise
`NoRefusal` covers the sequential driver only and a refusal has no
successor: a partial-correctness boundary, wording [USER]-approved
2026-09-28 (D2), relayed) and the `@[stepFn_eqns]` equation library
(`Equations.lean`, `EquationsAttr.lean`: one proved lemma per `stepFn`
arm, kept usable by `scripts/check-equations`'s client check), with
their support closure `StepFnFacts.lean` (the kept part of
`MachineSound.lean`, unchanged), and — fix round F1, 2026-10-21, pending the
owner's ruling — the relation-free single-goroutine pool bridge and
projections (`PoolFacts.lean`, `PoolProjection.lean`: `execProgLoop_single`,
`single_embedding`, `program_run_iff`, `observation_iff`, …), stated over the
executable driver only. No relation, no coherence theorem and no
relation-level pool statement is in the build; setup is a premise (its
no-globals, no-initializer case is the equation `runProgramSetup_noInit`)
and init-time printing is refused. (3):
the typed-admission profile family, the `GoLean/Interface.lean`
facade and the adapter spikes were PARKED 2026-09-16 ([USER] ruling;
tag `typed-profiles/last-main-2026-09-16`,
`docs/2026-09-16_typed-profiles-parked.md`), revivable from that tag
by the logic repository (`golean-logic`), which consumes
this repo at a pin. A consumer also inherits the Platform instance (gc, linux/amd64
— portability is a separate contract, latitude inventory §11) and the
machine's concurrency granularity (the reduction to Go's access
granularity is an explicit open obligation, not a theorem). This
paragraph replaced the 2026-09-04 consumer-interface pointer with
[USER] approval 2026-09-16.

- The semantics is **the weakest machine Go permits, all latitude
  included**. Differential testing is the lower bound (observed ∈
  modeled); spec/docs/corpus argue the upper. Doctrine:
  `docs/2026-08-11_essence-of-go-doctrine.md`; latitude census:
  `docs/2026-08-11_latitude-inventory.md`; spec pins:
  `docs/spec-sources.md`.
- The fixture corpus (`Corpus/`, incl. the imported-goose cases)
  plus the top-level raft subject/harness (`raftsubject/`,
  `raftharness/`) is the test suite for the semantics — every
  fixture is a differential test case first; the raft subject's
  lowering is pinned by `scripts/check-frontend-pins`.
- No Prop-level relation is part of the product: the relational layer
  was retired 2026-10-20 ([USER] ruling, above; tag
  `relational/last-main-2026-10-20`), and with it the merge invariant
  (`docs/architecture-rules.md`, retired there). `Prefix`/`Finish` and
  the `stepFn_eqns` library stay for the raft-proofs customer.

## The trusted surface (and nothing else)

1. The interpreter (`GoLean/GoCore/` — `stepFn` and its drivers)
   and the native frontend lowering (`tools/nativefrontend` +
   `GoLean/NativeToIR.lean`), validated by the differential corpus
   against `go run`; what the kernel accepted rests on the Lean
   toolchain pinned in `lean-toolchain` (the Go oracle pin's
   counterpart), whose kernel the gate's replay runs.
2. The differential apparatus: the coverage runners, the tracked
   baselines (`baselines/`) and the scripts that derive and compare
   them (`scripts/coverage-baseline-diff`, `scripts/coverage-cause` with
   its tables `tools/lowerdiag/causes.tsv` and `scripts/machine-causes.tsv`),
   the oracle pin (go1.26.5 exactly), and the re-pin guards (incl.
   `scripts/check-alternation-survival`, `scripts/check-cause-regressions`,
   `scripts/check-row-removals`). The oracle toolchain is never floated; pin
   moves are deliberate, with a full run and a written reason.

Everything else is untrusted tooling.

## Doctrine

- **The semantic core is total.** No `sorry`, no `native_decide`,
  no axioms anywhere in `GoLean/`; no `partial` in the semantic
  core `GoLean/GoCore/` — structural/well-founded recursion so the
  `Prefix`/equation proofs here and the customer's proofs downstream
  stay reachable. (Six files outside the core use `partial` for JSON,
  wire and search descent — 35 `partial def`s: the wire decoder
  `NativeToIR.lean` 17, `CLI.lean` 7, `StrictJsonParse.lean` 5,
  `ChoiceTrace.lean` 4, `NativeDeclaration.lean` 1, `EnumDedup.lean`
  1, as of 2026-10-12. The in-build Audit sweep left with the proofs
  package; the ci escape-hatch scans are the standing check here.)
- **Fail closed, always.** Unknown wire node, unsupported feature,
  unclassified case, exhausted budget → an explicit refusal that
  NAMES ITS CAUSE at the point of failure, never a silent default,
  never an absorbing fallback. Refusals are load-bearing signals:
  an `unsupported`/`stuck` outcome never counts as a pass, a gate
  that cannot run FAILS rather than skips. A visible red beats a
  hidden wrong answer.
- **No semantic choice hides in evaluator recursion.** Latitude Go
  permits is reified (the choice tape), not baked in; frontend
  concerns stay in the lowering and fail closed
  (`docs/architecture-rules.md` has the architecture rules).
- **Honest measurement.** Differential results are reported with
  their scope (full vs. partial, cached vs. re-certified); bounds
  as bounds; numbers derivation-anchored.

## The gates

- **Gates block.** `scripts/ci` before any commit that touches runtime
  code: the oracle pin, the escape-hatch scan, the `lake build` of every
  target (warning-free), the kernel replay of the built `GoLean` oleans
  (`scripts/check-kernel-replay`: the toolchain's `leanchecker` replays each
  module's declarations through the kernel into a fresh environment of its
  imports), the core totality audit, the eval tests, the
  frontend and harness `go test`s, the unseq-wire, wire-boundary,
  method-identity, frontend-pin, declaration and equation checks, and the
  baseline diff of the last recorded corpus runs with the forward re-pin
  guard. `scripts/ci --diff` before any merge to `main`: the same plus a
  FRESH run of the differential corpus and of the negative corpus (gc
  rejects each program AND the native frontend refuses it as a rejection:
  type-check, parse or file selection) against the tracked baselines
  (`baselines/`; the differential baseline pins each FAIL row's refusal
  cause, and a re-pin that moves a cause into a crash/non-verdict key or
  removes a row needs a `BUGS.md` Cases: line or a `# removed:` header
  line), every row, no cached tier, plus the unseq
  scheduler's whole-tape-space check. Every heavy step runs through
  `cap` (`scripts/cap.sh`): the box tool `capped` when it is on PATH, sized
  by `CAPPED_MEM_MAX` (default 32G; a COLD full build is the measured
  `CAPPED_MEM_MAX=64G scripts/ci` case), the bare command where it is
  absent — the cap is box tooling, detected at run time, never shipped
  ([USER] 2026-10-21, release-readiness row 46; `docs/operational-lessons.md`). Baseline
  re-pins only with a full run and a written reason; PASS→non-PASS flips
  must be on a `BUGS.md` Cases: line.
- **Speedbumps report.** The same run prints the consistency checks (bugs
  index, feature tags, spec anchors, stdlib register, the
  `AGENTS.md` alias, imported-goose verbatim, memory call sites; under
  `--diff` also the derived-artifact regeneration and `lake check`
  (`scripts/check-lake-check`, about four minutes: the toolchain's build +
  export + kernel replay + non-standard-axiom refusal over the default
  targets, which are the main-free libraries `GoLean`, `TestsData`,
  `AdmissionTests`, `GoCoreAuditTests` — the executables and the
  `main`-bearing test libraries are built by name, [USER] 2026-10-21,
  backlog row 42; sandboxed where `bwrap` can start,
  `--inadvisably-no-sandbox` where it cannot, saying which) and `lake
  comparator` (`scripts/check-comparator`, about 20 s: the 349 statements
  of the surface kept on main for the raft-proofs customer — every theorem
  of `Equations.lean`, the G11 family, the `Prefix`/`Finish` laws, the
  output-fold bridge, `enterFrame_declared`, the `Choices.consumeAt*` laws
  — FROZEN as text in `Contract/Challenge.lean`, judged against GoLean's
  own theorems through the generated aliases of
  `GoLean/Contract/Solution.lean` per `comparator.json`: Lake's judge
  compares the two exports' statements syntactically, requires standard
  axioms only and replays the solution through the kernel, so an edit to
  a kept theorem's statement is a mismatch naming the theorem, never a
  text diff. In-repo the frozen text is re-elaborated against the LIVE
  definitions, so a drift that enters through a definition's signature is
  caught only across a pin, by the consumer's `--challenge-from-export`
  route; the challenge is updated deliberately with a changelog row;
  [USER] 2026-10-23, backlog row 43; the same sandbox detection)) under
  their own heading. A red one never fails the
  gate; it is read at the merge ask and fixed or waived there, by name.
  The owner's `lake check` and `lake comparator` outside the sandbox are
  the gate at claim points, `lake check --paranoid` at the release claim
  point ([USER] 2026-10-20) — once that run is shown to
  start `bwrap` (unverified on this box: `bwrap` is not setuid and
  `apparmor_restrict_unprivileged_userns=1`); until then the in-tree
  no-sandbox run is what exists, and `--paranoid` is red today because
  nanoda crashes on this export (`docs/release.md` §3 gives the form that
  works). The kernel replay above stays in the fast tier (9.1 s at 4
  threads, 6.8 s at 8; no sandbox; it checks the on-disk olean set, which
  `lake check` does not). Outside BOTH kernel checks: the ten modules that
  are neither default targets nor `GoLean.*` — the executables' roots and
  the `main`-bearing test modules — two of which carry theorems
  (`Tests/EquationClient.lean`: 296 equation pins + 12 facts;
  `Tests/MethodIdentity.lean`: 12), kernel-checked at elaboration, not
  replayed against tampering; the follow-up is to turn their `main`s into
  build-time checks.
- **Self-tests are not gates.** `scripts/test-*` run by hand when the
  script they test changes.
- The pre-merge adversarial audit: the ask is unconditional; scope and
  waiver are the user's.
- The classification behind this section and every removed step:
  `docs/2026-10-12_gate-cull-plan.md` ([USER]-ruled 2026-10-12, D1–D9).

## The merge protocol (exact, every time)

1. All work on branches off `main`, in worktrees
   (`.claude/worktrees/<lane>`, one writer per worktree; primary
   checkout parked on `main`).
2. Arc complete → `scripts/ci --diff` green (speedbump reds named in
   the ask).
3. The audit ask — never skipped; the user may trim or waive.
4. Pause; merge only on explicit at-that-moment sign-off.
5. `git checkout main && git merge --ff-only <branch>` (if refused:
   rebase, re-gate, re-ask).
6. End parked on `main`, clean, green. Push is a separate sign-off.

## Working practices

- Capture decisions in tracked files, not chat; [AGENT]/[USER]
  provenance on every logged decision; snapshot refs before risky
  git ops; honest reporting (failures with output).
- Autonomous arcs: judgment delegated inside written boundaries; no
  gate weakening, no trust-surface changes, no merge/push;
  branch-complete + audit-ask posed is the end state. **Named
  design gates are HARD STOPS**: a run that cannot stop EXITS
  rather than self-adjudicating the gate.
- Decisions are recorded once, as a paraphrase with the [USER]/[AGENT]
  tag and the date, in the commit message, the backlog row or the BUGS
  entry; a quotation is for considered statements whose wording settles
  a trade-off, never for conversational remarks or sign-offs, in no
  file and in no commit message; code, corpus, baselines and scripts
  carry paraphrases with a pointer, never quotations, and user-facing
  messages carry neither quotations nor ruling citations ([USER]
  2026-10-16, backlog row 44).
- Reference checkouts in gitignored `deps/` (`scripts/setup-deps`;
  default set goose/raft/go — goose and go are gate-required —
  the rest opt-in by name) — consult before inventing.

## Pointers

The plan of record: the release-readiness backlog
`docs/2026-10-12_release-readiness.md` (each item carries its status)
and the seeded-heap design `docs/2026-10-09_seeded-heap-design.md`;
the batched-window charter `docs/2026-09-23_batched-window-charter.md`
and its window plan closed with the 2026-10-03 offer · The index of
living documents: `docs/README.md` · The semantics overview:
`docs/semantics-overview.md` · The CLI, wire and observation formats:
`docs/cli.md` · The earlier whole roadmap (dated, indexed by package;
§7 = the review's dispositions): `docs/2026-09-05_master-plan.md` · The independent project
gate audit (2026-09-05, verdict + F1–F13 + Gates A–D):
`docs/2026-09-05_project-gate-audit.md` ·
The split plan (this era's opening decision):
`docs/2026-08-31_repo-split-plan.md` · Reviving the parked
reasoning product: `docs/2026-08-31_reasoning-revival-guide.md` · Branch index for the parked
reasoning product and the era archives: `docs/ARCHIVE.md` ·
Semantics doctrine: `docs/2026-08-11_essence-of-go-doctrine.md` ·
Latitude census: `docs/2026-08-11_latitude-inventory.md` · Spec
truth pins: `docs/spec-sources.md` · Coverage structure:
`docs/coverage-suite-structure.md` + ledgers
(`docs/coverage-ledger.md`, `docs/language-coverage-ledger.md`) ·
Fidelity bugs: `docs/BUGS.md` · Operational lessons (build/OOM/tool
incidents, measured remedies): `docs/operational-lessons.md` ·
Architecture rules: `docs/architecture-rules.md` (`AGENTS.md` is an
alias of this file, not a separate document).
