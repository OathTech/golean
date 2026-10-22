# Architecture rules (formerly `AGENTS.md`)

Moved here VERBATIM from `AGENTS.md` on 2026-09-07 — `AGENTS.md` is now a
git-tracked symlink alias of `CLAUDE.md` ([USER] direction, Mike, relayed by
the [AGENT] coordinator — cite as relayed: make AGENTS.md a git-tracked alias of CLAUDE.md, noted in CLAUDE.md, so that other agents find the working instructions). The body below
is the old file from its "Plan of record" line on, unchanged.

> **Alias caveat** ([AGENT] 2026-09-07). GitHub's RAW view of a git symlink
> (`raw.githubusercontent.com/…/AGENTS.md`) returns the target PATH
> (`CLAUDE.md`), not the content; the web UI shows it as a link. If agents
> ever fetch over raw URLs, switch to a tracked COPY kept identical by the
> gate: `git rm -q AGENTS.md && cp CLAUDE.md AGENTS.md && git add AGENTS.md`.
> `scripts/check-agents-alias` (a `scripts/ci` step) accepts either shape and
> names which it found — symlink whose target is exactly `CLAUDE.md`, or a
> regular file byte-identical to `CLAUDE.md` — and refuses anything else; in
> the copy shape every `CLAUDE.md` edit must be mirrored (`cp CLAUDE.md
> AGENTS.md`) before commit or the gate goes red.

**Charter: `CLAUDE.md`. Plan of record ([AGENT] wording, 2026-10-12):
the batched-window charter closed with the 2026-10-03 offer
(`docs/2026-10-03_offer-to-logic-team.md`); the live plan is the
release-readiness backlog (`docs/2026-10-12_release-readiness.md`) and the
seeded-heap design (`docs/2026-10-09_seeded-heap-design.md`). Index of the
living documents: `docs/README.md`.** The "Planning Docs" pointers below are
historical operating documents, not current instructions.

## Project Context

- GoCore is the semantic center of this repo. The native Go frontend
  (`tools/nativefrontend`, built on `go/parser` + `go/types`) is the only
  frontend; it emits a typed wire schema that `NativeToIR` lowers into GoCore.
  (Gobra was an earlier temporary frontend and has been removed.)
- Differential testing is the feature gate for executable semantics: compare
  real Go output (`go run`) against Lean GoCore interpreter output and require
  equivalent observations.
- This repo is the SEMANTICS product only (repo split 2026-08-31,
  `docs/2026-08-31_repo-split-plan.md`): the executable interpreter
  (`stepFn` and its fuel iteration `execStmt`) as the differentially
  validated model. The verification chain built on it (machine-checked,
  kernel-judged theorems) lives on branch `park/reasoning-2026-08-31`,
  pending its own repo. The Prop-level relation (`Step`/`Steps` in
  `Machine.lean`), its observations, domain invariants and the
  executable↔relation coherence proofs LIVE HERE permanently and are
  co-designed with the interpreter ([USER] 2026-09-05, review F10 —
  `CLAUDE.md` "What this repo is"; the split plan's extraction slice is
  WITHDRAWN, its 2026-09-05 addendum). [Amended 2026-09-05; the sentence
  previously read "proof infrastructure destined for that side … until
  its extraction slice".] It must keep pace with the interpreter — see
  the merge invariant below. RETIRED 2026-10-20 ([USER] ruling, relayed):
  the relational layer left the build — tag `relational/last-main-2026-10-20` is the
  last main carrying it, `docs/ARCHIVE.md` the archive entry — so the
  Prop-level-relation sentences of this bullet are history; `Prefix`/`Finish`
  and the `stepFn_eqns` library stay on main for the raft-proofs customer.

## Architecture Rules

- GoCore may contain only Go runtime semantics — no frontend artifacts,
  name-mangling assumptions, or export-layout heuristics as semantic facts.
- Frontend-specific concerns (name resolution, desugaring, wire shape) belong in
  `NativeToIR` (or the Go emitter) and must fail closed when they cannot produce
  clean GoCore. Prefer a visible frontend/lowering failure over an inert or
  approximate GoCore node.
- Interface semantics must come from Go type identity, type sets, method sets,
  dynamic values, typed nils, and comparability rules.
- Stable semantic identity is `TypeId`/`FuncId`, not raw source strings.
- **Merge invariant — RETIRED 2026-10-20.** It read (from the 2026-07 design
  review): the proof-facing relation (`Step`/`Steps`, `Machine.lean`) and its
  premises must stay total and keep pace with the interpreter; do not add an
  interpreter feature without its relational rule shape (total premises;
  nondeterminism permitted where Go has it); do not hide a semantic choice in
  evaluator recursion just to pass a case (`docs/nondeterminism-design.md` and
  the design-review notes). The relation left the build with the [USER] ruling
  of 2026-10-20 (tag `relational/last-main-2026-10-20`), so the first two clauses
  no longer bind; the third stands on its own as the charter's doctrine («No
  semantic choice hides in evaluator recursion»: latitude Go permits is reified
  on the choice tape).

## Planning Docs

HISTORICAL (2026-09-05): the three documents below are the Gobra-era
operating guide, the cleanup inventory and the July handoff; they are kept
for their rules' rationale, but the current plan is
`docs/2026-09-05_master-plan.md` and the current handoff convention is the
lane `HANDOFF.md` + design-note pattern it describes.

- `docs/gocore-semantics-upgrade-goal.md` is the operating guide for the
  semantics cleanup/upgrade. Follow its phase gates, forbidden behaviors,
  validation rules, and handoff format.
- `docs/archive/semantics-cleanup-plan.md` records the current junk inventory and cleanup
  order. Regressions are allowed only when they remove forbidden semantics or
  expose invalid frontend assumptions.
- Persistent handoffs for the semantics upgrade belong in
  `docs/gocore-semantics-upgrade-handoff.md`; chat-only handoffs are not enough
  for long-running work.

## Testing Workflow

- Use focused slices during iteration:
  - `scripts/diff-one <case-id> ...`
  - `scripts/coverage run --id <case-id>`
  - `scripts/coverage run --tag <tag>`
  - `scripts/coverage run --last-failed`
- Use `scripts/coverage run ...`, `scripts/diff-coverage`, or
  `scripts/diff-one ...` for Go-vs-Lean conformance (native frontend by
  default). The harness also checks observation-invariance across nondeterminism
  oracles for native cases.
- Keep frontend (native emission/lowering) failures separate from GoCore
  semantic failures. Prefer fixing cases that reach Lean and produce a
  differential mismatch before chasing broad frontend coverage.
- For Lean changes, run `scripts/ci` before declaring the work complete (its
  build names every target; a bare `lake build` builds only the default
  targets, the main-free libraries, since 2026-10-21). Add focused
  differential runs for the feature touched.
- For cleanup work, record intentional regressions with the case id, previous
  and new stage/result, removed bad assumption, and intended clean fix. Never
  count `unsupported`, `stuck`, frontend failure, or JSON/lowering failure as
  Go-vs-Lean conformance success.

## Corpus Notes

- `Corpus/coverage/exec` is the executable differential corpus.
- Test metadata lives in each case's `cases.tsv`; expected executable statuses
  are `ok` or `panic`.
- Runtime panics belong in executable differential tests. Static invalid Go
  belongs under `Corpus/coverage/negative/compile`.

## Evidence on main

[USER] rulings: 2026-09-07 (Mike, relayed): (the evidence blob does not land; big evidence bundles are not dumped on main);
2026-10-12 (Mike, firsthand): the global «Artifacts: rebuild or push, never
hoard» rule means that any such records must be useful, with a high bar
for evidence, and the triage of `docs/evidence/` under that bar
(`docs/2026-10-12_gate-cull-plan.md` §9, D10).

- A record is committed under `docs/evidence/` only if the commit message's
  conclusion cannot stand without it: the capture of a non-reproducible
  event (a flake, a timeout class, a runner death), or a probe source whose
  oracle output pins a claim a reader must be able to re-run. Everything
  reproducible from the tree at a commit — gate tails, train stamps, audit
  transcripts, run dumps, wire dumps — is not committed: its conclusion goes
  in the commit message or the dated doc, and the bytes are rebuilt when
  needed.
- A probe that pins semantics belongs in `Corpus/` as a case, not here; a
  test fixture belongs beside its test (`testdata/`), not here.
- No size gate: the bar above is the rule (`scripts/check-evidence-size` and
  `SIZE-ALLOWLIST.tsv` were retired 2026-10-12). A bulky record that must
  exist goes on an archive branch listed in `docs/ARCHIVE.md`.
- Records deleted in the 2026-10-12 triage are in history:
  `git show 63c9ea65:docs/evidence/<dir>/README.md`.

## Sandbox And Scratch Files

- See `docs/agent-sandbox.md` before using temp files in agent sessions.
- Use unique scratch directories under the session's permitted `$TMPDIR`
  (or `/private/tmp` on macOS when that path is granted).
- For direct Go probes outside the coverage scripts, use the current
  worktree's cache, matching `scripts/diff-coverage`. From the worktree root:
  `GOCACHE="$PWD/artifacts/go-build-cache" go run ./path/to/package`
  (add `GO111MODULE=off` for standalone probes outside a Go module).
- **Under an OS sandbox (Linux):** do not hard-code `/private/tmp/go-build`;
  that was macOS-specific guidance. It can fail with `mkdir /private:
  permission denied` because the outer OS sandbox has not granted that path.
  Use the worktree-local cache above and unique scratch directories under the
  session's permitted `$TMPDIR`. If a different path is actually needed,
  diagnose it with the sandbox's own tooling and hand the user the exact
  grant to add; approval inside the agent cannot enlarge the outer OS
  sandbox. Nothing in the project's scripts or docs may depend on one
  sandbox or one box (release-readiness row 46).
- Do not run `rm`, `rm -r`, or `rm -rf` without explicit approval, even under
  `/private/tmp`. Leave scratch dirs for OS cleanup unless deletion is approved.
