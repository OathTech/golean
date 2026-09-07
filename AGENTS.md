# AGENTS.md

**Plan of record: `docs/2026-09-05_master-plan.md` (+ §7 addendum);
charter: `CLAUDE.md`.** The "Planning Docs" pointers below are historical
operating documents, not current instructions.

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
  the merge invariant below.

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
- **Merge invariant (from the 2026-07 design review):** the proof-facing
  relation (`Step`/`Steps`, `Machine.lean`) and its premises must stay total and keep pace with the
  interpreter. Do not add an interpreter feature without its relational rule
  shape (total premises; nondeterminism permitted where Go has it). Do not hide
  a semantic choice in evaluator recursion just to pass a case. See
  `docs/nondeterminism-design.md` and the design-review notes.

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
- For Lean changes, run `lake build` before declaring the work complete. Add
  focused differential runs for the feature touched.
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

[USER] ruling (Mike, 2026-09-07, relayed by the [AGENT] coordinator — cite
as relayed): «The evidence blob should not land, and generally we should
not dump big evidence bundles on main (they can't be easily hosted on GH
for one). … We'll want to decompose and land in sane chunks that can be
reviewed. And where appropriate fix some of the issues, eg. the choice
tape stuff».

- `docs/evidence/` holds RECORDS, not copies: gate tails, transcripts,
  small probe outputs, and the commit SHA the run was at
  (`docs/evidence/README.md`). Caps, gate-enforced by
  `scripts/check-evidence-size` (a `scripts/ci` step; the caps are
  PROPOSED [AGENT] 2026-09-07 and defined once at the top of that
  script): no tracked evidence file over 256 KiB; no top-level
  `docs/evidence/<dir>/` over 4 MiB; no archive extension (`.tar .tgz
  .gz .zip .xz .zst .7z`); no evidence blob byte-identical to a tracked
  file outside `docs/evidence/`.
- Pre-existing offenders on main are frozen in
  `docs/evidence/SIZE-ALLOWLIST.tsv` (rule, path, reason, date). The
  list may only SHRINK: the checker refuses entries dated after the
  freeze and entries that no longer match an offender.
- Bulky evidence (full-run result tables, wire dumps, source trees,
  archives) stays on an ARCHIVE BRANCH — `archive/evidence-<date>_<slug>`,
  listed in `docs/ARCHIVE.md` — and main keeps the directory's README
  plus a `MANIFEST.tsv` (`sha256`, `bytes`, `origin-commit`, `path`, one
  row per file left on the branch), so the record stays auditable
  without the bytes.

## Sandbox And Scratch Files

- See `docs/agent-sandbox.md` before using temp files in agent sessions.
- Use unique scratch directories under the session's permitted `$TMPDIR`
  (or `/private/tmp` on macOS when that path is granted).
- For direct Go probes outside the coverage scripts, use the current
  worktree's cache, matching `scripts/diff-coverage`. From the worktree root:
  `GOCACHE="$PWD/artifacts/go-build-cache" go run ./path/to/package`
  (add `GO111MODULE=off` for standalone probes outside a Go module).
- **Linux under nono:** do not hard-code `/private/tmp/go-build`; that was
  macOS-specific guidance. It can fail with `mkdir /private: permission
  denied` because the outer OS sandbox has not granted that path. Use the
  worktree-local cache above and unique scratch directories under the
  session's permitted `$TMPDIR`. If a different path is actually needed,
  diagnose it with `nono why --path <path> --op write`; granting it requires
  restarting with a narrow `nono run --allow <path>` grant or a reviewed
  derived profile. Codex approval cannot enlarge the outer nono sandbox.
- Do not run `rm`, `rm -r`, or `rm -rf` without explicit approval, even under
  `/private/tmp`. Leave scratch dirs for OS cleanup unless deletion is approved.
