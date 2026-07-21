# AGENTS.md

## Project Context

- GoCore is the semantic center of this repo. The native Go frontend
  (`tools/nativefrontend`, built on `go/parser` + `go/types`) is the only
  frontend; it emits a typed wire schema that `NativeToIR` lowers into GoCore.
  (Gobra was an earlier temporary frontend and has been removed.)
- Differential testing is the feature gate for executable semantics: compare
  real Go output (`go run`) against Lean GoCore interpreter output and require
  equivalent observations.
- The end goal is a complete trust chain: Go → executable model
  (differentially validated) → relational semantics (the proof authority) →
  machine-checked proofs (Goose/Perennial/Iris-style). The relational semantics
  must keep pace with the interpreter — see the merge invariant below.

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
  relation (`Rel.lean`) and its premises must stay total and keep pace with the
  interpreter. Do not add an interpreter feature without its relational rule
  shape (total premises; nondeterminism permitted where Go has it). Do not hide
  a semantic choice in evaluator recursion just to pass a case. See
  `docs/nondeterminism-design.md` and the design-review notes.

## Planning Docs

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

## Sandbox And Scratch Files

- See `docs/agent-sandbox.md` before using temp files in agent sessions.
- Use unique scratch directories under `/private/tmp` or `$TMPDIR`.
- For direct Go probes outside the coverage scripts, set
  `GOCACHE=/private/tmp/go-build` so Go does not write to the user cache.
- Do not run `rm`, `rm -r`, or `rm -rf` without explicit approval, even under
  `/private/tmp`. Leave scratch dirs for OS cleanup unless deletion is approved.
