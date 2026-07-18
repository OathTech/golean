# AGENTS.md

## Project Context

- GoCore is the semantic center of this repo. Gobra is a temporary frontend that
  exports artifacts for lowering; do not treat Gobra annotations or Gobra's
  reasoning model as the target semantics.
- Differential testing is the feature gate for executable semantics: compare
  real Go output against Lean GoCore interpreter output and require equivalent
  observations.
- The long-term aim is Goose/Perennial-style reasoning about Go programs, but
  current implementation work should prioritize executable GoCore semantics
  that survive real Go-vs-Lean differential tests.

## Architecture Rules

- GoCore may contain only Go runtime semantics. It must not contain Gobra proof
  artifacts, Gobra permissions/predicates/invariants, synthetic proof-wrapper
  calls, or runtime meanings for spec-only constructs such as `old`.
- Frontend-specific recovery belongs in `GobraToIR` or the Gobra JSON exporter,
  and must fail closed when it cannot produce clean GoCore. Do not make Gobra
  name mangling, export ordering, or adjacency in `program.types` a semantic
  fact.
- If a Gobra wire node has no clear Go runtime meaning, reject it at decoding or
  lowering. Prefer a visible frontend/json/lowering failure over an inert or
  approximate GoCore node.
- Interface semantics must come from Go type identity, type sets, method sets,
  dynamic values, typed nils, and comparability rules. Do not use
  `MethodSubtypeProof` or other proof evidence as dispatch infrastructure.
- Strings may be useful debug names, but stable semantic identity should be
  represented explicitly as the semantics upgrade proceeds. Avoid adding new
  runtime equality/dispatch behavior that depends on raw source or Gobra names.
- Keep executable semantics and future proof semantics aligned: new interpreter
  behavior should have an obvious future relational rule shape. Do not hide a
  semantic choice in evaluator recursion just to pass a case.

## Planning Docs

- `docs/gocore-semantics-upgrade-goal.md` is the operating guide for the
  semantics cleanup/upgrade. Follow its phase gates, forbidden behaviors,
  validation rules, and handoff format.
- `docs/semantics-cleanup-plan.md` records the current junk inventory and cleanup
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
  `scripts/diff-one ...` for Go-vs-Lean conformance.
- `scripts/gobra-smoke` is only a frontend/Lean smoke check. It does not run
  real Go and does not prove Go-vs-Lean equivalence.
- Keep Gobra/frontend export failures separate from GoCore semantic failures.
  Prefer fixing cases that reach Lean and produce a differential mismatch before
  chasing broad frontend coverage.
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
