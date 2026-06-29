# GoLean

This is the project repo for the Go/Gobra-to-Lean tool.

The parent workspace contains research notes and reference dependencies under
`../deps`. This subdirectory is intentionally its own git repository so the tool
can grow independently of those reference checkouts. Gobra itself is tracked as
a submodule at `third_party/gobra`, pointing at the `septract/gobra-json` fork.

Initial direction:

- Gobra frontend/export artifacts lower into a clean GoCore deep embedding.
- GoCore is the semantic center: Gobra is a frontend source, not a first-class
  verification target.
- Gobra verification annotations are erased at lowering; differential tests
  compare ordinary Go execution against Lean execution.
- A native Go frontend is a likely later replacement for Gobra once coverage
  demands it.
- Lean executes GoCore for differential testing, and later generated Lean views
  should be checked against the same GoCore semantics.
- Proof and VCG layers can later reuse ideas from Aeneas, Goose/Perennial,
  Strata, and Iris-Lean.

Design and roadmap docs:

- `docs/architecture.md`: project layers and ownership boundaries.
- `docs/semantics.md`: GoCore semantics design.
- `docs/roadmap.md`: phased implementation roadmap.
- `docs/differential-testing.md`: differential testing plan and generator notes.
- `TODO.md`: tactical backlog.

Useful commands:

```sh
lake build
lake exe golean
lake exe golean --help
scripts/coverage
scripts/diff-coverage
scripts/coverage-negative
scripts/diff-one litmus/if-return
scripts/gobra-smoke
scripts/semantic-edges-challenge-smoke
```

`Corpus/coverage` is the source of truth for small coverage litmus tests.
`scripts/coverage` runs both executable differential coverage and static
compile-negative coverage. The executable lane runs the same canonical Go files
with `go run` and through the frontend/Lean path; there are no separate Gobra
fixtures.

After cloning this repo, initialize submodules with:

```sh
git submodule update --init --recursive
```
