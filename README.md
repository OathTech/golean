# GoLean

This is the project repo for the Go-to-Lean tool.

The parent workspace contains research notes and reference dependencies under
`../deps`. This subdirectory is intentionally its own git repository so the tool
can grow independently of those reference checkouts.

Direction:

- A native Go frontend (`tools/nativefrontend`, built on `go/parser` +
  `go/types`) type-checks Go and emits a clean typed wire schema that
  `GoLean/NativeToIR.lean` lowers into a GoCore deep embedding. (Gobra was an
  earlier temporary frontend accelerator and has been removed.)
- GoCore is the semantic center; frontend-specific concerns stay in the
  lowering adapter and fail closed.
- Differential tests compare ordinary Go execution (`go run`) against Lean
  execution of GoCore.
- The proof-facing relational semantics is the eventual authority; the
  executable interpreter is a differentially-validated test artifact.
- Proof and VCG layers can later reuse ideas from Aeneas, Goose/Perennial,
  Strata, and Iris-Lean.

Design and roadmap docs:

- `docs/architecture.md`: project layers and ownership boundaries.
- `docs/semantics.md`: GoCore semantics design.
- `docs/roadmap.md`: phased implementation roadmap.
- `docs/differential-testing.md`: differential testing plan and generator notes.
- `docs/agent-sandbox.md`: scratch directory and temp-cache conventions for
  sandboxed agent sessions.
- `TODO.md`: tactical backlog.

Useful commands:

```sh
lake build
lake exe golean --help
lake exe gocore-eval-tests
scripts/coverage
scripts/diff-coverage
scripts/coverage-negative
scripts/diff-one litmus/if-return
```

Use `scripts/coverage run ...` or `scripts/diff-one ...` for Go-vs-Lean
equivalence during semantics work (native frontend by default).

`Corpus/coverage` is the source of truth for small coverage litmus tests.
`scripts/coverage` runs both executable differential coverage and static
compile-negative coverage. The executable lane runs the same canonical Go files
with `go run` and through the native frontend / Lean path.
