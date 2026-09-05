# GoLean

**Plan of record: `docs/2026-09-05_master-plan.md` (+ its §7 addendum,
the 2026-09-05 review dispositions); charter: `CLAUDE.md`.** The
pointers further down are historical unless they say otherwise.

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
- The Iris proof layer built on this semantics lives on branch
  `park/reasoning-2026-08-31`, pending migration to its own repo (the repo
  split, 2026-08-31 — `docs/2026-08-31_repo-split-plan.md`, with its
  2026-09-05 addendum: the semantic relation and its coherence proofs stay
  HERE; this repo makes no verification claims about Go programs).

The reviewed [Gate A1 consumer-contract experiment](spikes/gate-a1/README.md)
contains executable/relation bridges and a thin Iris adapter in a separate
Lake package, outside the default build. Its [review and proposed next phase](docs/2026-09-05_gate-a1-review-and-next-phase.md)
record the proved scope and remaining admission, composition, and adequacy
obligations. Run its dedicated gate with `bash spikes/gate-a1/check`.

Design and roadmap docs (HISTORICAL — superseded as current direction by
the plan of record above; kept for their design rationale):

- `docs/architecture.md`: project layers and ownership boundaries.
- `docs/semantics.md`: GoCore semantics design.
- `docs/roadmap.md`: phased implementation roadmap.
- `docs/archive/differential-testing.md`: differential testing plan and generator notes.
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
