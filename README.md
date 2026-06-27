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
- Lean executes GoCore for differential testing, and later generated Lean views
  should be checked against the same GoCore semantics.
- Proof and VCG layers can later reuse ideas from Aeneas, Goose/Perennial,
  Strata, and Iris-Lean.

Design and roadmap docs:

- `docs/architecture.md`: project layers and ownership boundaries.
- `docs/semantics.md`: GoCore semantics design.
- `docs/roadmap.md`: phased implementation roadmap.
- `TODO.md`: tactical backlog.

Useful commands:

```sh
lake build
lake exe golean
lake exe golean --help
lake exe golean gobra-export --manifest Corpus/gobra-smoke.txt
lake exe golean gobra-json-run --input artifacts/gobra-smoke/work/features/while1/while1.gobra.internal.json --function test_bda1d7d_F --arg-int 6 --arg-int 7
scripts/gobra-smoke
```

After cloning this repo, initialize submodules with:

```sh
git submodule update --init --recursive
```
