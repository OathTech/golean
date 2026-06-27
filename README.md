# GoLean

This is the project repo for the Go/Gobra-to-Lean tool.

The parent workspace contains research notes and reference dependencies under
`../deps`. This subdirectory is intentionally its own git repository so the tool
can grow independently of those reference checkouts. Gobra itself is tracked as
a submodule at `third_party/gobra`, pointing at the `septract/gobra-json` fork.

Initial direction:

- Gobra frontend/export artifacts feed a typed GoCore IR.
- Lean emits executable definitions over `GoM` for differential testing.
- Proof and VCG layers can later reuse ideas from Aeneas, Goose/Perennial,
  Strata, and Iris-Lean.

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
