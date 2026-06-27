# GoLean

This is the project repo for the Go/Gobra-to-Lean tool.

The parent workspace contains research notes and checked-out dependencies under
`../deps`. This subdirectory is intentionally its own git repository so the tool
can grow independently of those reference checkouts.

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
```
