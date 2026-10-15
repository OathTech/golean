# Concurrency compatibility experiment

Baseline: `fc52512a6644c04996d327865919556107cf84ba`.
Lane: `spike/relational-concurrency-1014`; all additions are experimental.

## Decisions

- [USER] 2026-10-15: run the relayed concurrency brief independently of
  RD5/C1, at the audited pin, with isolated build state and no runtime/API
  changes, merge, push, peer writes or live repin.
- [AGENT] 2026-10-15: use a print-apply boundary between two parent reads
  and an unbuffered rendezvous for the synchronization probe. These are
  existing pool boundaries; the examples use the existing singleton
  `execProg` entry and its empty detector, then the actual spawn.

## Checkpoint finding (implementation in progress)

`GoLean/GoCore/Ops.lean:2698` derives `Ord` for recursive `Loc`. On this
toolchain that generates opaque `GoLean.GoCore.instOrdLoc.ord`, backed by
`GoLean.GoCore.instOrdLoc.ord._unsafe_rec`, classified `DefinitionSafety.partial`
(despite its name, not `DefinitionSafety.unsafe`).
`Race.shadowSet` uses the comparator to insert or replace shadow keys.
This is a trust-surface finding under the charter's totality rule. The
standard-axiom check alone reports no axioms for this opaque constant and
does not establish the runtime comparator's equations.

`Concurrency.Obstruction` compiles the missing `RootComparatorContract`
without assuming it and checks the declaration classification. Ordinary
read phase reuse, a generic effect-to-pool helper, and cross-root read
preservation compile in `Concurrency.Reuse`. Executable probes alone are
not proof evidence for the unfinished detector/driver acceptance.

Reproduce the checkpoint from
`experiments/2026-10-14-concurrency-compatibility`:

```sh
LEAN_NUM_THREADS=2 capped lake build Concurrency.Obstruction Concurrency.Certificate Concurrency.Fixture
LEAN_NUM_THREADS=2 capped lake env lean Concurrency/Obstruction.lean
```

The obstruction requires an upstream decision; this lane changes no
runtime code. Remaining experiment proofs and the independent review are
still in progress at this checkpoint.
