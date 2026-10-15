# Frozen RD8 acceptance adapter

`U1RD8.simulation` proves the exact frozen
`RelationalCodeX.Sweep.SimulationLaw`; `U1RD8.closed_guarded` proves its original
`GuardedTarget` without a law parameter. The general U1 theorem remains public
GoLean's primary result. This local adapter interprets the same `Ranked.traversal`
used by `Domain.all_schedules`, consuming actual source paths and every ready
branch. Memory skeletons, row ownership and legacy Quiet stay here.

Frozen logic implementation: `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42`.
Reviewed input/handoff: `eba7d3bdaa7786cfc6daad949cd3217185e2c867`.
`setup.py` materializes that committed package under this worktree's `.tmp/rd8`,
independently clones the pinned dependencies from explicit read-only seeds,
copies their caches, and changes only generated package wiring. No peer build
or network operation occurs. The four requested inputs are checked byte-for-byte
on every setup invocation. The independent review also checked all 115 frozen
Lean sources. Reproduction needs the named local commits and dependency caches.

From the GoLean candidate root:

```sh
python3 experiments/2026-10-15-unseq-rd8/setup.py \
  --logic-source /home/mike/projects/golean-logic \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages
cd .tmp/rd8
LEAN_NUM_THREADS=2 capped lake update
LEAN_NUM_THREADS=2 capped lake build U1RD8.Audit
LEAN_NUM_THREADS=2 capped lake env lean U1RD8/Audit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose U1RD8
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose U1RD8.Audit
```

The normal replay covers the four adapter modules. The fresh replay reconstructs
the audit's entire imported environment, including dependency declarations, from
an empty environment. The audit checks every project declaration in its import
closure and headline axioms, then reports direct proof-body dependencies.

The implementation scan is **FAIL: 21 inherited findings, all unwaived**: 16
upstream and five from the frozen customer. Its axiom result is a separate
standard-axioms-only pass. The frozen Memory unused-variable warning remains.
The live logic suite's previously reported `35 NOT-PUBLIC` failure is unchanged
and was not rerun. See the root U1 stage/review documents for each disposition,
validation scope and the remaining interface limits. This is neither O1 uptake
nor live integration, concurrent transport, ownership adequacy for arbitrary
Go programs, or a public Plan API.

Generated `.tmp/rd8` and all logs/build output are disposable.
