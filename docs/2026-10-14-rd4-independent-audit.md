# RD4 phase laws: independent audit

[AGENT] 2026-10-14: review the semantic phase batch independently in
`audit/rd4-phase-1014`, with a separate worktree and copied, independently
writable caches. The review follows the paired coordination charter and
the concrete RD4 phase relay. No peer checkout, shared cache, merge or
remote was modified.

## Target and inputs

The reviewed implementation is
`67f7d1c5ba6a96055a41802b978386d019e03c67`. Its five source files match the
independently checked overlay on `e5fd589f25781255d90dfb528eea824322f58b39`
exactly, including the subsequent documentation-only correction to
`StepAdmission`'s comment. The candidate's remaining delta comprises three
documentation files, also inspected.

The downstream package was exported with `git archive` from logic commit
`a1ddc673e03d91060c51f451dc5cd274916f9a4f`, path
`experiments/2026-10-14_relational-codex/`. All 59 files matched the frozen
input manifest before scratch configuration changes. In particular:

- `RelationalCodeX/Phases.lean`:
  `ecaf8f4c43a225b62e34fa368d2b0466899e483640bb1e8989a603f688f37161`.
- `RelationalCodeX/Targets.lean`:
  `2e953a5cfe26967d367c25cad9c8545dd0815e06680de53486a5bc762f5c79fd`.

## Findings and domain checks

No correctness, trust or acceptance defect found in the reviewed batch.

1. **Intermediate preservation and uniformity.** `StorePath` fixes its
   controls and finite structure independently of the store. Each
   transition preserves that particular store, under the same operation
   fact. This is stronger than equal stores at run endpoints and supplies
   precisely the induction consumed by the frozen guarded lifting.
   `StoreEffect` does not carry the read premise across the update;
   assignment cleanup uses `True` over every post-store.
2. **Labels and choices.** The witnesses are actual `Transition` labels,
   with empty picks proved separately. Reads retain access traces and the
   write uses the canonical target access. Nothing asserts observer silence.
   `Transition.on_any_tape` supplies the all-tape success used downstream;
   the label is not synthesized by an unrelated observer abstraction.
3. **Admission and final control.** Each traversed source is nonterminal
   and passes `initPrintRefusal?`, including the effect source. Neither a
   zero-step path nor the final assignment continuation requires admission.
   This supports the unchanged targets' arbitrary `M.idx`, including init,
   without assuming safety of the caller's eventual continuation.
4. **Locations and aliases.** Assignment targets and variable destinations
   remain arbitrary `Loc`; no separation, distinctness or root premise is
   added to writes. Reads occur before the write. Successful `loadRoot`
   restricts the operand binding locations to roots, exactly as in the
   frozen requests and old endpoint laws: arbitrary `Loc` binders do not
   imply successful interior binding reads.
5. **Call entry.** The empty-operand branch exposes the initial call itself
   as the effect source. The inductive branch handles arbitrary nonempty
   operand lists, order and continuations, not only Keep's two operands.
   Lookup, method exclusion, arity and `LocalEntry` justify activation at
   the boundary. The body is not assumed safe by this semantic theorem.
6. **Boundary and existing laws.** The upstream addition has no Iris,
   resources, later modality or client-proof imports. Machine frame walks
   remain private implementation proofs. Existing assignment, entry and
   control modules are unchanged. In particular, the old `OperandValues`
   only promises endpoint preservation; replacing it by `OperandPaths`
   would strengthen the old domain. Keeping that older interface is sound.

## Independent validation

All Lean/Lake commands below used `LEAN_NUM_THREADS=2 capped` and Lean
4.32.2. Before copying the implementation cache, every tracked Lean source,
toolchain and Lake configuration was compared with the reviewer tree.
The reviewer removed the selected artifacts and freshly elaborated both
new modules, facade and both changed test modules with:

```sh
LEAN_NUM_THREADS=2 capped lake build GoLean.Relational Tests.RelationalContracts Tests.GoCoreAudit
```

This passed without warnings. The seven added headline axiom checks report
only `propext`, `Classical.choice`, `Quot.sound`.

A separate GoLean-only package contains the exact frozen `Phases.lean`
and an independently written `PhaseCheck.lean`. Induction translates
`StorePath` to `ReadPhase` and conversely, and translates operand paths;
the three exported source theorems then prove `AssignmentPhases`,
`VariablePhases`, `EntryPhases` without additional assumptions. The
50-job build passed and all three adapter axioms are standard. An initial
reviewer-only typo used Lean's reserved word `prefix` as a binder and
failed; after renaming it, the complete check passed without `sorryAx`.

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env leanchecker GoLean RelationalCodeX.Phases PhaseCheck
```

Direct kernel replay passed. Its scope was all 83 built GoLean source
modules (including `GoLean.lean`), the exact request module and the
reviewer's adapter. Built/source module sets matched, with no stale or
missing GoLean module. Replay includes the module data's private part.
The source scan of the additions found no trust escape hatch.
The independent core-audit harness also passed: 82 GoLean modules under
the source directory (71 core), 348 required theorems, and 22,371 imported
local declarations, all with standard axioms only:

```sh
LEAN_NUM_THREADS=2 capped lake env python3 tools/core-audit.py
```

The full frozen package was also bootstrapped at its original GoLean pin
using its unchanged `setup.py --copy-cache`: each dependency is an independent
clone, with matching sources, configuration and toolchain before cache copying.
Its baseline 307-job cached check passed. The existing unused-variable warning
at `GoLeanIris/Memory.lean:1625` remains visible; that frozen source was not
edited. Added reviewer modules contain only the phase adapters and the two
closed acceptance applications; no frozen proof or target was changed.
Direct `lake env leanchecker Iris Batteries Qq` also passed for the
independently copied, unchanged third-party dependency artifacts: 174 Iris,
18 built Batteries and 14 Qq modules. This is their built acceptance
dependency closure, not a claim to rebuild every source in those libraries.

## Completion record

The private GoLean clone and scratch `pins.json` were then updated to the
immutable candidate. The other 58 original files still match the input
manifest byte-for-byte; only the GoLean pin changed in `pins.json`.
The frozen setup script reverified all four dependency clones and pins.
Iris, Batteries, Qq and Lean remained fixed.

The independent full guarded build passed, 310 jobs, including fresh
elaboration of the affected upstream and downstream dependency chain.
The reviewer added `RelationalCodeX.AuditAdapters` (the independently
checked translations described above) and this wrapper, without changing
the frozen package configuration or any proof source:

```lean
import RelationalCodeX
import RelationalCodeX.AuditAdapters

namespace Audit
theorem closedSet : RelationalCodeX.SetTarget :=
  RelationalCodeX.set_body_at_acceptance assignment
theorem closedKeep : RelationalCodeX.KeepTarget :=
  RelationalCodeX.keep_body_at_acceptance entry variableAssignment
#print axioms closedSet
#print axioms closedKeep
#eval RelationalCodeX.audit
end Audit
```

Both closed targets have only the standard trio of axioms. The exhaustive
local audit checks 5,578 declarations with these seven adapter/wrapper
theorems included (5,571 in the original aggregate). The original target
lookup premises and Keep's logical `setContract` support remain exactly
as written; no phase-law parameter or execution-success assumption remains.

```sh
LEAN_NUM_THREADS=2 capped lake build +RelationalCodeX.ClosedTargets
LEAN_NUM_THREADS=2 capped lake env leanchecker GoLean GoLeanIris GoLeanIrisExamples RelationalCodeX
```

Final candidate-pinned kernel replay passed. Its selected module set
matches sources exactly: 83 upstream plus 54 local modules (52 frozen and
two added); no missing or stale module. The unchanged third-party replay
above supplies the remaining non-toolchain dependency check.

**Verdict:** the batch satisfies the three exact semantic requests and the
unchanged guarded Set/Keep acceptance at the reviewed candidate. No finding
requires a fix or waiver. This does not certify general observer coverage,
other source constructs, or downstream live uptake.

The [phase handoff](2026-10-14_relational-phase-acceptance.md) supplies the
full frozen export/bootstrap procedure and equivalent structural adapters
for reproduction. The reviewer adapter uses `outward`/`inward` translations
and performs operand induction inside `entry`; the handoff's separately
named operand helper is the same constructor translation.

Full differential CI is the implementing lane's separate evidence; the
reviewer does not claim to have rerun it. The lane predates the current
`scripts/check-kernel-replay` script, so the replay above uses the toolchain
checker directly. Downstream live uptake, merge approval and push approval
remain separate from this scratch acceptance.
