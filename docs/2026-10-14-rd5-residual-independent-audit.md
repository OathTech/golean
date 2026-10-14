# RD5 residual E/F independent audit

[AGENT] 2026-10-14: accept the residual integer-comparison and sequence-break
batch after independent source review and exact frozen original-target acceptance.
This report is an implementation audit, not merge, push or live-repin approval.

## Candidate and scope

**ACCEPT E/F at `fc52512a6644c04996d327865919556107cf84ba`: no new correctness or trust defect found.**

Candidate source/configuration identity with the reviewed overlay and scratch
clone was checked across all 114 Lean and build-configuration files. The
private clone was then cleanly checked out at that immutable commit and its
experimental pin updated. The reviewer started from
`2497d46f559a55d0dc003e3e804c482d091bd2b0` in the independent worktree
`.claude/worktrees/rd5-residual-audit-1014`, branch
`audit/rd5-residual-independent-1014`, and applied the three-file frozen overlay.
The implementation adds 43 lines: `ReadOnlyExpr.less_int`,
`sequence_signal_path`, `sequence_break_path`, and their axiom-print checks.
It does not change an executable operation or a frozen customer statement.

The independent customer copy is the exact 95-file archive of
`experiments/2026-10-14_relational-codex/` at logic commit
`8cf7c1652587366f324c1159a89d72cd0d297cf8`; relay/handoff
`57b677de9e76ca9c05de03d2b202910cabc660be`. Original file identity was checked
byte-for-byte. Only its experimental GoLean pin changes; two independent
validation modules are added. No peer source, live root, dependency pin,
charter or global state was changed.

## Semantic assessment

The comparison theorem has precisely the requested arbitrary context, store
predicate, local environment, expressions, integer values and common integer
kind. The integer arm of `valueLess` compares the stored `Int`s directly.
There is no normalization, fit premise, particular integer kind or small-count
bound in this export. The latter belongs only to the original Add contract.
Its proof evaluates the left operand, then the right operand using their
continuation-uniform paths, and applies the actual strict less-than operation.
The frame construction is upstream. Intermediate stores remain equal and
operand transition labels remain actual labels, including reads; empty picks
do not silently assert empty access traces. Source admission is proved for
the three administrative sources and inherited at every operand source.

The break theorem raises the actual break signal, then removes precisely the
public `sequence rest env k` frame. `rest` is skipped, not executed. The
underlying general signal law matches the machine's unconditional sequence
row and is valid for arbitrary signals. Neither law resolves any frame in the
arbitrary final tail or assumes that tail is admitted or safe. In particular,
this is not a general labelled-exit or cleanup theorem. It supplies the
sequence prefix which the existing while-loop break law did not supply.

Both laws are available through `GoLean.Relational` alone. They introduce no
Iris, WP, client ghost state, source-program catalogue or downstream imports.
The exact frozen requests are direct theorem applications. The earlier
`ExpressionPhases` is reconstructed through the frozen
`expressionPhases_of_comparison`, preserving existing addition normalization
and dereference behavior.

I followed the downstream proof from the exact requests through the counter
test, symbolic first/next iterations, guarded loop, zero-count exit, final
read and original result packaging. The original `AddTarget` remains the
same logical contract: arbitrary input uint64 cells, the original `n ≤ 16`
domain, update of the first cell by `n`, preservation and return of the second
cell. The proof performs symbolic iteration, not count enumeration. The
arbitrary caller continuation and resource obligations remain downstream.
Unconditional acceptance supplies both residual laws; no pending semantic-law
parameter remains. Alias is also checked through its direct logical-contract
proof, alongside Pair, Set and Keep.

## Validation

All Lean/Lake jobs used `LEAN_NUM_THREADS=2` and `capped`. Bootstrap used the
frozen `setup.py` with independent `--no-hardlinks` clones. Cache byte copies
were made only after checking every GoLean Lean source and Lake/toolchain
configuration against the overlay and checking each dependency's clean exact
pin. There are no shared cache symlinks or hardlinks. Lean is 4.32.2; Iris,
Batteries and Qq retain the frozen `pins.json` revisions.

- Full frozen experiment build: PASS, 348 jobs. Its aggregate audit checks
  5,801 local declarations. The existing `GoLeanIris/Memory.lean:1625:28`
  unused-variable warning is still present.
- Independent exact adapters and unconditional original Add/Alias/Pair/Set/Keep
  targets: PASS. The earlier E adapter and its full Add acceptance also pass.
- Independent public-only import harness: PASS for comparison, general signal
  propagation and the exact statement-view break type.
- All 122 axiom reports emitted during the build, ten in the acceptance
  harness and three in the public harness are subsets of the standard trio.
  The acceptance-local audit checks 5,813 declarations; the independent
  imported upstream/local/wrapper audit checks 23,562 declarations, with no
  nonstandard axiom. A scan of the changed semantic source finds no sorry, added axiom,
  native decision, unsafe/extern hook or disabled kernel checking.
- Both direct kernel replay invocations exit 0. The exact source-backed sets
  and multiplicities match: 382 modules, comprising 86 GoLean,
  49 RelationalCodeX, 34 GoLeanIris, five example modules, 174 Iris,
  18 Batteries, 14 Qq and two reviewer harnesses. No missing, extra or
  duplicate replay names.

The initial acceptance harness failed because its theorem name `alias` is a
Lean keyword; it was renamed to `aliasTarget` and the complete harness rerun.
An initial scratch-file creation used the wrong relative path and failed;
it was corrected before the public-only harness ran. A first log-summary
assertion incorrectly required the full standard trio rather than allowing subsets; it rejected a valid smaller set and was
corrected to the intended subset test. These reviewer-harness failures
required no implementation change; only successful reruns count as validation.

I did not independently rerun the full differential CI or the live logic
surface check. This audit establishes the isolated frozen acceptance and its
trust checks. The existing downstream Memory warning and reported live
**35 NOT-PUBLIC** failure are not resolved by E/F; this result is not full
mirror completeness or production readiness.

## Reproduction

Export the frozen experiment, set only `pins.json`'s GoLean value to the
candidate above, and run its `setup.py` with the GoLean source and seeds at
`/home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages`.
Fresh builds need no cache. For cache reuse, independently verify source and
configuration equality first. In the private experiment, the exact target
acceptance module is:

```lean
import RelationalCodeX
namespace ResidualAudit
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalCodeX

theorem comparison : IntegerComparisonPhases := by
  intro ctx fact env l r x y kind hl hr
  exact ReadOnlyExpr.less_int kind hl hr

theorem sequenceBreak : SequenceBreakPhases := by
  intro ctx rest env k
  exact sequence_break_path ctx rest env k

theorem expression : ExpressionPhases :=
  expressionPhases_of_comparison comparison

theorem add : AddTarget :=
  RD5Acceptance.addResidualTarget comparison sequenceBreak

theorem addEarlier : AddTarget :=
  RD5Acceptance.addTarget expression sequenceBreak

theorem aliasTarget : AliasTarget := alias_body_at
theorem pair : PairTarget := pair_body_at
theorem set : SetTarget := set_body_at
theorem keep : KeepTarget := keep_body_at

#print axioms comparison
#print axioms sequenceBreak
#print axioms expression
#print axioms add
#print axioms addEarlier
#print axioms aliasTarget
#print axioms pair
#print axioms set
#print axioms keep
#print axioms sequence_signal_path
#eval RelationalCodeX.audit
end ResidualAudit
```

The independent exhaustive audit additionally enumerated every imported
constant defined in a GoLean, GoLeanIris, GoLeanIrisExamples or RelationalCodeX
module, plus current-module declarations, and called `Lean.collectAxioms` on
each. Any axiom outside `propext`, `Classical.choice` and `Quot.sound` fails.
The separate public module imports only `GoLean.Relational` and directly
restates the universally quantified comparison, signal and break types above.

```sh
LEAN_NUM_THREADS=2 capped lake build RelationalCodeX
LEAN_NUM_THREADS=2 capped lake env lean -o .lake/build/lib/lean/ResidualAudit.olean ResidualAudit.lean
LEAN_NUM_THREADS=2 capped lake env lean -o .lake/build/lib/lean/PublicResidualAudit.olean PublicResidualAudit.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean Iris Batteries Qq PublicResidualAudit
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLeanIris GoLeanIrisExamples RelationalCodeX ResidualAudit
```

Compare replayed module names, including multiplicities, with source-backed
built `.olean` module names under precisely these prefixes. Build logs,
replay logs, clones and caches are disposable and are removed after reporting.
