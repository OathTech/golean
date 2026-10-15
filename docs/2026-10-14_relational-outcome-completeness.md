# C1: bounded local sequential outcomes

[USER] 2026-10-15: continue the checked constraint checkpoint under the mirror
outcomes brief; complete semantic operation failure and arbitrary-state local
main correspondence before initialization. Export through `GoLean.Relational`,
check clients and obtain independent implementation review. No merge, push,
live repin, peer write or global change. Concrete RD5 defects retain priority;
whole-program composition and the concurrency worker remain separate.

[AGENT] 2026-10-15: use compositional guard-ordered `OperationCheck` nodes and
semantic `Selection` witnesses for ordinary failure. Move the checked experiment
into `GoLean.GoCore.Relational.Local`, specializing all carriers to the concrete
`OperationFailure`; public clients supply no operation-law parameter.

## Pins and scope

E/F remains independently consumable at
`fc52512a6644c04996d327865919556107cf84ba`. C1's compiled constraint checkpoint
is `851e53a7a55033fd81ef53120f7ad7c85f46d289`. Concrete main correspondence was
checked first at `f87bd7bb229635150ee6318d71ea8096ee773ed5` (six modules,
1,036 module-owned declarations, seven headline laws, exact kernel replay).
Initialization followed at `2fabfb1688ce616b25a9e86ec310823ad12cfa4a` (1,062
declarations and eleven headlines). Those commits retain the experimental
sources; their permanent replacements are the five public modules below.

**Audited implementation pin: `55ad72493061b59363e846341380a9edce12a2de`.**
C1 is complete at its bounded local scope. The
[independent final audit](2026-10-15-c1-independent-audit.md) reports no findings
and confirms that all seven independently rebuilt/replayed source files match
this exact commit. This audit/handoff successor changes documentation only;
consumers can pin the implementation without taking any unfinished C1 work.

C1 covers **bounded local sequential execution from any supplied state** in
main and initialization modes. It neither changes executable behavior nor
adds a context/store/control well-formedness, refusal-freedom or success
premise. Normal completion, blocked deadlock, admitted panic with its chain
and rendering, rendering refusal, ordinary refusal/fatal and exhaustion are
all represented. Different choices may produce different outcomes.

## Public contracts

Import `GoLean.Relational`; namespace `GoLean.GoCore.Relational.Local`.

- `OperationFailure ctx a records cause`: `OperationCheck.Rejects` over the
  ordered operation checks at `a`, with the exact refusal or fatal cause.
  Neither a tape nor an evaluator defines this relation. Checks compose
  existing validation/commit operations and explicit selections at their
  actual guard positions. A passed check does not assert transition success.
- `Finish mode ctx a records outcome cost`: normal/deadlock boundaries cost
  zero; rendering and ordinary failing operations cost one step; init printing
  refuses at zero. Ordinary failure cannot bypass zero-cost or mode guards.
- `Prefix mode ctx a labels b`: labelled semantic transitions, preserving
  initialization admission at every traversed source. `Prefix.erase` is `Run`.
- `Execution mode ctx budget a labels b records outcome cost`: a selected
  bounded prefix and its finish or exhaustion. `within_budget`, `prefix`,
  `finish_or_exhausted` and `exhaustion_length` give cost/prefix accounting.
  Exhaustion has exactly `budget` successful labels, not a claim that no
  different selected run finishes earlier.
- `Avoids mode ctx a bad`: excludes `bad` at every reachable admitted prefix
  and every finishing alternative. Refusal and fatal are separate predicates.
  One successful successor is insufficient.

Under `Local.Correspondence` the closed theorem mapping is:

| Export | Exact named proposition |
| --- | --- |
| `operation_failure_coverage` | `OperationCoverage`: every ordinary non-zero-cost, non-aborted step refusal/fatal has a semantic witness replaying on the selected tape. |
| `operation_failure_replay` | `OperationReplay`: every failure works on **every** tape replaying its records. |
| `operation_failure_selections` | `OperationSelections`: any failure's records realize with any supplied suffix. |
| `main_coverage` | `Coverage .main` |
| `main_realization` | `Realization .main` |
| `initialization_coverage` | `Coverage .initialization` |
| `initialization_realization` | `Realization .initialization` |
| `main_refusal_exclusion`, `initialization_refusal_exclusion` | `RefusalExclusion` in the named mode. |
| `main_fatal_exclusion`, `initialization_fatal_exclusion` | `FatalExclusion` in the named mode. |

`Coverage mode` quantifies over every context, budget, supplied state and tape.
It yields an `Execution`, the exact successful executable prefix with those
labels, finishing consultation replay, and equality of the actual driver
result with `observe outcome endpoint suffix`. `Realization mode` conversely
realizes **each** admitted `Execution` at its stated budget with arbitrary
finishing suffix and the same labelled prefix/result projection.

`observe` returns store and tape only for normal completion. Every error
projection erases the semantic endpoint and suffix; failed calls do not
produce an invented label or returned tape. `FailureChecks.Correspondence.
atState_errors` proves the operation error projection; `OperationCheck.
Correspondence.replay_exact` proves complete replay of the structured check.
The positions of consultations are fixed structurally by the semantic checks,
not by `seqConsumption`, which is not accurate on every failed path.

## Implementation and acceptance

- `RelationalOperationCheck.lean`: compositional checks, semantic rejection,
  structured replay and selection realization.
- `RelationalOperationFailure.lean`: guard-ordered operation views, exact
  failure causes, concrete `OperationFailure`.
- `RelationalLocalExecution.lean`: mode, outcomes, finishes, selected bounded
  executions, exclusion predicate and exact correspondence statements.
- `RelationalOperationFailureSound.lean`: operation coverage/replay/selections
  for arbitrary supplied controls and stores.
- `RelationalLocalExecutionSound.lean`: main and initialization coverage and
  realization plus their separate exclusion corollaries.

`Tests/RelationalOutcomes.lean` imports only the facade. `classify` obtains a
relational execution, its budget bound and `Run` from an arbitrary selected
driver call. `selected_path_realizes`, `safe_from_refusal` and `safe_from_fatal`
consume closed exports without evaluator case analysis. Cheap additional
controls cover zero-fuel normal/init-print, exact empty-panic-chain refusal,
no fabricated records for unsupported expressions, skipped dependencies before
unseq selection, and randIntn validation before/commit failure after selection.
The exhaustive correspondence theorems, not those controls, establish coverage.
Existing `Tests.RelationalContracts` continues to build unchanged.

The frozen RD5 A–F GoLean-only adapters are rechecked against logic implementation
`8cf7c1652587366f324c1159a89d72cd0d297cf8`, using copied `CompositionRequests`,
`ContinuationRequests` and `ResidualRequests`, and the exact adapter source in
[the RD5 handoff](2026-10-14_relational-composition-acceptance.md). No logic file
or live dependency pin is modified. Full downstream Iris/Add/Alias/Pair/Set/Keep
acceptance is the independently audited E/F evidence at its E/F pin; C1 does
not claim a fresh downstream Iris build.

## Validation at the public source freeze

- `scripts/ci --diff`: PASS in 574 seconds; all gates and speedbumps green.
  Fresh differential: 3,989 cases, 3,749 PASS and 240 tracked FAIL, no baseline
  regression. All 405 negative cases pass. Interpreter checks: 396 PASS.
  Default targets build warning-free and the exhaustive core audit passes.
- Eleven headline correspondence laws and four facade clients print only the
  standard trio. The existing core audit covers all 90 GoLean modules under
  `GoLean/`, plus the imported Tests declarations including the new client.
- Exact kernel replay: all 91 GoLean modules (including the import root) and
  `Tests.RelationalContracts`, `Tests.RelationalOutcomes`, `Tests.GoCoreAudit`.
  Each invocation's names/multiplicities match its requested set; no missing,
  extra or duplicated module in a run. The two runs overlap on GoLean modules.
- Frozen RD5 GoLean-only A–F adapters: PASS, 62 jobs; seven adapter headline
  laws and all 64 local request/adapter/audit declarations use only standard
  axioms. Exact replay of the three request modules, two adapters and their
  disposable audit passes. No fresh downstream Iris result is claimed here.
- The independent reviewer rebuilt the five public modules, facade and new
  client warning-free in separate scratch, checked all fifteen headline/client
  axiom reports and replayed those seven modules successfully. Its additional
  print controls distinguish valid zero-budget init printing from malformed
  printing, which exhausts at zero and refuses with its exact cause at one.

The initial fast CI run **failed** because old corpus artifacts had been
removed, leaving no recorded differential/negative runs. It also reported two
new raw-memory call sites. The fresh `--diff` run supplies the missing evidence;
the inventory now records the append allocation and synchronization-word peek
in the semantic failure view, with their reasons. No gate was waived or weakened.
Source hashes were checked unchanged after validation and before committing.
Disposable experiment, compatibility, review and CI outputs were removed after
recording these conclusions; the active branch worktree is retained. Rebuild
with the commands below rather than relying on retained artifact logs.

## Review dispositions

Preparatory independent constraint review found:

- F1: the three abstract operation obligations alone allow a fake intn record
  to be added to an unsupported-expression failure. **Fixed structurally**:
  the public relation is now concrete `OperationCheck.Rejects`; the checked
  `unsupported_records` control rules out any such added record.
- S1: `seqConsumption` can predict an unseq selection even when a skipped
  dependency refuses first. **Addressed**: failure checks use the actual
  guard order and never `seqConsumption`. The checked
  `skipped_dependency_before_choice` witness has empty consultation records.

The fresh implementation reviewer independently checked the immutable main
checkpoint and its dependencies, malformed-state controls and six-module
kernel replay, with no concrete finding. That provisional result does not
cover final initialization/facade integration. The subsequent final-source
review, independent rebuild and replay cover both modes and the public client;
the reviewer subsequently confirmed all seven reviewed file hashes against
`55ad72493061b59363e846341380a9edce12a2de`, with no findings. No final finding
was waived. The separate audit records its own commands and exact scope.

## Reproduction

From the C1 upstream worktree, with the pinned Lean toolchain already installed:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped scripts/ci --diff
LEAN_NUM_THREADS=2 capped scripts/check-core-audit
LEAN_NUM_THREADS=2 capped lake env lean Tests/RelationalOutcomes.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose \
  GoLean Tests.RelationalContracts Tests.RelationalOutcomes Tests.GoCoreAudit
```

The existing core audit imports every GoLean module on disk and checks every
owned declaration, including generated/private declarations, against only
`propext`, `Classical.choice`, `Quot.sound`. Headline axiom prints are in the
facade client. Compare replay names/multiplicities with the GoLean source set
and the three named test modules. The installed toolchain is 4.32.2; exact
`leanchecker` replay is used, not the later `lake check` interface.

For frozen RD5 compatibility, follow the RD5 handoff's GoLean-only bootstrap
with the above frozen logic revision, copying the three request modules and
both `CompositionAdapters`/`ResidualAdapters`. Set the scratch GoLean path to
this checkout, build both adapters, then replay those five local modules.
Remove the disposable scratch after checking. No peer checkout is a build
output destination.

## Remaining limits

Whole-program all-outcome composition across validation, global setup, package
initialization, activation and final readback remains later work. C1 is not
program adequacy, full observer coverage, general locality or sequentialization.
`State` still contains machine control; the complete classification handles it
without clients splitting evaluator arms, but does not eliminate every machine
representation dependency. Iris/WP ownership and adequacy remain downstream.
Concurrency has its own worker and is neither awaited nor absorbed here.
