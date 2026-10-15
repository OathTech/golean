# I2: combined O1 and U1 development integration

[USER] 2026-10-15: integrate reviewed O1 and U1 in the existing owned lane;
check the unchanged frozen RD8 consumers together and their observation-policy
compatibility; obtain fresh independent review. No main merge, push, live repin,
peer writes, operational refactor or new main rebase.

## Immutable delivery

Combined implementation: **`4731d491999e113e5016ad975d1747614d100bd4`**.
The [fresh independent review](2026-10-15_relational-o1-u1-integration-review.md)
is saved verbatim. It found no new integration correctness defect and independently
bound all 4,385 tested source hashes to the implementation's committed blobs.
Both the author and reviewer verified the original 4,363-entry freeze is unchanged.
After setting only private pin metadata to this revision, all three acceptance
packages build successfully at the clean committed candidate (RD8 446 jobs;
RD6 and RD7 426 each). No source change or replay-input replacement occurred.

The separate implementation scans remain **FAIL: 16 upstream / 21 combined**,
all open and unwaived. This is an independently reviewed development integration
pin, not permission to land the full replacement interface. Immutable audited
inputs and historical experiment branches remain preserved. No main merge,
push, live repin, peer-worktree write or global change was performed.

## Immutable inputs

| Input | Pin |
| --- | --- |
| O1 implementation | `56168ed59da4c8972169bcaee778b767f35c6005` |
| O1 review/handoff | `3f39150d8e360b8ac4a2b13aa10a5200b627ba40` |
| U1 implementation | `82a2ff3139053c2a23d97cc90d8f21bb2400d96f` |
| U1 review/handoff | `ce0daf9f8dc7ff24e050becd1a1b58e34e144f93` |
| Common I1 implementation | `5d8e53e9f1a046fb645fce49901de714591e0819` |
| Historical main baseline retained | `31a6069d9dd457e1adb0b3a6060713002ab50480` |
| Frozen RD8 implementation | `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42` |
| Frozen RD8 reviewed handoff | `eba7d3bdaa7786cfc6daad949cd3217185e2c867` |

Own lane: `.claude/worktrees/relational-surface-1013`, branch
`refactor/relational-surface-1013`. Immutable input refs are retained under
`refs/integration/i2/o1` and `refs/integration/i2/u1`. U1 implementation and
review were applied to the O1 lane without conflicts. The two shared files
(`GoLean/Relational.lean` and `docs/relational-interface.md`) combine both
sets of additions. No conflict resolution or theorem rewrite was necessary.

## Combined interface and exact acceptance

All original O1 and U1 public theorem bodies remain byte-identical to their
reviewed inputs. The facade imports both. The runtime, detector, frontend and
drivers are unchanged against I1. `RelationalObservation.lean` differs only in
its O1 documentation; the other existing-source changes are facade imports and
the new-test import in `Tests.GoCoreAudit`. No Iris, Plan, memory skeleton or
legacy observer enters public GoLean.

The joint client is outside the default build at
`experiments/2026-10-15-o1-u1-integration/`. It imports the original private
O1 and U1 adapters, copied byte-for-byte into one frozen RD8 package.

| Exact requirement | Adapter/use |
| --- | --- |
| `Observed.EventAgreement events` | Unchanged `RD8Acceptance.agreement`; joint `I2.agreement` |
| Frozen prefix and guarded observation consumers | Unchanged `RD8Acceptance.prefix_history` and `.guarded` |
| Original observed adequacy headers | Unchanged `ObservationAcceptance.lean`, imported into the joint closure |
| `Sweep.SimulationLaw` | Unchanged `U1RD8.simulation`; joint `I2.simulation` |
| `Sweep.GuardedTarget` | Unchanged `U1RD8.closed_guarded`; joint `I2.guarded` |
| Reached-source policy compatibility | `I2.quiet_iff`, `.source_paths`, `.source_traversal`, `.plan_source`, `.projected_source` |

[AGENT] 2026-10-15: use the existing exact private adapters and a small joint
policy bridge, with no new public API. An identity observer retaining the full
entry/return payload proves that frozen universal `Quiet` is equivalent to
emptiness of O1's actual `Boundary.events`, for every supplied store. The proof
uses O1's checked all-state agreement; independent event completeness remains
O1's structural activation-stack proof.

`source_paths` and `source_traversal` consume the actual U1RD8 read/read/add
paths and ranked traversal. `plan_source` handles every non-final residual
plan source, including scheduler, binder write, allocation and completion/glue.
Its final-control inequality explicitly excludes the arbitrary following tail.
The bridge imposes no silence premise on unrelated transitions. This is policy
compatibility, not a new theorem reconstructing a residual plan after every
actual prefix or a new whole-segment history theorem.

The audit checks actual proof bodies: O1's prefix/guarded consumers use its
agreement; U1's simulation/guarded consumer uses the shared ranked traversal,
carried source paths, scheduler coverage, binder effects, real entry allocation
and completion paths. The joint policy conversions consume those original
proofs. Exact targets and their original remaining premises are retained.

## Limits and findings

All sixteen upstream implementation findings remain open and unwaived at the
individual dispositions in the I1 stage. The five additional frozen customer
findings remain individually open in the U1 stage/review: `pathTags_persistent`
and the four ScalarTy/FieldTys renderer implementations. The combined closure
must be scanned freshly; passing standard-axiom/kernel checks does not waive
implementation findings.

Retain the inherited Memory unused-variable warning and recorded live
**35 NOT-PUBLIC** failure. No live test or migration is claimed. The frozen
actual observed caller was unfinished; upstream policy compatibility does not
complete its downstream ownership proof.

Executed renderer correspondence remains open as specified in O1's stage.
U1 remains restricted to deterministic read-only expression occurrences with
fresh binders, ranked graphs, no guards/regions, phase-2 stores or internal
choices. Actual labels, scheduling picks and intermediate states remain
available; labels are not equated across schedules. The alias control's
`{-2, 7}` outcomes, output-order and allocator-bound controls are separate.
Richer effects, allocation transport, concurrent/infinite adequacy and the
full replacement landing remain later work.

## Validation and independent review

All heavy commands used `capped`, `LEAN_NUM_THREADS=2`, lane-private build and
temporary state, exact immutable customer inputs and explicit read-only
dependency seeds. Three exact independent customer dependency clones per
package have no alternates or writable cache links; the GoLean dependency is
this owned candidate root. All original frozen Lean sources are unchanged.

- Full `scripts/ci --diff`: **PASS**, 1,394 seconds, all gates and speedbumps.
  Cold build: 255 jobs, warning-free. Exact upstream kernel replay: 110 modules,
  37.50 seconds, peak RSS 4,694 MB. Core totality/exhaustive axiom check passes;
  interpreter tests: 396/396. Frontend/boundary/declaration checks and the
  whole-tape scheduler control pass. Fresh differential: 4,025 cases,
  3,767 PASS and 258 tracked FAIL; fresh negative: 415/415 PASS. Full baseline
  comparisons show no regression or cause drift; baselines unchanged.
- Frozen joint RD8: **PASS**, 446 jobs, only the inherited Memory warning.
  Original aggregate: 6,406 local declarations, standard axioms only (the
  actual combined-environment count, not copied from earlier evidence).
  Reused exhaustive closure audit: 26,808 declarations; supplemental audit:
  120 declarations across O1/joint adapters and original example modules;
  standard axioms only. All 14 proof-body dependency assertions pass.
  Exact replay: **PASS**, 439 modules, once each: 110 GoLean, 123 local,
  174 Iris, 18 Batteries and 14 Qq. Every upstream/local source has an output.
  Additional `leanchecker --fresh --verbose JointAudit`: **PASS**, exit zero;
  the complete imported environment is reconstructed from empty.
- Frozen RD6: **PASS**, 426 jobs. Original aggregate/acceptance audits:
  5,940/5,943 local declarations, standard trio. Original program header keeps
  explicit downstream `InitAssembly`; all three original C2 clients compile.
  Exact replay: **PASS**, 417 modules (110 upstream, 101 local, 206 dependency).
- Frozen RD7: **PASS**, 426 jobs; 6,058 local declarations, standard trio.
  Closed original program acceptance and RD5 Add/Alias/Pair/Set/Keep regressions
  remain in the unchanged aggregate. Exact replay: **PASS**, 420 modules
  (110 upstream, 104 local, 206 dependency).
- All 125 RD8, 106 RD6 and 113 RD7 original package files were compared with
  immutable git objects; only generated Lake wiring/manifest and private pin
  metadata may differ. Both O1 adapters and all four U1RD8 modules match their
  reviewed inputs byte-for-byte. No live source or uncommitted peer input used.
- U1 symbolic/output/allocation controls: **PASS**, 79 jobs; exhaustive audit
  20,143 declarations, standard trio. Implementation scan: **FAIL, 16**.
  Exact three-module replay passes. Fresh alias explorer retains exactly
  `{-2, 7}` (eight leaves); its certificate passes (226 nodes, 231 edges).
- D1 archived-C1 preservation control: **PASS**, complete output byte-identical.
  D1 build: 93 jobs; exhaustive audit: 22,555 declarations, standard trio.
  Implementation scan: **FAIL, 16**, exactly the U1 finding-name set. Exact
  replay passes for eight D1 modules plus five relational/audit clients.
- O1's twelve headline reports and unchanged C2 constraint's four headline
  reports pass with standard axioms. The latter client also compiles to a
  private output and its exact one-module replay passes.
- The combined implementation scan is freshly **FAIL, 21**. Exact name-set
  comparison finds the same upstream sixteen plus precisely the five frozen
  downstream declarations listed in the U1 review. No finding is waived.

The first joint compilation failed in the identity-observer list proof because
simplification unfolded the induction hypothesis's observer argument too early;
the corrected proof rewrites the list tail first. That failed run's generated
`sorryAx` output is not a checked result. The initial audit helper also failed
from an inferred counter type; explicit `Nat` fixes it. Subsequent builds,
axiom/dependency checks and exact replay pass without either failure. No frozen
consumer or public theorem was changed to make these checks pass.

Fresh independent review found no new integration correctness defect. It
independently compiled the joint client and a final-tail countercontrol,
checked exact consumer applications and substantive proof dependencies, and
replayed eight modules. Its expanded closure scan covers 26,922 declarations
including reviewer controls/examples, standard axioms; **FAIL, 21** inherited
implementation findings. It independently matched all three full replay
inventories; full CI remains inspected author evidence, not a second CI run.

CI correctly certifies the dirty tested tree, not an exact-commit invocation.
The original 4,363 code/config/script/corpus hashes remain unchanged; the
complete source freeze adds the acceptance clients (4,385 hashes). The handoff
binds these to the immutable implementation commit; the original dirty-tree
qualification remains explicit.

Reproduction: [joint acceptance README](../experiments/2026-10-15-o1-u1-integration/README.md),
with the existing I1/C2 and U1 recipes it names. Conclusions and commands are
retained in git; disposable build state and logs are removed after completion.
