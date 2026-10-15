# Independent I1 integration review

Scope: unrestricted source, semantic contracts, trust dependencies, exact main preservation and customer/concurrency compatibility. Inputs are refs/integration/i1/{main,c2-handoff,d1-handoff}; reviewed immutable integration implementation is 5d8e53e9f1a046fb645fce49901de714591e0819. All 122 saved reviewed Lean-source hashes match that commit, and recorded main is its ancestor. Reviewer outputs are confined to .tmp/i1-review.

## Finding I1-R1 — stale public scope/acceptance descriptions (low; fixed)

The interface guide described an initial small-demo surface and said exact RD6 acceptance was still being checked, despite the completed C2 acceptance. The author replaced those claims with the developing finite-run interface/unfinished full replacement threshold and immutable-C2 acceptance status. Independently inspected both edits; fixed. After RD7 became available, the guide also correctly separated the frozen RD6 assembly premise from RD7's now-closed assembly. No semantic change.

## Independent source results

- Compared every path changed by main since merge-base(main,c2-handoff) against current files. Only CLAUDE.md, changelog/20d3946d-WINDOW.md and scripts/ci differ from main. Their deltas preserve main's checks and additions, while retaining the authorized old equation API retirement. Frontend, CLI, baselines, corpus, Lean pin, escape scan and kernel replay script are byte-identical to main.
- All GoLean/GoCore/Relational*.lean and Tests/RelationalProgramOutcomes.lean are byte-identical to preserved C2. All three D1 modules and every concurrency experiment Lean source are byte-identical to D1.
- Inspected full-label Transition/Run closure, append/split/realize, uniform StorePath/StoreEffect and OrderedWrites. No termination premise was introduced into general steps/prefixes. Effects stay individual, labels/choice records are retained; path facts do not grant read stability under interference. Local terminal outcomes remain explicitly sequential.
- Inspected unrestricted Coverage/Realization and phase_projection: arbitrary inputs remain quantified; phase projection retains the exact tape and separate full budgets. The narrowed validated-entry corollary does not replace unrestricted outcome coverage.
- Inspected D1 actual shadow updates, order/lookup invariants, successful detector prefix folding, disjoint-write read reconstruction, scheduler boundary reuse and unconditional pre_pair_rejection. Exact key inequality is not confused with memory separation; detector success remains a premise.
- Independently inspected pinned Lean 4.32.2 deriving/Ord source: constructor ordering and lexicographic field order match locComparisonStep, with trailing eq. The replacement satisfies those equations; equality with the former opaque constant is still not a kernel theorem.
- git diff --check passed at source review time.

## Independent compiled results

- Re-elaborated LocationOrder, ShadowOrder, ShadowHistory, RelationalProgramOutcomeSound and GoLean.Relational into reviewer-owned outputs. Exact kernel replay passed with precisely those five names, once each. Imports came read-only from the author build; this is not an independent full dependency rebuild.
- Independently rebuilt all eight Concurrency modules into reviewer-owned outputs and replayed exactly those eight modules. Both selected executions, reusable step/effect/read laws and unconditional reached-state rejection compile. The retained audit reports 21,777 declarations with only standard axioms and a separate implementation-scan FAIL with 16 unwaived findings.
- Independently extracted verbatim ProgramRequests from frozen logic bbb372e2 and compiled direct assignments of phase_projection and unchanged initInvocation. Exact two-module replay passed, with only standard axioms.
- An independent facade-wide audit checked 19,127 GoLean declarations: only propext, Classical.choice and Quot.sound. All 16 partial-implementation names exactly match the individually open D1 rows. No new unsafe, extern or implemented_by declaration was found by that scan. This is an imported facade scope, not all repository tooling.
- An independent definition-value walk reaches Ty/GoValue/Expr opaque renderer endpoints from stepFn, stepMulti and runProgramM and none from raceUpdate. It stops at opaque endpoints and therefore does not certify their executed bodies. Exact executed diagnostic/printing correspondence remains a load-bearing obligation; the green mathematical axiom/replay results do not discharge it.
- Regenerated the old deriving-Ord algorithm on an isomorphic Loc datatype and compared it against the new comparator on 228 root/nested-field/index locations (51,984 ordered pairs). All matched, including differing static type tags, empty/Unicode names and negative indices. This finite control is not equality to the old opaque constant.
- The first reviewer scratch audit failed to elaborate because two local variable types were ambiguous; adding Nat/Bool annotations corrected it. A clone-identity probe also initially used capitalized Iris/Batteries keys instead of the actual lowercase JSON keys; the corrected probe passed for every clone. These were reviewer harness failures, not production failures.

## Reproduction

Use LEAN_NUM_THREADS=2, capped and a TMPDIR under the review scratch. Re-elaborate the five modules above with `lake env lean -o <private-root>/<module-path>.olean <source>`. Populate missing dependency files in that private root with read-only links to the completed author build, prepend it to LEAN_PATH inside `lake env`, and run `leanchecker --verbose` on exactly those five names.

For concurrency, compile Constraints, Reuse, Fixture, Certificate, Example, Synchronization, Obstruction and Audit in that order, using `--root=experiments/2026-10-14-concurrency-compatibility` and private output paths. Run `leanchecker --verbose Concurrency` and compare its output-name multiset with those eight names. Audit.lean reproduces the exhaustive imported-project axiom and separate implementation results; compare every reported finding to the D1 table.

For RD6, extract ProgramRequests.lean directly with `git -C /home/mike/projects/golean-logic show bbb372e2b97eec663f55a01ee4993f98be829e1b:experiments/2026-10-14_relational-codex/RelationalCodeX/ProgramRequests.lean`. Compile it and a facade client assigning `ProgramExecution.Correspondence.phase_projection` to `RelationalCodeX.C2.ProgramPhases`, and `RelationalCodeX.C2.initInvocation` to its original proposition. Replay both.

The maintained I1 reproduction document covers the author's full CI, D1 and frozen consumer checks. Reviewer logs/builds remain disposable, not committed evidence.

## Exact frozen customer results

The RD6 private package preserves 104 of its 106 original files byte-for-byte from bbb372e2; only pins.json and lakefile.toml have the intended private configuration changes. The RD7 private package preserves 112 of its 113 original files byte-for-byte from f314a4f7; only pins.json changes, and lakefile.toml is unchanged. All four clones per package are tracked-clean, at their prescribed pins, without root symlinks or object alternates. Both GoLean clones are at the reviewed integration commit.

- RD6: independently rebuilt C2Adapter, C2Acceptance and OriginalAcceptance, using read-only author imports. The wrapper's exhaustive audit reports 5,943 local declarations with standard axioms. Exact three-module replay passed. The two frozen consumers retain all original premises; the original-program wrapper retains its explicit InitAssembly parameter.
- RD7: independently compared the actual original theorem header from logic 14cef5e to ProgramAcceptance.lean at f314a4f7. After excluding the changed theorem name, bytes agree (SHA-256 9977c1891dcee16c675546265f9a411ed4adedc666b676fb34e537032f82ccec). Generated a separate client from that original text; it compiles against the integrated closed root without assembly or pending-law parameters.
- Independently rebuilt all six new RD7 proof modules: SequencedAdequacy, ProgramSupport, ProgramBoundary, ProgramAssembly, ProgramAdequacy and ProgramAcceptance. An independent audit checked all 6,058 local declarations, standard axioms only, and all eight proof-body dependency edges described by the immutable RD7 stage. These include the closed root's actual dependence on assembly/C2 phase projection/RD6 local adequacy, assembly's dependence on one-world sequencing/actual init adequacy/InitInvocation, and local/init adequacy's dependence on C1 main/init coverage.
- Exact eight-module replay passed for those six rebuilt RD7 source modules plus the independent original-header and audit probes. These use read-only dependency imports; no independent rebuild of all Iris dependencies is claimed.

For reconstruction, follow the I1 private-package setup at the same two frozen inputs. Re-elaborate RD6's three clients into separate output roots and replay their exact names. Re-elaborate RD7's six modules in the order listed above. Extract the original header from 14cef5e's packages/golean-iris/GoLeanIris/Logic/InitProgram.lean, rename the theorem, and prove it by applying the closed root with its original arguments. Traverse declaration proof bodies using value? (allowOpaque := true)/getUsedConstants for the eight recorded edges; select local declarations by defining module for the exhaustive audit. All commands use the same cap, two threads and lane-local temporary directory.

## Author validation inspected independently

Inspected fresh CI log: PASS in 1,233 seconds, 226 warning-free build jobs, exact replay of all 96 GoLean modules, core audit, 396 interpreter tests, frontend/boundary checks, 4,025 native rows (3,767 PASS / 258 tracked FAIL), 415 negative cases, no baseline/cause drift, all speedbumps green. This is inspected author evidence, not my own full CI/differential rerun. Precommit DIRTY metadata remains honestly identified; the reviewed implementation matches the source checked before commit.

The author reports both frozen package builds PASS, 412 jobs each. The inherited Memory.lean:1625 unused-h warning remains open, as does the recorded live 35 NOT-PUBLIC failure. This review does not rerun or repair the live gate. The author's full replays exited zero. Independently compared complete replay-name multisets with built module inventories: RD6 exactly 403 (96 GoLean + 101 local + 206 dependencies), RD7 exactly 406 (96 + 104 + 206), each once. Independently verified outputs for every GoLean/local source. These full replays are inspected author evidence; the separate limited replays above were run independently. The final reproduction guide agrees with these inputs, counts and commands.

## Assessment

No new semantic integration defect found. The documentation finding is fixed. The bounded integration preserves current-main behavior/checks, exact C2/RD6 contracts, D1 detector laws and selected executions, and now the unchanged closed RD7 acceptance. The independent checks and inspected full validation support completion of this bounded I1 development checkpoint.

All 16 inherited implementation findings remain open and unwaived. The result does not establish full interface replacement, general observation completeness, locality/unseq laws, whole-library migration, all-schedule safety, fairness or infinite-run adequacy. No merge/push authorization or waiver follows from this review.
