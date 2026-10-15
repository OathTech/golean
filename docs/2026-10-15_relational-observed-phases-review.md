# RD8 observed phases: independent implementation review — 2026-10-15

The three requested semantic refinements and their frozen actual-caller applications check. I found no new semantic or acceptance blocker in this increment. This is approval of the bounded upstream phase increment, not a full replacement-interface landing verdict, a completed ordinary downstream uptake, or a waiver of the inherited implementation findings.

## Inspected inputs

The implementation is additive to I2 handoff `8bcaef3764257ed262a7801be2cf6484cab4dfaa`, in the owned `refactor/relational-surface-1013` lane. I inspected the three new `GoLean/GoCore/RelationalObserved*.lean` modules, the public facade import, both acceptance modules and the audit/reproduction instructions; I followed dependencies through the existing path/effect contracts, call boundary, activation, entry/return semantic views and actual downstream guarded call/history rules. Prior review verdicts were not correctness premises. Final immutable source identity is recorded in the addendum below.

The unchanged logic input is `3c9be98f8de86f04c4cec53d75490199718da066`, reviewed handoff `621316254d5a32c1489593ad0e7b8c26122df0e4`. My comparison against Git objects verified 137 original package files, including every original Lean source, byte-for-byte. Only the private Lake configuration and regenerated manifest were excluded. Both private acceptance sources equal their permanent experiment sources. The four actual-caller theorem headers (`hist_code`, `adequate`, `caller_prefix`, `outcomes`) equal the originals verbatim; only the three law parameters are discharged in the new surrounding declarations.

## Semantic assessment

`Observed.StorePath` specializes U1's `StorePathFor`; it does not infer observation silence from equal endpoint stores, empty labels, or endpoint call stacks. Each traversed source carries the conditional `Boundary.events = []` fact, its actual pick-free transition and terminal/init admission. `StoreEffectFor` similarly conditions its source policy on the actual pre/post operation relation. `OrderedWritesFor` exposes each intermediate write and store-preserving segment. Erasure keeps the earlier contracts, and path composition uses the shared carrier. A read fact is not carried into the post-write suffix.

The assignment laws are symbolic in identifiers, values, locations, environment and continuation. Preparation uses genuine variable/reference reads and the owned write uses `storeLoc`; its actual access label is retained. Interior write destinations and aliasing are unrestricted by distinctness or blanket well-formedness assumptions. Successful `loadRoot` remains the existing operation restriction on a read source. General read-only expression and pointer-RHS variants are provided, and the variable-variable request is a corollary.

Call entry is a general operand-list theorem, not an Identity-specific single-Boolean theorem. The argument traversal accumulates the supplied values in order and exposes the activation source separately. Lookup, non-method, arity and `LocalEntry` premises apply to the activation effect. `Enters` identifies the resolved function, exact supplied values and pre-store, and entails the actual transition/label. The zero-operand case begins at the eventful entry source with a reflexive preparation path; it is not incorrectly declared silent. Callee body behavior is unrestricted by the preparation policy.

Delivery exposes a `Boundary.Returns` before destination evaluation or writing. The readback is required only at the original store. Values are then held in the target/write controls, so later destination aliases cannot retrospectively change the return snapshot or require stale result reads. Both normal exit modes, empty/multiple results, repeated/interior destinations and arbitrary final continuations are supported in the stated declared-call domain. Result-slot validity remains an explicit semantic premise, derived from activation in the compiled consumer. No pending-defers claim beyond the existing `CallBoundary` representation is added.

I compiled an additional boundary test: quiet empty-sequence cleanup may end at a frame whose next step emits a return. This confirms that the final tail is not accidentally required to be quiet. The unchanged `pure_return_counterexample` remains compiled. Here “quiet” concerns public entry/normal-return events; it does not erase or claim emptiness of all access/output labels or all conceivable observations.

The public laws do not import Iris or the downstream request types. Their proofs contain machine constructors internally, but the request adapters and ordinary guarded call consumers do not need to reconstruct target plans, activation frames or return signals. The old erased APIs are unchanged, avoiding a stronger quietness premise on their earlier domain. Some existing phase proof structure is repeated in the refined implementation; the mathematical carriers and expression primitives are shared. I found no resulting inconsistency or correctness blocker.

## Checked consumer and dependency results

Independent Lean elaboration checked exact applications to `AssignmentQuiet`, `VariableEntryObserved`, `DeliveryObserved`, `CalleeTarget` and `CallerTarget`, with no remaining law parameters. The actual history/adequacy wrappers supply those laws to the original proofs and preserve symbolic Boolean input, exact `[call [v], returned [v]]` history, StringPlain/setup assumptions, fuel exhaustion and the original supplied tape and normal/panic witnesses.

Thirteen independent proof-value closure checks passed. Each adapter reaches its new public phase theorem. The caller reaches `caller_body`, `call_rule_value`, `History.update`, `RD8Acceptance.guarded` and `Frame.roots_valid`; it does not reach `identity_body` or `callee_acceptance`. Actual adequacy reaches both caller and callee acceptance, and actual outcomes reach `closed_program_outcomes_hist`. Thus logical contract assembly occurs outside the caller proof, rather than hiding a reopened callee implementation in it.

I additionally traversed both types and values from the five new roots `callee`, `caller`, `adequate`, `caller_prefix` and `outcomes`. None reaches any of the five inherited logic implementation parents or their five generated helpers. All ten named endpoints were verified present. This bounded dependency fact does not prove executed renderer correspondence or waive their findings.

Independent headline axiom reports for all nine `PhaseAcceptance` public results and the counterexample contain only `propext`, `Classical.choice`, `Quot.sound`. Focused kernel replay of exactly the three new public modules and `PhaseAcceptance`, `CallerAcceptance` passed, exit 0, each once. This is not a claim that I independently repeated the author's full CI, exhaustive audit or entire dependency replay; those remain separately recorded author evidence.

Two initial probe commands failed: first Lean rejected an output module outside its default root; then a guessed qualified name for `RD8Acceptance.guarded` was wrong. The corrected `--root` argument and actual global namespace passed. Those initial failures are not counted as checks.

## Findings and remaining obligations

No new implementation finding requires a source fix from this review. The semantic part of the relayed R1 blocker is discharged by the exact adapters and checked caller applications. Ordinary downstream installation and its result review still belong to logic. R2's ordinary unseq uptake is separate; the older I2 acceptance must remain a distinct immutable result, not be replaced with this package.

The implementation scan remains **FAIL: 21, unwaived**: sixteen upstream findings and five downstream findings. The ownership helper's proof-only diagnosis is bounded to its inspected kernel usage; the four Source renderer correspondences remain unresolved, as do the relevant upstream renderer issues. Standard axioms and replay do not establish compiler-selected executable-body correspondence. The inherited Memory warning and historical live **35 NOT-PUBLIC** failure remain separate; this review did not rerun live validation. Nothing here authorizes merge, push, live repin, global changes or peer writes.

The new phase interface is sufficient for the frozen clients, not an exhaustive quiet-expression or call-syntax calculus. General observation-sensitive body reasoning, ownership splitting, typing/layout, event projection and invariant assembly remain downstream. Full sequential replacement readiness and future concurrent/infinite adequacy are not established by this increment.

## Reproduction

Use the experiment README to recreate the frozen private package from the immutable Git input at the final upstream pin. All reviewer commands used `LEAN_NUM_THREADS=2`, `capped`, and a lane-private TMPDIR; no reviewer Lake build or peer write occurred. From that package, the focused replay is:

```sh
LEAN_NUM_THREADS=2 TMPDIR="$lane/.tmp/observed-phase-review" capped lake env leanchecker --verbose \
  GoLean.GoCore.RelationalObservedPath GoLean.GoCore.RelationalObservedPhases \
  GoLean.GoCore.RelationalObservedDelivery PhaseAcceptance CallerAcceptance
```

For exact target checks, import `CallerAcceptance` and use `example : REQUEST := PhaseAcceptance.assignment/entry/delivery` and the analogous callee/caller targets. For the eventful-tail check instantiate `Observed.empty_sequence_path ctx env` at continuation `⟨.frame [] env [] [] k.toMachine fid⟩`; the endpoint's public event projection is definitionally `[.returned ⟨fid, [], s⟩]`.

The dependency checks use a visited-name traversal of `ConstantInfo.value? (allowOpaque := true)` and `Expr.getUsedConstants`; the inherited-helper exclusion additionally includes `ConstantInfo.type`. `PhaseAudit` contains reproducible positive/negative proof-dependency checks and headline axiom reports. Source identity is reproduced by comparing each original archive member to `git show 3c9be98:experiments/2026-10-14_relational-codex/<path>`, excluding only private Lake wiring. Compare complete theorem headers up to the final ` := by`, preserving inner `let ... :=` expressions.

The sorted filename/NUL/content/NUL SHA-256 of the three new public modules, `GoLean/Relational.lean`, `PhaseAcceptance.lean` and `CallerAcceptance.lean` inspected and independently replayed is `90c3011f4d85aa2f685c2d389f05f52e0ad30bbbf8e793181c722e338182edef`. Disposable reviewer probes/logs are not permanent evidence and may be removed after this report is committed.

## Support-edit and draft-stage follow-up

I inspected the added `scripts/mem-callsites.tsv` row for `OrderedWritesFor` and independently reran `scripts/check-mem-callsites`: PASS, 89 rows. The classification is justified: the raw `storeLoc` occurrence belongs to an inductive Prop premise, while the delivery proof constructs actual `Step.storeStep` through emitting `storeTarget`/`Mem.store` with its write label. The row does not exempt an executable non-emitting access or change the checker. The initial missing-row speedbump was a failure and is repaired by this explicit inventory update.

I also read the draft `docs/2026-10-15_relational-observed-phases-stage.md`. Its bounded semantic/acceptance claims and separation of ordinary downstream uptake, inherited implementation failures and broader landing obligations match the inspected result. The validation section was still awaiting final author results at this inspection; no full-CI completion is inferred from the draft. All six independently checked Lean source files still match the recorded digest.

## Final immutable binding and validation inspection

This review is bound to implementation **`82353580814b66399cdc472a4c4edf9044d0c097`**. The six independently checked Lean files match both that commit's blobs and the recorded review digest. I independently compared all 4,398 final source/configuration freeze entries with the immutable archive and worktree: all match. Comparing the pre-inventory and final manifests confirms that the only validation-period source/configuration change was the disclosed memory-inventory row. The worktree was clean at this inspection. My first manifest comparison accidentally used the final rather than pre-inventory manifest; the corrected comparison of the two explicitly named manifests passed.

I inspected the completed stage and reproduction commands, the author CI summary, new audit output, fresh-replay log and alias result. The CI log reports PASS/902 seconds, 113 upstream module replays, 396 eval tests and complete 4,025/415-row baseline comparisons without regression; it correctly retains the initial memory speedbump RED and dirty-worktree certification. The separately checked inventory repair and final blob binding account for that failure and source state; the report does not pretend the initial speedbump was green. The full-CI process exit is author-reported evidence, not a rerun by this reviewer.

I independently recomputed exact built/replayed module multiset equality from the author's logs and actual private build outputs: the new package has 113 upstream + 131 local + 206 dependency modules = **450**, and the separate older I2 package has 113 + 123 + 206 = **442**, with no duplicate or missing built module. I also independently compared the new audit's 21 finding names with the committed I2 inventory: the sets are identical. The fresh `PhaseAudit` log uses the supported single-root form, and the alias output retains exactly `{-2, 7}`, eight leaves, 226 certificate nodes and 231 edges. These are inspections of the author's whole-package evidence, distinct from my independent five-module replay and probes above.

The final stage distinguishes checked semantic discharge from ordinary downstream uptake and preserves the unwaived trust findings. The README retains independent frozen packages and gives the corrected single-root fresh-replay command. No new finding arose from this final inspection. The bounded upstream implementation is accepted by this review; full landing, live migration and unresolved renderer correspondence remain outside that acceptance.
