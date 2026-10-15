# D1 independent review and dispositions

Fresh reviewer: `detector_review`, started without the implementation
conversation. The brief supplied the charter, baseline, source paths and
private build setup, with unrestricted scope and no prescribed verdict.
The following is the review returned verbatim before immutable identity
verification. Final identity verification is recorded below when completed.

## Review

Reviewed the D1 candidate against audited C1 `55ad72493061b59363e846341380a9edce12a2de`, the supplied charter, and the historical experiment/review. Review covered the tracked changes and all five new files. The candidate was still uncommitted above carry commit `6f27dc09103e62624c05c9b9f4b0d7ee04764f29`; immutable identity verification remains pending.

I found no defect in the new comparator, shadow-history laws, or unconditional negative control. The behavior-preservation argument is credible within the charter’s permitted source-derivation approach. It does not establish kernel equality to the former opaque constant, and the documentation correctly preserves that distinction.

Findings:

1. **Low — inaccurate individual rendering-helper descriptions.** The original disposition table in `docs/2026-10-15_relational-detector-contracts.md:154`–`:162` misidentified some generated helpers by their enclosing instance name. For example, `instReprField.repr_1._unsafe_rec` and `instReprMethod.repr_1._unsafe_rec` both take `Declaration.Ty`. Each of the three generated families has `_1 = Ty`, `_2 = Field`, `_3 = Method`. Accurate roles matter because the charter requires individual, checkable dispositions. **Fixed during review:** I inspected the corrected table and independently checked all nine declaration types.

2. **Low — stale opacity description.** `experiments/2026-10-14-concurrency-compatibility/Concurrency/Synchronization.lean:86` still described the retained shadow state as including “the opaque ordering,” contradicting D1’s replacement. This is a comment defect, not a theorem defect. **Coordinator reports fixed; final identity/fix verification pending.**

Supported conclusions:

- The location laws cover arbitrary finite recursive locations, including field type/name components and signed indices. The shadow-key encoding checks the existing derived constructor/component order.
- Replacement and unrelated-key retention concern the actual `shadowSet`. Strict ordering implies uniqueness, is preserved through detector operations, and is established from the empty detector along actual checked prefixes.
- Retention requires exact key inequality, not non-overlap. The prefix theorem preserves detector-success premises and handles attributed events and HB actions.
- `pre_pair_history` applies the general prefix law across the actual intervening 16 steps. `pre_pair_rejection` then proves the actual negative detector control unconditionally using the retained conflicting history.
- Both original positive executions retain their 25/38 iteration driver statements, output, scheduling records, attribution and detector checks. Their supplied-entry-state and selected-schedule scope remains explicit.
- The former conditional countermodel is correctly retained with an impossible premise; it is not presented as a historical runtime bug.
- The remaining 16 implementation findings remain visible and unwaived. Their dispositions do not claim general rendering or derived-expression-equality adequacy.

Independent validation:

- Re-elaborated `LocationOrder.lean`, `ShadowOrder.lean`, `ShadowHistory.lean`, both positive example modules, and `Concurrency/Audit.lean` using `LEAN_NUM_THREADS=2 capped lake env lean`. All succeeded.
- Audit: standard-axiom check **PASS**, 21,517 declarations; implementation scan **FAIL**, 16 findings. Printed headline dependencies contained only standard axioms.
- Inspected the pinned Lean 4.32.2 derivation handler and regenerated the old derived comparator. Its constructor/component equations match `locComparisonStep`.
- Independent executable controls compared regenerated old/new comparators over 171 locations and 855 keys, all pairs, plus three insertion/replacement sequences checked after every insertion. All matched. These are supporting finite controls, not archived-baseline or universal equivalence proofs.
- Inspected the actual detector, prefix and certificate definitions, rendering-helper declarations and diagnostic call sites; `git diff --check` passed.
- I did not independently rerun archived-C1 preservation, full CI/differential testing or kernel replay. Those remain coordinator evidence to complete and report.
- No files, refs or shared state were edited.

Overall: the scoped D1 result is supported by the reviewed source and independent checks. Completion still requires the pending immutable-candidate verification and charter-required final validation. This review supplies neither merge approval nor a waiver of the remaining implementation findings.

## Dispositions

1. **Fixed:** every rendering-helper row now identifies both its actual
   argument type and its generated family. The reviewer independently
   verified all nine types and the corrected rows.
2. **Fixed:** the `transfer_boundary` comment now says that the detector's
   actual shadow state is retained, without the obsolete opacity claim.
   This changes no statement or proof.

All 17 baseline implementation findings are individually dispositioned in
[the stage record](2026-10-15_relational-detector-contracts.md).
The 16 unresolved findings are raised there explicitly and remain unwaived.

## Final identity verification

The following is the reviewer's final verification, verbatim. The final
handoff commit adds this review and updates only the stage documentation,
including the clarified explicit-list reproduction command; implementation
code remains exactly the identified commit.

Verified implementation commit `9c6efcfcf9dc6f4b96cf6b2d8bb052f1fa4d9124`. Its implementation matches the reviewed candidate, with the reported comment correction and expanded documentation. The tracked worktree is clean; only the pending review record is untracked. `git diff --check` passed.

Both review findings are fixed:

- The disposition table correctly identifies all nine rendering helpers’ argument types and generated families.
- `transfer_boundary` now describes retained actual shadow state without the obsolete opacity claim.

The recorded review reproduces my response verbatim. Its individual dispositions preserve the findings’ meaning.

I inspected the coordinator’s final validation evidence:

- Full CI/differential **PASS**: 3,989 rows, comprising 3,749 PASS and 240 unchanged baseline FAIL; 405 negative cases and 396 interpreter tests passed. All speedbumps passed.
- Experiment build and standard-axiom audit **PASS**: 21,517 declarations. Implementation scan remains **FAIL**, with 16 explicitly unwaived findings.
- Archived-C1 preservation controls report byte-identical output.
- Kernel replay covers the 105-import aggregate’s complete closure and eight separately replayed entry modules. I independently checked that every separate entry’s project imports are covered by the aggregate. The coordinator confirmed successful command exits and clarified that the eight-module replay used an explicit list; the disposable entries file containing only `Main` belonged to the additional fresh replay, not the coverage run. The initial aggregate-construction failure is disclosed and not counted as success.

These final runs were inspected, not independently rerun. My earlier independent elaboration, audit and executable comparison checks remain applicable.

No additional findings. The reviewed implementation supports completion of the scoped D1 detector-contract result. The old opaque-constant equivalence limitation, selected-execution scope and 16 remaining implementation findings remain explicit. This assessment provides neither merge/push authorization nor a waiver of those findings. No files, refs or shared state were edited.
