# Proposed punch list for the first release

2026-10-26 · [AGENT Codex]

Based on the [deep-clean review](2026-10-26_deep-clean-release-pass.md) of
`62bb461463d94c9eb4f3d003aa441db653bd77c3` and its five supporting reports.
**All entries are proposals and remain open.** This document grants no authority
to change release policy, edit the charter, merge, tag, push, or change baselines.
Product fixes were outside the review's read-only scope.

## First: repair concrete correctness and evidence failures

These are the reviewer's recommended prerequisites for releasing the affected
behavior with its present claims. They are not additions to the gate machinery.

| Item | Finding | Proposed change | Acceptance evidence |
|---|---|---|---|
| P01 | DC01: pointer identity | Give pointer equality/map-key comparison a canonical physical-location identity while preserving dynamic Go type identity. Audit adjacent identity uses; avoid a global erasure of type tags. | The complete converted-struct probe returns Go's `true`, `12`, `true`; add named-type, nested-field, array-field and distinct-allocation controls. Source differential, map lookup/delete and interface equality agree. Existing proof checks and corpus stay green against intentionally unchanged baselines, except deliberate new rows. |
| P02 | DC02: negative oracle status | Preserve compiler process status before interpreting diagnostics. Reject timeout, signal death, inability to execute and non-verdict exits. | Actual timeout-after-diagnostic and SIGKILL-after-diagnostic publish no PASS and fail explicitly; normal compiler rejection plus frontend rejection still passes. Existing negative corpus is freshly rerun. |
| P03 | DC03: seed allocation | Check seed type/value shape and materialization cost before allocating default values. Share or deliberately reconcile decoder/core budgets; account for nested types and the whole seed. | Tiny oversized seed fails quickly with a named structured error, including with zero fuel and unused cells. Small malformed value still fails by name. Valid cyclic seeds, references and at-budget controls work. No cap kill is counted as a refusal. |
| P04 | DC04: absent dedup proof | **Owner choice:** restore soundness against the live checker and observation definition, or withdraw the verified-checker claim and explicitly include the checker in the trusted executable apparatus. Update API docs, comments and diagnostic wording consistently. | If restored: theorem exists on the live build path, its statement covers the emitted claim, standard axioms only, replay/check and consumer-facing contract review pass. If reclassified: no active claim attributes output to a missing theorem; release trust description explicitly includes the checker. Old proofs at a tag are not current evidence. |
| P05 | DC05: upstream notices | Include the pinned goose MIT copyright/permission notice and map it to imported source. Inventory notices for copied raft and protobuf-derived code. Qualify the root Apache summary. | A source archive made from the proposed release includes required notices without `deps/`. Check against exact upstream revisions. Do not introduce a heavyweight licensing gate. |
| P06 | DC10: destructive output directories | Refuse populated unowned `--out` directories, or generate in a uniquely owned child. Clean only created paths. Cover runprobe and codeccheck siblings. | A foreign sentinel survives both success and failure, with and without `--keep`; empty/new destinations still work. A blocked deletion is reported, never silently ignored. Test only on wholly owned scratch. |

Suggested implementation grouping: P01 as a semantic arc; P02 and the process
status parts of P09 below as an apparatus arc; P03 as a seed-admission arc;
P05 as packaging. P04 requires a direction decision before implementation.
These groups are suggestions, not restrictions on a reviewer or engineer.

## Next: close admission and instrument gaps

| Item | Finding | Proposed change | Acceptance evidence |
|---|---|---|---|
| P07a | DC06 / FE-03: module syntax | Use a complete module parser or strictly validate every accepted directive/block in the supported subset. Refuse unsupported syntax rather than skip it. | Missing/duplicate module declaration, malformed require and unterminated block fail with named diagnostics. Valid supported files continue to lower. Match pinned Go's rejection status without assuming diagnostic text is identical. |
| P07b | DC06 / FE-04: Go patch requirement | Compare the complete minimum version, including patch, against the supported toolchain. Retain a separate test even if combined with P07a. | `go 1.26.99` refuses under go1.26.5; admissible patch floors within the current Go 1.26 language policy continue to pass. This does not widen support to older language versions. Cover prerelease policy explicitly if accepted. Do not silently float or download a new oracle. |
| P08 | DC07: observation protocol | Route observation text through strict parsing and validate value domains, including each byte being 0–255. | Duplicate status/output keys and unpaired surrogates return protocol error; `bytes:[256]` and other impossible values refuse. Valid equivalent observations still compare equal and genuinely different ones remain unequal. |
| P09 | DC08–09: raft verdicts | Validate scenario selection and positive iteration count; require at least one executed scenario. Validate both Go-oracle and machine process status in runprobe/codeccheck/tracereplay, including negative modes. Store exit status in resumed trace records; recompute or refuse old records without it. | Typo/zero/negative controls fail; actual selected scenario runs. Matching stdout followed by SIGKILL/timeout is red. An unrelated compiler/dependency/process failure is not an expected Go stop. A resumed matching observation without recorded status cannot pass. Normal ok and intended panic controls work. Then run the real dependency-backed harness when available. |
| P10 | DC18: choice-trace campaigns | Consume only this invocation's chunks, propagate summarizer/pipeline failure, and normalize relative/absolute output paths once. | Previous success cannot mask a fresh ERROR; stale malformed chunk is ignored as outside the run or rejected explicitly, never a green traceback. One/multiple jobs and relative/absolute destinations yield the same current-run account. |
| P11 | DC11: malformed blocked core state | Decide the public validity contract; propagate load failures through readiness, or enforce/document a valid-state precondition at the entry that owns it. | Missing/wrong channel cell returns a named refusal at the supported entry. A genuine blocked valid program remains deadlock. State clearly whether a decoded-source reachability regression is needed; none was demonstrated in this review. |
| P12 | DC12: broad Lean options | Remove broad warning suppressions, fix warnings, and narrow genuinely necessary resource or linter exceptions to declarations with justification. Obtain approval for any standing-rule exception. | Required build/checks pass; remaining exceptions are narrow and listed in the working-practices document if approved. Do not equate a suppressed warning with a fixed warning or raise global resource limits. |

## Make the release legible and reproducible

| Item | Finding | Proposed change | Acceptance evidence |
|---|---|---|---|
| P13 | DC13: release contract | Publish one current supported-scope and known-limits statement for this release. Distinguish model fidelity, lowering trust, theorem scope, test evidence and optional instrument coverage. Give the three release predicates separate true/false/unknown results. | A reader can tell which platform/version, features and observations are covered without reconstructing months of dated amendments. No zero-known-wrong-answers claim is inferred from the untriaged counter. The owner explicitly decides any new profile or criterion. |
| P14 | DC14: living docs | Update repaired `make`/seed/uintptr descriptions; correct BUG-132 references, retained pool-fact wording and contract counts; align the known sort-over-refusal disposition. Link to generated lists rather than copying counts everywhere. | Read README → overview → CLI → release in sequence against current code. Run their short examples. History stays history; current pages agree. No new enumerative documentation gate is needed. |
| P15 | DC15: dependencies | Give released raft subject/harness reproduction an exact dependency pin and documented protobuf prerequisites; label any separately floating research checkout. | Fresh setup resolves exact tracked revisions or stops naming the missing prerequisite. Source digests still catch drift; a successful wire pin is not described as fresh execution of raft. |
| P16 | DC16: existing remarks | Owner decides which existing human quotations remain public and which current passages should be paraphrased. | Agreed passages are changed without misattributing decisions or rewriting history. No private wording is copied into new review/fix records. |
| P17 | DC17: operational cleanup | Propose a shorter current charter; replace obsolete sandbox guidance; remove or explicitly externalize the retired fast-evaluator route. Document caps/cost for long optional instruments. | An ordinary clone has a usable documented command path. Current instructions are distinguishable from historical rationale. Any standing-rule edit gets owner approval. Preserve useful tests/fixtures; no indiscriminate artifact purge. |

## Revalidation and release decisions

**P18 — DC19, comparator locale failure (found in the fresh full gate):** replace
the locale-sensitive subscript range in `scripts/gen-contract:84` with a check
that works in both C and C.UTF-8 while retaining the intended name restrictions.
Distinguish a regex/validator error from an invalid name or stale contract.
Acceptance: `gen-contract --check` and the real comparator complete under both
locales, valid ASCII/subscript names pass, invalid names refuse. The original
full run's red speedbump remains a failure even if a diagnostic C-locale run
succeeds; a process-local workaround is not a source fix. Do not change the
machine-global locale or regenerate the contract just to hide the failure.

1. Add minimal regressions to the existing appropriate suites when repairing
   concrete bugs. Self-tests for scripts run when those scripts change. Avoid
   creating a separate check for every review sentence.
2. Follow the existing runtime-commit and merge checks. On this shared box,
   acquire the primary build lock for full builds/gates/check/comparator, use
   `capped`, and serialize heavy work. A killed or unavailable check is a
   failure, never evidence of success.
3. Run the full fresh corpus after semantic/admission/apparatus repairs and
   inspect each changed result and refusal cause. New counterexamples become
   tests. Do not re-pin a baseline merely to absorb an unexplained failure.
4. Re-run theorem axioms, kernel replay, comparator and relevant contract
   checks after trust-surface changes. A proof about the model cannot close a
   source-Go mismatch by itself. A missing theorem needs an explicit direction
   decision, not a weaker green label.
5. Obtain the owner's outside-sandbox claim-point checks in the form required
   by the current release procedure. The review's no-sandbox result is not
   that gate. Report the known nanoda/paranoid limitation honestly; this punch
   list does not waive it.
6. Request independent critical review of completed changes and disposition
   every finding individually: fixed with evidence, answered with a checkable
   reason, or explicitly deferred with the affected release claim narrowed.
7. Prepare the release record at the actual release candidate, including exact
   revision, toolchain pins, fresh row counts, check results and stated limits.
   Merge, release tagging and push remain separate explicit sign-offs.

The concurrent raft harness/codec differential could not run in this review
because the required protobuf module was absent offline. A network-enabled
operator must make the required dependency available before anyone claims a
fresh result for those instruments. No machine-global cache/configuration change
is proposed here; prefer project-scoped setup.

## Completion criterion for this punch list

Each DC finding has one explicit disposition with the claimed evidence and
remaining scope stated. No source bug is closed by prose alone, no absent
proof is closed by an unrelated green build, and no deliberately deferred
limitation disappears from the release contract. Lower-priority cleanup may be
deferred by name; this list is not permission to prolong the release indefinitely.
