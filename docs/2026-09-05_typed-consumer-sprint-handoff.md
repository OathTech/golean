# Typed-consumer sprint handoff

## Authority and state

[USER], 2026-09-05: K1–K5 approved, with K4 clarified: merges to main
always require user approval; agents may integrate feature branches under
standing user approval. The [charter](2026-09-05_typed-consumer-sprint-charter.md)
records the exact ruling. This sprint has standing internal integration and
independent-review approval, but no approval to merge to main or push.

[AGENT] Status: **IN PROGRESS — BOOLEAN FOUNDATION**, updated 2026-09-06.
No full numbered outcome is complete. Main remains clean at `47195683`.
The sprint integration branch is `typed-consumer-sprint`, currently based on
`a392fab0` (reviewed static admission integrated); the current helper work is
described below and will be bound by its own evidence record.

## Required outcomes

| Outcome | Status | Next evidence |
|---|---|---|
| O1 typed Boolean contract | Static judgment/checker reviewed and integrated; storage/setup increment under validation | Structural control invariant, all-successor preservation, progress; exact generic initial bindings/values and driver readout |
| O2 typed recovery customer | Pending | O1 foundations, shared recovery/call contracts and second fixture |
| O3 evidence/reviews | Fresh preflight gates passed; static admission and candidate runtime statement reviews complete | Seal supplementary whole-corpus observations/choices; review helper implementation and final integrated contracts |
| O4 B7/I1 | Pending | Reviewed O1 contract; pure representation correspondence kept separate from I1 |
| O5 closing branch/packet | Pending | All mandatory outcomes, final gates, final independent review |

## Decision ledger

- K1–K5: [USER] APPROVED, 2026-09-05, recorded in charter §2.
- [AGENT] Start with independent statement review in parallel with executable
  preflight and local study of Boolean environments/setup. Do not begin B7
  edits until the initial typed contract has a concrete reviewed shape.
- No critical issue has yet been identified. No additional user decision is
  required to begin the authorized work.

## Evidence and continuation

The draft's link/anchor and whitespace checks passed; no Lean sources changed
in drafting. Runtime results in the prior A3 handoff are historical and must
not be reported as fresh sprint preflight. Record commands, exact tested
sources, toolchain pins, logs, failures and evidence hashes here as they run.

## Live lane state (2026-09-06)

- Integration: `.claude/worktrees/typed-consumer-sprint`, branch
  `typed-consumer-sprint`, tip `a392fab0`; coordinator owns BooleanStore,
  generic setup and integration documents. The helper increment passed the
  expanded interface audit, ordinary CI, A1 and A2 (fresh artifact, 3/3
  differentials), and independent implementation review. This is not yet a
  complete O1 runtime invariant. See the
  [helper claim ledger](2026-09-06_boolean-storage-setup.md).
- Static typing: `.claude/worktrees/typed-boolean`, branch `typed-boolean`;
  reviewed static increment `c7a439f7` is integrated, with 38 kernel tests,
  whole native artifact equality and 3/3 differentials. The agent now owns
  structural control typing, preservation and progress in that worktree.
  Its runtime modules now elaborate, including all-successor preservation and
  bounded run safety/readout with choices unchanged; source integration,
  final dependency audit and independent implementation review remain owed.
- Preflight: `.claude/worktrees/typed-preflight`; fresh full CI differential
  passed at `10fefeb3`: 3598 executable cases (3353 PASS, 245 known FAIL),
  394 negative Go-oracle checks, 202 eval checks. Existing admission,
  interface, A1 and A2 gates passed. One slow certificate is explicitly
  cached. Supplementary complete observation/choice capture is being sealed.
- Statement review: `.claude/worktrees/typed-contract-review`, `71183a62`,
  integrated. Kernel/Go counterexamples and candidate-contract review;
  this is not final implementation signoff. That reviewer now owns a separate
  narrow Unicode/newline panic repair in `typed-panic-rendering`, to receive
  independent implementation review before integration.

The [runtime design](2026-09-05_boolean-runtime-contract-design.md) records
candidate statements, constructor obligations and actual-vs-static context
issues. `seqCont` declaration splicing was found during review and corrected
in the static design before its checker proof was finalized.

## Investigations and existing authority

- O2 abort rendering: valid Unicode/newline/invalid-UTF8 string payloads can
  reach abort but be refused by the current renderer. The reviewer preserved
  kernel and Go witnesses. A separate K3 repair preserves the existing
  first-line observation policy for valid UTF-8/newlines. Invalid bytes remain
  under investigation against existing R-1 authority and the current String
  terminal representation; no new policy has been selected.
- O2 equal recovered/repanicked string payloads: rendering refuses the
  boxing-identity case (existing BUG-004). **Dated correction, 2026-09-06:**
  [R-1](2026-08-20_w32-re-envelope-charter.md) already authorizes a quotient
  over the rendered panic text while preserving the forced panic/kind/control
  half. Completing that existing rendering contract need not choose a new
  identity policy. Preserve the witness; do not assume equal strings imply
  identical boxes or narrow O2. The sealed earlier review is historical;
  this correction records authority found after that review.

These are open investigations, not permission to weaken O2 or stop independent
O1 work. Next: commit the reviewed helper increment, connect actual setup to
structural control typing, and seal preflight observation/choice capture.
The preflight recorded all 3598 cases; existing BUG-090's model timeout is an
explicit incomplete observation/trace capture, with no prefix substituted as
a complete observation. The B7 sufficiency of this bounded capture remains
an evidence-review obligation. B7 is still pending the
first generic setup/invariant contract; its before/after baseline must be
rebased after any separately justified semantic repair.

Coordinator follow-on: `.tmp/boolean-exact.6TBh5u/Exact.lean` contains compiled
generic exact binder/allocator equations, distinct-name lookup, parameter
value/result-zero loads, result-pin distinctness, and `setup_typed_exact`
with canonical actual setup, all typed storage/context premises and derived
`MachineWf`. Promote to an audited public module after this helper commit;
scratch elaboration alone is not an accepted public contract.

## Integrated checkpoint update (2026-09-06)

This update supersedes the earlier live-lane status above. The reviewed
storage/setup increment is committed at `f251abcb`, the sealed preflight at
`8b0a6a22`, and independent exact-initialization review at `815227ad`.
The exact setup increment is now `GoLean/GoCore/BooleanInitialization.lean`,
exposed and audited through the facade. Its unchanged reviewed source passed
fresh interface checks (41 exports, seven compiled poison controls), ordinary
CI and eight independent kernel challenges. See the
[source-bound evidence](evidence/2026-09-06_boolean-initialization/README.md)
and [claim ledger](2026-09-06_boolean-initialization.md). This checkpoint
derives exact setup and machine bounds; it does not yet compose setup with
the structural runtime invariant or establish the complete O1 driver chain.

Next integrate the separately reviewed runtime commit `8717b974`, derive the
generic admitted initial invariant, and expose actual driver safety/readout.
The O2 agent is implementing the separately reviewed recovery typing design
in `typed-recovery`. The observer agent has preserved red valid-UTF8 NUL and
control-byte regressions in `typed-observer-controls` and is repairing raw
byte transport under the existing observation policy. The separate renderer
repair is committed at `ff7173dd`, with complete differential evidence and
final ordinary CI; its bounded independent review precedes integration.
B7 design is available at `45f7955e`, with representation edits still pending
the generic setup/invariant checkpoint. All O1–O5 outcomes remain in scope.
Main remains clean at `47195683`; no main merge or push is authorized.

## Current continuation checkpoint (2026-09-06, 01:45 UTC)

- Exact initialization is committed at `354ef7f2`; runtime `8717b974` has
  been merged. The independently accepted renderer review is `c7eeaf57`.
  The renderer merge itself is staged with all four test/audit conflicts
  resolved by retaining both lanes. Do not restart or abort that merge:
  its fresh full CI is running before the merge commit is finalized.
- Parent process: unified exec session `67619`, command
  `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 scripts/capped scripts/ci --diff`,
  log `artifacts/boolean-runtime/renderer-integration-ci.log`. It passed
  the default warning-free build, 44-export/all-nine-poison interface gate,
  admission and Boolean gates, frontend checks and 202 eval tests; the
  full corpus is still running. Poll this existing handle. The full runner
  publishes `latest.tsv` only on completion; an absent published table is
  not evidence that the live run died. The separately run combined interface
  gate also passed (`renderer-integration-interface.log`).
- The complete next O1 increment is compiled in
  `.tmp/boolean-program.RmDTYt/Program.lean`: generic setup-to-`Inv`, exact
  canonical setup-to-`Inv`, sequential typed readout, same-fuel singleton
  output-driver correspondence, exact private events with no output/picks,
  shipped `runProgramPoolOutM` typed readout or explicit fuel exhaustion,
  and a successful-run contract retaining the original choices in both
  `Trace` and `Pool.Run`. `Tests.body` supplies seven concrete kernel
  consumers; `CombinedTests.lean` compiled warning-free. `Ledger.md` is the
  accompanying draft claim ledger. These draft files remain frozen for
  review while the preceding runtime gate runs. They are not yet public.
- Independent O1 bridge review by `typed_boolean` returned bounded PASS,
  independently elaborating the exact-initialization and full new draft
  against its own committed imports, all seven supplied tests and six
  additional fuel/output/choice/safety challenges. It is sealing a tracked
  report; public promotion, expanded audits and A1/A2 integration are still
  required. The earlier statement-only review is `6489c986` on preflight.
- Observer core byte transport has source-bound independent review
  `83c177c2`. Its author is completing a separate full CI in
  `typed-observer-controls`. Review of three diagnostic copies discovered
  an inherited false acceptance of fatal-during-unwind as panic, then found
  the related strict/sampling core path. This is a blocking follow-on
  classifier repair, with red controls and a new reviewed increment; it is
  not waived by the earlier bounded byte-transport PASS. Preserve the
  original frozen CI and add fresh full evidence after the classifier fix.
- O2's separate static judgment/checker now compiles through whole-program
  admission and acyclic calls/deferred calls, with no fixture or generic
  recovery-runtime completion claim yet. Its agent is working on the
  complete A2 and second native fixture/adversarial checks. B7/I1 remain
  pending the clean initial contract checkpoint; preserve correspondence
  separately from R-1/invalidUTF8 and observer repairs. The BUG-090 complete
  before/after capture gap remains open, unchanged.

Next finish and seal the current renderer integration CI/merge, promote the
reviewed O1 draft into audited public modules and validate its actual-source
interface/customer chain, then begin B7 in a separate worktree alongside O2.
Do not present the current milestones as all O1–O5 complete.

### Renderer integration gate complete

The previously live session `67619` is now terminal, exit 0. Fresh full CI
passed: 3607 executable cases (3363 PASS / 244 known FAIL), 394 negative
cases, 202 evals and all standing gates. Every executable result/stage
matches the reviewed renderer full run. Source-bound logs/tables and hashes
are sealed in [renderer integration evidence](evidence/2026-09-06_renderer-integration/README.md).
The resolved merge can now be committed; do not restart that completed run.

The complete O1 draft and seven consumer tests have a sealed independent
implementation review at `fadcb0c3`, to integrate with public promotion.
Preflight has additionally verified a declaration-marker census from the
sealed original corpus: 522 PASS / 174 FAIL rows contain wire quarantine
markers, all at declaration boundaries. A blanket I1 lowerer rejection
would therefore break supported cases; 70 PASS rows also have syntactic
call-closure hits on quarantined guard/dead-path declarations. This is an
engineering obligation for clean signature/type facts and code availability,
with no waiver or descriptor-algebra policy inferred from the census.
