# Typed-consumer sprint handoff

## Authority and state

[USER], 2026-09-05: K1–K5 approved, with K4 clarified: merges to main
always require user approval; agents may integrate feature branches under
standing user approval. The [charter](2026-09-05_typed-consumer-sprint-charter.md)
records the exact ruling. This sprint has standing internal integration and
independent-review approval, but no approval to merge to main or push.

[AGENT] Status: **IN PROGRESS — O1 PUBLIC CONTRACT VALIDATED**, updated
2026-09-06. Main remains clean at `47195683`. The sprint integration branch
is `typed-consumer-sprint`; the current public-program increment is based on
`761d4e28` and bound by its own source/evidence inventory. O1's current
representation has the reviewed generic contract; its B7 transport and
the remaining O2–O5 outcomes are still required. Later dated checkpoints
supersede earlier process handles and branch tips retained below.

## Required outcomes

| Outcome | Status | Next evidence |
|---|---|---|
| O1 typed Boolean contract | Independently reviewed judgment/checker, exact setup-to-invariant, all-successor preservation/progress and actual shipped-driver typed readout; fresh public/customer gates pass | Transport the complete contract through B7 and review final integration |
| O2 typed recovery customer | Separate static judgment/checker and both native fixtures validated; independent review requests diagnostic separation; mixed-store runtime work started | Generic setup, call/capture/return/defer/panic/recover preservation and reusable Iris proofs for both fixtures |
| O3 evidence/reviews | Original preflight and fresh renderer integration full CI sealed; O1 implementation/promotion reviewed; observer transport reviewed with separate classifier finding | Close diagnostic/classifier findings, complete observation/choice capture and final independent reviews |
| O4 B7/I1 | B7 old-model/store correspondence prototype started in a separate worktree; independent I1 declaration census/design complete | Whole fixed-context migration/correspondence; separate I1 support/closure implementation with no convenience PASS-to-refusal changes |
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

## Current checkpoint: public Boolean contract validated (2026-09-06)

The renderer merge is committed at `82e177c7`; its formerly live full-CI
session `67619` finished exit 0 and must not be restarted. The B7 design,
statement review and complete O1 implementation review are integrated
through `761d4e28`.

The public O1 program modules now pass all required increment gates. Sessions
`37399` (interface), `93172` (ordinary CI) and `21278` (full admission,
native Boolean, A1, A2) are terminal with exit 0. Exact source, logs and
focused observations are sealed in
[public-program evidence](evidence/2026-09-06_boolean-program-integration/README.md).
The separate promotion review `638af8dd` verifies unchanged theorem/test
bodies and all new audit/poison selection. The new source remains frozen for
its integration commit. No runtime/observer source changed in this increment;
ordinary CI explicitly reused the preceding source-bound 3,607-case record.

Current parallel work:

- `typed-recovery`: static recovery judgment/checker, all A2 entries and the
  corrected second native fixture pass their full dedicated gate and ordinary
  CI. The root independent review freshly elaborated all six source bodies
  plus thirteen new probes. Finding RS-1 requests distinct outside-profile
  versus malformed-body diagnostics without changing admission; the author
  is fixing it. The generic mixed store/runtime module has started. Static
  acceptance alone is not O2 runtime/customer completion.
- `typed-context-store`: B7 implementation off `761d4e28`; the actual frozen
  old state, new heap-only store, default-context fiber isomorphism and
  allocator/update correspondence prototype compile. Whole-machine/drivers,
  live explicit platform, both consumer migrations and final measurements
  remain. Bring the public O1 commit before migrating consumers.
- `typed-observer-controls`: reviewed core byte-transport commit `d0dbd469`
  is ready with source-bound full 3,616-case evidence (nine new PASS cases,
  no other drift). Its independent review `83c177c2` accepts only transport.
  The separate classifier finding in `0e3f7e2` remains blocking: panic-looking
  output can precede a real fatal error. Default-trace classifier drafts are
  explicitly rejected. Root independently checked the proposed pinned
  `GOTRACEBACK=system` design against installed runtime source: it supplies
  terminal evidence from the same oracle execution without wrapper changes
  or a semantic-policy change. Implementation, adversarial review and fresh
  full CI are still owed in `typed-observer-classification`. BUG-106 is
  reserved for that finding. Do not narrow O2 string admission as a remedy.
- I1: the full independent design/census `02abf956` has been read. Root owns
  follow-through on exact declaration facts, clean bodies and checked
  support/closure. Keep it separate from B7 and from any fidelity expansion;
  the census does not establish a descriptor-algebra blocker or authorize
  blanket declaration rejection.

Next commit the gated public O1 increment and integrate its promotion review,
seal RS-1 independently, continue recovery runtime and B7, then integrate
the separately reviewed observer repairs with their exact measurement scope.
Complete whole-corpus observation/choice capture still has the explicit
BUG-090 gap; no byte-identity claim is available for that case. O1–O5 remain
the goal, with no main merge or push authority.

## Current checkpoint: recovery static integration validated (2026-09-06)

O1 public promotion and its independent review are committed at `26f0dc09`
and `8b5ce690`. Root subsequently integrated the independent observer
transport/classifier findings and I1 census/design through `c2057e78`.
The pending merge of static recovery `e8a665e9` into that parent is clean and
fully gated for this proof/API increment. Sessions `36327` (ordinary CI) and
`84146` (full recovery typing, A1, Iris customer) are terminal with exit 0;
do not restart them. Exact evidence is in
[recovery integration](evidence/2026-09-06_recovery-integration/README.md).
The original recovery diagnostic finding RS-1 is independently closed by
`c2057e78`; the independent promotion review is `f569eb7f`. Static admission
does not discharge the recovery runtime/customer obligations.

Current responsibilities and remaining work:

- `typed-recovery-runtime`, committed base `212842a9`: the author is proving
  mixed storage, expression and structural control/call/unwind contracts.
  Its focused helper gate passed; helpers are still drafts pending their
  own ordinary CI and independent review. Root takes actual generic entry
  setup in a separate worktree using frozen store/environment/allocation
  helpers. No setup-success or future-safety premise may replace the proof.
- `typed-context-store`: actual Ops, Machine/Step and StateWf compile with
  explicit ProgramCtx and a heap-only Store. StepFn, pools, coherence,
  customers and complete old/new correspondence remain unfinished. The
  whole worktree is not green, and no B7 runtime commit is accepted yet.
- `typed-observer-classification`: independent review `80bf1251` found a
  printed-prefix forgery even with system tracebacks. Its unsound full run
  was stopped at exit 143 with 256 partial rows retained. A bounded
  same-execution crash-channel prototype is under independent review; no
  production hook is accepted. Of 40 relevant current oracle rows, exactly
  `sync/mutex-unlock-fatal/during-panic-unwind` would expose an apparatus
  refusal because fatal messages precede crash-channel duplication. That
  stage change requires an explicit independently reviewed BUG-106
  disposition. Do not narrow the required recovery profile to fix this.
- `typed-i1-declarations`, root-owned, `8ea5a74b`: a bounded prototype proves
  actual method-signature and satisfaction queries factor through exact
  declaration metadata independently of bodies. Build and fresh dependency
  audit passed; independent review and actual I1 implementation remain.
  It neither removes the four IR markers nor solves checked code closure.

Next seal/commit the static integration and its promotion review, continue
generic recovery setup and control in parallel with B7, then integrate only
separately reviewed fidelity repairs. The required equal-string repanic and
invalid-UTF8 observations, BUG-090 full capture gap, I1 declaration/closure
work, shared Iris rules and final O1–O5 completion packet remain open. Main
remains clean at `47195683`; no main merge or push is authorized.

## Current checkpoint: recovery storage reviewed and gated (2026-09-06)

Static recovery is integrated at `77f154e0`, its promotion review at
`0079ece9`, and the blocking old observer finding at `838adc51`.
The six recovery helper modules passed independent review `efc2712c` and
were committed by their author at `4f7aedef`. The clean staged integration
into `a34bc969` passed fresh ordinary CI (session `27352`, terminal exit 0),
including its eight compiled poison controls; seal at
[helper integration evidence](evidence/2026-09-06_recovery-storage-integration/README.md).
The whole runtime corpus remains explicitly cached for this proof increment.

Root-owned `typed-recovery-setup` fast-forwarded to committed `4f7aedef`
after byte-checking and preserving the original copied helpers. Seven new
semantic modules now compile: source/address shape and distinct lookup,
exact binder/zero allocation, result roots, actual program setup, derived
MachineWf, exact initial readout and actual `enterFrame`/`enterFramePick`.
The latter preserves incoming root aliases and arbitrary original choices.
The first dedicated gate passed; adding the generalized block-scope lookup
contract and a real heterogeneous-shadow allocation regression justifies its
affected rerun. These new modules still need final tests/audits, ordinary CI,
independent review and public integration. They do not prove full recovery
control preservation or the reusable Iris customer yet.

The helper author continues structural expression/control and call/unwind
preservation in isolated scratch. B7 now compiles actual Ops, Machine,
StateWf, StepFn, Race/Multi and sequential coherence with explicit context
and heap-only store. Pool coherence, consumers, complete old/new transition
and driver correspondence, and corpus capture remain incomplete.

Independent observer hybrid design acceptance is integrated at `96be72c9`,
with explicit K3 BUG-106 disposition at `a34bc969`. The exact measured
`sync/mutex-unlock-fatal/during-panic-unwind` old PASS may be exposed as
`go-observation` refusal because the old apparatus lacked authenticated
message/output evidence. This neither changes fatal GoCore semantics nor
narrows O2. Production focused evidence now has 22 PASS / that one named
refusal across 23 rows; production source review and fresh full CI remain
owed. The older rejected full run remains terminal 143 and partial.

I1 still has only the root metadata prototype `8ea5a74b` and design/census;
actual positive declaration facts and checked executable closure remain.
Equal-string repanic, invalid byte-string observations, BUG-090 complete
capture, reusable Iris proofs, final B7/I1 preservation, roadmap/migration/
C1 handoff and the closing decision packet are still required. O1–O5 remain
the full goal. Primary main remains clean at `47195683`.

## Current checkpoint: actual recovery entry publicly integrated (2026-09-06)

The user explicitly resumed the full charter goal after a safe readiness
pause. The preceding readiness turn was a safe checkpoint, not a completed
sprint. All three lanes resumed with their original responsibilities.

Actual recovery setup/call entry `63769964` passed independent review
`997d74ed` (integrated at `4158368f`). Its facade promotion passed separate
review `29ac266d`. The pending merge into `4158368f` passed ordinary CI
`63627`, native recovery 5/5 and all controls, A1, and Iris artifact/3/3
differential gates. Sessions `63627`, `20187` and `22601` are terminal;
the first spike launch in `20187` failed because the mode-100644 script was
invoked directly, then the correct Bash invocation passed in `22601`.
Do not repeat these completed checks without changed source or a concern.
The [integration seal](evidence/2026-09-06_recovery-entry-integration/README.md)
binds 196 source files, 84 public exports and nineteen compiled poisons.
Whole runtime and compile-negative records remain explicitly cached here.

The recovery runtime lane has fifteen frozen control modules proving actual
setup-to-Inv, structural all-successor preservation, normal/semantic-abort
progress, and typed readout/unchanged choices for successful actual drivers.
Its dedicated gate passed with 124 exports and seventeen poison controls.
Root independently rebuilt all seventeen core/test modules and proved
fourteen additional adversarial checks, including actual aliased result
writeback and typed abort-query payload kind. Review source/evidence is on
`typed-recovery-setup` at `9e6c4234` plus reproducibility follow-up `ba930ba2`.
Author ordinary CI `21839` is now terminal with exit 0; its source/evidence
commit is being sealed. No control runtime commit is integrated yet.
Shared Iris allocation/call layout is a further isolated draft.

The observer implementation has bounded independent review `1bd2022b`,
integrated at `7774739a`. Its new full CI is live in the author lane at
session `34382`; preserve its eventual terminal result, never infer full
success from partial rows. Diagnostic source review is `c5b83045` with
additive packaging correction `0333f0a1`; integrate both together. The
older rejected classifier run remains terminal 143. BUG-106's exact
sync-unwind observation refusal remains the independently reviewed K3
disposition. A separate arbitrary-byte/equal-string rendering repair is
under development against existing R-1 authority and needs its own review,
forced-half controls and actual terminal readout proof.

B7 now compiles sequential/pool coherence, traces and dedup/customer
infrastructure against explicit context. Its bounded equality guard remains
at the certificate boundary so dropping repeated context comparisons cannot
widen old certificate acceptance. Complete actual old/new correspondence,
contract/customer migration and full captured byte/choice equality remain
open. I1 still needs positive declaration metadata and checked executable
closure beyond prototype `8ea5a74b`. BUG-090 capture completeness, final
Go-fidelity evidence, reusable Iris proofs, B7/I1 validation, C1 handoff,
roadmap/migration and the O1–O5 closing packet remain mandatory. Main is
unchanged and no main merge or push is authorized.

## Current checkpoint: recovery control integration (2026-09-06)

Entry promotion landed on the sprint branch at `30b09c08`; independent
promotion review is `f5f228ca`. Diagnostic review and its additive packaging
correction are `313d1781`/`639192b2`. Root control review is integrated as
`1078c910` plus `bfecf455`, and the independent R-1 design review is
`4a8a8ad1`. Main remains unchanged at `47195683`.

The control author sealed `f160d7ca` after dedicated gate and ordinary CI
passed. The pending clean merge into `4a8a8ad1` has also passed ordinary CI
`43232` and fresh A1/Iris gates `62843`, both terminal exit 0. Separate
promotion review `62377799` approves the four public files. The
[control integration seal](evidence/2026-09-06_recovery-control-integration/README.md)
binds 215 sources, 102 interface exports and twenty-two compiled poisons.
Do not restart these completed runs. Post-gate documentation/evidence
updates do not change reviewed semantic source.

`typed-shared-customer`, owned by the recovery author, now has separate
drafts for exact arbitrary-heap call allocation, one shared Iris call rule
covering seven actual call/defer entry forms, unwind/recovery/readout rules,
and the A2 refactor. The second functional customer remains open. This lane
also owns the actual reached-abort witness: the head bytes and recovered
flag must be tied to the real driver/trace and actual abort query, with
fuel/choices/output preserved, so the R-1 apparatus does not trust text pins
or caller-supplied payload metadata.

Observer classifier `b5dd4076` and diagnostic increment `2b679404` are
reviewed, gated and ready for the next integration. The fresh full record
has 3,627 rows: 3,382 PASS and 245 FAIL, exactly eleven new marker PASS rows
plus the independently justified sync-unwind PASS-to-observation-refusal.
Initial full CI `34382` exited 1 for that raw delta, BUG punctuation and
registration-free old sampling mocks; all evidence is retained. The narrow
mock repair has independent review `198aee9f`, its affected gate passed,
and final ordinary CI `58628` passed without repeating the unchanged full
corpus. Diagnostic CI `43806` passed with 105 controls and five mutants.
These increments are not yet merged here.

The isolated `typed-string-members` lane has constructive byte escaping/
decoding and first-line correspondence plus actual abort-point lemmas in
development. Its explicit membership certificate design still needs review,
production implementation and forced-half evidence. Uniform suffix/byte
rendering authority is the existing R-1, not a new scope ruling.

Root-owned `typed-i1-declarations` still has prototype base `8ea5a74b`, plus
uncommitted positive declaration serializer/tests and schema notes. Four
focused tests and the full frontend unit suite passed; ordinary CI `47743`
is live and independent review is queued. The helper is not connected to
the emitter/lowerer: exact decoder/envelope facts, query preservation,
guarded code closure and actual marker removal are still mandatory. B7
continues actual old/new correspondence and consumer migration. Complete
capture (including BUG-090), final fidelity review/gates, C1 handoff,
roadmap/migration and closing O1–O5 decision packet remain unfinished.

## Current checkpoint: observer integration and I1 foundation (2026-09-06)

The explicit goal continuation resumed all three lanes after the readiness
pause. Main was rechecked clean at `47195683`. The sprint parent is clean
commit `99e0225d`, containing actual public control integration `b3d6fa6e`,
its independent review `e4318e01`, and mock-protocol review `99e0225d`.

Reviewed observer/diagnostic `2b679404` is merged **without committing** into
the sprint worktree. Snapshot `snapshot/typed-sprint-before-observer-20260906`
preserves the parent. All three reviewed production/integration manifests
match except `scripts/ci`, whose diff only adds the two observer gates and
retains every recovery/interface gate. The complete input inventory and
comparison are in `docs/evidence/2026-09-06_observer-integration/`.
Fresh capped `scripts/ci --diff` session **74005 terminated with exit 0**,
log `artifacts/observer-integration/ci-diff.log`, archived in the evidence
directory. All 3,627 executable rows (3,382 PASS / 245 FAIL) and 394 negative
rows match the reviewed baseline. Original dirty-parent metadata is retained;
regenerated full manifests exactly match its original SHA-256 values.
`verify.py` checks complete unique inventories and allowed stages. Two HIGH
report-only ledger findings were corrected: current totals and the additional
BUG-106 `sync/mutex-unlock-fatal/during-panic-unwind` refusal. Historical
counts are preserved. Fresh reconciliation has no HIGH findings. Independent
bookkeeping/CI-union review `c8bab8a9` is PASS, including all 3,844 source
inputs, both complete inventories/manifests, exact case/stage delta and the
two additive CI hooks. This checkpoint accompanies the accepted merge seal.

I1 serializer foundation is sealed on `typed-i1-declarations` at
`298e4da1`, followed by independent reviews `7ae7fc0a`/`cf13789f` (original
review commits `58cd8b69`/`08f7984f`). Four focused tests, full frontend
tests and 324 independent pairwise identity comparisons pass. Initial CI
`47743` exited 1 for eight new untracked diagnostic formats and absent
local corpus records. The exact inventory update passed separate review
and full diagnostic tests; corrected ordinary CI **1329 exited 0**. Its
3,607/394 renderer records are explicitly cached, retaining original
metadata and a checked source-difference inventory. The serializer has no
production caller. It does not remove markers, admit code closure, or
replace the future full differential/slow wire train. An ignored root-owned
identity draft under `.tmp/i1-identity.ilDgsl` is superseded by the separate
positive identity/decoder increment on that worktree. It proves exact total
structural equality, decodes the closed positive schema, and checks 24 real
Go types / 576 ordered identity comparisons, 17 actual decoder negatives and
four compiled unused-declaration poisons. Dedicated gate **34109 exited 0**.
Ordinary CI **31463 exited 1** solely because comment prose contained the
scan token `admit`; changing it to `authorize` leaves code and gates intact.
Independent review `e9045844` and exact comment-delta review `d2ed3ecd` PASS.
Corrected ordinary CI **3794 exited 0**, including the default build and new
declaration gate, with the original explicitly cached 3,607/394 records.
This increment is committed at `0ff12435`, followed by review cherries
`18f90eb9`/`798e9c76`; production envelope, executable closure, query
preservation and actual marker removal remain mandatory I1 work.

The string certificate/byte-guard design has bounded root review in
`2026-09-06_string-member-certificate-design-review.md`, with exact input
copies. The renderer author integrated observer source internally at
`90128828`, preserving pre-guard source hashes. The guard now checks decoded
bytes before selecting direct text, otherwise choosing the proved reversible
escape; whole lane validation remains owed. A complete actual abort-chain
record is required for broader string membership as well as the head. Go
fidelity cannot be inferred from a string head with arbitrary tail payloads.
The runtime author owns extraction and exact driver erasure; broader rows
must connect to the shipped pool driver, not an unrelated sequential replay.

Actual abort-observer independent review is sealed at `ad961e41`: six new
modules freshly elaborated against audited-base compiled dependencies, ten
additional kernel probes, and the 43-export/14,549-declaration audit PASS.
The author's frozen gate and ordinary CI also pass, with cached provenance
explicit. The complete record comes from an actual pool abort step and
retains all byte/output/choice/fuel facts; integers and nonstring tails are
refused even with equal rendering. The author selectively committed the
unchanged observer increment at `04109912`; integration is the next action.
Full typed terminal classification and R1 fidelity remain separate work.

Both shared Iris functional proofs now compile, including arbitrary-input
`wp_shared` with a single owned cell through both handlers and the A2
refactor using the same call/recovery rules. Generic actual setup, Iris
adequacy and exact empty-output bridges now compile in the author's draft,
as does transfer of successful executions to every choice stream. Final
audits/review and full typed normal/panic/fuel classification remain open. B7 is
developing at `99e0225d` with its WIP retained: recovery storage/setup and
call entry have migrated; correspondence and the rest of the customers
remain unfinished. A capped proof exit 137 was retained and is being
replaced by smaller explicit dependency rewrites, without raising limits.

O1 survives at the current representation. Full O2 driver/customer evidence,
R-1 membership and final O3 evidence, actual B7/I1 and complete byte/choice
capture (including BUG-090), and the O5 closing packet/C1 handoff remain
mandatory. No main merge, push, stable pin, or Gate A completion is claimed.

## Client restart checkpoint: accepted observer seam and identity repair

Observer classifier integration is committed at `563c01de`, bookkeeping
review at `4bfeba58`, abort-observer review at `53ca910a`. The selectively
committed observer `04109912` is accepted for integration here: ordinary
CI 98487 has a complete terminal PASS log, exact 3,855-input source inventory
and byte-identical cached prior 3,627/394 corpus records. The client restart
lost its numerical process handle; no owned OS process remained on recovery.
This checkpoint accompanies the observer merge commit, with evidence in
`docs/evidence/2026-09-06_abort-observation-integration/`.

The I1 identity/decoder foundation is ready on feature tip `798e9c76`, with
source commit `0ff12435` and independent reviews. During the next metadata
bridge investigation, a fresh actual probe exposed pre-existing BUG-107:
`NativeToIR` identifies `uintptr` with `uint64`. Go 8 versus Lean 15 exposed
two cross-type assertions and incorrect method satisfaction. The root-owned
`typed-uintptr-identity` worktree at `53ca910a` preserves five differential
red cases, two earlier observer refusals and an existing wrapping positive.
The isolated distinct-kind repair builds and its 48 identity/atomic focused
cases pass. Independent implementation review and full/slow validation are
still owed; no repair commit, baseline re-pin or B7 equivalence across this
wrong-answer correction is claimed.

The shared customer's 35-input frozen package remains in its author's
`typed-shared-customer` worktree at `04109912`: its dedicated gate and
ordinary CI pass; root independent review is next. The separate
`typed-recovery-terminal` draft now compiles unconditional typed
normal/string-panic/fuel classification and actual pool metadata completeness,
using explicitly hashed borrowed renderer/shared sources. It needs tests,
audits, committed-source reconciliation and independent review. B7's latest
completed strict/channel/select correspondence and remaining statement/driver
work remain in its own handoff. The restarted agent team was reconstructed
from these disk checkpoints; no completed task was restarted from scratch.

## Declaration integration and customer acceptance after restart

The reviewed I1 positive declaration foundation `798e9c76` is integrated
with the actual-abort observer at parent `414a2abe`. All 3,865 source inputs
were revalidated after ordinary CI 80248 completed with exit 0. Independent
union review `60f541c6` confirms the exact additive build/CI union; the
remaining accepted inputs are unchanged. Evidence lives in
`docs/evidence/2026-09-06_i1-positive-integration/`. Full 3,627/394 corpus
records are explicitly cached and byte-identical to their sealed originals;
the positive declaration channel has no production caller yet. Actual I1
admission/query preservation/marker relocation remain incomplete.

The shared Iris functional increment now has independent review `163d44ea`
and sealed feature tip `bd31dd5d`: a separate-worktree complete gate, six
additional kernel challenges, exact 35-input revalidation and bounded PASS.
The extra customer proves framing of an arbitrary unrelated heap cell while
both handlers share one owned result root. Recovery directness, invalid
payload bytes, ownership exclusivity and all-choice empty output are also
checked. Root integration and facade/terminal work remain separate steps.

BUG-107's isolated full CI is still running in `typed-uintptr-identity`
(session 35064); its 48 focused identity/atomic cases and 204 eval checks
passed, with independent source review and additional Go/kernel probes.
No baseline repin or repair merge is yet justified by the unfinished full
run. R1 production review has found missing apparatus source inputs; the
author is repairing the inventory and preserving the superseded run as
incomplete. B7 has a checked whole-step correspondence at its old frozen
runtime, with driver/pool and final-runtime migration still owed. O1–O5
remain active; no main merge, push or completion claim is made.

## Shared functional customer integrated

The reviewed shared customer feature `bd31dd5d` is now integrated into
`3cdde025` with all 35 accepted inputs identical and no source conflicts.
Ordinary CI and the full customer gate completed with exit 0 in job 44200;
all 3,896 integration input hashes were rechecked. Fresh evidence includes
the 136-export/15,390-declaration audit, 23 compiled poisons, both complete
native artifacts and 3 A2 plus 5 shared/control differential cases. The
3,627/394 full records remain explicitly cached and byte-identical.
See `docs/evidence/2026-09-06_shared-customer-integration/`.

R1's frozen v3 implementation now has independent apparatus review
`d59b4ab1` and root Lean/model review `75da9338`. Six omitted source inputs
(two executable roots, three embedded frontend tables and its runtime pin)
were reproduced and repaired with compiling negative controls. Root replay
passed the complete interface gate, nine additional kernel probes and one
fresh invalid-after-LF row with all thirteen controls, plain/race Go and
four model streams. R1's full CI is still running; baseline disposition is
not yet accepted. Generic terminal/facade work is compiling in its own lane.

Root scaled BUG-090 probes on `798e9c76` distinguish allocation from writes:
4,096-byte allocation takes about 0.023 seconds; a 1,024-element write loop
takes about 1.39 seconds; 4,096 writes and 256 repetitions of the 16-byte
string each exceed 20 seconds. Raw probes are retained in the I1 worktree's
`docs/evidence/2026-09-06_bug090-scaled-profile/` and unique scratch. The
current `storeLoc` normalizes the whole backing array on every element
write. This is a supported performance hypothesis, not yet a repaired
runtime or completed capture. No large unchanged capture was repeated.

## Restart recovery: final R1 integration and remaining lanes (2026-09-06)

[AGENT] Main remains clean at `47195683`. Integration parent `b34cee67` has
a pending merge of reviewed R1 `819182b5`, after snapshot
`snapshot/typed-sprint-before-r1-20260906`. Only CI had a source conflict;
the resolution retains both complete gates. All nine member pins changed
only apparatus source inventories (160 to 169); other fields are unchanged.
Independent union review `731beb0b` checked all 3,923 integration inputs.
Ordinary CI then nine fresh member rows are running as job 40908; frozen
inputs and evidence are in `docs/evidence/2026-09-06_r1-integration/`.
This pending merge is not yet an accepted integrated runtime.

R1's completed author full run has 3,635 rows: 3,391 PASS/244 FAIL, plus
394 negative PASS. Exactly eight new rows and the historical same-value
repanic member row account for the movement. Baseline review `8e8bca46`
and follow-up `2094de72` retain the intermediate stale BUG-004 Cases failure
and narrow correction. The full run's 32-worker deviation is recorded;
subsequent conformance uses two. Final ordinary CI has a complete PASS log
but a lost numerical supervisor handle. Integration uses these full records
as cached evidence, separate from the fresh nine rows.

The root `typed-uintptr-identity` repair remains runtime WIP at docs-only
`169ec3c3`. Initial full CI returned 1: eight new PASS rows (3,635 total,
3,390 PASS/245 FAIL; 394 negative PASS) and missing pinned `deps/goose`.
Independent disposition reviewed the narrow baseline/ledger movement and
verified the restored dependency. Job 57432 runs final `scripts/ci --slow`
on 3,851 frozen inputs with two workers. Seal, integration and measured
combined baseline remain owed; its row set differs from R1's same-size set.

Root `typed-i1-json` adds strict byte/JSON input before positive declaration
decoding. Its 14-input candidate passed focused checks and ordinary CI 85137
with exit 0: 47 inputs, 24 fresh Go types/576 identity pairs, 17 malformed
declarations, 1,712 audited declarations and six compiled poisons. The
3,627/394 full records are cached. Its 3,899-input post-run reconstruction
is explicitly separate from the pre-run 14-input freeze. Independent review
is being sealed. Production lowering is unchanged: complete declarations,
metadata-query and demand preservation, runtime-error context and actual
marker relocation remain mandatory I1 work.

B7 now proves whole-step, setup, driver, pool/event/choice/output, race and
Step/Steps/StepE/StepM correspondence to original `761d4e28`. Root review
`2831473d` reconstructed 345 inputs and checked four generic kernel probes,
17,617 declarations and an unused-axiom poison. Customer migration review
`0f5ae41f` separately reconstructs 409 inputs, with a fresh 320-job build,
five kernel challenges, a 135-export/15,005-declaration audit and rejection
of a wrong-context use. The author compared all 2,117 transitively borrowed
GoLean kernel bindings against a fresh original environment with zero
differences. The durable closure checker/controls, final repaired-runtime
basis, warning cleanup and full trace capture still need completion/review.
No equivalence claim silently spans the `uintptr` wrong-answer repair.

O2 terminal/facade reconciliation with committed R1 is in
`typed-recovery-terminal`. Initial union CI preserves missing local
dependency/cached-record failures. Exact pinned input restoration and
source-only member inventory refresh precede a new final freeze; theorem
sources are unchanged by this reconciliation. Root final review and gates
remain owed.

BUG-090's original large capture remains incomplete. The local byte-store
proof `39add7fd` has root review `8e50c38e`; consuming extension `68590160`
awaits independent review. Both are opt-in spikes. Exact local refinement
and six small measurements do not establish runtime certificate handling
or close BUG-090. No cap increase, timeout waiver or runtime optimization
has occurred. O1–O5 remain mandatory; final integration, claims ledger,
roadmap/C1 handoff and closing decision packet remain incomplete.

### R1 integration accepted; strict JSON candidate sealed

The pending R1 union above completed ordinary CI and all nine fresh member
rows with numerical exit 0 (job 40908). All 3,923 frozen inputs and all
nine 169-source certificate inventories were rechecked. Independent union
review `731beb0b` accepts the exact additive changes. Fresh certificates,
full raw focused artifacts (excluding the hash-inventoried harness binary),
logs and source hashes are retained in the integration evidence packet.
This checkpoint accompanies the R1 merge commit; full 3,635/394 evidence
remains explicitly cached from the accepted author run.

The strict JSON candidate is clean at `7ac3eb46` in `typed-i1-json`, with
implementation `b9136a05` and independent I1 review `8051028b` attached.
That review passed 107 adversarial inputs and an extra imported-helper
poison. Its source inputs are unchanged. Integration is a separate next
step and must refresh the member source inventories for the new parser.

## Model interruption recovery and sealed isolated repair

[AGENT] The accepted R1 merge is `c969079a`. The parser merge of `7ac3eb46`
is now pending on that tip, with 3,926 frozen inputs in
`docs/evidence/2026-09-06_i1-json-integration/`. Its nine member pins refresh
only source inventories (169 to 170): add StrictJsonParse and change the
NativeDeclaration/lake hashes. Ordinary CI followed by nine member rows
continues in root job 21926. A separate agent reviews the additive union.

The user reported a model interruption. The old three agent identities were
no longer live; replacement owners `b7_resume`, `i1_resume` and `byte_runtime`
recovered the existing worktrees and disk checkpoints. No completed work
was restarted merely because its supervisor disappeared. The earlier ENOSPC
failures remain recorded; the filesystem now has about 500 GiB available.

The isolated `uintptr` repair is clean at `5f185fb3`, with final `--slow`
CI job 57432 numerically returning 0. All 3,851 inputs and twelve candidate
files revalidated. The exact full 3,635-row results remain 3,390 PASS/245 FAIL,
with all 394 negative rows PASS and no status/stage change from the reviewed
first full run. The sole slow row, imported Google Search, was freshly
re-certified with unchanged set/wire/parameters. Complete evidence is in
`docs/evidence/2026-09-06_uintptr-identity/FINAL.md`. Combined integration,
its measured baseline union and final slow train are still owed.

O2 author candidate `7bd32ad6` has completed ordinary CI, nine fresh member
rows and the complete customer gate. Independent review is attached in the
clean author worktree at `f3971190`: exact 239-input revalidation, four
additional kernel challenges, fresh semantic elaboration and additive union
checks. Both native artifacts and all eight customer rows are fresh; full
3,635/394 records remain cached. Root integration is the next O2 step.

I1's package-envelope author tree is at docs-only `090ae32c` with runtime
candidate WIP preserved. Independent v2 review (`23362c6d`/`4d492cea`) found
and checked repairs for an interface-index bijection gap and private method
requirements from distinct packages sharing a spelling. All 32 candidate
and 3,917 selected source hashes revalidate. Previous CI ran out of disk
before conformance; resumed full CI is job 73832. The actual source/query
bridge and marker removal remain owed. Read that lane's HANDOFF for its
defined-Mix dispatch collision limitation and unchanged 85-wire checks.

B7 has a frozen structural cleanup checkpoint with 413 inputs (manifest
`69a7710a87506fb3d4df77e5387cd8c2d56da8eb001c5d6c4da33b8d93275ec3`),
warning-free reference/customer builds and a final dedicated customer gate.
The incomplete kernel inventory requires expansion: pinned Lean's
`getUsedConstantsAsSet` does not traverse every metadata name or recursor
rule body; its expression traversal also omits projection structure names.
Six additional project names already occur in `details.all`. Equality of
the original 2,117 records is bounded evidence, not complete closure. A
separate v2 apparatus will expand all these references and receive a new
independent review; the original packet remains unchanged. Root's older
409-input reconstruction and both successful build logs remain in
`typed-b7-kernel-review`; numerical build handles were lost, not fabricated.

The consuming byte-store extension now has independent review `631b883f`:
twenty unchanged inputs, four fresh kernel challenges and 3,492 audited
declarations. Actual caller work is in `typed-byte-runtime`. The relevant
path is Repeat → Builder.WriteString → appendSlice's per-byte storeLoc loop.
It also exposes quadratic array construction inside normalizeListWith.
Exact local normalization/certificate improvements are being proved and
measured; these are not yet production changes or completed BUG-090 capture.
O1–O5 and final review/closing deliverables remain active and incomplete.

### Strict JSON integration accepted

Parser integration job 21926 completed with numerical exit 0 for ordinary
CI and the nine fresh string-member rows. All 3,926 input hashes and all
nine 170-source certificate inventories revalidated. Independent union
review `893a7ad2` is attached, and the evidence packet retains raw focused
artifacts, certificates, logs and hashes. This checkpoint accompanies the
parser merge commit. The 3,635/394 full records remain cached; this merge
adds the strict declaration byte boundary and does not finish runtime I1.

### Recovery terminal integration accepted; remaining representation evidence

[AGENT], 2026-09-06. The parser integration is `39235f65`. Its merge of
O2 author/review tip `f3971190` completed root job 81343 with numerical exit
0 for ordinary CI, nine fresh member rows and the Iris customer gate.
Both whole native artifacts and all eight customer cases are fresh. All
3,952 frozen input hashes and all nine 172-source certificate inventories
revalidated. Independent additive-union review `352d09f9` is attached.
The packet `docs/evidence/2026-09-06_o2-terminal-integration/FINAL.md`
retains logs, exits, certificates, native artifacts and raw focused archives.
The full 3,635/394 records remain explicitly cached. This checkpoint
accompanies the O2 merge; the next integration is reviewed `uintptr`
repair `5f185fb3`, with measured combined baseline and slow gates owed.

B7's v2 closure work expanded the original incomplete inventory. Its
current boundary starts with all 4,142 public/private B7Before roots and
traverses every reachable dependency, including twenty helpers generated
inside frozen modules whose user names are outside that namespace. A
broader experiment rooting every frozen-module declaration found a live
callback in a dormant generated lemma; that failure is retained and the
final boundary requires independent review. No complete original/new
kernel-sharing comparison is accepted yet. Full B7 CI resumed as job
34180 on 3,988 selected inputs, using worktree-local scratch.

The byte append candidate now has an exact theorem for the entire actual
`applyStmtOp` result for arbitrary raw states and choice tapes. Its 115
frozen inputs await root independent review and full CI. Small runtime
measurements improve substantially, but the 2 MiB probe still times out.
A separate diagnostic found that growing `Builder.String()` results remain
in heap cells. Measured small runs support a source-derived prediction of
about 17.2 GB of distinct retained byte positions for the original case,
before the pointer-sized array representation's overhead. This is a
prediction, not a completed 16 MiB execution. Exact-value sharing options
need assessment; no GC, footprint change or cap increase is authorized.
BUG-090's original capture remains incomplete.

I1 envelope full CI 73832 continues on its unchanged v2 source. The positive
declaration query probes expose 149 disagreements with legacy queries,
all explained by the separately repaired `uintptr` collapse. A generic
kernel bridge and a narrow diagnostic-vocabulary proposal are preserved in
that lane's evidence; neither substitutes for connecting production queries,
moving markers or proving the final accepted-program contract.

The user's authorized primary `.tmp` cleanup removed 68,122 files whose
mtime and ctime were older than seven days, approximately 14.2 GiB of
allocated files. Current job scratch and all worktree-local scratch were
preserved; deletion and verification records are in the integration tree's
ignored `artifacts/tmp-cleanup/`. Main remains clean. O1–O5 retain their
original scope; final integration, full evidence and closing deliverables
remain incomplete.
