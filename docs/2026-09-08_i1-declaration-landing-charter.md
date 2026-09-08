# I1 declaration boundary — landing charter

[AGENT] 2026-09-08. Status: LANDED ON MAIN at `960ee230` after the
MERGE-CLEAN second review and explicit [USER] sign-off. Branch `land/i1-declarations`, worktree
`.claude/worktrees/land-i1-declarations`, starting main
`ae9c807923f371a7349430a443a635a754ef816f`.

## Authority and purpose

[USER] 2026-09-08, firsthand in this session: “Great, let's work on I1.
Can you set up a charter document for this work, then set up a goal, and
work on this until you finish and you consider it ready for merge sign-off?”
This accepts the preceding proposal for the strict declaration-wire
foundation (L1b), with its two audit fixes and fresh validation.

The contract: closed Go declaration identities survive serialization and
Lean decoding exactly within the stated schema; malformed inputs receive
named refusals; successful or failing declaration queries do not change
subsequent executable emission. This is a tested translation boundary over
the existing kernel-checked declaration equality, not a compiler-correctness
theorem or a new claim about executing Go programs.

Plan pointers: [master plan v2](2026-09-07_master-plan-v2.md), §2.2 R7,
§3.1 T3 and §4.3 W3; [landing plan](2026-09-07_typed-sprint-landing-plan.md),
L1b and A-R11/A-R12. The foundation can land independently of B7; production
I1 context integration follows B7 as the master plan requires.

## Deliverable and boundary

1. Select the committed declaration producer, strict byte parser, decoder,
   tests, dependency audit, gate and relevant notes from `typed-i1-json`
   (`7ac3eb46bb3e2fe9c15b86b509569ef086327453`). Record each selected blob.
   `GoLean/GoCore/Declaration.lean` and the I1 spike already on main are the
   semantic foundation. Integrate a named `DeclarationTests` target and
   `scripts/check-declarations` CI step.
2. Repair A-R11: compare freshly generated declaration-fixture bytes against
   a tracked expectation and reject drift. A printed hash is provenance,
   not a pin check. Exercise a deliberately corrupted expectation/artifact.
3. Repair A-R12 for the whole declaration-query path: isolate mutable
   identity, diagnostic, substitution and display bookkeeping from executable
   emission. Test success and refusal, including unknown local identities.
   Missing-package checks must distinguish legitimate universe declarations
   such as `error` from malformed objects; retain exact package-sensitive
   private-member identity and raw struct-tag bytes.
4. Preserve and strengthen controls for closed basic/nominal/composite types,
   aliases, local scopes, ordered instantiation arguments, recursive nominal
   references, canonical method sets, and strict raw JSON/Unicode handling.
   Keep the existing 24-type/576-pair Go `types.Identical` matrix as a
   discriminating cross-language test; additions are recorded separately.
5. Publish concise source-bound evidence, resolve findings, and update the
   master plan by a dated addendum and this charter's completion record.

Production package emission, `NativeToIR`, executable admission, method-query
preservation, removal of runtime refusal markers, B7, general identity redesign,
reflection and other missing sprint gates remain subsequent milestones.
No old whole-branch merge or dirty-worktree overlay is part of this landing.
No executable baseline re-pin is planned. A behavior/wire change is a finding
to resolve within the contract, never evidence that the contract can relax.

## Acceptance and validation

- Fresh frontend units and producer-to-decoder equality comparisons pass;
  malformed types, inventories, JSON and UTF-8 fail with named causes.
- Kernel declaration equality remains unchanged. The post-import dependency
  audit includes the parser/decoder/tests and rejects compiling unused/private
  axiom controls. The fixture check rejects corrupted controls.
- Success/failure declaration queries preserve executable-emitter state and
  byte-identical executable output in focused interference regressions.
- `scripts/capped scripts/ci --diff` passes before any runtime commit, with
  zero baseline drift against 3,654 executable rows (3,403 PASS / 251 FAIL)
  and 394 negative PASS at the starting tip. These are expected baselines,
  not newly measured successes. The gate runs at the final committed source
  as well; a final `--slow` run may discharge that full differential and
  freshly confirm the certified set without changing its membership.
- Executable frontend pins remain byte-identical. The new parser stays
  outside the total core, with no production caller. Existing totality and
  escape-hatch checks remain in force. The root build remains Iris-free.
- The branch is committed, clean and green, its source/evidence scope is
  explicit, material findings are resolved, and the mandatory adversarial
  audit ask has been posed. Independent review, if requested by the user,
  is separate from the author's own adversarial checks. Merge/push require
  the charter's explicit at-that-moment approvals.

## Execution and records

All edits and artifacts belong to this worktree. Other prototype worktrees
and their uncommitted content stay untouched. Dependencies are obtained with
`scripts/setup-deps --from /home/dev/projects/golean`; scratch/cache paths
are worktree-local. All Lean/Lake work uses `scripts/capped`; full builds
and gates use the box-wide build lock. Initial settings: 16 GiB cap,
three Lean threads, two differential workers; record any justified changes.
No uncapped fallback, gate weakening, destructive cleanup or oracle drift.

Keep full logs in ignored worktree artifacts. Main-bound evidence contains
small gate tails, source hashes and review findings, subject to the existing
evidence-size policy. Imported historical notes are labeled as historical;
their recorded success is never presented as fresh validation here.

## Completion record

[AGENT] 2026-09-08. Implementation is complete at
`3e393be5d7f72d3be2dd57e45872e9fcc4a90518`, with the corrected full candidate
`--diff` gate and clean committed-source `--slow` gate both PASS, actual
exit 0. The 3,654 executable and 394 negative baselines match; fresh slow
enumeration reproduces the six-member certified set and its wire exactly.
A-R11/A-R12 and author finding I1-R1 are repaired with discriminating controls.
The mandatory independent-audit ask was posed; the user's scope/waiver
decision remains pending. No independent review or merge approval is implied.
The [completion record](2026-09-08_i1-declaration-landing.md) names source,
evidence, limitations and follow-up scope. This closes the authorized
branch-ready implementation goal, not a merge or completion of all I1 work.

### First review correction round

[USER] 2026-09-08 authorized fixes to the supplied coordinator review and
obvious related improvements, then a pause for a second review. This supersedes
the earlier pending first-audit choice. [AGENT] R1–R4 and the related parser
budget/diagnostic/scratch fixes are tracked in the
[review response](2026-09-08_i1-review-response.md). The production boundary,
unchanged baselines, worktree discipline and merge/push prohibitions remain
in force. A fresh candidate `--diff` gate precedes the code commit, followed
by a clean committed-tip `--diff` run for the second reviewer. The previous
`--slow` record stays historical; this round does not edit either production
wire entry point that would trigger merge-protocol 5a.

[AGENT] Correction round complete at `061904f0`: the full candidate and
clean committed-source `--diff` gates both passed, exit 0. All 3,654 executable
and 394 negative rows match their baselines. The updated review response and
compact evidence form the second-review handoff. Follow-up records are docs
only; the branch is paused, with no second review, merge or push performed.

### Second review and landing authority

[AGENT] 2026-09-08. The supplied [second review](evidence/2026-09-08_i1-declarations/coordinator-review-update.md)
at `4eb2ab1c` is MERGE-CLEAN. Its only required follow-up, N5, is resolved
by the master plan's new R10 owed row for a declaration fixture re-pin
authorization guard. The optional N1 acceptance-boundary residual is named
under R7 for resolution before a production consumer. Runtime code and pins
are identical to the independently reviewed and gated source.

[USER] 2026-09-08, firsthand in this session: “updated review landed. can
you fix the remaining minor issue, then land it on main?” This supersedes
the prior second-review stop and authorizes the fast-forward merge after
the documentation checks. Push remains a separate sign-off. The
[review response](2026-09-08_i1-review-response.md) records this disposition.

[AGENT] Landing completed by fast-forward from `ae9c8079` to `960ee230`
on 2026-09-08. The [landing record](2026-09-08_i1-declaration-landing.md)
records checkpoints, validation scope and retained follow-ups. This closes
L1b; production I1 and master-plan R10 remain owed. No push was performed.
