# Package-correct method identity — work charter

[AGENT] 2026-09-08. IN PROGRESS on `fix/package-method-identity`, worktree
`.claude/worktrees/fix-package-method-identity`, from main
`f54753fa91ed125fd600ffd11fcd5b10d4a5fe02`. Proposal: commit `b12b4a31`,
`docs/2026-09-08_next-increment-method-identity.md` on
`plan/method-identity-increment`. Roadmap: master-plan-v2 W4, FR-31 / BUG-098,
the bounded method-identity part of F7.

## Authority and objective

[USER] 2026-09-08, firsthand: "Endorsed, go ahead. Set up a charter and
execute on this goal." The same message attaches four conditions: one I1
member-identity system; identity distinct from display; compatibility with
future native promotion; three reviewable stages, with the BUG-098 guard
retained until the final stage, fresh pins/certification and a Cedar census.

Private methods with the same name and different declaring packages must
remain distinct from source emission through interface matching, generated
function identity and actual dispatch. The defining regression is a type
promoting both `p.m` and `q.m`: both method identities survive, both matching
interfaces are satisfied, and their calls return distinct sentinel results.

No main merge or push is authorized. The user supplies the independent
adversarial review as in the preceding increments. Each stage ends with a
separate committed source, measured gate record and review handoff. Pending
the user's clarification of review cadence, pause at each stage's handoff;
do not treat elapsed time as review acceptance.

## Three stages

| Stage | Scope and endpoint | Guard and baseline policy |
|---|---|---|
| 1 — wire and decoder | Executable method records and interface requirements carry I1 `Declaration.MemberId`; one shared producer and strict decoder; core stores the identity with name projection for unchanged matching; malformed-identity controls; justified twin wire re-pin and fresh slow certification | BUG-098 guard retained; all existing case results/stages unchanged; no claim of repaired satisfaction or dispatch |
| 2 — interface satisfaction | Requirements compare full identity and signature; exported-only coverage remains fail-closed; package/signature/Unicode matrix and kernel regressions; display text unchanged | Guard retained; new hand-built and controlled source tests establish the new matcher independently of its removal |
| 3 — dispatch and guard retirement | Package identity reaches generated function IDs, wrapper deduplication, interface anchors, method values/expressions and actual dispatch; collision controls; retire guard and its static twin; three BUG-098 rows green; fresh Cedar census | Every baseline movement explained; no PASS-to-refusal regression; fresh full differential and slow certification |

Stages are review units, not three unapproved main merges. Stage 1 deliberately
preserves current lookup behavior behind the standing guard; this boundary
must be named in its source comments, evidence and review ask. Any discovery
that the staging itself introduces a wrong answer is a finding and stops that
cut from being offered as green.

## Identity, display and promotion contract

[AGENT] The executable layer adopts `GoLean.GoCore.Declaration.MemberId`
itself, or a definitionally derived view; there is no second independent
package/name encoding or Unicode/export classifier. The executable wire's
member object uses I1's exact `{"name": ..., "package": ...}` schema. Shared
producer/decoder helpers enforce the same rules in both channels. A method's
original declaring package is obtained from the checked Go object, never
guessed from its receiver, embedding type, display name or call site.

The bare spelling remains a projection of the identity record for display.
Missing-method panic text, ordering and wrapper/recover behavior must match
the pinned Go oracle. A changed gc-visible observation is a finding, never
absorbed by a golden update. The current supported package-path grammar and
the imported full/exported/absent method-set distinctions remain in force.

Alignment with G-P and the [method-set record contract](2026-08-10_method-set-record-contract.md):
method identity denotes the declaring package/name independently of how a
callable body is reached. In this increment the frontend still materializes
promotion wrappers, and each dispatch target identifies its receiver plus
that full member identity. G-P can later resolve the embedding path in the
core and reuse the same member key and method-set coverage facts; it need
not infer a member from a wrapper name or invent new private-name semantics.
The function-key serialization is an internal target identifier, not a
second semantic member identity or a gc display string. Ordinary and promoted
targets must have an explicit collision/injectivity argument within the
existing supported key grammar before stage 3.

## Scope and gates

[AGENT] Authorized changes: native method identity emission/consumption,
the executable decoder, shared member helpers, core method records and
resolution, proof plumbing and kernel regression lemmas, focused Go/wire
tests, explicit CI steps as needed, pin/ledger/diagnostic records and compact
evidence. All interpreter/relation coherence theorems must keep pace; no
theorem weakening, axiom, proof hole, native decision or partial core code.

Excluded: B7/C1, native promotion implementation, the general F7 TypeId
redesign, I1 production envelope/marker removal, new imported-method support,
runtime-error representation, evaluation-order fixes, reflection and a Cedar
functional driver. New counterexamples outside this identity boundary are
recorded separately. Paused prototypes are read-only source material.

Every Lean/Lake command runs through `scripts/capped`. Initial envelope is
32 GiB, three Lean threads and twelve differential workers. Full builds/gates
take the primary checkout's box-wide build lock; target builds at at most
48 GiB use the existing exemption. Worktree dependencies are pinned by
`scripts/setup-deps`; warm artifacts may be independently copied from the
identical main source, without hardlinks or writable aliases between worktrees.

Before each runtime commit, full capped `scripts/ci --diff` must pass, and
wire/decoder stages additionally run fresh `--slow`; repeat certification at
clean committed sources before records-only handoffs. A source-bound full run
and written reason precede any baseline/pin update. The starting baseline is
3,654 executable rows (3,403 PASS / 251 FAIL) and 394 negative PASS. Stages 1/2
preserve those existing results; stage 3 records the three named improvements
and each other change or new control. No unexplained certified-set movement.
The train owes merge-protocol 5a at any eventual authorized wire/decoder merge.

Fresh method tests exercise exported/private Unicode names, identical package
names at different paths, signatures/variadicness, pointer/value receivers,
multi-hop promotion, embedded interfaces, method values/expressions, exact
missing-method text and distinct dispatched results. Negative mutations erase
package identity or collide wrapper keys and must fail for the intended cause.
Decoder controls reject malformed/missing/conflicting identity data by name.
Tests of schema validity do not claim source provenance or full Go typing.

Record cost for every new standing check and the total gate, with actual exit
codes, cache mode, source SHA/tree and pin hashes. New scratch stays under
this worktree's `.tmp`, uses symlink dependency overlays, is deleted on success
and retained on failure with output and a reason. Never delete old scratch.
Evidence remains below the existing size caps; no archive or source-copy
payloads on main. All decisions and findings carry [AGENT]/[USER] provenance.

The final stage re-runs the pinned Cedar census to test the historical
eight-of-twenty-four package claim, reporting `ast`, `resolved`, `all` and any
new refusal separately. Each stage pauses for the agreed review boundary;
merge and push remain separate explicit user decisions.
