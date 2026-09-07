# Typed-consumer sprint — handoff, closed at landing (2026-09-07)

**Status ([AGENT] landing chunk L6 `land/sprint-records`, 2026-09-07):
PAUSED BY THE USER on 2026-09-06; its work LANDED ON MAIN IN REVIEWED
CHUNKS on 2026-09-07; outcome PARTIAL in the charter's §6 vocabulary —
O1 and O2 landed, O3 partially, O4 NOT implemented, O5 is the landing
record itself; the critical decisions the sprint deferred are listed
below and remain the [USER]'s.** This file REPLACES the sprint-era handoff
of branch `typed-consumer-sprint` (17 dated checkpoints, 847 lines at the
tip `7edc298f`), which is retained verbatim on the archive branch
(`git show 7edc298f:docs/2026-09-05_typed-consumer-sprint-handoff.md`) and
is NOT reproduced here: its checkpoints record process handles, live
sessions and interim claims that the landing audits found stale or
unfounded (audit B R6, R15, R16, R18, R23). What is kept is what a reader
of main needs — the authority, the final outcome per required outcome,
the CORRECTED decision ledger, and where everything else lives.

## Authority, as relayed

- **The charter** (`docs/2026-09-05_typed-consumer-sprint-charter.md`,
  landed verbatim with a preface): K1–K5 approved by [USER] Mike on
  2026-09-05 — «Agree with all 5» — with K4 clarified: «merges *to main* are
  always user-approved. Feature branches can be merged to by agents, when
  standign approval is given by the user» (typo included). Both statements
  were received by the [AGENT] coordinator and relayed into the charter —
  cite as relayed, not firsthand (audit B R18: the sprint's records carried
  no relay marker on any of its seven [USER] citations; every [USER]
  statement in this file is marked).
- **The landing ruling** ([USER] Mike, 2026-09-07, verbatim as relayed by
  the [AGENT] coordinator — cite as relayed): «The evidence blob should not
  land, and generally we should not dump big evidence bundles on main (they
  can't be easily hosted on GH for one). Can you make a plan to land this
  work cleanly? We'll want to decompose and land in sane chunks that can be
  reviewed. And where appropriate fix some of the issues, eg. the choice
  tape stuff». The plan: `docs/2026-09-07_typed-sprint-landing-plan.md`.
- **The merges** (rounds 20–24, 2026-09-07): each landing chunk merged to
  main on a separate at-that-moment [USER] sign-off, relayed by the
  coordinator — «Go ahead and merge it» (twice), «go ahead and merge», «Go
  ahead with the merge» (the last, round 24 = L3, also ratifying D2, D5, the
  BUG-087-shape extension and the C4 re-classification, as the L3 note
  posed them — the tracked ruling record is `docs/2026-08-31_qrow-rulings.md`,
  "The merge-train round-24 ruling record"). Which quote closed which
  round is not recorded here beyond the last; the sign-offs are the
  coordinator's conversation record. Main after round 24:
  `29f77b43`, baseline 3654 = 3403 PASS / 251 FAIL (re-derived by awk).
- **The pause** ([USER], 2026-09-06): recorded by the sprint's pause-state
  snapshot (`docs/2026-09-06_typed-sprint-pause-state.md`, landed verbatim
  with a header) as "PAUSED BY USER" — an [AGENT] report of the statement;
  no verbatim text or relay marker exists for it. The sprint was never
  resumed; the landing superseded resumption.
- The charter's K4 standing approval was sprint-scoped feature-branch
  integration. It conferred nothing on main and expired with the sprint.
  No standing permission of any kind is asserted by this record.

## Required outcomes — FINAL status

Every "landed" below names the main commit; "not landed" names where the
work lives. Nothing here claims more than the chunk notes prove
(`docs/2026-09-07_land-{typed-core-proofs,gate-tooling,observer-terminal,panic-text-tape}.md`).

| Outcome | Final status | Landed via | Not landed / boundary |
|---|---|---|---|
| **O1** typed Boolean contract | **LANDED.** `BooleanTyping.TypedBooleanAdmission` + `checkTypedBoolean` with `checkTypedBoolean_iff`; the A3a unbound-variable counterexample REJECTED (`old_unbound_rejected`) beside its A3a acceptance; `setup_typed_exact`, `Inv.step` (every relational successor), `Inv.reachable_progress`, `Inv.run_readout`; shipped-driver `runProgramPool_typed` / `runProgramPool_no_refusal`; native fixture 3/3 differential. Axioms: `checkTypedBoolean_iff` on `[propext, Quot.sound]`, the driver theorems on the classical trio. | L1 `f70ea4bf` (gated tip `bfcd3d77`, `baseline diff FULL (3598/3598, no regression)`, `RESULT: PASS`) | Profile: `var/boolLit/not/and/or` + `seqn/block/initialization/assign(var)/ifThenElse/return` — no calls, no loops, no ints; no termination bound; `StateWf illTyped` still decides `true` (the exclusion is profile-local, F5). L3 changed nothing for O1 (the Boolean profile draws no choice). |
| **O2** typed recovery customer | **LANDED, in two chunks.** L1: `RecoveryAdmission` + `checkRecovery` with `checkRecovery_iff` (both A2 entries and the second native fixture admitted), `setup_typed_wf`/`setup_inv`, `Inv.step`, `Inv.reachable_progress` (normal ∨ nonempty semantic abort ∨ successor), `Inv.run_readout`, `Inv.run_choices`, call/defer entry and direct/indirect recovery control contracts, `Inv.pool_eq_runConfig`, `runProgramPool_eq_sequential`, the generic abort observer (`*_erasure`/`*_witness`/`Inv.observation_complete`); the Iris customer's reusable `wp_call`/`wp_frame_result`/`wp_store_cell`/`wp_initialize` and the shared-capture fixture proofs (`Shared`/`Reversed`/`Outside`/`DirectRecoveryControl`, 5/5 differential). L3: the TERMINAL slice (the plan's L1-T) RESTATED over the unchanged-then-reworked renderer — `StringPanic.stringPanicHead … : Option String`, `RecoveryTerminal.Inv.run_classified` with FOUR disjuncts (normal / the member at the stream's `repanicCollapse` pick on the reached chain / the NAMED invalid-first-line refusal / fuel exhaustion), `Inv.run_refusal_named`, `runProgram_typed`, `runProgramPool_typed`, `runProgramPool_refusal_named`; `RecoveryPoolObservationTyped` over the event's recorded pick; the spike's `Terminal.lean` restated (`*_no_refusal` → `*_refusal_named` + `fixtures_not_refused_at_fuel`); `scripts/check-recovery-terminal` as a ci step. | L1 `f70ea4bf`; L3 `a6a068ce` + `25c665b7` + `29f77b43` (round 24; pre-rebase gate at `0ccefe3f`: `baseline diff FULL (3634/3634, no regression)`, `RESULT: PASS`; at the merged tip the reconciler's re-pin 3654 = 3403 / 251, 0 PASS→non-PASS — L3 note §7.2) | The sprint's `*_no_refusal` theorems for the recovery profile are NOT on main: they were true only of the sprint's TOTAL renderer (audit A R3), which never landed; refusal-freedom is now conditional and named (`*_refusal_named`). Gate C's exit criterion is NOT met — the customer «still uses machine internals and unfolds operations» (`spikes/iris-customer/README.md:101`). Uncaught panic remains stuck in the adapter; no Iris `NotStuck` from typing. |
| **O3** evidence that can challenge the contract | **PARTIAL.** Landed as SMALL files: the positive/negative admission tests, the semantic counterexamples, the dependency audits (`*Audit.run`, all constants on the classical trio) and both native fixtures (L1); 36 born differential rows with gc witnesses — `panic-recover/panic-text/` (14), `panic-recover/repanic-collapse/` (22, 18 in the membership lane with both members gc-certified), `repanic-same-value-abort` re-laned — plus 38 gc witness programs with byte-exact stderr (`docs/evidence/2026-09-07_land-panic-text-tape/`) (L3); 20 observer rows — `panic-controls/` (9), `panic-markers/` (11) — and the six-row movement table (`docs/evidence/2026-09-07_land-observer-terminal/`) (L4); every chunk's ci gate tail; the two landing audits (`docs/2026-09-07_landing-audit-{A,B}.md`, this chunk). | L1, L3, L4, L6 | MANIFEST-ONLY (bytes on the archive branch, inventoried in `docs/evidence/2026-09-05_typed-consumer-sprint/MANIFEST.tsv` + `manifest/*.tsv`, 2,159 files / 114,156,315 B / 78 dirs): every sprint-era integration packet, seal, independent-review packet, full-run result table, source copy and archive. The sprint's ~40 independent-review COMMITS are on the archive branch and are credited by SHA in each chunk note; their prose is not on main. The `string-member` lane's 9 pins and 13 control roles: RETIRED (L3, D2), not landed. |
| **O4** B7 + its I1 companion | **NOT IMPLEMENTED.** B7: `grep ProgramCtx GoLean/` on main → one deferral comment (`GoLean/GoCore/Platform.lean:19`); the design note landed (`docs/2026-09-06_b7-context-store-design.md`, L1). I1: of the plan's 19-path declaration-wire sub-chunk L1b, only `GoLean/GoCore/Declaration.lean` (consumer-free identities) and `spikes/i1-declarations/{Prototype.lean,README.md}` landed (L1); the wire itself — `tools/nativefrontend/declaration.go` + tests, `GoLean/{NativeDeclaration,StrictJsonParse}.lean`, `Tests/{DeclarationWire,StrictJsonParse,DeclarationAudit}.lean`, `scripts/check-declarations`, `tools/check-declaration-wire.lean`, `tools/declaration-audit.py`, the `unclassified-formats.txt` rows, the four `docs/2026-09-06_i1-*.md` — did NOT land (L1 routed it to tooling, L2 routed it back to L1; neither cut it). | design note only (L1) | DEFERRED to a future chunk: the plan's **L1b** (`land/typed-core-proofs` sub-chunk "I1 declaration wire"), with its own gate (`scripts/check-frontend-pins` unchanged, certified set byte-identical — no executable wire byte may change) and the owed fixes A-R11 (track the fixture hashes or rename the step) and A-R12 (the serializer's `badLocalTypes` side effect; the nil-package silent default). Listed in `docs/2026-09-05_master-plan.md` §7.8 as owed. The B7 work lives on `typed-context-store` @ `ca1e01d5` (substantial uncommitted work; the V1 kernel-sharing completeness claim WITHDRAWN — pause-state record), the I1 envelope on `typed-i1-envelope` @ `3d49e9e9` (runtime V2 uncommitted), the byte-store candidate on `typed-byte-runtime` @ `35aee5d3` — all unmerged into the sprint tip and unreviewed by the landing. The C1 handoff exists as the tracked DRAFT `docs/2026-09-06_c1-contract-handoff.md`. |
| **O5** a branch ready for the closing decision | **REALIZED AS THE LANDING, not as the sprint's own closing packet** (never written — the sprint paused first). What stands in for it: the archive branch at the named commit `7edc298f` (retained UNMODIFIED, `docs/ARCHIVE.md`); the landing plan; four chunk notes with gate results and credits by SHA; this corrected ledger; the tracked pause-state and C1-handoff records; the roadmap update (`docs/2026-09-05_master-plan.md` §7.8); the manifest of what did not land. The charter's "Main is unchanged" held until the landing began: main moved by the chunks, each on its own sign-off, never by the sprint. | L6 (this chunk) + L1–L4 | The sprint's claims ledger (charter §6, "for each public theorem … status: proved, tested, assumed, or deferred") was never written as one document; the per-profile claim ledgers the sprint did write (`docs/2026-09-06_boolean-*`, `recovery-*-contract.md` …) are among the 32 sprint design/contract notes NO chunk landed — an owed records chunk (§7.8). The `GoLean/Interface.lean` docstring on main cites four of them. |

## Decision ledger — CORRECTED (audit B R15)

The sprint-era ledger consisted of three lines and ended «No critical issue
has yet been identified. No additional user decision is required to begin
the authorized work.» — the only occurrence of "critical" in 847 lines,
unchanged since kickoff, while the branch carried at least four charter-§7
critical issues that were adjudicated in-lane under a K3 reading rather
than frozen and packaged for the closing review (audit B R13, R14, R3,
R16). That sentence is WITHDRAWN. The table below is the closing packet
charter §6 required, written at landing: each issue with its reproducer,
the claim it affects, the rule, the alternatives, and its disposition.
Provenance: every disposition is [AGENT] unless it names a relayed [USER]
sign-off.

| # | issue (charter §7 class) | reproducer / affected claim | rule | alternatives | disposition at landing | cost of the deferral taken |
|---|---|---|---|---|---|---|
| 1 | **Terminal classification / crash-channel authentication** (B R14: "change observation or terminal policy") | `print("panic: forged\n\t"); panic("actual")` forges a panic observation under main's marker-search classifier; a fatal error DURING panic unwinding prints before `m.dying`, so `sync/mutex-unlock-fatal/during-panic-unwind` cannot be authenticated → PASS→FAIL/go-observation (BUG-106); with the channel MANDATORY (A-R6), four pre-`main` aborts have no acknowledgement → PASS→FAIL (BUG-107). Affected: how trusted surface #2 accepts an abort; `GOTRACEBACK=system` and the `main()` splice change the oracle's invocation. | `CLAUDE.md` trusted surface #2; charter §7; K3 excludes "changes to the trusted base" | (i) ratify the policy; (ii) refuse → re-cut to byte transport only (`d0dbd469`), five rows stay green on unauthenticated bytes | Decision packet D4 written as the "Authenticated crash observation" policy (L4 note §3, with the ownership boundary and the auditor's working forgery stated); **RATIFIED by the [USER] sign-off that merged L4** (relayed; the L4 note states that the merge sign-off is the ratification). BUG-107's THREE options (keep red / named exception / variable-initializer hook over an fd-passed channel) are **PENDING [USER]**; default (a) keep red is in force. | one PASS row lost honestly (BUG-106); four rows red pending BUG-107's ruling; `land/observer-fd-channel` owed |
| 2 | **`uintptr` latitude override** (B R13: "alter the trusted base" / "choose among unresolved interpretations of Go latitude") | red-first: Go 8 vs old model 15 (`uintptr` vs `uint64` identity; two cross-type assertions, method satisfaction); the repair un-refuses a refused observation kind and edits `GoLean/NativeToIR.lean` + four `GoLean/GoCore/` modules; it cites neither `docs/2026-08-21_w7-desugar-inventory.md:2740` («`uintptr` is a gc-pin of latitude R1 — record it there rather than "fix" it», J-8) nor latitude row R1 («observations of it refused»). Affected: latitude row R1, register extension #6, the certified set (5a fires). | w7 J-8; latitude R1; K3; merge protocol 5a | (a) record per w7/R1, red-first rows, observations stay refused; (b) fix with both records amended, third-lane review of the override, a REAL full + `--slow` run (the staged 3,643 baseline was a provisional union) | **NOT landed — L5 HELD; PENDING [USER] D1** (landing plan §2.5, §4; recommendation (a) now, (b) as its own later arc). Numbering: the sprint's "BUG-107" for this item exists only in the sprint worktree's staged index and in two evidence copies (manifest class `review`); main's BUG-107 is L4's pre-`main` abort entry; **the `uintptr` item takes the next free number when (if) L5 is ruled and lands** (recorded on BUG-107's MERGE-TRAIN NOTE). | the type-identity wrong answer stays unrepaired on main; the isolated repair (`typed-uintptr-identity` @ `5f185fb3`, full/slow job exit 0 in isolation) waits |
| 3 | **The R-1 authority reading — abort-line rendering** (B R3 / A R1–R3: "choose among unresolved interpretations of Go latitude") | `panic(r)` after `recover()` of `"orig"`: gc go1.26.5 prints `orig [recovered, repanicked]`, the sprint's machine `orig [recovered]` (a single hard-coded member in evaluator recursion, A-R2); `panic("a\n\xff")`: gc's first line `a`, the sprint's machine `"\x61\x0a\xff"` (an escape form no Go prints, A-R3); the `string-member` lane never compared gc's transported `messageBytes` (A-R1) — 5 of 9 PASS rows demonstrably divergent. Affected: the "observed ∈ modeled" lower bound on those rows; R-1's scope. | R-1 (`docs/2026-08-20_w32-re-envelope-charter.md`); `CLAUDE.md` "No semantic choice hides in evaluator recursion", "Fail closed, always"; BUG-087's ruling SHAPE | keep the lane with A-R1's fix and accept the reds; retire the lane; a byte-level observation channel (schema change) | **REDONE by L3 (round 24)**: the collapse is `ChoiceSite.repanicCollapse` on the tape (width 2 exactly at a recovered head with an equal successor payload; both members gc-certified in the membership lane); valid-UTF-8 first lines render byte-exactly (a strict-lane FIX); a string payload whose first line is not valid UTF-8 is REFUSED by name (D5 default (i)); the escape member is never a member; the `string-member` lane RETIRED (D2 default). D2, D5, the BUG-087-SHAPE extension and the C4 (c)→(a) re-classification were applied as [AGENT] defaults, tagged PENDING in every record, and **RULED [USER] 2026-09-07 at round 24 — «Go ahead with the merge»** (relayed; tracked in `docs/2026-08-31_qrow-rulings.md`; every PENDING tag now reads RULED). At the merged tip L3's renderer also flipped six of L4's embedded-LF rows FAIL→PASS (the retired lane's `Controls` role covered; FR-33 retired) — L3 note §7.2. | three `panic-text/invalid-*` rows red by name on BUG-004's `Cases:` line until a byte channel is ruled (D5(ii), its own arc); the abort-message TAIL is unobserved on both sides (FR-32) |
| 4 | **Withdrawn B7 V1 kernel-sharing completeness claim** (pause-state record; "weaken a theorem/gate" if it had been relied on) | V1's 1,998 roots / 2,117 borrowed declarations missed private declarations, metadata and recursor dependencies; V2 (4,142 roots + 20 helpers, 81 sealed files, 55.7 MB) is uncommitted and not independently replayed; the 4,356-root diagnostic FAILED (a dormant generated lemma borrows a live declaration). Affected: any B7 old/new equivalence claim. | charter §4 (B7 zero-drift + byte-identical traces); §6 (independent review; the implementer cannot waive its own finding) | — | **NOT landed; no claim on main** (O4 unimplemented). Recorded here so the withdrawal is tracked. | none on main |
| 5 | **The `.tmp` cleanup attribution** (B R23) | the sprint handoff's final checkpoint: «The user's authorized primary `.tmp` cleanup removed 68,122 files … approximately 14.2 GiB» — no quote, no date-time, no relay marker, no ledger entry. | `CLAUDE.md` provenance rule; the global rule on destructive operations | quote the [USER] text; or downgrade | **DOWNGRADED to [AGENT]**: an [AGENT]-executed deletion of 68,122 files older than seven days under the primary checkout's `.tmp/` on 2026-09-06 (~14.2 GiB), whose authorization is NOT evidenced in any tracked file. Its journal is gitignored scratch (`artifacts/tmp-cleanup` in the sprint worktree). It is not precedent for anything. | none |
| 6 | **The uncommitted `AGENTS.md` "Retired Worktrees" hunk** (B R5/R19: "take an action outside the approved authority") | grants "standing approval for routine retirement of finished, merged lanes" under a `[USER]` tag with no quote, three paragraphs below `AGENTS.md`'s own "Do not run `rm` … without explicit approval"; its cited storage charter is untracked. | the global rule: standing or implied permission is forbidden | — | **REJECTED outright; never on main** (landing plan §1 item 1). If the storage-maintenance branches ever land, that content is re-checked against the same rule (plan §5). | none |
| 7 | **The `CLAUDE.md` merge-protocol retitle** (B R4) | "The merge protocol (to main, exact, every time)" + a K4 paraphrase scoped gate-green and the audit ask off feature-branch merges; K4 spoke to approval only. | `CLAUDE.md`; K4's verbatim text | land a one-line approval-scoped note inside step 5; or not at all | **NOT landed; PENDING [USER] D6** (default: not landed — sprint-scoped, sprint over). | none |
| 8 | **The evidence payload** (B R7/R7a/R10/R11/R17) | 2,159 files / 114 MB / 36 `.tar.gz` / source copies / whole-file ledger copies, one carrying a BUG number the ledger lacked. | the 2026-09-07 ruling; `docs/evidence/README.md` rule 4 (record the SHA, not the tree) | — | **NOT landed**; inventoried in `docs/evidence/2026-09-05_typed-consumer-sprint/`; the size gate (L2) is the standing rule; its caps are **PENDING [USER] D7** (proposed [AGENT]). | none |

Also deferred by the landing, [USER]-owned: **D3** — the coverage worker
count (no verbatim ruling of "2 workers" exists in any tracked file; the
chunks ran at jobs 2 / 2 / 16 / 12 / ≤ 12 and recorded it).

## BUG numbering reconciliation (audit B R17)

- Main ends at **BUG-107 = L4's pre-`main` abort entry** (`60bbf466`,
  numbered against main's top BUG-104 at cut time, with a MERGE-TRAIN NOTE).
  BUG-105 (control-byte transport, fixed) and BUG-106 (fatal-during-unwind,
  open) are the sprint's numbers for the same two entries.
- The sprint's "BUG-107" — the `uintptr` repair — never reached main: it
  exists in the sprint worktree's staged, uncommitted index and in two
  whole-file ledger copies on the archive branch
  (`docs/evidence/2026-09-06_uintptr-disposition-independent/bugs-proposed.md`
  and `…/coverage-proposed.md`; manifest class `review`). The pause-state
  record's "BUG107" means that item.
- When (if) L5 is ruled and lands, the `uintptr` item takes the **next free
  number at landing** (landing plan §2.5 D1; BUG-107's MERGE-TRAIN NOTE
  says the same). No number is reserved.
- L3 (round 24) allocated no new BUG number: its three red rows are
  BUG-004 item 3's residue under D5 (main at `29f77b43`: 107 `## BUG-`
  headings, top BUG-107).

## Where everything else lives

- **Archive branch** `typed-consumer-sprint` @ `7edc298f` — the full
  96-commit history and the evidence payload, unmodified (`docs/ARCHIVE.md`;
  manifest `docs/evidence/2026-09-05_typed-consumer-sprint/`).
- **Lane branches, unmerged and unreviewed by the landing**:
  `typed-uintptr-identity` @ `5f185fb3` (L5, HELD), `typed-context-store` @
  `ca1e01d5` (B7), `typed-i1-envelope` @ `3d49e9e9` (I1), `typed-byte-runtime`
  @ `35aee5d3` (byte store), the `typed-*-review` branches; the
  storage-maintenance branches are out of the landing's scope (plan §5).
- **Landing records on main**: the plan; the chunk notes; the two landing
  audits; the pause-state and C1-handoff records; `docs/2026-09-05_master-plan.md`
  §7.8 (roadmap disposition, owed follow-ups, pending decisions).
- **Sprint design/contract notes NOT on main** (32 files, none landed by
  any chunk; an owed records chunk): `docs/2026-09-05_boolean-{runtime-contract-design,typing-design}.md`,
  `docs/2026-09-06_{abort-observation-contract,abort-observation-independent-review,boolean-initialization,boolean-program-contract,boolean-runtime-invariant,boolean-storage-setup,historical-string-member-argument,i1-admission-design,i1-declaration-wire,i1-json-boundary,i1-positive-declarations,panic-rendering-repair,recovery-control-contract,recovery-entry-contract,recovery-facade-customer,recovery-facade-migration,recovery-runtime-design,recovery-static-claims,recovery-terminal-contract,shared-recovery-customer,string-member-certificate-design-review,string-member-certificate-design,string-member-claims,string-member-design-review,string-member-fixture-argument,string-member-production-review-request,string-panic-member-assessment,string-panic-member-implementation}.md`.
  Four of them are cited by `GoLean/Interface.lean` on main
  (`boolean-program-contract`, `recovery-static-claims`,
  `recovery-entry-contract`, `recovery-control-contract`); the profiles'
  domains are stated meanwhile in `docs/2026-09-07_land-typed-core-proofs.md`
  §3. Several describe work that was REWORKED or RETIRED at landing (the
  string-member notes, the total-renderer terminal contract); each must
  land with a preface saying so, or be marked archive-only.

## Provenance

[AGENT] landing worker, lane `land-sprint-records`, worktree
`.claude/worktrees/land-sprint-records` off main `dd636996`, 2026-09-07.
Inputs read in full: the charter and handoff at `7edc298f`, the untracked
pause-state and C1 records in the sprint worktree, both landing audits,
the landing plan, the four chunk notes (L3's read from its branch before
round 24 merged), `docs/2026-09-05_master-plan.md` §7, BUG-105–107 on main.
Credits (sprint commits whose records this file supersedes): `10fefeb3`,
`5a4aca9e`, `c53bb6a7` and the handoff's checkpoint commits `7edc298f`,
`39235f65`, `c969079a`, `b34cee67`, `2a70246f`, `414a2abe`, `563c01de`,
`b3d6fa6e`, `30b09c08`, `123fd48e`, `77f154e0`, `26f0dc09`, `82e177c7`,
`354ef7f2`, `f251abcb`. No process was killed; nothing on the archive
branch, in the sprint worktree, on main or in `deps/` was modified; not
merged, not pushed.
