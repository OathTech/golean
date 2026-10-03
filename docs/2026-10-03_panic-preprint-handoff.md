# Unit 6b — BUG-004 item 4, the preprint phase: lane handoff (`core/panic-preprint-1003`)

[AGENT worker, lane `core/panic-preprint-1003`] 2026-10-03. Window unit 6b (charter rev. 2; placement RULED
[USER] Mike 2026-09-30, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Yes, agree, do the fix
inside this window» — ledger `docs/2026-08-31_qrow-rulings.md` «BUG-004 item 4 (error/Stringer panic payloads) —
placement and design RULED (2026-09-30)»). Specification: the design note `docs/2026-09-30_bug004-item4-design.md`
with its §5 decisions as recommended — design (i), the preprint phase; the two-field `PanicEntry` encoding; the
per-pair identity consult at the existing `repanicCollapse` site (bound 2); the fatal text exact for string and
user-defined payloads, runtime-error payloads refused by name (BUG-099); option (ii) NOT taken; G-C3's elaboration
stop rule — and its probes `docs/evidence/2026-09-30_bug004-item4-design/probes.md` (cited `pNN`). Before = `main`
@ `cd043086` (train r59 closed); after = the lane tip. Branch complete + the audit ask posed is this lane's end
state; merge/push are the coordinator's and the [USER]'s. **No design gate was crossed; two implementation-level
refinements of the note's wording are recorded in §2 for the audit.** Evidence: `docs/evidence/2026-10-03_panic-preprint/`.

## 1. State (what landed)

**The shape.** gc's `preprintpanics` (`deps/go/src/runtime/panic.go:702`–`:730` at the pin) CALLS a panic
payload's `Error()` / `String()` on the panicking goroutine after every deferred call and before anything prints,
walking the chain newest → oldest and SKIPPING an entry whose older neighbour holds the identical eface (the older
is marked `repanicked`; `printpanics` then prints ` [recovered, repanicked]` on a recovered marked head and
suppresses the newer line — `:741`, `:751`). The machine does the same as ORDINARY machine steps at the empty
continuation:

- `inductive Rewrite | none | pending (member : MemberId) | unrecorded | done (text : GoString)`;
  `PanicEntry` gains `rewrite : Rewrite := .none` and `repanicked : Bool := false`. The mark is decided at the
  RAISE (`rewriteMark`/`panicEntryOf`, `Step.panicArgValue`): `Error() string` first, then `String() string`
  (gc's order, p01), by today's method-set check (`hasNoArgStringMethod`); a carrier without a method-set record
  is `.unrecorded` (BUG-053 — the abort refuses by name, recovering stays supported); the `runtime.Error` twin and
  the un-rewritten families are `.none`.
- `Config.abort?` keeps its TYPE (BridgeSet row 19); a `some` answer is a SETTLED chain at `.stop`
  (`splitNewestPending? (first :: rest) = none` — `Config.abort?_some_iff`). An unsettled chain at `.stop` is a
  running configuration.
- `Frame.preprintK (older : List PanicEntry) (entry : PanicEntry) (newer : List PanicEntry)` (appended last,
  `FrameClass.preprint`, crossed by no walk): the chain split around the newest pending entry.
- The steps, each at an EXISTING `stepFn` arm position (no positional `fun_cases` tag moved): the `.stop` arm's
  `stepPanicStop` (settled → today's abort verbatim; unsettled → the identity draw at a collision with the older
  neighbour, bound 2 — slot 0 drops the newer entry and marks the older (`preprintDrop`), slot 1 or no collision
  selects the entry into the frame); the `.next` catch-all's `stepNextOther` (`preprintDispatch` = `resolveMethod?`
  on the payload's dynamic type + `receiverAt` with the resolution's path/adjustment — the loads are the step's
  trace, a nil `*T` under a value method panics here as at any dispatch — re-queued as the nullary value call
  `.retV (.funcVal fid [recv]) (.callValCalleeK [] [] [] …)`, the `Entry.again` shape, so the frame entry rides the
  existing `callValCalleeK` position with its own `nilValueMethodText` consult); `stepFrameExit`'s
  `[], rl :: rls, []` sub-arm (the method frame on the preprint frame delivers its ONE result, `Mem.loadBinding`);
  the `.retV` catch-all's `stepRetOther` (stores `.done text`, resumes the chain at `.stop`); the `.panicking`
  non-glue arm's `panicUnwindStop` (a panic reaching the preprint frame is `.terminal (.fatal ("panic while printing
  panic value: " ++ t))` — `preprintFatalStop`: exact for a string payload's first line and a defined type with a
  display record; a runtime-error payload REFUSED by name (BUG-099: gc names `runtime.errorString` /
  `runtime.plainError`); other families refused as unpinned).
- The relation: seven rules — `preprintCollapse` / `preprintDistinct` / `preprintSelect` (the `.stop` arm, the pick
  record literal in the label as `probeDefer`/`probeRaise`), `preprintResolve` (through `deliver`), `preprintReturn`
  / `preprintFall` (the exit twins), `preprintStore`. `Step` 127 → 134. No rule for the fatal (as the sync-misuse
  fatals: `Finish.fatal`, cost 1).
- Rendering: `renderPanicPayload : PanicEntry → Option (String × Bool)` — the value arms FIRST (string, the twin,
  int, bool), then `renderPanicRewrite` (`.done text ⇒ stringFirstLine? text.bytes`; `.pending`/`.unrecorded ⇒
  none`; `.none ⇒` the defined-int `main.T(v)` shape, the method-set guard kept); `repanicEqualNext` additionally
  requires `first.rewrite ≠ .done _`; `recoveredSuffix` and `StringPanic.collapseBit` read
  `first.repanicked || (repanicEqualNext … && pick == 0)`; `abortRefusal` names `.unrecorded` and `.pending`.
- Projections: `seqConsumption`'s `.stop` arm and `consumesRepanicCollapse` cover the phase's collision draw;
  `poolThreadOblivious` refuses it (fail closed; the CLI enumerator carries such rows); `innerVecs` already
  refused the shape; `ChoiceTrace.repanicCollapseFacts` recomputes the phase's width.

**Proofs.** `stepFn_sound` / `step_complete` / `step_complete_any_wf_aux` (the seven rules), `step_preserves_wf_loc`
(seven cases; `panicChainSup_preprintDrop`, `preprintDispatch_locSup`), `stepFn_strict` (the helpers' strictness
leaves), `stepFn_consumption_none` / `_some` and `stepFn_picks_none` / `_some` (the `.stop` arm's draw:
`stepPanicStop_consumption_none` / `_some`; the catch-alls' stream transparency), `stepFrameExit_sound` and its
consumption lemmas (the sub-arm), `MachineEqb` (`Rewrite.eqb`, `PanicEntry.eqb` 4 conjuncts, the `preprintK` arm).
Every packet A/B `_stmt` theorem, `stepFn_no_stray_panic`, `finish_*`, `run_panic_iff`, `boundary_*`,
`classification` re-proved AS STATED. The rendering equations the logic side asked for: `renderPanicHead_text`,
`abortMsg_text` (+ `_refused`, `_ok`), `stepFn_text_abort` (+ `_refused`), `runConfig_text_abort` (+ `_refused`)
in `StringPanic.lean`, the string lemmas' shape with `rewritableBox first.value` and `first.rewrite = .done text` as
the payload premises. `BridgeSet.lean` RE-PIN 9: rows 1–154 byte-identical; rows 155–173 added.
`Tests/GoCoreAudit.lean`'s required list +20.

## 2. Decisions ([AGENT] implementation choices under the ruled design — flagged for the audit)

1. **One consult per step — the note's «phase step» (§2 (i) 3) is SPLIT.** The note fuses the identity consult and
   the frame entry into one step. The frame ENTRY itself can consult (`nilValueMethodText` on its panic path), so
   a fused step could draw two sites, which breaks `seqConsumption`'s one-site projection and `stepFn_picks_*`
   AS STATED. The lane splits: P1 (the `.stop` arm) draws the pair's identity and selects the entry into the
   preprint frame; P2 (the frame's `.next`) resolves the call and re-queues it as the existing `callValCalleeK`
   value-call shape (its entry is the next step, at an existing entry position); P3 (`.retV`) stores. Cost: +1
   machine step per called method against the note's [inf] count; every ruled decision (design (i), the two-field
   entry, the per-pair consult at the same site and bound, the fatal texts, option (ii) not taken) is untouched.
2. **The frame carries the chain SPLIT `(older, entry, newer)`, not `(i, chain)`.** Isomorphic
   (`i = older.length`, `chain = older ++ entry :: newer`); list-structural, so the wf and completeness proofs need
   no index arithmetic. The note's name `preprintK` is kept.

## 3. Statement changes (internal — unpinned on main; posed here, exact old/new). Correction (audit F6): `step_abort_elim`'s NEW form is pinned as BridgeSet row 170 (`step_stop_unsettled` row 171)

| Theorem | Old | New |
|---|---|---|
| `Prefix.abort?_some` | `c.abort? = some (first, rest) → c = .panicking (first :: rest) .stop` | `… → c = .panicking (first :: rest) .stop ∧ splitNewestPending? (first :: rest) = none` |
| `Prefix.stepFn_abort` | `stepFn ctx s (.panicking (first :: rest) .stop) ch = (match abortMsg … with …)` | the same equation under the hypothesis `(hs : splitNewestPending? (first :: rest) = none)` |
| `MachineSound.step_abort_elim` | `¬ Step ctx (.panicking chain .stop) σ c' σ' tr` | `splitNewestPending? chain = none → ¬ Step ctx (.panicking chain .stop) σ c' σ' tr` (+ the converse `step_stop_unsettled`) |

Every pinned `_stmt` keeps its text (they are stated through `c.abort?`, `abortMsg`, `repanicCollapseWidth`).
`MultiSound.stepFn_abort` (pool side) keeps its statement (over `c.abort? = some …`).

## 4. Rows born / flipped

Flipped FAIL → PASS: `panic-recover/panic-defined-payload-methods/{error,stringer}` (`boom` / `strung`; off
BUG-004's Cases line; item 4 FIXED in `docs/BUGS.md`). Born: `panic-recover/panic-preprint/*` (21 rows, one per
design probe, gc1.26.5-validated under the harness env before the gate — statuses, first lines, `CALLED` counts and
exit codes agree with `probes.md`): 13 strict (`error-wins-over-stringer`, `nil-ptr-receiver-const`,
`ptr-method-not-in-value-set`, `post-defer-state`, `recovered-not-called`, `chain-order`,
`recover-inside-method`, `wrong-signature-not-rewritten`, `promoted-error`, `multiline-text`, the two fatals
`method-panics-string` / `method-panics-defined`), 5 membership (`repanic-same-box`, `repanic-reboxed`,
`repanic-distinct-equal`, `unrecovered-equal-pair`, `panic-nil-repanic`; `members=2`, gc's draw recorded per row),
1 deadlock (`blocking-method-deadlock`), 1 confluent (`other-goroutine-blocked`), 2 RED by design
(`nil-ptr-receiver-deref`, `value-method-nil-ptr` — refused by name, BUG-099's Cases line).

## 5. Gate record

**Base moved under the lane:** the branch was cut at `cd043086` and fast-forwarded to `aeab81c5` (train r59's
close, records only — a certified JSON, the C4 handoff, an evidence tail; no overlap with the lane's files) before
the first gate finished; the 5a records refresh is therefore in the tree.

**Focused runs before the gate** (`scripts/diff-one`; `docs/evidence/2026-10-03_panic-preprint/
diff-one-born-and-flips.tsv`): the two flips PASS (`boom` / `strung`); 19 of the 21 born rows PASS (the five
membership rows at `enumerated=2 exhibited=1 draws=32` — gc exhibits one member per row, as the probes recorded;
the confluent row `|set|=1 certified over all schedules`; the deadlock row and both fatals exact); the two
refused-by-name fatals FAIL/lean-observation with the BUG-099 text, as designed. `lake exe gocore-eval-tests` PASS.

**First `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (pre re-pin, pre test fix; tail in the evidence
dir):** RESULT FAIL on exactly (a) the core-audit step — two TEST modules the audit harness compiles
(`Tests/StringPanicMembers.lean`'s generic string-abort theorems were quantified over EVERY tail `rest` and are
false once a tail may owe a rewrite — they now take the settled premise `splitNewestPending? (entry :: rest) =
none`; the new `Tests/PanicRendering.lean` kernel tests used `=` on `BEq`-only types and `⟨7⟩` for a `Nat`
index — fixed; `scripts/check-core-audit` then PASS, +20 required names) — and (b) the differential's baseline
drift: the two planned flips, the 21 born rows, and `imported-goose/channel/google-search`
(`certification: STALE certification: changed dependency build/files/GoLean/ChoiceTrace.lean` — the 5a row at a
lane tip, re-certified by the train). 3821 cases run, 3583 PASS / 238 FAIL (the 238 = 237 − 2 flips + 2 born reds
+ the 5a row). NO other row's result or stage moved. Baseline RE-PINNED surgically (header prose + counts; the two
rows flipped in place; the 21 rows inserted at their sorted position with the lane as stage for the membership /
confluent rows); the re-diff shows the 5a row only (`ci-diff-1-drift.txt`).

**Whole-corpus choice trace vs main** (`docs/evidence/2026-10-03_panic-preprint/choice-trace.txt`;
`scripts/choice-trace-corpus --dump` on both sides over this worktree's corpus, main's side with the primary
checkout's binary built by train r59, the two precedent exclusions): every consumption of every row OUTSIDE the 23
lane ids is byte-identical (26445 dump rows, sha `79b1c69b56da4b44` both sides) and every per-row × stream result
outside them is identical; inside them the two flips move `unsupported → panic` and the born membership rows show
the phase's `repanicCollapse` bound-2 draw at their equal pair.

**Twin:** `check-frontend-pins: ok [twin-wire] — fresh emit = pinned wire (d5186f43aae8…)` — byte-identical (the
wire is untouched).

**Elaboration A/B** (`elaboration-ab.tsv`, back-to-back per module against a detached worktree at `aeab81c5`,
same box load): Machine 1.07×, StateWf 1.05×, StepFn 1.00×, MachineEqb 1.02×, StringPanic 0.74×, MachineSound
1.17× (69 → 81 s), PrefixFacts 1.44× (16 → 23 s — the largest: the two `.stop`-arm record lemmas and the two
catch-all `okp` cases), StepErrors 1.16× (213 → 248 s), BridgeSet 1.10×. No module over the G-C3 1.5× stop; no
`maxHeartbeats` raised or added.

**Second `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the tip tree (post re-pin, post test fix;
`ci-diff-2-tail.txt`):** RESULT FAIL on EXACTLY the 5a pair — `certificate provenance` (STALE certification: the
lane changes the semantic sources; the train re-certifies at merge) and the baseline diff's one drift line,
`imported-goose/channel/google-search PASS/membership → FAIL/membership` (the certified row) — every other step
ok: core build warning-free, core totality audit (the required list +20), bug-index cross-check, feature coverage,
frontend pins (twin byte-identical), eval tests 298 ok, re-pin guard 0 PASS→non-PASS flips, 3821 run = 3583 PASS /
238 FAIL (237 + the 5a row). The tree committed differs from the gated one by this record and the gate tail only.

## 6. Open items / follow-ups

- Library `Error()` bodies reached only through a payload may be absent from a reachability-pruned wire
  (`tools/nativefrontend/stdlibreach.go`); the phase refuses by name (`callee?` none → `GoCore function not found`).
  The reach set gaining «methods of panic-payload types» is a frontend follow-up (wire content, `--slow`).
- BUG-099 now also gates the two preprint fatals (concrete runtime-error type names).
- Packet D states its abort and frame-exit equations over the phase's arms (`stepPanicStop`, `stepNextOther`,
  `stepRetOther`, the `stepFrameExit` sub-arm) — statable as landed.

## 7. Landing notes ([AGENT] coordinator, train r60)

[USER] Mike 2026-10-03, verbatim, relayed: «Great, land it» — the merge sign-off, acknowledging the three internal statement changes of §3. Audit (`docs/2026-10-03_panic-preprint-audit.md`, MERGE-CLEAN) follow-ups recorded, not done here: F1 — `PrefixFacts` elaborates at 1.48× (2 % under the G-C3 stop); the next lane that adds `stepFn` arms restructures the `fun_cases` sweeps in `stepFn_picks_none/_some` first; F2 — the BUG-099 refusal in `preprintFatalStop` also covers `*runtime.PanicNilError` (`panic(nil)` inside `Error()`), its text names only two types — widen the text with BUG-099's fix; F3 — a non-head `.unrecorded` entry is treated as settled (not constructible via the frontend; BUG-053 area); F4 — fatal payloads of pointer/basic type refuse as «payload family not pinned» (cheap widenings).

## Merge train r60 — the 5a record ([AGENT] coordinator, 2026-10-03)

[USER] Mike 2026-10-03 «Great, land it» (relayed). Pre-merge main `aeab81c5` → `refs/snapshots/r60/main`; train tip `a1327d1a`
fast-forwarded; fresh primary build (0 foreign references). `release-check` EXIT=2 (EXPECTED — STALE,
`build/files/GoLean/ChoiceTrace.lean`); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1, 1217 s — red on EXACTLY the
5a pair; 3821 rows, 3583 PASS / 238 FAIL = the pin 3584 / 237 with the one 5a-class row red. Candidate: `claim` and
`observations_sha256` IDENTICAL (receipt `a1327d1a`, 150.961 s) — INSTALLED; a provenance refresh. Tail:
`docs/evidence/2026-10-03_panic-preprint/r60-ci-slow.tail.txt`.

**Green re-run at the records commit `53c5ea28`** ([AGENT] coordinator, 2026-10-03): `ci --diff` EXIT=0, `RESULT: PASS`, baseline diff FULL 3821/3821, certificate provenance ok. Round 60 closed: the panic preprint phase landed.
