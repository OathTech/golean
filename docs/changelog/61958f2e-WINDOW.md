# Changelog `61958f2e` → the window's offer commit (LIVE draft)

[AGENT packet A worker] 2026-09-27 — window charter row 0 (`docs/2026-09-23_batched-window-charter.md` §1),
packet A brief `docs/codex-briefs/2026-09-24_packet-A-contract.md` §6, run as an Opus 5.5 subagent under the
execution-model ruling of 2026-09-27 (`docs/2026-08-31_qrow-rulings.md`, «E6's shape, train r49 and the execution
model — RULED (2026-09-27)»). `61958f2e` is the customer's pin (train r39 close, 2026-09-17). «Now» is `main` @
`5946adfa` (train r49 close; the packet's input commit — the brief's `3fb4a0d1` superseded by the coordinator:
`git diff --stat 3fb4a0d1 5946adfa -- GoLean/GoCore` is empty; r49 moved only the decoder and the frontend). The
packet branch was rebased onto `main` @ `7d2a62e5` (r49 5a records + r50 docs: no `GoLean/` change), so every cell
holds there too. It now sits on `core/stray-panic-refusal-0927` @ `05d0dbd4` (under audit), whose changes are the
window line below, not the table (the table's line numbers are stated at `5946adfa` and hold there; the lane's edits shift later declarations in `GoLean/GoCore/Ops.lean` after line 1380 by 13–14 lines, e.g. `AccessTrace` 1841 → 1854 — packet A audit re-verification R1).

Every cell is RESOLVED from `git diff 61958f2e 5946adfa -- GoLean/` and `git show 61958f2e:<path>`; `file:line` is
at the commit named in its column (paths under `GoLean/GoCore/` unless given). `Tests/` is out of scope. Every
«what to touch» cell is an inference **[inf]**.

## Shapes changed since the pin

| Arm / shape | Before (61958f2e) | After (main @ 5946adfa) | What a re-pin must touch [inf] |
|---|---|---|---|
| `Step` arity | `inductive Step : Config → Store → Config → Store → Prop` (`Machine.lean:4390`) | `… → Store → AccessTrace → Prop` (`Machine.lean:5315`); `AccessTrace := List MemEvent` (`Ops.lean:1841`; `MemEvent = access \| hb \| attributed`, `:1821`) | [inf] every `Step` mention gains the label argument; `Prim`-style wrappers quantify or fix it |
| `stepFn`'s result | `Except Stop (Config × Store × Choices)` (`StepFn.lean:255`) | `Except Stop (Config × Store × Choices × AccessTrace)` (`StepFn.lean:326`) | [inf] every `stepFn … = .ok (c', s', ch')` premise gains a fourth component (`[]` on a pure step); destructuring lemmas bind one more |
| `stepFn_sound` / `step_complete` | `stepFn … = .ok (c', s', ch') → Step ctx c s c' s'` / converse `∃ ch ch'` (`MachineSound.lean:473`, `:819`) | `… = .ok (c', s', ch', tr) → Step ctx c s c' s' tr` / `Step ctx c s c' s' tr → ∃ ch ch', stepFn … = .ok (c', s', ch', tr)` (`MachineSound.lean:1681`, `:2079`) | [inf] every use: one more tuple component and one more `Step` argument, the same `tr` on both sides |
| read / write labels | no label (no `AccessTrace` type at the pin) | the emitting accessors: `Mem.load` → `[.access .read (.data l.canon)]`, `Mem.store` → `[.access .write …]`, map payload `Mem.mapRead` / `Mem.mapWrite` (`Ops.lean:1939`–`1968`) | [inf] read/write step equations name the singleton label |
| alloc label + `Store.alloc` | `Store.alloc : Store → GoValue → Ty → Loc × Store`, total, NO normalization (`Store.lean:41`) | NO alloc event (`AccessKind = read \| write \| atomicRead \| atomicWrite`, `Ops.lean:1745`); `Store.alloc : … → Except Stop (Loc × Store)` NORMALIZES the value at its type and refuses what the normalizer refuses (`Ops.lean:1251`); `HeapNormal ctx σ` is a `StateWf` conjunct (`StateWf.lean:708`) | [inf] allocation equations see a normalized cell and an `Except` result; `StateWf` users carry `HeapNormal` |
| `Trace.step` | `stepFn ctx s c ch = .ok (c₁, s₁, ch₁) → …` (`Trace.lean:18`) | `… = .ok (c₁, s₁, ch₁, tr) → …` (`Trace.lean:18`); `run_ok_iff` / `Trace.erase` statements textually unchanged (`Trace.lean:60`, `:42`) | [inf] none for users of `run_ok_iff` + `Trace.erase` only |
| `Step` rule count | 122 | 128 — added `unseqRunRecv`, `unseqRunAlloc`, `unseqRunWide` (`Machine.lean:6081`, `:6090`, `:6099`), `unseqRecvDone`, `unseqAllocDone`, `unseqWideDone` (`:6139`, `:6145`, `:6151`); none removed. Counting command, run at both commits: `git show <rev>:GoLean/GoCore/Machine.lean \| awk '/^inductive Step :/{f=1;next} f&&/^[^ -]/{exit} f&&/^  \| /{n++} END{print n}'` → 122 / 128 | [inf] an exhaustive `cases` on `Step` gains six arms |
| `Stmt` / `Cont` / `ChoiceSite` / `Config` constructors | 44 / 33 / 10 / 10 | IDENTICAL lists at both commits (verified by extracting each `inductive`'s `  \| ` constructor names from `Syntax.lean` / `Machine.lean` / `State.lean` at both revs and diffing: equal, in order) | [inf] none |
| the legacy `unseq-probe` triple | present | PRESENT and SURVIVES into the re-pin ([USER] 2026-09-27, rulings ledger above): `Stmt.unseqProbe` (`Syntax.lean:774`), `Cont.probeK` (`Machine.lean:3512`), `Step.unseqProbe` (`Machine.lean:6009`), `ChoiceSite.unseqPanic` (`State.lean:329`) | [inf] one extra `Cont` constructor and one `Step` rule to port; their retirement is a LATER removal-only change (the triple at the r52 tip, shape vs behaviour: § «The legacy evaluation-order triple» below; the line numbers in this cell are at `5946adfa`) |
| the wire | no `"unseq"` statement key-schema in the decoder (`GoLean/NativeToIR.lean` @ pin: 0 matches) | `{"stmt":"unseq","cells","occs","stores","then"}` and eight occurrence kinds `eval`/`invoke`/`target`/`load`/`guard`/`recv`/`allocate`/`wide` (key schemas `GoLean/NativeToIR.lean:212` and `:898`–`905`); the map arms inside a graph carry `keyType`/`valueType` CHECKED against the base's declared type (`GoLean/NativeToIR.lean:1004`, `:1007`); no other key schema changed (diff of the decoder's `some [...]` key tables: additions only) | [inf] re-emit fixtures; a fixture whose statement fires the observability trigger now sees `Stmt.unseq` |
| the decoder's named refusals | 62 `fail` sites, 0 `unseq:` | 142 `fail` sites (`git show <rev>:GoLean/NativeToIR.lean \| grep -cE '(^\|[^A-Za-z])fail +(s!)?"'` → 62 / 142; audit F6), 80 `unseq:`-prefixed named refusals (`grep -c 'fail s!"unseq'`), all in the `unseq` grammar (`decodeUnseq`, `GoLean/NativeToIR.lean:2278`); incl. E6a's `after` edge on a literal `allocate` (`:2545`) and the scope-exact source-local checks (`:1189`, `:1195`, `:1201`); no non-`unseq` `fail` line added or removed | [inf] none for wires the frontend emits; a hand-built wire meets the refusals by name |
| the window's contract modules (packet A) | — | NEW, in the default build via `GoLean.lean`: `GoLean/GoCore/BridgeSet.lean` (24 pinned statements — a drift fails the build) and `GoLean/GoCore/ExecutionStatement.lean` (`Prefix`, `Finish` with FIVE constructors incl. `fatal` — [AGENT] coordinator disposition 2026-09-27 — `LRun`, `replays`, `NoRefusal`, the owed `_stmt` Props; statements only, packet B proves; audit F1 resolved by `core/stray-panic-refusal-0927`, disposition (b), [AGENT] coordinator, disclosed at the merge ask); one `scripts/mem-callsites.tsv` row («NO EXECUTION», `program_bridge_stmt`) | [inf] import the two modules; `BridgeSet.lean`'s diff between pins IS the interface diff |

## Window lines (landed since the pin, per lane)

- **E6a (2026-09-24) — the `unseq` grammar.** The observability trigger admits a FAILING occurrence unordered
  against an E1 participant's window that holds another failing occurrence or may itself fail (panic identity —
  the EVENT-MEDIATED form, a faithful subset of the ruled wording; the general form posed); `len`/`cap` over map /
  channel operands; callees and methods of EVERY source unit (bare, `pkg.F`-qualified, receiver-qualified) — sweeps
  in imported and stdlib source-through units lower as `unseq` graphs. A consumer of a GoCore program sees
  `Stmt.unseq` where the legacy `unseq-probe` / ANF hoist stood in those sweeps (14 corpus rows; the raft twin's
  `raft.isHardStateEqual`, `raft.MustSync`, `raftpb.(*Snapshot).SizeMessage` — admitted through the unit boundary
  by Stage E's E3 rule, not by the refinement; all-forced singletons). No core constructor, `Step` rule or choice
  site changed; the legacy triple stays (see below: it SURVIVES into the re-pin).
- **E6a — the wire decoder** (`GoLean/NativeToIR.lean`): two named refusals — an `after` edge on a literal
  `allocate` (`slice-lit`, `map-lit`, `new` over a `struct-lit`); a source-local atom whose `type` annotation
  disagrees with the declaration IN SCOPE at its statement, or which names no local in scope (`LowerCtx.locals` —
  scope-exact since the audit fix round: block / clause scope, the innermost declaration wins). Emitted wires are
  unaffected.
- **E6a — the raft twin pin** e1a87725… → 1c4e7038… (three graphs born by the unit boundary under E3's rule;
  `scripts/check-frontend-pins`).
- **E6a — the corpus**: `evalorder/unseq-strings/str-index-status-diverse` born (the first status-diverse `unseq`
  row); `builtins/e13-sibling-panic-order/assert-left-min-inline`, `channels/recv-order/dead-recv-len-operand`
  strict → membership.
- **E6a audit fix round (2026-09-24) — the corpus and BUGS.md**: BUG-116 filed (fixed) — a late-realized failing
  NON-CALL operand left of an inline `len` / `cap` / `min` / `max` whose operand panics, call-free, answered the
  LEFT panic on main where gc realizes the built-in's operand's; seven membership rows born in
  `builtins/e13-sibling-panic-order` (`idx-left-vs-min-operand`, `idx-left-vs-len-slice-expr`,
  `deref-left-vs-len-operand`, `ptr-field-left-vs-len-operand`, `div-left-vs-len-operand`,
  `shift-left-vs-len-operand`, `compound-load-vs-len-operand`); BUG-032's A6 sentence corrected. Baseline 3761 →
  3768 = 3532 / 236.
- **E6a audit fix round 2 (2026-09-24) — the wire decoder** (`GoLean/NativeToIR.lean`): the audit
  re-verification's R1, a FAIL-CLOSED WRONG REFUSAL introduced by fix round 1 — a `range` statement's key / value
  variables leaked into the ENCLOSING block, so a legal program that shadows an outer variable of another type
  with a range variable and graphs the OUTER one after the loop was refused whole (gc and main answer 23; the
  key-variable spelling 9). A `range` node now contributes NOTHING to the enclosing scope (`rangeBinderLocals`,
  opened by `decodeRange` for the body alone); the scope rule is stated once, with the construct table, as the
  docstring on `nestedStmtKeys`. NATIVE witness `e6arange` (the auditor's two positive controls verbatim + the h12
  base), mutant `mut-local-range-var-after-loop` (55 → 56). No corpus row, no baseline change, the choice trace
  byte-identical.
- **2026-09-27 core/stray-panic-refusal-0927** (packet A audit F1; disposition (b), [AGENT] coordinator, disclosed at
  the merge ask): root-only reader `loadRoot` (+ `Mem.loadBinding`/`loadBindingFor`) at the six binding-cell reads; a
  non-root location refuses as `.internal «binding cell is not a root location»` instead of escaping `stepFn` as an
  unwound Go panic (audit F1); `Step.evalVar`'s premise follows; no row moved. (The lane note's «changelog line»,
  `docs/2026-09-27_stray-panic-refusal.md`, verbatim.)
- **E6 re-scoped ([USER] Mike 2026-09-27, verbatim, relayed — rulings ledger «E6's shape, train r49 and the
  execution model — RULED (2026-09-27)»):** E6a lands; E6b–E6d and the retirement E6e LEAVE the window's critical
  path. The legacy triple `Stmt.unseqProbe` / `Cont.probeK` / `Step.unseqProbe` / `ChoiceSite.unseqPanic`
  SURVIVES into the re-pin offer — one extra `Cont` constructor and one `Step` rule to port; retirement becomes a
  later removal-only change.

(The E6a lines above are the E6a lane's «changelog lines», `docs/2026-09-24_unseq-stage-e6a-handoff.md` §«Changelog
lines for the window», folded here verbatim except the closing clause of the first line, which pointed at E6e.)

## The legacy evaluation-order triple (survives the re-pin, [USER] 2026-09-27)

[AGENT records worker] 2026-09-28, at the logic team's request (their reply of 2026-09-28, rulings ledger «The logic
team's reply on the legacy triple (2026-09-28)»). Every cell is read from `git show 61958f2e:<path>` against the train
r52 tip `d640a5ac` (the step label + packet B landed); an aligned-block `diff` of each definition at the two commits.
`file:line` is at the commit of its column; paths under `GoLean/GoCore/` unless given. A SHAPE change alters an arity, an
index or a label field; a BEHAVIOUR change alters which configuration steps to which, or what the tape consumes. The
intermediate state (main @ `5946adfa`, after C1, before the label reshape): the four rules carried the `AccessTrace` label
`[]` (`Machine.lean:6010`–`6019` there) and the consult used `Choices.consumeAt` (`StepFn.lean:366` there).

| Constructor / arm | At `61958f2e` | At the tip `d640a5ac` | Shape vs behaviour | What a re-pin touches [inf] |
|---|---|---|---|---|
| `Stmt.unseqProbe (e : Expr)` | `Syntax.lean:689` (docstring from `:672`) | `Syntax.lean:774` (docstring from `:757`) | textually IDENTICAL, docstring included; `Stmt` constructor list identical (44) | nothing but the line shift |
| `Cont.probeK (k : Cont)` and its structural arms `Cont.tail` / `Cont.withTail` / `Cont.class` (`.probe`) | `Machine.lean:2751`; arms `:2802`, `:2838`, `:2871` | `Machine.lean:3530`; arms `:3581`, `:3617`, `:3650` | IDENTICAL (constructor, docstring, the three arms) | nothing |
| `ChoiceSite.unseqPanic` (the site; slot text DEFER = 0 / RAISE = 1) | `State.lean:344`; census entry `:263`–`282`; slot text `:379`–`380` | `State.lean:329`; `:248`–`267`; `:364`–`365` | IDENTICAL; `ChoiceSite` constructor list identical (10) | nothing |
| `Step.unseqProbe` — `.exec (.unseqProbe e) env k` → `.evalE e env (.probeK k)`, store unchanged | `Machine.lean:5071`, no label (`Step : Config → Store → Config → Store → Prop`, `:4390`) | `Machine.lean:6071`, label `⟨[], [], []⟩` (`Step : … → StepLabel → Prop`, `:5374`) | SHAPE only (the fifth index: C1's `AccessTrace`, then the reshape's `StepLabel`); same successor | the label argument (`⟨[], [], []⟩`) |
| `Step.probeValue` — `.retV v (.probeK k)` → `.next k` (the value discarded; no consult) | `Machine.lean:5073`, no label | `Machine.lean:6073`, `⟨[], [], []⟩` | SHAPE only | the label argument |
| `Step.probeDefer` — `.panicking chain (.probeK k)` → `.next k` (slot 0) | `Machine.lean:5077`, no label | `Machine.lean:6077`, `⟨[], [⟨.unseqPanic, 2, 0⟩], []⟩` | SHAPE only: the label's `picks` now RECORDS the consultation (site, bound 2, value 0); same successor | the label, whose `picks` names the pick |
| `Step.probeRaise` — `.panicking chain (.probeK k)` → `.panicking chain k` (slot 1) | `Machine.lean:5080`, no label | `Machine.lean:6080`, `⟨[], [⟨.unseqPanic, 2, 1⟩], []⟩` | SHAPE only, as `probeDefer` (value 1) | as `probeDefer` |
| `stepFn`'s `.exec (.unseqProbe e)` arm | `StepFn.lean:482`–`486`, result `(.evalE e env (.probeK k), s, choices)` | `StepFn.lean:556`–`560`, `…, choices, ⟨[], [], []⟩)` | SHAPE only (`stepFn`'s fourth component, `StepFn.lean:255` → `:329`) | the fourth tuple component |
| `stepFn`'s `.retV v (.probeK k')` arm | `StepFn.lean:761`–`764`, `(.next k', s, choices)` | `StepFn.lean:845`–`848`, `…, choices, ⟨[], [], []⟩)` | SHAPE only; still NO consult | the fourth component |
| `stepFn`'s `.panicking chain (.probeK k')` arm — THE consult | `StepFn.lean:282`–`296`: `let (pick, ch') := Choices.consumeAt .unseqPanic 2 choices`; `if pick = 0 then .next k' else .panicking chain k'` | `StepFn.lean:356`–`370`: `let (pick, ch', ps) := Choices.consumeAtE .unseqPanic 2 choices`; the same `if`; label `⟨[], ps, []⟩` | SHAPE only: `consumeAtE`'s pick and stream ARE `consumeAt`'s (definition `State.lean:467`–`471`; `Choices.consumeAtE_eq`, `:482`); `ps` = the record | the fourth component; a proof that unfolded `consumeAt` here now meets `consumeAtE` (`Choices.consumeAtE_eq` / `_inv` rewrite it back) |
| `.signal _ (.probeK _)` / `.next (.probeK _)` (unreachable; refused through `signalRefusal`'s expression-frame arm and the `.next` catch-all) | `StepFn.lean:835`, `:848`; the reachability comment `Machine.lean:5050`–`5070` | `StepFn.lean:919`, `:932`; `Machine.lean:6050`–`6070` | the refusals IDENTICAL (only the success returns gained a label); the comment identical | nothing |
| `seqConsumption`'s `.panicking _ (.probeK _) ↦ some (.unseqPanic, 2)`; `consumesUnseqPanic` | `Machine.lean:4322`; `:4277`–`4278` | `Machine.lean:5249`; `:5188`–`5189` | IDENTICAL code; `consumesUnseqPanic`'s DOCSTRING changed (the certified dedup engine enumerates the site since Stage D, 2026-09-20 — apparatus, not semantics) | nothing |
| the decoder's `"unseq-probe"` arm (`GoLean/NativeToIR.lean`; the two named refusals: an operand mentioning `recover()`, an allocating conversion) | `GoLean/NativeToIR.lean:1205`–`1223`; key schema `:199` | `GoLean/NativeToIR.lean:1794`–`1812`; key schema `:211` | IDENTICAL. NEW beside it (the graph path, Stage C onward): `decodeUnseq` refuses a legacy `unseq-probe` inside an `unseq` completion by name (`GoLean/NativeToIR.lean:2641`) — a mixture is refused; the probe itself is untouched | nothing for emitted wires |
| the stray-panic reader (`loadRoot`, `Ops.lean:1381`; 2026-09-27) | — | touches NO probe arm; a probed operand's binding-cell reads go through it | BEHAVIOUR unchanged on every reachable configuration (a non-root binding location is a machine-invariant breach, now an `.internal` refusal; no row moved) | nothing |

**The triple's choice consumption.** `ChoiceSite.unseqPanic` is consulted at exactly ONE place: `stepFn`'s
`.panicking chain (.probeK k')` arm (`StepFn.lean:282` at the pin, `:356` at the tip), mirrored by `seqConsumption`'s
`.panicking _ (.probeK _) ↦ some (.unseqPanic, 2)` (`Machine.lean:4322` / `:5249`). Its bound is the CONSTANT 2 — so the
uniform bound-≤-1 rule (`Choices.consumeAt`: `(0, ch)`, nothing popped, `State.lean:393`–`396` at the tip) never applies
at this site. A probe whose operand yields a value consults nothing (`.retV v (.probeK k') ↦ .next k'`). On a non-empty
tape the head `c` is popped and the pick is `c % 2` (`Choices.consume`, `State.lean:173`–`177`); on an EMPTY tape the pick
is 0 and the tape is unchanged — DEFER, the pre-E13 trajectory. Slot 0 DEFER steps to `.next k'` (the operand is
re-evaluated at its residual position after the sibling events); slot 1 RAISE propagates the panic now
(`.panicking chain k'`). All of this is textually the pin's. What the tip ADDS is the record: the step label's `picks`
carries `⟨.unseqPanic, 2, pick⟩` (`Choices.consumeAtE`, `State.lean:467`; the relation's rules state it literally,
`Machine.lean:6078`, `:6081`; `PrefixFacts.lean`'s `stepFn_consumption_some'` covers the arm at `:485`–`500`, and
`stepFn_picks_some`, `:300`, equates a step's `picks` with `PickRecord.ofPick` of `seqConsumption`'s site and bound). Because the bound is
2 > 1, the record is emitted on an EMPTY tape too (pick 0, the tape not advanced) — the uniform rule of
`consumeAtE`, not a site-specific choice. The pool layer's stream-obliviousness checker answers `false` at the site (fail closed;
`MultiStreams.lean:122` at the tip, `:119` at the pin), as at the pin.

**What changed around it: which programs reach the triple, not what it does.** At the pin the decoder had no `"unseq"`
graph statement (`GoLean/NativeToIR.lean` @ `61958f2e`: no match); every sibling-panic sweep the frontend handled lowered
through the probe. Since the pin, Stages C–E5 and then E6a moved sweeps to the `unseq` graph path AT LOWERING TIME: the
frontend emits fewer probes; the triple's rules are unchanged. The choice-trace `unseqPanic` consultation census over the
corpus records the movement stage by stage: 417 → 288 (Stage C, `docs/2026-09-19_unseq-stage-c-handoff.md:161`), 288 → 204
(Stage E, `docs/2026-09-21_unseq-stage-e-handoff.md:129`), 204 → 168 (E5, `docs/2026-09-22_unseq-stage-e5-handoff.md:137`),
168 → 96 (E6a, `docs/2026-09-24_unseq-stage-e6a-handoff.md:121`). E6a's emitter census
(`docs/2026-09-24_unseq-stage-e6a-handoff.md:97`, §3; the fix round re-took it at `:112`): legacy `unseq-probe` emission
**corpus 58 → 47** (in 17 packages), **the raft twin 128 → 128** (the twin gained 3 graphs at its unit boundary, no probe
removed); the 175 remaining emitters are classed at `:97`–`104`. The logic team's fourteen fixtures and eight F2 variants
lower with zero probes and zero graphs (`docs/2026-09-24_customer-fixture-inventory.md`), so for their fragment the
survivors cost `cases` arms only (their reply, 2026-09-28).

## Window rows (PENDING)

| Row | Line |
|---|---|
| E6e | OFF the critical path ([USER] 2026-09-27): no retirement in this window; the legacy triple SURVIVES (above). PENDING — filled by the landing lane, if any |
| label (2a) | **Row 2a, the label reshape** ([AGENT worker, lane `core/step-label-0928`], 2026-09-28; design note `docs/2026-09-28_step-label.md`; before = `main` @ `84f0a9e4`, after = the lane tip). `StepLabel := { trace : AccessTrace, picks : List PickRecord, out : List GoString }` (NEW, `Ops.lean:1878`) is `Step`'s fifth index and `stepFn`'s fourth component, and the pool event's label — ONE label type at both layers. Shapes, before → after: `Step : Config → Store → Config → Store → AccessTrace → Prop` (`Machine.lean:5315`) → `… → StepLabel → Prop` (`:5374`; still 128 rules; a pure rule's label `⟨[], [], []⟩`; a helper-trace rule's `⟨tr, [], []⟩`; the apply/entry rules take the label `deliver` returns); `stepFn : … → Except Stop (Config × Store × Choices × AccessTrace)` (`StepFn.lean:326`) → `… × StepLabel` (`:329`); `stepFn_sound` / `step_complete` (`MachineSound.lean:1681` / `:2079`) → same statements over `tr : StepLabel` (`:1685` / `:2103`); `StepEvent := {who, action, picks, out, trace}` (`Multi.lean:1009`) → `{who, action, label : StepLabel}` (`:1029`; `ev.picks` / `ev.out` / `ev.trace` kept as reducible projections of `ev.label`); `deliver` / `deliverS` / `deliverV` deliver a `StepLabel` (a delivered panic `⟨[], panicPicks, []⟩`, `panicPicks` a NEW optional argument, `[]` except at a frame entry's panic-path text pick); the consulting helpers return their records beside the stream — `enterFramePick(V)` `… × Choices` → `… × Choices × List PickRecord`, `applyStmtOp(.plan)` `Store × Choices × AccessTrace` → `Store × Choices × List PickRecord × AccessTrace` (`Commit.withStream ch ps c`), `applySyncOp` `Config × Store × Choices × AccessTrace` → `… × Choices × List PickRecord × AccessTrace`, `applySelect` `… × Choices × Option EvClause × AccessTrace` → `… × Choices × List PickRecord × Option EvClause × AccessTrace`, `spawnStep` `… × Choices × AccessTrace` → `… × Choices × List PickRecord × AccessTrace`; `StepE` labelled by `StepLabel` (`StepE.spawn`'s label `⟨edge :: child reads attributed, entry picks, []⟩`); `StepM` / `StepMFine` KEEP `AccessTrace` (their `thread` rule takes `l.trace` — the labelled pool relation is after the window, charter §2). NEW: `PickRecord.ofPick`, `Choices.consumeAtE_eq` / `_inv` (`State.lean`), `stmtOpOut` + `printOut?_toList` (`Machine.lean:4105` / `:4114`), `StepLabel.fold` + `StepLabel.fold_silent` (`Ops.lean:1889` / `:1895`), `stepThread_privateStep_label` (`MultiSound.lean:1707`, the pool projection). Content: `picks` = every consultation of bound > 1 the step KEEPS, exactly as `consumeAtE` returns it, in order (`mapIter`, `appendSpill`, `l2Entry`, `tryLock`, `nilValueMethodText`, `unseqPanic`, `unseqNext`; at the pool also `l1Sched`/`postOp`/`backEdge`, `l2Arrival`, `l4Waiter`, the tombstone's `repanicCollapse`; the driver's `l5ExitWindow` belongs to no step); `out` = the `print`/`println` bytes (`stmtOpOut`); the pool takes both FROM the sequential label (the former `(printOut? c).toList` re-derivation is gone). The event's `picks` channel now ALSO carries the sequential sites (before: pool-layer sites only). `initPrintRefusal?` RETAINED ([USER] 2026-09-24 ruling 10), text unchanged. ZERO behaviour change (the `--diff` gate, the choice trace and the raft twin — the handoff records the runs). Packet A's `ExecutionStatement.lean` RE-STATED over `StepLabel` (`Prefix`/`LRun`/classification carry `List StepLabel`; `replays` is replay BY RECORD over a label's picks — signature `List PickRecord → Choices → Choices → Prop`; `silent_projection_stmt` over `StepLabel.fold`); `BridgeSet.lean` RE-PINNED (rows 1, 2, 13, 15, 22 changed; rows 25–34 added; line numbers refreshed). [inf] A re-pin touches: every `Step`/`stepFn` label (`AccessTrace` → `StepLabel`; `[]` → `⟨[], [], []⟩`; a trace `tr` → `⟨tr, [], []⟩` or `l.trace`); every destructuring of the five helpers above (one more component); every `StepEvent` literal (`{ who, action, label }`); an exhaustive `cases` on `Step` names one more inaccessible (the helper trace no longer unifies with the index) at the helper-trace rules. The bridges over this label: row 2b below ([AGENT packet B worker]). |
| bridges (2b) | **Row 2b, the execution bridges** ([AGENT packet B worker], branch `window/packet-b-bridges-0928` off `core/step-label-0928` @ `61bdc65d`, 2026-09-28; handoff `docs/2026-09-28_packet-b-handoff.md`). Completes the label row: every `<name>_stmt` of `ExecutionStatement.lean` (23) is a `theorem <name>` in NEW `Prefix.lean` — the `Prefix` algebra (`prefix_refl`/`_comp`/`_split`/`_erase_steps`/`_erase_trace`/`_iter`), `Finish` against the executable (`finish_abort_step`, `finish_refused_step`, `finish_replay`), the fuel bridges with `ZeroCost` (`run_ok_iff`, `run_panic_iff`, `run_deadlock_iff`, `run_fuelOut_iff`), `replay_coverage` PREMISE-FREE (no `appendTargetLocal`), `classification` (unconditional, refusal-separate) and `classification_wf`, `silent_projection`, `single_embedding`, `program_bridge`, the four `boundary_*` statements; plus the boundary controls as `example`s. Supporting NEW modules: `PrefixFacts.lean` (`stepFn_picks_none` / `stepFn_picks_some`: a step's `l.picks` is exactly `PickRecord.ofPick` of `seqConsumption`'s site and bound at the tape's pick, `[]` when `none`; `stepFn_consumption_some'`: `stepFn_consumption_some` without its never-used `appendTargetLocal` premise) and `StepErrors.lean` (`stepFn_strict`: away from the abort and the four blocked forms `stepFn` raises only a refusal or `fatal` — NO STRAY PANIC, no deadlock, no race terminal, no fuel-out — machine-checked over the whole helper closure). Statements UNCHANGED; `stepFn`, `Step`, the rules, `Config`, `StepLabel`, `StepEvent` untouched. Theorem-only strengthening (label-reshape audit F1, [AGENT] coordinator disposition): `stepThread_privateStep_label` now also states `arrivalPlan … = .ok (none, ch₁, ps₁) ∧ selectApplyPlan c = none`. `BridgeSet.lean` RE-PINNED: row 34 changed; rows 35–64 added (the 23 statements by name, seven supporting facts written out, incl. `noRefusal_step`, the domain premise's one-step preservation). Comment-only (audit F3): `ExecutionStatement.lean`'s file:line references refreshed; `applyStmtOpCore.plan`'s print arm says the bytes are the step label's `out`. [inf] A re-pin touches: nothing for users of the pinned rows 1–33; a user of row 34 destructures two more conjuncts; the bridges are new API. |
| P | PENDING — filled by the landing lane |
| C3 | PENDING — filled by the landing lane |
| B6 | PENDING — filled by the landing lane |
| C4 | PENDING — filled by the landing lane |

LIVE through the window; FROZEN at the offer commit (charter row 7).
