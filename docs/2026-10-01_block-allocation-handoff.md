# C4 — block-entry allocation: lane handoff (`core/block-allocation-1001`)

[AGENT worker, lane `core/block-allocation-1001`] 2026-10-01. Window row 6 (charter rev. 2, [USER]-RULED
2026-09-24, relayed). Design note `docs/2026-10-01_gc4-block-allocation-design.md` — G-C4 PASSED with all nine §7
decisions ([USER] Mike 2026-10-01, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Those costs seem
fine to me. Go ahead with these decisions. You can work on block allocation on the basis of approving all of your
recommendations.»; ledger `docs/2026-08-31_qrow-rulings.md` «G-C4 (block-entry allocation) passed — RULED»). Before =
`main` @ `52eddf4c`; after = the lane tip. Branch complete + the audit ask posed is this lane's end state; merge/push
are the coordinator's and the [USER]'s. **The one STOPPED item (§4: a fuel-budget row flipped at its pinned work
cap — decision 7) was RULED 2026-10-03 — option (a), raise the row's work cap:** [USER] Mike, 2026-10-03, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «yeah, agree with 1, land it». The row's `work=500000` is landed (§4);
the gate is red on the expected 5a pair only. The pre-merge audit (`docs/2026-10-02_block-allocation-audit.md`,
branch `review/block-allocation-1001` @ `305afc95`) is MERGE-CLEAN; its records corrections F1–F6 are folded in below,
each marked «(audit Fn)». Evidence: `docs/evidence/2026-10-01_block-allocation/`.

## 1. State (what landed)

**The shape.** Every local of a decoded program is a declaration of its innermost enclosing `.block`, allocated at the
block's entry by `Step.block` (`allocDecls` over `env.pushScope`), zero-valued at its declared type; its initializer
stays at the source point as the `.assign` it already was. `Stmt.initialization`, `Step.initialization` and `stepFn`'s
arm (with its two refusal texts) are DELETED: `Stmt` 45 → 44 constructors (audit F3: 5b's `randIntn` landed between the design note's base and this lane's), `Step` 128 → 127 rules. A `Frame.seq rest
env`'s environment is fixed from creation to pop — no rule rewrites it. The `unseq` sweep (decision 3, D3 (b)):
`unseqEnter` allocates the binder cells over `env.pushScope` (a sweep-private scope — the sweep frame's `env`) and its
continuation keeps the source environment (`.seq rest env k`, was `.seq rest env' k`); `thenB` runs under the sweep
scope, so its binder reads resolve there and its source assignments reach the enclosing block's cells. Side effect to
record (audit F6, by the rule text): the binder cells no longer persist in the enclosing `.seq` environment after a
sweep, so the B6 F3 runtime check `unseqEntryCheck?` («binder already bound in the enclosing scope») can no longer fire
for two sweeps in ONE block that reuse a binder id — `main` refused such a hand-built wire by name at the second ENTER;
the lane accepts it (harmlessly: the cells are private). Decoded programs are unaffected (the frontend numbers binders
uniquely per function); the Stage C mutants still pass; K2's «distinct binders per sweep» is now a frontend fact. `seqCont`
unchanged (decision 4): with D3 (b) its non-splicing branch IS reached — at a sweep completion whose `thenB` is a
`.seqn` (`seqCont ss env' (.seq rest env k)` with `env' ≠ env`) — and is correct there (the design note's «unreachable
for decoded programs» aside was too strong; the ruling — keep the test — stands). Wire `golean-native-v3` UNCHANGED
(decision 2, W1): the decoder hoists.

**Decoder (`GoLean/NativeToIR.lean` only; commit `59ac9431`).** `LowerSt.pending` + `declarePending` /
`declareTargets` / `declTmp` / `closeBlock(With)`: every former `.initialization` site records its declaration on the
innermost OPEN block; the block closers claim the recorded list as `.block decls stmts` — the wire `block`, the if-init
block, `decodeFor`'s init / `loop` / body blocks, the three index / chan / string range outer + iteration blocks
(`mapRange` runs the wire body, checked to be a block — D1, fail closed). The decode order is the old one, so
temporary ids are unchanged wherever a spelling has one type. **D5 as realized ([AGENT] implementation choice under
decision 5 — flagged for the audit):** a DECLARED temporary is interned per `(spelling, type)` (`temps : Array (String ×
Option Ty)`; the name table keeps the spelling). Reason: a block-entry cell has ONE declared type and `storeLoc`
normalizes at it, so the note's «one cell per id» for `_ = a; _ = s` (`$blank0` at `int` and at `string` in one block)
would have been one wrong-typed cell — a `writeAt` refusal on common rows — not an unobservable share; with the typed
key the share is exactly the same-spelling-same-type case, which is unobservable as the note argued. The same id at
two types in one block refuses by name (unreachable now); a declaration left pending at function end refuses by name.
CONFIRMED by the audit (F5: sound, the minimal correct reading; probe p11 — `$blank0`/`$cr0`/`$ta`/`$mlv` at two types in
one block — identical on both binaries and to gc) and ACCEPTED by the landing. Consequence to record (audit F5): a
function's `locals` name table may now carry the same `$`-spelling twice (kind `.temp`, two ids); `Func.localsOk` /
`tableNamed` accept it.
The `.seqn #[s]` wrappers were kept (no shape change beyond the deleted declarations).

**Core (commit `58fe18f9`).** `Syntax.lean` (constructor deleted; the `UnseqGraph` / `unseq` docstrings),
`Machine.lean` (rule deleted; `unseqEnter` D3 (b); docs), `StepFn.lean` (arm deleted; `stepUnseqEnter` D3 (b)),
`Unseq.lean` (`Stmt.names`), `Locals.lean` (`Stmt.declIds`), `StateWf.lean` (`Stmt.locSup`; the `initialization` case
gone; the `unseqEnter` case over `pushScope_locSup`), `SyntaxEqb.lean`, `AdmissionIndices.lean`,
`AdmissionPolicy.lean` (`BoolStmt.initialization` gone; an unused simp argument dropped), `MachineSound.lean` (the two
`case13` blocks deleted; every positional `fun_cases` tag ≥ 16 renumbered by −3 — the deleted arm contributed THREE
cases: the ok path and its two refusals; the design note's «shift by one» undercounted), `PrefixFacts.lean` (the same
−3). `stepFn_sound` / `step_complete`, every packet A/B `_stmt` theorem and `StepErrors.stepFn_strict` re-proved AS
STATED; no new or raised `maxHeartbeats`. `scripts/mem-callsites.tsv`: the two rows naming the deleted sites dropped
(commit `ed423c72`; the check demands it: an inventory naming absent sites is a false witness).

**D8 — the layout function and the lifetime lemmas** (decision 8; `Machine.lean` unless noted): `entrySlot s i :=
.base ⟨s.heap.size + i⟩` with `entrySlot_def` / `_inj` / `_not_allocated`; `blockEntry_shift` / `_lookup` /
`_lookup_outer` / `_zero` (+ `allocDecls_zero`, `allocDecls_heap_get_lt`, `Store.alloc_cell`); `blockEntry_fresh`
(`StateWf.lean`, over the sup laws); `blockExit_store_eq` (`StepFn.lean`, the executable equation beside
`Step.seqDone`); `heap_size_mono` (`StateWf.lean`, the `step_preserves_wf_loc` conjunct named — it carries that
theorem's `StateWf`/`ConfigWf` premises); `enterFrame_shift`; `frameEntry_lookup_arg` / `_result` (rows 124–125
restated through `entrySlot`); `frameEntry_fresh` (layout arithmetic: `s₁.heap.size + n ≤ s₂.heap.size → entrySlot s₁
i ≠ entrySlot s₂ j` for `i < n`; the lifetime premise is `heap_size_mono` composed); the D7 pair as equations —
`pushDefer_saves_values` (the deferred record is `(callee value, argument values)`; `pushDefer` takes no store) and
`funcVal_captures_locs` (`applyStrictOp … (.funcValOf fid) vs = .ok (.funcVal fid vs, s, [])`) beside `Step.evalRef`
(a capture operand `.ref x` is the cell's address). `BridgeSet.lean` RE-PIN 8 (the note said «RE-PIN 7»; 5b took that
number): rows 1–131 and 133–135 byte-identical; **row 132 RE-PINNED** (D3 (b) — it pins the `unseqEnter` rule
decision 3 changes; the note's «rows 1–132 unchanged» overlooked that); rows 136–154 added; the row-132 re-pin is
ACCEPTED by the landing (the audit confirms rows 1–131/133–135 byte-identical). `Tests/GoCoreAudit.lean`'s
required list +19 (core audit PASS).

**Tests.** `Tests/GoCoreContract.lean` (`zeroBody`, `scopedFunction`), `Tests/GoCoreEval.lean`
(`coreClosureShareFunction`), `Tests/UnseqScheduler.lean` (R5: `thenDeclS` is the assign; K2's `x`/`y` and K3's
per-iteration `x` are block declarations — K3's loop body is a `.block #[x]`) rewritten to the block form; expected
outputs unchanged (eval 298 ok; unseq scheduler PASS).

## 2. Runs (the acceptance list)

1. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, box-wide lock held, at `59ac9431` (the hoist
   alone; EXIT 1, 1047 s) and at `58fe18f9` (the deletion + D8; EXIT 1, 909 s): `RESULT: FAIL` on the expected 5a
   pair — `certificate provenance` (STALE: changed compiled inputs) and the drift line `imported-goose/channel/
   google-search baseline[PASS/membership] -> now[FAIL/membership]` (the certified slow-tier row, CERTIFIED-CACHED →
   STALE; the r55/r57 precedent) — AND on ONE further drift line, `sync/trylock/spin-until-trylock baseline[PASS/
   membership] -> now[FAIL/membership]` (§4). `differential coverage summary: cases=3800 pass=3561 fail=239` = the
   baseline's 3563 / 237 with those two lines. At `58fe18f9` also `check-mem-callsites` (the two stale rows; fixed at
   `ed423c72`, PASS 71 rows). Every other step ok both times: core build warning-free, core totality audit, admission,
   declarations, wire boundary, method identity, unseq scheduler (Stage B) + wire (Stage C), frontend pins (**the raft
   twin = the pinned bytes — the wire does not change**), import-goose, frontend unit tests, lowering diagnostics,
   harness unit tests, eval tests 298 ok, negative baseline 394. NO `baselines/native-full.tsv` edit; nothing under
   `baselines/` touched. Tails: `ci-diff-2a-*.txt`, `ci-diff-2b-*.txt`. **After the ruling** (`14231757`, the row's
   `work=500000`): the same gate EXIT 1, 850 s, red on EXACTLY the 5a pair — `certificate provenance` + the one drift line
   `imported-goose/channel/google-search` — `cases=3800 pass=3562 fail=238` = the baseline's 3563 / 237 with that line;
   `spin-until-trylock` PASS. Tail: `ci-diff-ruled-*.txt`.
2. **Whole-corpus choice trace, byte-identical.** `scripts/choice-trace-corpus --dump` (the B6 method; excludes
   `goroutines/send-then-spin`, `strings/trimspace-repeat/repeat-bound-refused`) — pre = the primary checkout at
   `main` @ `52eddf4c` with its certified binary (`579c0206…`), post = the lane @ `58fe18f9`: 14 of 15 tsv/txt files
   identical modulo the `--out` path (`results-0.tsv` — per row × stream status, consumption count, wide count,
   per-site menu, `obsHash`, driver agreement — IDENTICAL); 26445 dump rows on both sides, concatenated dumps sha256
   `6bf9800841e8e5c4` on both; 3764 rows exported, the same 34 frontend refusals. `summary.txt` differs only in the
   truncation of the pre-existing BUG-078 line (the longer `--out` path). Picks UNCHANGED, observations UNCHANGED.
   `choice-trace.txt`.
3. **Twin.** Byte-identical to the pin (`scripts/check-frontend-pins` ok in both gates; the frontend is untouched).
4. **The certified slow-tier row** (`GOLEAN_SLOW=1 scripts/diff-one imported-goose/channel/google-search` at the lane):
   «Fresh certification: unchanged set» — the six members, `observations_sha256 e40ba07d…` identical to the tracked
   record, `claim` identical (wire `f448d579…` unchanged); statistics moved as the note allowed: nodes 6193933 →
   5908017, edges = steps 6565663 → 6279747 (−4.4%: fewer steps per block entry), `dedupHits` 371731 → 371731
   (identical), wall 156.9 s → 105.8 s; `stats_sha256` moved. The candidate is at
   `artifacts/coverage/membership/…/certification-candidate.json` (not installed: a candidate is not a record — the
   train's 5a `--slow` installs it). `google-search-recert.txt`.
5. **Elaboration A/B** — §5.

## 3. Fuel (decision 7 — no compensating no-op step ADDED; the movements, corrected per audit F2)

Each former `.initialization` cost TWO `stepFn` steps — its `.seq` dispatch (`Step.seqNext`) and its `.exec`; a block
entry is one step for all its declarations (and `Step.block` was already a step for the empty list), so a run loses
exactly TWO steps per declaration executed (audit F2 — the first draft said one; every bisection delta below is even).
PLUS one step per completed `unseq` sweep: with D3 (b) `thenB`'s continuation is `.seq rest env k` with `env' ≠ env`,
so `seqCont` no longer splices a `.seqn` `thenB` and the nested frame costs a `seqDone` pop (audit F2; the enumeration
sweep shows 11 DFS rows with identical trees and total steps up by exactly the sweep count per path). «No compensating
step» (decision 7) means no padding no-op step was ADDED; D3 (b)'s one pop per sweep is the rule's own cost. Measured
as the MINIMAL COMPLETING FUEL by bisection on identical wires, main vs lane (`fuel-bisect.tsv`):
`noodler/budget/loop-100k` 5300089 → 5300083 (−6: no declaration inside the loop body), `map-20k` 880099 → 880091,
`recursion-1k` 46055 → 44053 (−2 per activation: ONE declaration, the hoisted call temporary `$c0`, × 2 steps), `recursion-5k` 230055 → 220053,
`slice-1k` 120206 → 116184, `string-build-5k` 245091 → 245085, `control-flow/for-loopvar-escape` 424 → 402,
`functions/closure-share` 134 → 126, `control-flow/goto-loop` 498 → 490. Every sequential budget row keeps its status
(`noodler/budget/*` PASS; `arrays/materialization-budget/over-budget` FAIL at the lowering refusal, as pinned). The
run-fuel budget (10 M) is nowhere near. The ONE budget that flips is an enumerator's per-branch step budget — §4.

## 4. The fuel-budget row flip (decision 7) — RULED 2026-10-03: option (a), the work cap raised

**Row:** `sync/trylock/spin-until-trylock` (membership; params `width=4,sites=200,members=1,nonterm=200,backedge=1`;
work cap 200000 — the manifest default). **RULING:** [USER] Mike, 2026-10-03, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «yeah, agree with 1, land it» — option (a). **Landed:** `work=500000` on the row
(`Corpus/coverage/exec/sync/trylock/cases.tsv`, with the reason in its `why`). Measured on the lane binary at
`nonterm=200`: the enumeration needs 240834 work units (214263 steps + 26571 probes) — `--work-cap 240000` refuses
(«exceeded after 213499 step(s) + 26502 probe(s)»), 250000 / 300000 / 500000 pass with the identical tree; 500000 is
the smallest round value with ≥ 2× headroom. The observation set {42}, `leaves=2571`, `maxdepth=18` are the pinned
tree's. NO baseline re-pin: the row returns to PASS at its pinned status. **Before:** PASS — `observations=1 steps=115312 probes=19464 sites=6812
leaves=2571 maxdepth=18 nonterm=4242`. **After:** FAIL — «work cap exceeded after 177861 step(s) + 22140 probe(s) with
subtrees still unexplored». **Diagnosis** (`spin-until-trylock.txt`): at a raised cap (4 M) the lane completes with the
IDENTICAL observation set ({42}), identical `leaves=2571` and `maxdepth=18`, and `steps=214263 probes=26571
sites=9272 nonterm=6702`. The cause is the row's `--allow-nonterm 200` — a PER-BRANCH STEP budget: the child's spin
iteration (`for !m.TryLock() {}`: the loop-body block's one temporary declaration) is one step shorter since C4, so the
budget admits more spin iterations before cutting a branch, each a width-2 `tryLock` pick and a `backEdge` boundary —
the lane at `--allow-nonterm 190` reproduces main at 210 almost exactly (probes 26331 / 26331, sites 9101 / 9102,
nonterm 6531 / 6532) — a tree that was never pinned; main's PINNED tree (nonterm 200: probes 19464, sites 6812, leaves
2571, maxdepth 18, nonterm 4242) is reproduced by the lane at `--allow-nonterm` ∈ [182, 185] (audit F1; re-run here:
182 → steps 104890, 185 → steps 117616, every tree statistic identical; `spin-until-trylock.txt`). All FOUR
`nonterm=200` rows moved, not one (audit F1): `goroutines/send-then-spin` steps 11187 → 12859, probes 14355 → 17103;
`race/atomics-free/cas-failure-acquires` steps 21838 → 28552, nonterm 275 → 720; `atomics/spin/flag-wait` steps 23103 →
30074, nonterm 277 → 815 — the three still PASS at 15–18 % of the 200000 cap. A per-branch STEP budget moves with
EVERY step-count change (the `.seqn #[s]` clean-up of §7 would move these rows again) — hence the apparatus follow-up
in §7. This is the escape audit's channel 10 (fuel), not channel 8 (the merge rate: `dedupHits` is
untouched on the certified row); the per-iteration scheduling points are unchanged (only spawns, registry-op
completions and loop back-edges open boundaries). **Not absorbed:** the manifest row and the baseline are untouched.
**Options for the ruling:** (a) raise the row's work cap (`work=` in `Corpus/coverage/exec/sync/trylock/cases.tsv`;
the enumeration needs ~241 k at `nonterm=200`; a 2× margin is 500000) — the budget is the apparatus's, the observation
set and the claim are unchanged; (b) lower the row's `nonterm` to 182–185 (the pre-C4 PINNED tree, exactly — audit F1 corrected the first draft's
«190», which is main's tree at 210) — a tighter per-branch budget, same observation, the step-dependence explicit in
the row; (c) re-pin PASS → FAIL with a `BUGS.md` Cases line — contrary to decision 7's
intent (a visible refusal where nothing semantic changed). [AGENT] recommendation was (a), with the reason written into
the row's `why` — RULED as (a) (above); the gate is red on the 5a pair only.

## 5. Elaboration A/B (G-C3 stop rule: any module > 1.5× or a new/raised `maxHeartbeats` stops the lane)

Sequential, same box, `scripts/capped` (32G), under the box-wide lock, alternating main / lane per module
(`lake env lean <module>` against each tree's own up-to-date oleans; main = the primary checkout @ `52eddf4c`, lane =
`ed423c72`): `Machine` 4.32 s → 4.27 s (0.99×), `StepFn` 0.99 → 0.95 (0.96×), `StateWf` 16.54 → 17.13 (1.04×),
`MachineEqb` 4.91 → 4.81 (0.98×), `MachineSound` 67.02 → 65.93 (0.98×), `StepErrors` 213.27 → 195.38 (0.92×),
`BridgeSet` 0.91 → 0.97 (1.07×; sub-second noise). No module above 1.5×; no `maxHeartbeats` added or raised (`git diff
52eddf4c -- GoLean Tests | grep maxHeartbeats` is empty). `elaboration-ab.tsv`; the parallel fresh-build times for
reference in `build-times-parallel.tsv`.

## 6. Posed / for the audit

1. §4 — the budget-row ruling (decision 7): RULED (a), landed.
2. The D5 realization (typed temporary keys) — CONFIRMED by the audit (F5) and accepted by the landing (§1).
3. BridgeSet row 132 re-pinned (D3 (b)) — accepted by the landing; the changelog's «what a re-pin touches» names it.
4. The positional-tag shift is −3, not −1 (two refusal cases the note did not count) — mechanical; recorded.
5. D8's `blockEntry_fresh` sentence, AMENDED (audit F4): `blockEntry_fresh` is the ENVIRONMENT half of «no existing
   value, env or label names the new cell» (`LocalEnv.locSup env ≤ s.nextAddr → lookup env id ≠ some (entrySlot s i)`),
   `entrySlot_not_allocated` the heap-domain half; the value and label halves are DERIVABLE from `StateWf`/`ConfigWf`'s
   sup bounds the same way (`Loc.locSup` is strict, `Store.nextAddr = heap.size`) and are NOT named — BridgeSet rows
   142–143 say exactly what they prove. Naming the value half is a later-slice candidate (§7).

## 7. Follow-ups (not taken here)

- `unseqEnter`'s statement-sequence match (`.seq rest env k` with `kenv = env`) is now only a position requirement — the
  in-place extension that needed it is gone; the rule could take any `k`. Left as ruled («the continuation stays
  `.seq rest env k`»); a one-rule simplification for a later slice (UnseqSound/StateWf cases + row 132 again).
- The `.seqn #[s]` wrappers the hoist left behind (one extra step each) — a shape clean-up with its own fuel movement.
- Channel 5 (`locJson` raw ids) — recorded as a standing schema limit (decision 6), untouched.
- APPARATUS, post-window (audit F1; [USER] 2026-10-03 ruling text): express the membership rows' spin bounds in LOOP
  ITERATIONS (loop back-edges), not raw steps — `nonterm=` is a per-branch STEP budget, so the four `nonterm=200` rows
  move with every step-count change in the machine; the C4 raise of `spin-until-trylock`'s work cap is the second time
  a budget row carried a non-semantic step shift.
- Name the value half of the freshness statement (a `StateWf`-premised lemma over `Heap.lookup` / `HeapCell.locSup`)
  — audit F4.
