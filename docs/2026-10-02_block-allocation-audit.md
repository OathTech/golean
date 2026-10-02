# Pre-merge adversarial audit — lane `core/block-allocation-1001` (window row 6, C4 block-entry allocation)

[AGENT auditor], 2026-10-02, branch `review/block-allocation-1001` (worktree `.claude/worktrees/audit-block-allocation`,
fresh `.lake`, `deps/` at the pins via `scripts/setup-deps --from`). Candidate tip `ada8cf34` (7 commits over `main` @
`52eddf4c`); main's binary built from `git archive 52eddf4c` under `.tmp/`. Every build and gate `scripts/capped`, full
builds and the gate under the box-wide lock (never taken over). No edit to the candidate or `main`; no merge; no push.
Scope: the brief's seven attacks. Evidence: `docs/evidence/2026-10-02_block-allocation-audit/` (small; the scratch
`.tmp/` probes, wires, mutant copies and the main archive deleted at the end).

## Verdict

**MERGE-CLEAN**, with the records corrections of F1–F3 asked for before or at the landing (none touches runtime
code, none changes a verdict). No behaviour difference between `main` and the candidate was found anywhere except
the step count (strictly fewer); the coherence theorems are re-established as stated; the D8 pins are load-bearing;
the decoder's two D1/D2 fail-closed checks refuse by name; the gate at the tip is red on exactly the expected 5a pair
plus the one STOPPED row. The STOPPED row (`sync/trylock/spin-until-trylock`) is a pending [USER] ruling, not a
finding — but ONE of the handoff's three ruling options is mis-stated (F1), and the ruling should see the corrected
number.

## Findings (by severity)

**F1 — MEDIUM (records accuracy of a pending ruling).** Handoff §4 option (b): «lower the row's `nonterm` to 190 (the
pre-C4 tree, exactly)». FALSE as stated. Reproduced on both fresh binaries at a 4 M work cap
(`evidence/nonterm-rows.txt`): the candidate at `--allow-nonterm 190` yields probes 26331 / sites 9101 / nonterm
6531 — that is `main`'s tree at nonterm = **210** (26331 / 9102 / 6532), a tree that was never pinned. `main`'s
PINNED tree (nonterm = 200: probes 19464, sites 6812, leaves 2571, maxdepth 18, nonterm 4242) is reproduced by the
candidate — in every tree statistic, with fewer steps — at `--allow-nonterm` ∈ **[182, 185]** (a plateau; 181 is
below it, 190 above). The diagnosis itself (channel 10, a per-branch STEP budget; identical observation set `{42}`,
identical leaves/maxdepth) is CORRECT and reproduced exactly (handoff numbers = mine). Two further facts the ruling
should have: (i) all FOUR `nonterm=200` rows moved, not one — `goroutines/send-then-spin` steps 11187 → 12859, probes
14355 → 17103 (nonterm 216 both), `race/atomics-free/cas-failure-acquires` steps 21838 → 28552, nonterm 275 → 720,
`atomics/spin/flag-wait` steps 23103 → 30074, nonterm 277 → 815; the three still PASS at 15–18 % of the 200000 cap; (ii) `nonterm=` is a per-branch step budget, so it moves
with EVERY step-count change — the handoff's own follow-up (dropping the `.seqn #[s]` wrappers, §7) would move
these rows again. Neutral assessment of the options: (a) raise `work=` to 500000 — apparatus-side, observation set
unchanged, but it certifies a LARGER tree than before (nonterm 6702 vs 4242) and leaves the step-sensitivity in
place; (b) lower `nonterm` — the honest equivalent is **182–185, not 190**; it certifies exactly the pinned tree
again, and makes the budget's step-dependence explicit in the row; (c) PASS → FAIL re-pin — a visible refusal where
nothing semantic changed, against decision 7's intent. A fourth, out of C4's scope: an apparatus change making the
per-branch budget count loop back-edges rather than steps. The ruling is the [USER]'s; this audit only corrects the
option text and widens the picture.

**F2 — LOW (records: the fuel arithmetic, in BOTH directions).** Handoff §3 «a run loses exactly one step per declaration
executed», changelog C4 row «one `stepFn` step fewer per declaration executed, NO compensating step … any fuel-indexed
statement loses one step per declaration executed», design note §2 #10 «each declaration was ONE `stepFn` step».
Measured on identical wires (`evidence/fuel-bisect.tsv`): (i) **TWO** `stepFn` steps per declaration executed — the
deleted statement's `.seq` dispatch (`Step.seqNext`) and its `.exec` (0 declarations → 0; 1 → −2; 3 → −6; 8 → −16;
every probe's delta is even); the lane's deltas are right, the explanation is off by 2× — `recursion-1k` −2002 =
1001 activations × ONE declaration (`$c0`, the hoisted call temp of `1 + depth(n-1)`) × 2, not «two body
declarations»; (ii) **PLUS one step per completed `unseq` sweep** — D3 (b) makes `thenB`'s continuation
`.seq rest env k` with `env' ≠ env`, so `seqCont` no longer splices the `.seqn` and the nested frame costs a `seqDone`
pop (the handoff §1 notes the branch is reached but not its fuel cost): probes q05/q06 (the same program with and
without a sweep in assignment form) move −7 vs −8; in the enumeration sweep 11 DFS rows have IDENTICAL trees
(probes/sites/leaves) and total steps up by exactly the sweep count per path (`evaluation-order` and `e13` rows,
`evidence/enum-sweep.txt`). Neither movement is semantic; both belong in the fuel story the changelog's `[inf]` line
hands the logic side. Fix: the three sentences, the `[inf]` line, and «NO compensating step» → «no compensating
no-op step was added; D3 (b) adds one pop per sweep».

**F3 — LOW (records: the constructor count).** Design note §5, handoff §1 and the changelog C4 row say `Stmt` 44 → 43.
Counted on both trees: **45 → 44** (`Stmt.initialization` present on `main`, absent on the candidate; 5b's
`Stmt.randIntn` landed between the note's base `ac6baa31` and the lane's base `52eddf4c` — the 5b changelog row
itself says «45 statements»). `Step` 128 → 127 is right (counted).

**F4 — LOW (proof completeness vs the D8 text; posed by the handoff, item 5).** The design note's D8 promised
`blockEntry_fresh` as «no existing value, env or label names them». Realized: the ENVIRONMENT half only
(`LocalEnv.locSup env ≤ s.nextAddr → lookup env id ≠ some (entrySlot s i)`, StateWf.lean) plus the heap-DOMAIN half
`entrySlot_not_allocated`. The value and label halves follow from `ConfigWf`/`StateWf`'s sup bounds the same way
(`Loc.locSup` is strict, `Store.nextAddr = heap.size`) but are not named. Adequate for the acceptance list as pinned
(rows 142–143 say exactly what they prove); recommend either naming the value half (a `StateWf`-premised lemma over
`Heap.lookup`/`HeapCell.locSup`) in a later slice or amending the D8 sentence. Not blocking.

**F5 — INFO (D5 as realized: confirmed).** One cell per (spelling, TYPE) for declared `$`-temporaries is SOUND and is
the minimal correct reading of «one cell per id»: a block-entry cell has one declared type and `storeLoc` normalizes
at it, so the note's per-id share would have made `_ = a; _ = s` (`$blank0` at `int` and `string` in one block) a
`writeAt` refusal, not an unobservable share. Probe p11 exercises `$blank0`/`$cr0`/`$ta`/`$mlv` at two types in one
block — identical on both binaries and to gc. Sharing happens only for same-spelling-same-type temporaries within one
block, all of them write-then-read within one statement, never captured or address-taken (checked every `declTmp`
site: `$cr/$cv/$ca0/$ta/$taok/$mlv/$mlok/$blank/$ret/$intn`; the range temporaries `$rcoll/$rlen/$ridx/$rfirst/
$rnext/$roff` are read across iterations but each range owns its own synthetic block, nested ranges shadow by scope).
One consequence to RECORD: a function's `locals` name table may now carry the same `$`-spelling twice (kind `.temp`,
two ids); `Func.localsOk`/`tableNamed` accept it (p11 runs). Confirm as posed.

**F6 — INFO (a D3 (b) side effect, record it; by the rule text, not run).** With the binder cells in a sweep-private
scope they no longer persist in the enclosing `.seq` environment after a sweep, so the B6 F3 runtime check
`unseqEntryCheck?` («binder already bound in the enclosing scope») can no longer fire for two sweeps in ONE block that
reuse a binder id — on `main` the second ENTER refused such a hand-built wire by name; on the candidate it is
accepted (harmlessly: the cells are private). Decoded programs are unaffected (the frontend numbers binders uniquely per function); the Stage C
hand-built mutants still pass. The K2 test's «two sweeps in ONE block must use distinct binders» comment is now a
frontend fact, not a machine-enforced one.

**F7 — INFO (positive).** The D1/D2 fail-closed checks are load-bearing: a range-over-map wire whose body is not a
block is REFUSED by name on the candidate, while `main` ACCEPTED it and computed a DIFFERENT value (33 vs 10 —
`evidence/mutants.txt`); a declaration left outside any block is refused by name («1 declaration(s) recorded outside
any block»). Three BridgeSet pin mutants (rows 136, 139, 143) each fail to elaborate (`Type mismatch`); the
byte-identical control elaborates.

## What was checked, by attack

1. **Behaviour preservation.** 27 probes (`evidence/probes.tsv`), each lowered ONCE with the unchanged frontend and
   run on both fresh binaries and on go1.26.5: forward `goto` over a nested declaration, backward `goto` over
   `var x int`/`var arr [2]int` (no initializer — the frontend's `degradeGotoDeclares` re-zeroes explicitly) and
   re-entering a nested block, per-iteration loop variables captured by closures and by address in three-clause
   loops with `continue`, `range` over slice (modified copy), int, string, channel and `*[N]T`, if/switch init
   declarations captured, shadowing at block entry (`x := x + 1`), declarations after an early `return`/`break`/
   `panic`, defer with saved arguments vs captured block locals, named results modified by defers, the typed
   temporaries, two `unseq` sweeps per iteration with closure captures and a `continue` (the wire carries the two
   `unseq` nodes), `select` receive declarations in a loop, zero-valued structs/arrays/slices/maps per iteration,
   a recursive closure, pointer identity across iterations and sibling blocks, labeled `continue`, a type-switch
   binding captured, and a `values`-returning subject. **27/27 identical between `main` and the candidate and equal to
   gc's output.** The only difference anywhere is the step count: 11 probes bisected, every delta negative and even.
2. **Fuel.** Every row with a budget parameter was identified (91 rows: `work=` on 50 enumeration rows, `depth=` on 38
   strict rows — a choice-stream depth, not a step budget — and `nonterm=200` on 3 membership rows). The strict
   driver's 10 M fuel is nowhere near (the largest minimal fuel in the lane's table is 5.3 M on `loop-100k`, which
   moved by −6). The four `nonterm` rows on both binaries: `spin-until-trylock` is the ONLY flip; the other three
   moved and pass (F1). Full enumeration-lane sweep: §Sweeps below.
3. **D5.** F5.
4. **Scoped preservation claim.** `GoLean/CLI.lean` has zero changed lines (channel 5's `locJson` untouched, as
   decision 6 requires); the certified record carries no `addr` token; pointer equality/aliasing identical (p04, p17);
   the certified slow row: §Sweeps.
5. **Coherence.** `Stmt` 45 → 44 (F3), `Step` 128 → 127 (counted on both trees); `stepFn_sound`/`step_complete`/
   `stepFn_consumption_*`/`stepFn_picks_*` and every packet A/B statement unchanged in the diff (only positional
   `case` tags moved; `step_complete` names no `initialization` case and needed no edit; `StepErrors`,
   `ExecutionStatement`, `Prefix` untouched). The −3 shift is consistent: `case13` was the ok path and 14/15 its two
   refusals, which the old proof closed in the generic `all_goals` closer — a mislabelled tag could not close a wrong
   goal silently, `fun_cases` goals are checked whatever their name. D8 lemmas read true and as pinned (F4 on
   completeness; `heap_size_mono` carries `step_preserves_wf_loc`'s wf premises, as the handoff says; the D7 pair is
   `rfl` equations — what request 4 asked for, no more). Rows 1–131 and 133–135 byte-identical, row 132 re-pinned
   exactly to the D3 (b) rule (justified: decision 3 changes that rule), rows 136–154 added, the audit list +19;
   pins load-bearing (F7). No `sorry`/`native_decide`/axiom/`partial` in the core; no `maxHeartbeats` added or raised
   (the one in the diff is a context line). Fresh parallel builds, both trees, hot modules within ±4 %
   (`evidence/build-times.tsv`); 0 warnings.
6. **D2.** No file under `tools/` in the diff; the gate's `frontend pins` step (twin = pinned bytes) ok; the stopped
   row's wire sha256 `776d8690…` equals the lane's evidence header. Mutants: F7.
7. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `ada8cf34`, lock held: `RESULT: FAIL`, exit 1,
   1044 s; `cases=3800 pass=3561 fail=239`; red on `certificate provenance` (STALE: changed compiled inputs — the 5a
   pair's first half) and `baseline diff` with exactly the two drift lines `imported-goose/channel/google-search` and
   `sync/trylock/spin-until-trylock`; every other step ok (`evidence/ci-diff-tip-tail.txt`).

## Sweeps (main vs candidate, identical wires from the gate's run)

- **Enumeration lanes (390 rows: 243 membership, 102 confluent, 45 racy)** — `coverage-observations` with the
  manifest's params on both binaries, exit code AND sorted observation set compared (`evidence/enum-sweep.txt`):
  **387 SAME, 1 DIFF = the STOPPED row (exit 1 vs 0), 1 NOWIRE** (`builtins/print/refused/race-with-output`, a
  frontend-refused racy row — no wire on either side), 1 slow row run separately: `imported-goose/channel/google-search`
  (dedup, 60 M work) — observation set identical on both binaries, sha `e40ba07d…` = the tracked record's
  `observations_sha256`; nodes 6193933 → 5908017, edges 6565663 → 6279747, `dedupHits` 371731 both, exactly the
  lane's figures. Statistics: 9 rows byte-identical, 378 moved; total steps GREW on 20 rows — the 4 `nonterm` rows
  (F1), 5 dedup-engine rows (merge rate — `goroutines/pipeline/two-stage` nodes 866780 → 934642, +7.8 %, work/cap
  0.477 → 0.515) and 11 DFS rows with identical trees (+1 per sweep per path, F2 (ii)). Budget margins: the highest
  work/cap on the candidate is `multipkg/mini-raft-twin/choice-order` 0.892 (was 0.913 — improved); no row above 90 %.
- **Whole corpus (3800 rows)** — `native-json-run` at the default fuel on both binaries, stdout (status, output,
  values, message) AND exit code compared: **3756 SAME** (3091 exit 0 + 665 exit 1 — refusals and panics — identical
  on both sides), 43 NOWIRE (frontend-refused / no-wire rows on either side), 1 SKIP (`goroutines/send-then-spin`,
  which spins to the fuel cap at the default fuel; covered by the nonterm runs). **Zero differences.**

## Not verified here

- The run-level simulation of §3 is not a theorem (the note says so); this audit's evidence for it is differential.
- The lane's whole-corpus choice trace (26445 dump rows, sha `6bf9800841e8e5c4` both sides) was not re-run; the
  whole-corpus sweep above is the independent output/exit check over every wire (per-consumption picks not compared).
- The handoff's sequential elaboration A/B (`lake env lean` per module) was not repeated; the parallel fresh-build
  times are a weaker, consistent datapoint.
- The train's 5a `--slow` re-certification is the train's; the slow row's re-enumeration here is on both binaries at
  the manifest's parameters only.
