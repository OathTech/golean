# Stage C handoff — the native `unseq` pilot end to end (lane `core/unseq-stage-c-0919`, 2026-09-19/20)

[AGENT] Lane handoff (worker), branch `core/unseq-stage-c-0919` off main `6a7beb3d` (train r43
closed; C1 complete modulo its owed list), worktree `.claude/worktrees/unseq-stage-c`. Design of
record: `docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §7 row C; this lane's C0 record
`docs/2026-09-19_unseq-stage-c-design.md` (the pilot grammar as the emitter's decision procedure,
the census, the wire schema, the decoder spec, the lowering rules, the predictions — and its §10
«as landed» addendum); evidence `docs/evidence/2026-09-19_unseq-stage-c/` (README with every gate
line). Authority: the mechanism ruling [USER] Mike 2026-09-16 «the Cerberus model is the correct
one» (relayed); Stage C directly after C1 — «(1) agreed» [USER] 2026-09-18 (relayed); the three
Stage C rulings [USER] Mike 2026-09-19, verbatim «Agree, merge», relayed by the [AGENT]
coordinator — cite as relayed (`docs/2026-08-31_qrow-rulings.md`, «The C1 completion and Stage C
rulings record»): (3) width of P = ALL mutable reads, STAGED — the pilot carries the minimal
P(ii) reads its fixtures need, then widens; (4) N1 = SPLIT; (5) N3 = REFUSE by name. No [USER]
gate was ruled by this lane; §6 lists what is PENDING. The Stage B construct (`Stmt.unseq`,
`Cont.unseqK`, `ChoiceSite.unseqNext`, `GoLean/GoCore/Unseq.lean`) is UNCHANGED: no Lean file
under `GoLean/GoCore/` moved, no theorem restated, no positional proof tag touched.

## 1. What landed, per slice (each runtime slice ONE gated commit; the gate lines are in the evidence README)

1. **C0 `ccd3bdab` — records + census tooling, WIRE-NEUTRAL.** `tools/nativefrontend/unseq.go`:
   `unseqClassify`, the ONE whole-sweep decision procedure (design §1) shared by the census mode
   `nativefrontend --unseq-census` and the emitter; `unseq_test.go` (3 tests: the admitted
   witnesses with their counts, the legacy reasons by name, the address-taken analysis). Census
   at `6a7beb3d`: 1353 packages, 107 773 sweeps across all units, 120 admitted in 28 packages
   (0 in imported units), the raft twin 0 of 10 203; main-tip vs C0 frontend byte-identical on
   all 1353 packages. The design note's §3 predicted the flips, the lane moves, the widened
   pins and the one depth declaration; gc's draws for the four flips measured
   (`gc-flips.txt`). Gate: fast `ci` EXIT=1 on the 5a-class STALE certificate
   (`tools/nativefrontend/main.go` is a certification input) + the fresh worktree's two «no
   recorded run» items only.
2. **C1 `fb03e38f` — the decoder [TRUST-SURFACE `GoLean/NativeToIR.lean`].** The `unseq` wire arm
   (design §4 schema, §5 checks D1–D14 as named refusals: exact keys, `$` binders, non-empty
   graph, kind, sorts, LIST ORDER = a linear extension of every edge, the internal NORMAL FORM of
   heads/callees/args, head type = cell type, `resultTypes` = cell types, guard cells bool, the
   STATIC G rule, the frozen target shape, a completion free of nested `unseq` / legacy
   `unseq-probe` / `recover`); `import GoLean.GoCore.Unseq`. `Tests/unseq-wire/` (build.py +
   12 witness programs → 35 fixtures): the real frontend's envelope around a HAND-WRITTEN `unseq`
   node per witness (W1–W6, R1 + the refuted reduction, R2a + the invalid join, R2b + the entry
   anchoring, R2c, R4, R6 + the fused read) and 18 one-edit mutants with needles;
   `Tests/UnseqWire.lean` (harness factored into `Tests/UnseqHarness.lean`, shared with the
   unchanged Stage B tests — 64 ok): every reference set of the v2.1 spike EXACT over the wire
   (check (b) «machine equals reference over the wire»), every mutant refused by name in-process
   and through the real CLI (`scripts/check-unseq-wire`, a new `scripts/ci` step `unseq wire
   (Stage C)`; `scripts/check-wire-boundary` extended with the W1 control + 6 unseq-node
   controls; lakefile `UnseqWireTests`, registry `unseq-wire`). Gate: `ci --slow` EXIT=1 in
   1001 s — 3686 rows 3437/249, every step ok EXCEPT the two 5a-class items (certificate STALE
   for `NativeToIR.lean`; the one certified row's fresh re-certification «unchanged set»); no
   other row moved.
3. **C2 `ce33ffd1` — the lowering [TRUST-SURFACE `tools/nativefrontend`] + the rows + the baseline +
   the BUGS.md moves.** `unseq_lower.go` (`emitUnseqSweep`; design §6): atoms /
   reads / N1-split accesses / ops / `len`-`cap` as E1 events / calls (0–2 results, discard
   cells) / guards (entry + region + completion, E1 at the entry for earlier events, at the
   completion for later ones) / frozen element target plans shared by load and store / the
   private-local compound fold / the completion forms; the CANONICAL partition per frame (a
   level's event blocks — each a nested event with its own operand subtree — then the level's
   residual: today's ANF at every nesting level); the mixture guard (a leaked legacy hoist
   refuses by name). The hook in `emitStmtList` consults `unseqClassify` first; `unseqBody`
   bookkeeping in `emitFuncDecl`/`emitFuncLit`; the classifier refuses interface-typed element
   targets (boxing inside a graph is outside the pilot). `unseq_lower_test.go` pins the canonical
   shapes (W1, W6, R6, BUG-104, BUG-102, R2c, `g(a[0], f())`) and the shared target binder.
   `Tests/unseq-wire/native-*.json`: the frontend's OWN lowering of the 12 witnesses — the SAME
   reference sets, exact (v2.1 §7 row C's exit); the four §8 edge mutants of the lowered graphs
   (data / lexical / guard / phase) decode and the exact-set check names each. The E13 guard
   tests updated to the pilot's truth for the admitted shapes (one graph, zero probes; the
   narrowed-A6 residue test asserts the graph, not the retired refusal). The corpus package
   `evalorder/unseq-pilot` (13 rows: W1/W2/W3/W5/W6, R1, R2c ×2, R4, R6 membership; R2a ×2, R2b
   strict) born PASS on the first run. The row edits (§4), the baseline re-pin (3699 = 3455 PASS
   / 244 FAIL, the reason in its header), BUGS.md (BUG-101 fixed; BUG-102 / BUG-104 Cases moves
   with their notes; BUG-112 the fixed entry for the two compound-target flips), lowerdiag's
   `causes.tsv` row `unseq-lowering-invariant` (the lowering's 17 internal `unseq lowering:`
   formats — unreachable for an admitted sweep — classified; vocabulary 388/425). Gates:
   `ci --diff` #1 (measurement, 705 s) and #2 (confirmation, 701 s): the drift EXACTLY the
   design's predicted 25 lines; the fast `ci` on the committed tree (evidence README).
4. **C3 — the records (this commit; gate `ci --diff`, the line in the evidence README):** latitude
   inventory (E2 heading + Stage C bullet; E12 census note; E13's residuals (1)/(9) retired on
   the pilot's rows; §10 known-≠-oracle list — E2's value axis LEAVES, BUG-104 to four rows;
   §10.1 movement entry), the language-coverage ledger (§8 tally 3699 = 3455 / 244, the reds
   table 134 → 133 / 73 → 70, FR-28's cell 6 → 5, §8y), the design note §10 addendum, the
   `why` correction on `multi-assign/index-target-rhs-call-order` (752 → 932 — the design's own
   arithmetic slip), this handoff, the evidence README's C3 section, the whole-corpus
   choice-trace comparison (§4).
5. **Audit fix round (2026-09-20; §10) — the runtime commit `e73c706f` [TRUST-SURFACE
   `GoLean/NativeToIR.lean`] + a records commit.** The adversarial audit
   (`docs/2026-09-20_unseq-stage-c-audit.md`) returned FIX-FIRST: F2 (the decoder refused the
   frontend's own constant-in-a-cell copy — a coverage REGRESSION on legal Go; D8 now admits
   constant heads, three red-first rows `evalorder/unseq-const-cell/*` born FAIL → PASS, three
   hand-built + three native fixtures, a `check-wire-boundary` control), F3 (D12 now confines a
   nested guard's completion binder to its enclosing region; the 19th mutant), F1 (a pre-existing
   LEGACY-path wrong answer — a `||`/`&&` evaluated after a later call — ROWED as BUG-113 with two
   FAIL rows + a control in `evalorder/legacy-logical-vs-call/`, fix owed to Stage E), F4 (the
   K=80 claim backed by this round's `ci --slow`), F5–F9 records. Gate: `scripts/capped scripts/ci
   --slow`, EXIT=1 in 954 s (2026-09-20 19:39:04–19:54:58Z), K=80 (`membership_draws 80`); 3705 rows 3458 PASS / 247 FAIL in the run = the pinned 3459 / 246 with the one 5a-class row red; DRIFT = exactly `imported-goose/channel/google-search` PASS→FAIL/membership (STALE certificate for `NativeToIR.lean`; fresh re-certification «unchanged set; seconds=164.598»); every other step ok; re-pin guard 0 PASS→non-PASS. Baseline 3705 = 3459 / 246.

## 2. The pilot grammar and the census

Design note §1–§2. In one line: a block-level `x := e` / `x = e` / `a[i] = e` / `x op= e` /
`a[i] op= e` / `x++` / `return …` / call statement / `println(…)` over int/bool/string/slice/`any`
locals, slice elements, slice expressions, `len`/`cap`, same-package calls (0–2 results),
arithmetic/comparison/unary ops, type assertions and `&&`/`||`, lowered as ONE `unseq` graph iff
it carries ≥ 1 CALL and ≥ 1 occurrence observable against it (a read of an address-taken local,
a slice-element checked access, a failing pure op, an element target plan, a guard); everything
else — globals, pointers, fields, methods, maps, arrays, strings indexing, named types, floats,
conversions, allocations, receives, sends, `recover`, comma-ok, multi-target, blank targets,
if/for/switch heads — stays on the legacy E13 probe path BY NAME (the census prints the
reason). Census after C2: 1354 packages, 133 admitted sweeps in 29 packages; 25 packages' wires
carry `unseq` nodes (117 nodes; the other 4 are exports the standing `fmt.Formatter` boxing
refusal kills); the raft twin 0 (pin byte-identical at every C2 build).

## 3. The decoder spec and its refusal texts

Design note §5 (D1–D14); the needles in `Tests/unseq-wire/mutants.tsv`; the machine's
`wellFormed?` texts surface through the arm as `unseq: malformed graph at <path> — <text>`. The
decoder is the STATIC net at the wire boundary; the machine's own refusals (Stage B §9.1) stay
the enforcement — hand-built graphs cannot bypass them.

## 4. The rows born / flipped / moved, with their sets (measured at gate #2; `c2-moved-rows.txt`)

| row | before → after | set (output · result) | gc |
|---|---|---|---|
| `evalorder/unseq-pilot/{w1,w2,w3,w5,w6,r1,r2c-true,r2c-false,r4,r6}` | born PASS/membership | the v2.1 spike's sets, exact (w3/r4 as checksums 1120/1021, 11100/10101) | in every set |
| `evalorder/unseq-pilot/{r2a-true,r2a-false,r2b}` | born PASS strict | singletons (the guard protocol forces every edge) | = |
| `…/assert-ok-early-len-hoist` (BUG-101) | FAIL/lean-observation → PASS/membership | {`mut`·6, `mut`·conversion panic}, statuses ok+panic | `mut`·6 |
| `…/slice-value-early-len-hoist` (BUG-101) | FAIL/differential → PASS/membership | {`mut`·12, `mut`·22} | 12 |
| `…/compound-call-target-vs-call` (BUG-104 → BUG-112) | FAIL/differential → PASS/membership | {`f wit 5`·[9], `f`·[9]} | `f wit 5`·[9] |
| `…/compound-call-target-vs-len` (BUG-102 → BUG-112) | FAIL/frontend-export → PASS/membership | {``·[5], `f`·[5], `f`·[9]} | `f`·[5] |
| `…/assert-right-call` | PASS/- → PASS/membership | {``·conversion, `wit 5`·conversion} (E13 residual (1) retired) | `wit 5`·conversion |
| `multi-assign/index-target-rhs-call-order` | PASS/- → PASS/membership | {932, 1209} (E2's value axis) | 1209 |
| `noodler/latitude/args-index-vs-call` | PASS/- → PASS/membership | {15, 1005} | 1005 |
| `noodler/latitude/concat-var-vs-call` | PASS/- → PASS/membership | {`ab`, `zb`} | `zb` |
| `noodler/latitude/index-call-index` | PASS/- → PASS/membership | {4, 103, 301, 400} | 400 |
| `noodler/latitude/return-operands` | PASS/- → PASS/membership | {(1,5), (100,5)} | (100,5) |
| `noodler/maps/slice-compound-call-mutates` | PASS/- → PASS/membership | {15, 105} | 105 |
| `…/assert-middle`, `…/index-middle` | PASS/membership, members 2 → 3 | + the operand before the FIRST call (E13 residual (9) retired) | unchanged |
| `…/index-assert-left-call` | members 3 → 4, width 2 → 3 | each failing operand wins, before or after `wit 5` | unchanged |
| `…/two-index-left-call` | members 3 → 4, width 2 → 3 | `[9]` or `[5]`, before or after `wit 5` | unchanged |
| `spec-examples-stmt/continue-label` | PASS strict, `depth=128` | singleton; w=18 wide picks (one per loop iteration + the `enc` reads) | = |

NOT flipped (outside the pilot — Stage E): BUG-104's `map-compound-index-key-vs-{call,recv,
method}` and `compound-call-target-vs-recv`; BUG-102's five structural-allocation rows. No
PASS→non-PASS flip anywhere. Every strict row whose sweep now lowers as an all-forced graph
(the goose `ok = ok && …` chains, the fmt shim helpers, `s := expensive()[:]`, …) and every
row with ≤ 8 wide picks kept its observation (gate #2: no other drift line).

**Whole-corpus choice trace, rows outside the pilot byte-identical vs main's binary:**
`docs/evidence/2026-09-19_unseq-stage-c/choice-trace-c2.txt` — the S3 lane's method (`scripts/choice-
trace-corpus --dump --jobs 6`, the two standing exclusions) on main `6a7beb3d`'s frontend + binary
(a `git archive` export tree) and on this tree's frontend + binary, compared PER ROW on the sorted
dump records (stream, idx, phase, site, bound, streamValue, pick) and the results (status,
consumed, wide, obsHash) per stream: 3663 row ids; **3613 byte-identical; 0 differ outside the
pilot's 25 packages**; 50 differ inside them — 20 with the observation IDENTICAL on every stream
(only the consumption site moved: `unseqNext` picks where main's binary consumed `unseqPanic` or
nothing) and 30 with an observation difference on some stream: the 13 born rows, the 4 flips
(three WIDEN main's singleton to the predicted set; `compound-call-target-vs-len` main `unsupported`
→ members), the 7 lane moves (each WIDENS main's singleton by exactly the predicted member(s); the
default tape's observation = main's on every one), the 4 widened pins, and 2 membership rows whose
SET is unchanged but whose stream→member mapping differs (`compound-assert-vs-len`,
`compound-index-vs-len`; gate #2 enumerated the same sets). The default (all-zero) tape's
observation is main = C2 on every pre-existing row except the two designed fixes
(`compound-call-target-vs-call`: main `f`·[9] → C2 `f wit 5`·[9], gc's; `compound-call-target-vs-len`:
refused → ``·[5]). Consumption census: `unseqNext` 532 appears, `unseqPanic` 417 → 288, every other
site's count identical on both sides. **What the born `r2b`'s difference from main IS (audit F5,
added at the fix round):** on `sinkL(left || b, change())` main's legacy default is `logical true 0`
— the `||` evaluated AFTER the lexically later call, a member spec#Order_of_evaluation FORBIDS (gc
`logical false 0`); the pilot's graph anchors `change()` at the guard's COMPLETION and answers gc's
value. The difference is a fix, not latitude — and on the legacy path (an operand outside the pilot
grammar, e.g. a package variable) the wrong answer is still main's and the candidate's: BUG-113,
rowed red-first (`evalorder/legacy-logical-vs-call/`), Stage E's fix (§10).

## 5. The latitude re-classifications (C3; `docs/2026-08-11_latitude-inventory.md`)

E2 and E12 stay (b) PINNED as ENTRIES and are (a) ENVELOPED on exactly the rows of §4 (each
named on the entry) — «(b) PINNED → (a) ENVELOPED on the pilot's rows only»; E2's `known ≠ gc`
marker retires (BUG-101 fixed) and E2 LEAVES §10's known-≠-oracle list; BUG-104 stays listed
with four rows; E13 stays (a), its residuals (1) and (9) retired on the pilot's rows; E3/E4
unchanged (the pilot has no multi-target form); the census row for `unseqNext` (Stage B) is
now REACHED from native Go. Entry class counts unchanged ((a) 15 / (b) 17). The twin pin does
not move: none of its sweeps enters the pilot (stated per the brief). The wire schema has no
version field to bump (`golean-native-v1`; the `unseq` tag is a new statement kind under the
exact-key discipline, refused by every earlier decoder as an unknown statement).

## 6. PENDING [USER]

1. RATIFICATION at the merge ask (v2.1 §5 items 1/4/6, posed there): the E2/E12 VALUE-axis
   envelope on the seven lane-moved rows and the two BUG-101 rows (§4) — the machine now offers
   both values where the spec orders neither; the strict rows that pinned gc's call-first point
   are membership rows.
2. The two E13 narrowings retired on the pilot's rows — residual (1) (an operand RIGHT of the
   event) and residual (9) (the operand before the FIRST of several events) — are the spec's
   silence realized; the members are argued from spec#Order_of_evaluation, gc's draw stays in
   every set. Ratify with item 1.
3. Nothing else: no flip outside §3's prediction, no lane move the strict-lane rule does not
   license (every moved row varies in OBSERVATION across tapes → `membership`; the one singleton
   with exhausted streams → `depth=128`), no semantic difference from the reference sets.

## 7. Owed to Stage D / Stage E

- Stage D (economics): the workload ladder with recorded budgets — the fmt shim loops
  (`out += goleanShimFmt…(verb, args[ai])`: all-forced graphs, 0 picks, but a cell allocation
  per iteration, never reclaimed until C4), `continue-label` (w=18 on a 3×4 nested loop), the
  E13 family; route α (certify `unseqNext` in the dedup engine: `EnumDedupCheck.innerVecs`
  still refuses it by name — every membership row of the pilot enumerates on the default DFS);
  the strict-lane cost is REAL: one wide pick per unordered pair per execution, the fixed
  streams hold 8–10.
- Stage E (family migration): widen P — globals, pointers/`*p`, fields, maps (BUG-104's three
  map rows), receives (BUG-104's receive row; comma-ok), methods, conversions, allocations
  (BUG-102's five structural-allocation rows), multi-target/tuple forms, if/for/switch heads,
  interface-typed element targets, `len`-only and call-only sweeps if a fused-panic observable
  ever demands them; retire `unseqProbe`/`probeK`/`unseqPanic` after every caller moved (the
  E13 rows outside the pilot still ride the probe); the twin's sweeps when they enter.
- Still owed from Stage B (unchanged): the multi-step composition of the wire scheduler
  theorem, the stream-composition lemma, the machine-checked «trace», the source-to-wire
  translation certificate (v2.1 §7(a)) — the generated exact-set tests here are TESTS, not the
  certificate; the generator proper (`tools/evalorder-gen`, v2.1 §6) beyond build.py's
  witnesses is Stage D/E's.

## 8. Where this lane stopped; the next command

Branch-complete at the audit fix round's records commit (§10; the C3 records commit was the
pre-audit end state), parked, clean. The merge train's command: `git checkout main && git merge
--ff-only core/unseq-stage-c-0919`. **5a IS OWED**: the
wire schema and the decoder changed (`GoLean/NativeToIR.lean` is a certification input — the
certificate reports STALE at every gate of this lane; C1's `--slow` re-certified the one
tier=slow row «unchanged set»), so at the merged tip the train runs `scripts/build-certified`,
`python3 tools/certification.py release-check --base refs/snapshots/<round>/main`, then
`scripts/capped scripts/ci --slow`, installs the reviewed `certification-candidate.json` as the
round's 5a records commit and re-runs the gate green.

## 9. The audit ask (posed; scope and waiver the [USER]'s)

- The whole-sweep boundary: is `unseqClassify` (unseq.go) a faithful decision procedure for the
  design's §1 grammar — every admitted shape lowers, every refused shape names its construct,
  no sweep is lowered by both paths (the mixture guard; the E13 probe hook is suppressed inside
  a graph lowering)? Probe the boundary with shapes the tests do not name (a captured func
  local as callee, a shadowing `x := x + f()`, an address-taken parameter, a nested literal).
- The lowering vs the design's §6 graph: the E1 chain (`after`) through nested calls and
  guards; the region membership of nested `&&`/`||`; the frozen header (a captured slice's
  header read into a slot vs a private slice's header read at the plan step); the private-
  local compound fold's claim that the read is unobservable; the canonical partition = today's
  ANF at every level (the `args-index-vs-call` correction) — is any strict row's default tape
  still not gc's where gc is call-first?
- The decoder's D7 (list order = linear extension) and D12 (static G) against the machine's
  dynamic refusals: is there a graph the decoder admits that the machine refuses, or vice versa,
  beyond the intended defence-in-depth?
- The set claims: the 18 hand-built + 13 native + 4 edge-mutant sets vs `outcomes.txt`; the
  widened E13 pins (3 → 4 on two rows) vs spec#Order_of_evaluation; the claim that no member is
  outside Go's permission on the seven lane-moved rows.
- The records: the baseline re-pin's header vs gate #2's drift block; BUG-101/102/104/112's
  Cases lines vs `check-bugs`; the inventory's §10 list edit; the census numbers (120/28,
  133/29, 25/117, twin 0).

## 10. Audit fix round (2026-09-20) — the dispositions of `docs/2026-09-20_unseq-stage-c-audit.md`

[AGENT] fix-round worker, the same lane (`core/unseq-stage-c-0919`, worktree
`.claude/worktrees/unseq-stage-c`), over the candidate `2dac6a75` (main `6a7beb3d`, no drift). The
audit returned FIX-FIRST — MERGE-CLEAN on the semantics of every emitted graph, three items to fix
before the merge (F1–F3), one records claim (F4), nits (F6–F8), one note (F9). Authority: [USER]
Mike 2026-09-20 «Great, launch the audit» (verbatim, relayed by the [AGENT] coordinator — cited as
relayed); the dispositions below are the coordinator's ([AGENT]), disclosed at the merge ask. Two
commits: the RUNTIME commit `e73c706f` [TRUST-SURFACE `GoLean/NativeToIR.lean`] (the decoder's
D8/D12, the fixtures, the gate controls, the six corpus rows, BUG-113, the baseline) gated by the
full `scripts/capped scripts/ci --slow`, and the RECORDS commit that carries this section (the
design note, the inventory, the ledger, the evidence README). No `GoLean/GoCore/` file changed; no
legacy-emitter semantic change (`tools/nativefrontend` is byte-identical to `2dac6a75`'s); no
theorem changed. Evidence: `docs/evidence/2026-09-19_unseq-stage-c/fixround-*.txt`.

| finding | disposition | what changed | where |
|---|---|---|---|
| **F2** COHERENCE-GAP, a fail-closed REGRESSION: the frontend copies a CONSTANT into a cell (`x := true && f()`, `a[f()] = 5`, `a[f()] = "s"` — design §6's «a constant or atom value is copied into one»), the decoder's D8 refused the head by name; all three ran on main | **FIXED, decoder side** (the design is the authority): D8 admits a bare `int`/`bool`/`string` head — the copy into a cell, trivially in normal form; D9's existing check refuses a constant whose type disagrees with its cell (the named refusal the brief asks for). The refusal text lists the constant among the admitted heads. | `unseqCheckHead` (`\| "int" \| "bool" \| "string" => pure ()`); design §5 D8; three RED-FIRST rows `evalorder/unseq-const-cell/{const-guard-left,elem-assign-const-int,elem-assign-const-string}` (the audit's a14/a15/a16 verbatim): born FAIL/lean-observation on the pre-fix candidate binary (`dbf8fab1…`: «head 'bool' … outside the Stage C fragment», the program refused at its first function), PASS on the fixed binary (`90024323dbe00082`) — `fixround-born-state.txt`, `fixround-postfix-state.txt`; the fix RESTORES: main's frontend + main's binary (`a014183b…`) give the SAME three observations byte for byte (2; `f`·59; `f`·"xs") — `fixround-main-vs-candidate.txt`. Fixtures: `Tests/unseq-wire/{cguard,celem,cstr}.json` (hand-built) + `native-{cguard,celem,cstr}.json` (the frontend's own lowering) — each a singleton = main's answer, exact over the wire; `scripts/check-wire-boundary` gains the constant-head positive control (9 unseq-node controls). | `GoLean/NativeToIR.lean`; `Tests/unseq-wire/build.py`, `src/{cguard,celem,cstr}/`; `Tests/UnseqWire.lean`; `scripts/check-wire-boundary`; `Corpus/coverage/exec/evalorder/unseq-const-cell/` |
| **F3** COHERENCE-GAP: D12's static G did not confine a NESTED guard's completion binder to the OUTER region — a hand-built `then` consuming it decoded and RAN when the outer region was active, refused only dynamically when it skipped | **FIXED, decoder side**: `unseqConfinedTo?` confines a guard's completion binder to THE GUARD'S OWN region (`region`, `none` for a top-level guard) instead of to nothing; the outer join (inside the outer region) still consumes it, a store/`then`/outside occurrence no longer can. The machine's dynamic refusal `UnseqGraph.unproducedConsumer?` (GoLean/GoCore/Unseq.lean, UNCHANGED; Stage B tests F1/A4–A5 in `Tests/UnseqScheduler.lean`) stays behind the static net — DEFENCE IN DEPTH, now said in the spec (design §5 D12). | Mutant `mut-nested-completion-join` (the audit's m02/m02b on R2c: `sink3` consumes the inner `&&`'s completion `$u4` instead of the outer `$u5`): refused BY NAME at decode for BOTH `b` values — «'call9' uses '$u4', confined to the region of 'guard2'» (`fixround-cli-sanity.txt`); the 19th mutant in `mutants.tsv`, in-process and through the CLI; `check-wire-boundary` control `unseq-nested-completion`. The untouched R2c wires (the inner completion consumed INSIDE the outer region by `join7`) still decode and run to their sets. | `GoLean/NativeToIR.lean` `unseqConfinedTo?`; `Tests/unseq-wire/build.py`, `mutants.tsv`; `scripts/check-wire-boundary`, `scripts/check-unseq-wire` |
| **F1** WRONG-ANSWER, pre-existing on the LEGACY path: `sinkL(left \|\| b, change())` with `left` a package variable evaluates the `\|\|` AFTER the later call (main = candidate `logical true 0`; gc `logical false 0`; spec#Order_of_evaluation orders binary logical operations and calls lexically among themselves) | **ROWED, not fixed** (Stage E's; the legacy emitter is out of this round's scope): **BUG-113** filed — `Status: open`, `Pinned-by: differential`, the cause (the ANF hoist lifts the call to a temp BEFORE the statement, the `\|\|` stays inline), the fix plan (Stage E's migration of the `&&`/`\|\|` sweeps to `unseq`, or the E1 completion anchoring in the legacy hoister). | Package `evalorder/legacy-logical-vs-call/` (the audit's c01/c02 verbatim): `or-vs-call`, `and-vs-call` born FAIL/differential (Lean `logical true 0`, Go `logical false 0`) on BUG-113's `Cases:` line — the ratchet: a NEW red, added to the baseline with its written reason; `call-first-control` (`sinkR(change(), left \|\| b)`) PASS. The two frontends' wires for the package are byte-identical and both binaries answer the same (`fixround-main-vs-candidate.txt`). | `docs/BUGS.md` BUG-113; `Corpus/coverage/exec/evalorder/legacy-logical-vs-call/`; `baselines/native-full.tsv` |
| **F5** RECORDS: the C3 trace analysis did not say what `r2b`'s difference from main IS | **CORRECTED** here and in the evidence README §C3: the born strict row `evalorder/unseq-pilot/r2b` (a PRIVATE `left`, lowered as an `unseq` graph with E1 anchored at the guard's COMPLETION) answers gc's `logical false 0`; main's legacy default on the same source is `logical true 0` — a spec-FORBIDDEN member, the F1 wrong answer on the legacy path. The difference is a FIX, not latitude: `r2b` is the pilot-grammar spelling of BUG-113. | §4 of this handoff (the C3 paragraph) and `docs/evidence/2026-09-19_unseq-stage-c/README.md` §C3 carry the sentence. | — |
| **F4** RECORDS: «K=80» claimed for the lowered E13 rows without a `--slow` after the lowering | **MADE TRUE**: this fix round's gate IS `scripts/capped scripts/ci --slow` (K=80, `GOLEAN_SLOW=1`) at the fix tree — EXIT=1 in 954 s (2026-09-20 19:39:04–19:54:58Z), K=80 (`membership_draws 80`); 3705 rows 3458 PASS / 247 FAIL in the run = the pinned 3459 / 246 with the one 5a-class row red; DRIFT = exactly `imported-goose/channel/google-search` PASS→FAIL/membership (STALE certificate for `NativeToIR.lean`; fresh re-certification «unchanged set; seconds=164.598»); every other step ok; re-pin guard 0 PASS→non-PASS. BUG-112 and the inventory's E13 Stage C bullet now cite THIS run. | `docs/BUGS.md` BUG-112; `docs/2026-08-11_latitude-inventory.md` E13 | — |
| **F6** NIT: design §6 «discard cells `$d<n>`» vs the emitted `$u<n>` | **CORRECTED** in §6 (discard cells are minted like every other cell, `$u<n>`). | design §6 | — |
| **F7** NIT: `## BUG-112` above `## BUG-111` | **REORDERED**: BUG-111, BUG-112, BUG-113 ascending (`check-bugs.sh` parses by heading; it has no order rule — the file's convention is ascending). | `docs/BUGS.md` | — |
| **F8** NIT: decoder limitations implied, not stated | **STATED** in design §5 («What the decoder does NOT check»): (i) D8's «no hidden read» for `ident` heads/callees is relative to the frontend's privacy analysis — identifier privacy is the frontend's; (ii) `then` is restricted by exclusion only, v2.1 §3.1's completion contract is not checked; both hand-built-only, the trust in `unseqClassify`/`emitUnseqSweep`. | design §5 | — |
| **F9** NOTE: gc realizes TYPE ASSERTIONS EARLY (`order.go` copies `x.(T)` at its lexical position for non-pointer-shaped T) while the canonical slot realizes them late | **RECORDED** in design §6 and the inventory's E13 (Stage C bullet) and E2 (Stage C bullet): members only, membership rows only (`assert-left-call`, `assert-middle`, `index-assert-left-call`, BUG-101's pair, the audit's a34); a STRICT row of that shape goes red at `differential` rather than passing silently — the exception to route, not a machine bug. | design §6; inventory E13/E2 | — |

**The gate (the runtime commit's tree; captured exits).** Frontend: `go build` EXIT=0, `go test
./tools/nativefrontend/...` ok EXIT=0, `go test ./tools/lowerdiag/...` ok EXIT=0 (the frontend is
unchanged; the tests are the standing suite). Decoder: `scripts/capped lake build GoLean.NativeToIR`
EXIT=0 (11 jobs, warning-free), then `lake build UnseqWireTests golean` EXIT=0 (99 jobs; binary
`90024323dbe00082`). `lake env lean --run Tests/UnseqWire.lean`: 60 ok lines, «every reference set exact
over the wire, 19 mutants refused by name», EXIT=0. `scripts/check-wire-boundary` PASS (11 byte-level
+ 9 unseq-node controls) EXIT=0. `scripts/check-unseq-wire` PASS (58 fixtures byte-identical to the
generator; 19 mutants through the CLI; 80 ok lines) EXIT=0. `scripts/check-bugs.sh` ok — 113 entries;
BUG-113 open with two FAIL rows; BUG-101/112 fixed with PASS rows; the ratchet unchanged (coverage
10/10, latitude 4/4, wrong-answer 0/0). **The full gate: `scripts/capped scripts/ci --slow` under the
box-wide lock — EXIT=1 in 954 s (2026-09-20 19:39:04–19:54:58Z), K=80 (`membership_draws 80`); 3705 rows 3458 PASS / 247 FAIL in the run = the pinned 3459 / 246 with the one 5a-class row red; DRIFT = exactly `imported-goose/channel/google-search` PASS→FAIL/membership (STALE certificate for `NativeToIR.lean`; fresh re-certification «unchanged set; seconds=164.598»); every other step ok; re-pin guard 0 PASS→non-PASS.** Expected red = the two 5a-class items (`certificate provenance`
STALE for `NativeToIR.lean`; the one certified row `imported-goose/channel/google-search`
PASS→FAIL/membership in the run, PASS kept in the baseline for the train's 5a step) and NOTHING else:
the six new rows reproduce their pre-pinned states (3 PASS F2, 2 FAIL/differential BUG-113, 1 PASS
control) — the baseline was pinned from the focused measurements BEFORE the gate so `check-bugs`
could see BUG-113's rows, and the gate confirmed every line. The run's per-row lines (`fixround-gate-tail.txt`): the three F2 rows PASS strict (`wide=0` / `wide=3` / `wide=2`, `exhausted=none depth=fixed` — the wide picks the graphs mint are covered by the three streams), BUG-113's two rows FAIL/differential (Lean `logical true 0`, Go `logical false 0`), the control PASS; BUG-112's two rows `draws=80 (K=80; pin members=N NOT reached — 1 distinct drawn)`: gc draws its one member every time, inside the set (audit F4 made true).

**Choice-trace subset vs main's binary + main's frontend (rows OUTSIDE the pilot's 25 packages).**
The C3 method (`scripts/choice-trace-corpus --dump --jobs 6`) on 279 ids — every 12th outside-pilot
id of the manifest, 210 packages — on the main export tree (`.tmp/main-tree` = `git archive 6a7beb3d`,
main's frontend, main's binary `a014183b…`) and on this tree (the candidate frontend, the fixed
binary `90024323dbe00082`): **278/278 traced rows byte-identical** on the sorted dump records
(stream, idx, phase, site, bound, streamValue, pick) and the per-stream results (status, consumed,
wide, obsHash); sha256 of the identical block `af6e9b95e7aad5c3`; the 279th id
(`complex/generic-type-set/explicit-constant`) refuses identically on both sides (`complex64`);
headline counts identical (1668 (id, stream) lines; every site's consumption count equal) —
`fixround-choice-trace.txt`. The decoder change touches only the `unseq` arm, which no
outside-pilot wire reaches.

**PENDING [USER] (unchanged, posed at the merge ask):** the E2/E12 value-axis envelope on the nine
rows (§6 item 1) and the two E13 narrowings retired on the pilot's rows (§6 item 2). Nothing in this
round rules either.

**Re-verification ask for the auditor** (what to re-run at the fix-round tip): (a) the F2 probes
a14/a15/a16 (`decoder-constant-head-regression.txt`) — the candidate frontend + the fixed binary must
run each to main's observation (2; `f`·59; `f`·"xs"); the corpus rows `evalorder/unseq-const-cell/*`
via `scripts/diff-one`; (b) the F3 mutants m02/m02b (`mutants.tsv`) — both must now refuse at DECODE
with «invalid branch join … confined to the region of 'guard1'» (the audit's a18 graph) — and the
tracked `mut-nested-completion-join.json` (R2c) for both `b`; the control m17 (a18 unchanged) still
runs `f g` / 1; (c) the 18 original mutants unchanged; the r2a/r2c hand-built and native wires
still decode and give their sets (`scripts/check-unseq-wire`); (d) the F1 rows
`evalorder/legacy-logical-vs-call/*` — `or-vs-call`/`and-vs-call` FAIL/differential with Lean
`logical true 0` vs Go `logical false 0`, `call-first-control` PASS; BUG-113's text against
`legacy-logical-op-vs-call.txt`; (e) the default-tape comparison over the pilot's 25 packages
(`default-tape-comparison.txt`) — unchanged (the fix touches no lowered graph's set); (f) the
baseline delta over `2dac6a75`: exactly the six rows added, nothing else moved.
