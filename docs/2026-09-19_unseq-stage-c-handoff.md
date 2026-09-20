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
site's count identical on both sides.

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

Branch-complete at the C3 records commit (this file's commit), parked, clean. The merge train's
command: `git checkout main && git merge --ff-only core/unseq-stage-c-0919`. **5a IS OWED**: the
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
