# Adversarial audit — Stage E5 (families E5a–E5e) of the evaluation-order model v2.1, branch `core/unseq-stage-e5-0922` (candidate tip `403cde75` over main `dc5de785`)

**VERDICT: FIX-FIRST (one minor decoder FAIL-OPEN, F1, plus four RECORDS corrections F2–F5) — no WRONG ANSWER, no
OVER-WIDE SET, no spec-forbidden member found.** Every member of every born / moved set is spec-permitted and gc's
draw is inside on my own draws (46 corpus subjects × 20 draws; 60 probe subjects × 8–12 draws); every computing
position of `&x` refuses by name; every phase-2 check in a multi-target assignment lands AFTER the phase-1 events;
the spec's own `y[f()], ok = g(z || h(), i()+x[j()], <-c), k()` traces `f h i j <-c g k` on the tip and on main;
the `wide` kind and the `mapLit` arm are coherent (both directions, in the same commits as the interpreter arms), total
and pick-free; the baseline delta is exactly 25 born / 9 changed (strict → membership) / 0 lost / 0 PASS→non-PASS; the
census (108 236 sweeps, 177 admitted, 47 packages; 58 corpus probe emissions in 17 packages + 128 twin) and the trace's
DIFFER/ONLY_B lists reproduce; 260 outside-family rows are byte-identical on both frontends × both binaries; all 51
born / moved / affected rows PASS in their pinned lanes here; every gate the candidate claims exits 0 on this box.
F1 is the Stage E audit's F3 class (a forged wire that decodes and answers), reached through the new `wide map-lookup`
arm and already present in the E2 `map-get` head — a one-check fix with two mutants. The five PENDING [USER] items are
real decisions, honestly posed; none is self-adjudicated (§ PENDING).

[AGENT] auditor, 2026-09-22, ordered under the [USER]'s standing direction that every merge is audited adversarially
(Mike, 2026-09-11, relayed by the [AGENT] coordinator — cite as relayed) and the coordinator's dispatch of 2026-09-22.
Worktree `.claude/worktrees/audit-unseq-stage-e5`, branch `review/unseq-stage-e5-0922` at the candidate tip;
`scripts/setup-deps --from` the primary (goose `3be88bb`, raft `56e3200`, go `c19862e5f8`); the lane's `.lake/build`
rsynced at identical sources, `scripts/capped lake build` EXIT=0 under the box-wide lock (binary sha256 `2159163d…` =
the lane's E5d binary); tip frontend built from this tree (`772a4a39…`), main's frontend from `git archive dc5de785`
(`888781fe…`; `.tmp/main-tree`), main's binary the primary's `/home/dev/projects/golean/.lake/build/bin/golean`
(`73734062…`, read-only, verified by sha). No edit to the candidate or main; no merge; no push. Evidence:
`docs/evidence/2026-09-22_unseq-stage-e5-audit/` (26 files, 336 KiB; `scripts/check-evidence-size` EXIT=0). Every
decision below is [AGENT].

## Findings, by severity

### F1 — FAIL-OPEN (decoder, minor): a `wide map-lookup` whose `keyType`/`valueType` disagree with the base map's type decodes; on the canonical tape it answers a Go-observable value

What I did. `mutants-e5.py` mW12: the native wire of my probe `commaOkMapVsWriter` (`xs[f()], ok = m[1]`, f
deleting `m[1]`) with the `wide` occurrence's `keyType` rewritten `int → string` (the base cell `$u65` is declared
`map[int]int`). The candidate DECODES it; `native-json-run` (canonical tape) exits 0 with `{"status":"ok","value":0}` —
the delete-first order leaves the map empty, so the lookup performs no key comparison; on the other tape the machine
sticks LATE («string equality expected string operands, got int 1 and int 1»). mW17 (the base atom's `type`
annotation AND `keyType` both `string`, consistent with each other, inconsistent with the cell) — the same. The
pre-existing E2 `map-get` HEAD with the same edit (mE2, on `Tests/unseq-wire/e5cmaplit.json`) sticks late on the
canonical tape only because its map is non-empty — the same class, differently exposed: neither arm compares
`keyType`/`valueType` with the base atom's declared type (`GoLean/NativeToIR.lean` `"map-get"` head arm; the `wide`
arm's `"map-lookup"` case checks the value cell against `valueType` and the flag cell against `bool`, nothing against
`base`). Related, harmless: mW16 — an operand ATOM's wire `type` annotation is never compared with its cell (a
`[]bool` annotation on the `[]int` cell `$u1` decodes; the machine uses the cell; set {6, 15} unchanged).

Why it matters. The decoder's contract (Stage C design §5, v2.1 §3.1 «sort/type mismatch … declared type vs head»):
fail closed on shapes the emitter never produces. A forged wire answering `0` is the Stage E audit's F3 class exactly
(«malformed wires answer with Go-observable panics/values»), which that fix round closed for `slice-lit`/`make`.
The emitter never emits a disagreeing `keyType` (go/types fixes it), so no corpus row can expose it — it is a
decoder-latitude defect, not a wrong answer.

Where. `GoLean/NativeToIR.lean`: the `"map-lookup"` case of the `"wide"` arm (`kt`/`vt` decoded, not compared with
`base`); the `"map-get"` head arm (`keyTy`/`valueTy` decoded, not compared with `base`); the `"map"` target plan may
share the shape (not probed).

Disposition (proposed, small). At decode: resolve the base atom's type (a `$` cell → `cellTy`; a source local → its
declared type on the wire) and refuse by name unless it is `.map keyTy valueTy`, in both arms (and the map target plan
if it carries the types); mutants `mut-wide-lookup-keytype-vs-base`, `mut-mapget-keytype-vs-base`
(`check-unseq-wire` 45 → 47). Optionally compare every operand atom's annotation with its cell (closes mW16's class).
Re-gate `check-unseq-wire`, `check-wire-boundary`, `lake build`, `ci --diff` (the 5a-class pair stays red as in the
lane's runs — the decoder already changed in this lane).

### F2 — RECORDS: E5c's `mapLit` arm restates a (b) PIN as spec behaviour — the spec's own example says a literal's map-assignment order is NOT specified

What I did. Probe `mapLitDupDynamic`: `map[int]int{k1: 1, k2: 2}[1] + m()` with `k1 = k2 = 1` (private locals,
admitted sweep) → machine set **{7}** (the last entry wins, source order); probe `mapLitDupDynamicSpec` — the spec's
own `a := 1; f := func() int { a++; return a }; f(); mm := map[int]int{a: 1, a: 2}` → machine **21** (`mm[2] = 2`,
`len 1`). spec#Order_of_evaluation, verbatim example: «`m := map[int]int{a: 1, a: 2} // m may be {2: 1} or {2: 2}:
evaluation order between the two map assignments is not specified`» — so `6` and `11` are spec-permitted members the
machine never produces. gc draws 7 / 21 (source order) on 8/8 configs — inside. The pin is PRE-EXISTING (the legacy
`hoistMapLit` stores in source order; `maps/map-literal-duplicate-eval-order` is a strict row, 123414 here and on
main; the inventory's E12 entry names it: «duplicate-map-key evaluation order was already pinned by …»); v2.1 §9 lists
«no composite-literal internal store order» as NOT DONE. What the lane changed is the RECORD: `GoLean/GoCore/
Syntax.lean`'s `AllocSpec.mapLit` docstring, design §E5c and the inventory bullet say «a later duplicate DYNAMIC key
overrides, as Go's successive stores do» — a spec claim that is false, now written into the core's documentation of a
new constructor. Not a wrong answer, not over-wide: a missing-member (b) pin, honestly a pin, dishonestly labelled.

Disposition. Reword the three places: «the entries are stored in SOURCE ORDER — a (b) PIN of gc's realization;
spec#Order_of_evaluation leaves the order of a literal's map assignments unspecified (its own example, {2: 1} or
{2: 2}); the re-envelope obligation rides E12 with `maps/map-literal-duplicate-eval-order`». A membership row for the
duplicate-dynamic-key shape is the natural future envelope (a per-entry store node, or a store-order pick inside the
arm — a design choice, not this fix round's).

### F3 — RECORDS / coverage: E5b silently widens the supported surface — map-element targets in multi-target assignments, which the legacy emitter quarantines by name, now RUN when (and only when) the trigger admits the sweep

What I did. `tools/nativefrontend/emit.go:7466` refuses «map element as assignment target outside a single
assignment» (audit 2026-07-26: no address to take). E5b's `unseqMultiTarget` classes a map element as a `planned`
target and the graph stores through E2's `{"target":"map"}` plan. Probes, tip vs main (frontend + binary each):
`mapCapturedKeyTargetVsWriter` (`m[k], y = 7, f()`, f writing `k`) — tip **{709, 79}**, gc 79 (6/6) inside; main
`unsupported` (the quarantine). `nilMapCapturedKeyTarget` (nil map, captured key) — tip `wit 1` · «assignment to entry
in nil map» = gc's; main `unsupported`. `nilMapTargetVsCall` (`m[1], y = 1, wit(1)` — constant operands, no
observable) — tip AND main `unsupported`, while gc runs it (`wit 1` · panic). So the same source shape now answers or
refuses depending on the observability trigger; the answers are spec-correct (phase-1 key read unordered against f;
the nil-map store's panic in phase 2 after `wit`). Nothing in design §E5b, the handoff or the language ledger says the
quarantine is bypassed on the graph path, and no corpus row exercises it («every detected gap is rowed», [USER]
2026-09-03).

Disposition. One paragraph in §E5b and the ledger naming the widening and its trigger-dependent boundary; two rows
(`evalorder/unseq-multi/map-target-key-vs-writer` {709, 79} membership; a nil-map strict control); the legacy
quarantine's lifting for the call-free shapes is a separate item (not this lane's).

### F4 — RECORDS: the E5e status-diverse split is misdescribed — a row CANNOT declare `ok,panic`; the split was forced, and the detected latitude is unrowable today

What I did. Probe `strIndexStatusDiverse` (`int(s[i]) + m()`, m: `i = 9`) — the lane's first `str-index-vs-call`
shape: the tip's set is **{102, panic}** exactly (`coverage-observations --expect-status ok,panic`), gc's draw the
panic (4/4), inside. Design §E5e / handoff §6 say the membership lane refuses a status-diverse set «unless the row
declares `ok,panic` — audit F8's mechanism, unused by every corpus row» and that the lane chose not to be «the first
consumer of an unexercised path». But `scripts/diff-coverage:629` admits ONLY `ok|panic|deadlock|race|fatal` in a
row's `expected_status` («invalid expected Go status … use ok, panic, deadlock, race, or fatal»); the status SET exists
at the CLI only. The split was the only option, and the shape a sibling call flipping a checked read's STATUS — a
genuine, spec-permitted latitude the lane detected — has no row and cannot have one until the manifest admits a set.

Disposition. Correct the two records («the manifest admits one status; the CLI's set is not reachable from a row»);
row the gap as a harness follow-up (manifest `expected_status` sets, the F8 CLI path behind it) with this probe as the
future row's body. No runtime change.

### F5 — RECORDS (count precision, three items)

(a) E5c «+2 from the widening»: THREE pre-existing sweeps entered the graph — also
`evalorder/unseq-conv-alloc/map-lit-control` (the trace's E5c DIFFER list has it; the census diff filed it under
«rows only in AFTER» because the comment edit shifted its line — `census-e5c.txt` line 50). (b) «E5b's eleven»:
`census-newly-admitted-e5b.tsv` lists TWELVE sweeps; the twelfth, `noodler/evalorder/logicalShortCircuit`, is admitted
(blank-assign, events 3) but its graph never picks at bound ≥ 2 (its `wide=2` in `diff-one` is two `appendSpill`
picks of the digits helper — `trace-logical-short-circuit.txt`: dump and results byte-identical on both sides, 7
`appendSpill` records each, no `unseqNext`), so «12 sweeps admitted, 11 rows differ» is the exact sentence. (c) The
coordinator's brief says «25 born + 10 moved» and «28 named rows»: the baseline changes exactly NINE rows (all strict →
membership, `baseline-delta.txt`) and the handoff §2 item 5 names exactly 27 = 18 born membership + 9 moved, matching
the baseline set by name with no surplus or omission — the brief's 10/28 are miscounts, the lane's records are right.

### F6 — NIT (refusal text): `&a[i]`, `&s.f`, `&*p`, `&pkg.V` refuse as «unary operator & (address of a variable) in a computing position»

None is the address of a variable (the handoff's own E6 table classes `&a[i]` as «an `index-addr` head: the address
of an ELEMENT»). Probes `addrElemVsCall`, `addrFieldVsCall`, `addrDerefVsCall` all refuse (legacy, correct answers 16
= gc) — fail-closed, but the cause named is the wrong one. Name the operand shape.

### F7 — NIT (dead check): «full slice expression on a string (Go forbids it)» is unreachable

go/types rejects a 3-index slice of a string before emission (spec#Slice_expressions); the classifier branch is dead.
Harmless.

### F8 — NIT (decoder latitude, late-named): undeclared `ref` ids and type-confused constant payloads decode and stick late

mD1/mD4 (`ref nosuch` as a payload / an argument) → machine `stuck` «unbound GoCore variable address: nosuch»;
mA1/mA2/mA6b/mA9/mW1/mW8/mW11b/mM4b (a `ref`, a bool, a string where an int is declared; an int atom where a slice is)
→ `stuck` «expected int value, got …» / «expected slice value …» / «mismatched < operands». Closed late, by name — the
standing class the Stage E audit recorded («closed (late, named)»); the emitter never produces them. A declared-id
check on `ref` is cheap; not required.

### F9 — NIT (records): the E5d refusal text for a planned target's `&x` value is a claim about the DECODER («the store would copy a `ref` head into a cell») — true, and the decoder keeps refusing a `ref` head (mutant `mut-addr-head`); fine as a design fact. mA5 (an `after` edge on a `map-lit` allocate) DECODES with the set unchanged {6, 15} — the Stage E audit's F8, PENDING item 4, confirmed on the new arm.

## (a) Member permission, per family — every born / moved row and my probes

Sets re-enumerated here (`row-sets.txt`, `row-sets-multivalue.txt`: tip frontend + tip binary, `coverage-observations`);
gc = my own draws (`gc-row-draws.txt`: 5 runs × GOMAXPROCS 1/8 × default / `-gcflags=all='-N -l'` = 20 per subject,
go1.26.5). Permission ground: spec#Order_of_evaluation (only calls / method calls / receives / `&&` `||` are mutually
ordered; «the order of those events compared to the evaluation and indexing of x and the evaluation of y and z is not
specified»); spec#Assignment_statements (two phases; a target's own check is the store's — its own `x[1], x[3] = 4, 5
// set x[1] = 4, then panic setting x[3] = 5`); spec#Built-in_functions «called like any other function» under the
RATIFIED reading (a).

| family | row | set (here) | gc | permitted because |
|---|---|---|---|---|
| E5a | `unseq-builtins/min-read-vs-call` | {7, 16} | 16 | `min` E1-ordered before m; y's read unordered vs m |
| E5a | `…/append-read-vs-call` | {6, 15} | 15 | append E1-ordered before m (in-place store); the result's `[0]` read unordered vs m |
| E5a | `…/copy-effect-vs-read` | {2, 9} | 9 | the checked read of `d[0]` unordered vs the effectful copy |
| E5a | `…/append-spread-str-vs-call` | {9, 18} | 18 | x's read unordered vs m; the spread string inside append's window |
| E5a | `…/{min-vs-call, copy-stmt-control}` | 6; 78 strict | 6; 78 | forced under reading (a) / one observation |
| E5a | `e13/{assert-left-append, assert-left-copy, tgt-assert-vs-min-call, tgt-assert-vs-copy-call, tgt-assert-vs-append}` | 2 members each (the assertion's panic vs the index panic / vs `wit 5`) | the assertion alone | two failing occurrences unordered; the E13 class, sets = the legacy probe's |
| E5b | `unseq-multi/tuple-header-vs-call` | {15, 57} | 15 | the element plan's frozen header before / after m's rebind (phase-1 operand) |
| E5b | `…/blank-panic-vs-call` | {panic·``, `wit 1`·panic} | `wit 1`·panic | the blank target's checked read unordered vs wit |
| E5b | `…/comma-ok-recv-target-vs-panic` | {`len 1`·panic, `len 0`·panic} | `len 0` | the target's index read unordered vs the receive |
| E5b | `…/multi-call-header-vs-call`, `…/define-tuple-vs-call` | {15, 57}; {6, 15} | 15; 15 | as above |
| E5b | `multi-assign/call-write-back-order/{deref-target, slice-header-base}`, `…-value/deref-target` (BUG-052) | {42007, 4207}; {1120003, 774203}; {42007, 4207} | 4207; 774203; 4207 | the frozen pointer / header plan before or after the redirecting call |
| E5b | `noodler/latitude/rhs-list-index-call-index` | {(1,5,1), (1,5,9), (9,5,1), (9,5,9)} | (9,5,9) | two reads of `a[0]` unordered vs f and vs each other (R1) |
| E5b | `spec-examples-stmt/eval-order-calls/{verbatim, traced-recv}` | `f,h,i,j,g,k`·192·true; `f,h,i,j,c,g,k`·192·true (singletons, wide=13) | = | the spec's own forced trace; main's frontend + binary give the same (`spec-rows-main-frontend-binary.txt`) — main never had the red-first wrong answer (the first E5b cut was never committed; its red is the lane's `diff-one-e5b.txt` run 1) |
| E5c | `unseq-maplit/map-lit-entry-vs-call`, `…/map-lit-key-vs-call` | {6, 15}; {5, 6} | 6; 6 | the literal's entry / key read unordered vs m; gc realizes the literal at its position |
| E5c | `noodler/latitude/map-literal-key-vs-call` | {5, 50} | 50 | the key read vs the value's call inside the literal (spec: «n may be {2: 3} or {3: 3}») |
| E5c | `e13/map-lit-payload-vs-call` | {panic·``, `wit 5`·panic} | panic alone | the key's index panic unordered vs wit (the F6 shape, membership by rule) |
| E5e | `unseq-strings/str-index-vs-call`, `…/str-slice-vs-call` | {102, 103} ×2 | 103; 102 | the byte read / substring unordered vs m (gc realizes them on OPPOSITE sides of the call — both inside) |
| E5e | `…/str-index-panic-vs-print` | {panic·``, `wit 5`·panic} | `wit 5`·panic | E13's class on a string base |
| E5e | `e13/bytes-conv-payload-vs-call` | 2 members | panic alone | probe → graph, set reproduced |
| E5d | `unseq-addr/{addr-arg-vs-read, addr-global-arg-vs-read}` | {2, 8} ×2 | 8 | the address-taken variable's read unordered vs the call writing through the address |
| E5d | `…/addr-payload-vs-call`, `…/addr-stored-vs-read` | {6, 15}; {72, 78} | 15; 78 | as above through a literal payload / a stored pointer |
| E5d | `multi-assign/deref-target-before-rhs`, `…/selector-target-before-rhs` | {181, 188, 822, 828}; {171, 177, 722, 727} | 188; 177 | the target's operand read × the right-hand read of p, each before / after the call |
| E5d | `channels/make-edge/ordinary-receive-eval-order` | {170, 171, 182} | 182 | score's read before / between / after the two writing calls |

No spec-forbidden member; gc inside on every row (46/46 subjects, `gc-row-draws.txt`). My probes
(`probes-*.go`, `probe-results.txt`, `gc-probe-draws.txt`; gc 8–12 draws per subject, 60 subjects, every draw inside):

- **E5b phase-2 checks** — `oobTargetVsCall` (`xs[9], y = 1, wit(1)`) {`wit 1`·panic} singleton (a panic before
  `wit 1` would be forbidden — absent); `secondTargetPanics` (`xs[0], xs[9] = 4, wit(5)`, deferred print) `wit 5` ·
  `xs0 4` · panic singleton = the spec's example; `nilDerefTargetVsCall` `wit 1`·panic (legacy); `specExampleOldIndex`
  (`i, xs[i] = f(), 2`) 122 (x[0] uses the OLD i); `capturedIndexTarget` {1127, 1723} (a captured i's read before /
  after f); `sameTargetTwice` 2; `plainTargetWrittenByCall` 19 (the plain target's `.var` plan stores in phase 2 after
  f's write); `targetOperandCallsOrder` `f g two` 78 and `targetOperandVsRHSCalls` `f g h` 12 (target operands' calls
  lexically first — the red-first class, correct); `swapVsCall` {205, 2005}; `commaOkClosedChan` 100; `commaOkNilIface`
  100 (forced, legacy); `commaOkMapVsWriter` {0, 11}; `chanBoolCommaOk` 11; `defineRecvTuple` {306, 307};
  `globalBesidePlanned` refused by name («package-level target beside a planned target») 13.
- **E5a** — `minArgVsCall` (`min(x, m())`, m writing x) {1, 5} — both orders, no hidden pin (gc 5: gc reads x AFTER
  m); `callThenMin` {6, 15}; `callThenMinTwo` {6, 7, 15} (a, b unordered vs m and each other); `appendAliasRead`
  (`append(s, 3)[0] + s2[2]`, shared backing) {0, 3} — the in-place element store is an effectful event a sibling
  read is unordered against; `copyOverlapVsRead` (`copy(s[1:], s) + s[2]`) {5, 6}; `appendFullBase` {6} (the spill
  decouples the read; the `appendSpill` capacity site joins at bound 30 — refused by name at width 6, enumerated at 32);
  `appendResultPlanned` {2, 3}; `capVsAppendCall`, `minStringVsCall` forced (legacy); `maxFloatVsCall` refused
  («result type outside the pilot grammar (float64)»); `realVsCall` refused (complex128 quarantined).
- **E5c** — `mapLitCallsInside` (`map[int]int{k(): v()}[1] + m()`) `k v m` 7 singleton — the literal's inner calls are
  E1 events in lexical order, none dropped or late; `mapLitIfaceValue` {6, 15}; `mapLitStringKeyVsCall` {5, 6};
  `mapLitNestedValue` {6, 15}; `mapLitAsCommaOkBase` {-1, 7}; `mapLitValueCallVsKeyRead` {5, 50}; F2's two pins.
- **E5e** — `strReassignVsIndex` (m reassigning s) {102, 127}; `strIndexVsReassignBoth` (s AND i written) {102, 125,
  127, panic} — all four (R1, no read-order reduction); `strSliceOOBVsPrint` {panic·``, `wit 5`·panic} (gc: the
  slice hoisted BEFORE wit — the panic alone, inside); `strConcatIndexVsCall` {102, 103}; `strSliceReassign` {bc!, yz!};
  `strLenSliceForced` 7; F4's status-diverse {102, panic}.
- **E5d** — computing positions ALL refuse by name (F6's text): `*(&x)`, `&x == &y`, `&a[0]`, `&s.f`, `&*p`,
  `append(ps, &x)`, `ps[m()] = &x` («as a planned target's value»); value positions: `addrMapValue` {6, 15} (a
  `map[int]*int` literal's value), `addrGlobalPayload` {6, 15} (`globaladdr` payload), `addrNestedLit` {6, 15} (elided
  struct type inside a slice literal), `addrArgThenWrite` 1 and `addrArgCallWritesFirst` 5 (forced: E1 / D),
  `addrTwoWritersRead` {4, 10, 76} (two writers through `&x`, the read in every position), `addrPtrRecv` {7, 17, 106}
  (`(&v).Bump()` receiver), `addrReturnPairDriver` {1006, 1015} (`return &x, m()+x` — the returned pointer valid),
  `addrParamDriver` {2, 8} (a parameter's address), `addrClosureAdmitted` 67 (an ADMITTED sweep inside a lifted body
  carrying `&x` of a CAPTURED variable — the pointer-parameter spelling writes the outer x). The address-taken
  analysis is function-wide (`unseqAddrTaken`), so `&x` in a sweep makes x's reads occurrences everywhere in the
  function — never a forced singleton where the spec has two members.

## (b) Multi-target: the target-operand-first order

`targetOperandCallsOrder` / `targetOperandVsRHSCalls` and the spec example trace the target operands' calls before the
right-hand side's on the tip (`f g two`, `f g h`, `f h i j <-c g k`); main (legacy) agrees on all three. The E5a-commit
frontend refuses multi-target assignments by name («multi-target or tuple assignment» → legacy), so the pre-fix E5b
cut's wrong answer exists only in the lane's `diff-one-e5b.txt` run 1 — never in history, never on main. No BUG entry
is needed (the corpus caught it red-first inside the lane, as the design records).

## (c) The core

`WideSpec` (4 arms, `arity` 1/1/2/2), `UnseqBody.wide`, `AllocSpec.mapLit`: total (structural matches; no `partial`,
`sorry`, `native_decide`, axiom, `unsafe`, `implemented_by`, `decide +native` in the core diff — grep; `check-core-audit`
EXIT=0); the two `Step` rules `unseqRunWide` / `unseqWideDone` mirror the alloc pair (store unchanged, trace `[]`);
`stepUnseqNext`'s `.run`/`.wait` arms, `stepUnseqNext_sound`, `step_complete`, `step_complete_any_wf_aux`,
`stepUnseqNext_run_wait_stream`, `step_preserves_wf_loc` (`unseqWideStmt_locSup`), `unseq_record_stable`,
`unseq_done_permanent`, `valueBinds`/`mentions`/`names`, `eqbF` + soundness, the indices and the loc-bound network
all landed in the E5a commit `eba20f2d` (the E5b/E5c arms in `f70903dc`/`f5903528` with their `names`/`eqbF`/
`indices`/`sup` cases — `git show --stat`, § evidence `gate-tails.txt`). `unseqWideStmt` builds the LEGACY statements
(`Stmt.appendSlice`/`copySlice`/`mapLookup`/`typeAssert` with the binder cells as targets; a binder list of another
arity reaches `.unsupported` by name behind `wellFormed?`'s static arity check — mW6/mW7/mW9/mW10 «duplicate result»,
mW15 «flag cell … not bool»); no raw memory op (`check-mem-callsites` 70 rows PASS); no new pick (`unseqNextBound`,
`ChoiceSite`, `canonicalSlot` untouched in the diff; `check-unseq-scheduler` 35 theorems, classical trio only). The
`append`'s in-place element store is the legacy `appendSlice` statement's own write under the wait frame (its accesses
are the legacy path's — delegated, not re-modelled), observable to a sibling read as `appendAliasRead` shows.

## (d) Decoder mutants (`mutants-e5.py`, `mutants-e5b.py`, `mutant-results.txt`; 44 one-edit mutants through the real CLI)

| # | mutant | result | class |
|---|---|---|---|
| mA1/mA2/mA9/mA6b | `map-lit` key a `ref x` / a bool / a string on keyType int; value a string on valueType int | machine `stuck` «expected int value, got …» | closed (late, named) — F8 |
| mA3 | `map-lit` value `ref $u1` (a binder) | REFUSED «takes the address of a binder cell … (audit F2)» | closed |
| mA4 | cell `map[int]bool` vs valueType int | REFUSED «yields … but cell … declared …» | closed |
| **mA5** | `after: [call0]` on the `map-lit` allocate | **DECODED, ran; set {6, 15} unchanged** | Stage E F8 = PENDING item 4 |
| mA7 | `entries` not an array | REFUSED «array expected» | closed |
| mA8 | duplicate constant key (control) | REFUSED «duplicate constant key … (spec#Composite_literals)» | closed |
| mW1/mW8 | `append` elems / `copy` src an int atom | `stuck` «expected slice value» | late, named |
| mW2 | `append` slice a `ref s` | REFUSED «hidden read in a wide built-in» | closed |
| mW3 | `append` elem bool vs cell `[]int` | REFUSED «yields … but cell … declared …» | closed |
| mW4/mW5 | unknown key / unknown region on a `wide` | REFUSED (exact-key; «region … not a guard occurrence») | closed |
| mW6/mW7/mW9/mW10 | duplicate result cell — append, copy, a two-binder lookup `[$u94, $u94]`, a two-binder recv `[$ok, $ok]` (chan bool) | REFUSED «duplicate result (a value binder produced twice)» | closed (the flattened binder list is checked) |
| mW11b | `map-lookup` index a string on keyType int | `stuck` «expected int value» | late, named |
| **mW12/mW17** | `map-lookup` keyType string (± base annotation) vs base cell `map[int]int` | **DECODED; canonical tape RAN, answered 0; other tape stuck late** | **F1 FAIL-OPEN** |
| mE2 | E2 `map-get` HEAD keyType string (pre-existing arm) | `stuck` late on the canonical tape (its map is non-empty) | F1's class, pre-existing |
| mW13/mW19 | `type-assert` target / `map-lookup` valueType vs the value cell | REFUSED «yields … but its value cell … declared …» | closed |
| mW14 | `type-assert` operand `ref $u1` | REFUSED (F2 text) | closed |
| mW15 | `type-assert` binds `[$u0, $u0]` (int) | REFUSED «flag cell … declared int, not bool» | closed |
| **mW16** | append's slice atom annotated `[]bool` on the `[]int` cell | **DECODED, ran; set unchanged** (annotation unused) | NIT (annotation never checked) |
| mW20 | valueType bool + value cell bool on a `map[int]int` base | `stuck` late (the zero `false` stored into `xs[]`) | late, named |
| mD1/mD4 | `ref nosuch` payload / argument | `stuck` «unbound GoCore variable address: nosuch» | late, named — F8 |
| mD2 | `globaladdr gid 9999` payload | REFUSED «globaladdr gid 9999 out of range» | closed |
| mD3 | `ref m` (a func-typed local) as a `*int` field payload | `stuck` «expected int value, got funcVal» | late, named |
| mM1 | `min` head type string over int args | REFUSED «head type … disagrees with cell» | closed |
| mM2/mM3 | `min` arg a `ref x`; `min` with no args | REFUSED («not an atom»; «no operands») | closed |
| mM4b | `min(x, "z")` mixed operands | `stuck` «mismatched < operands» | late, named |
| mB1/mB2/mB3 | `.var` target `nosuch`; a binder as a store target; a TARGET binder as a store value | REFUSED («unbound target operand»; «a binder … cannot be a store target»; «store value … is not a VALUE binder») | closed |
| mB4 | the same target stored twice | DECODED, ran; set {15, 57} = unmutated | legitimate Go shape (`x[0], x[0] = …`) |

The lane's own 45 mutants all refuse through the CLI (`check-unseq-wire` EXIT=0 here).

## (e) Trigger, census, traces, outside-family

Census (my run, tip frontend, `census-tip-summary.txt`): **108 236 corpus sweeps, 177 admitted in 47 packages, all in
`main` units; twin 10 203 / 0** = the lane's `census-e5d.txt` exactly; probe emissions (`probes-tip.tsv`): **58 in 17
corpus packages, 128 in the twin, 175 `unseq` graph nodes, 25 export refusals** = the lane's. The 24 DIFFER ids of
`choice-trace-main-vs-e5d.txt` are exactly the rows of the sweeps `census-newly-admitted-e5{a,b,c,d,e}.tsv` name plus
`map-lit-control` (F5a), minus `logicalShortCircuit` (F5b, no bound-≥2 pick); the 25 ONLY_B ids are the 25 born rows of
`baseline-delta.txt`. Outside the family: 260 baseline-PASS strict rows outside DIFFER ∪ born, ≤ 2 per package (204
packages), exported with BOTH frontends and run on BOTH binaries on the default tape — **260/260 identical
observations, 0 frontend errors** (`outside-check.log`, `outside-check-rows.tsv`). The grammar was not widened merely
to reduce probes: E5d's three entering sweeps carried no probe (58 → 58), E5e/E5c one each, E5b three, E5a seven —
each retirement is a sweep whose probe the graph now realizes as a member set (the five e13 built-in rows keep their
two members; `bytes-conv-payload-vs-call` its two). The residue table (handoff §3): 128 twin + 23 corpus non-main-unit
emitters + 21 panic-vs-panic pairs + 5 shapes outside the grammar + 9 singletons = 58 + 128 — sums.

## (f) Records

Baseline (`baseline-delta.txt`): main 3732 = 3497 / 235 → tip 3757 = 3522 / 235; born 25 (18 membership + 7 strict
controls), changed 9 (all strict → membership, each with a written reason in the header), lost 0, **PASS→non-PASS 0**;
the header carries one re-pin paragraph per family. `docs/language-coverage-ledger.md` §8 tally 3757 = 3522 / 235 ✓.
BUG-052 gains an ENVELOPED paragraph (correct: the fixed post-call order is one member); BUG-032 stays `fixed` and its
rows legacy under the trigger, as §E5b says. Every [AGENT] choice is tagged; the `wide` kind carries «PENDING [USER]»
in Syntax.lean, design §E5a, handoff §2 and the inventory; nothing is briefed as a default. `check-bugs.sh`,
`check-spec-anchors` (968 spec# citations resolve at the pin), `check-evidence-size`, `tools/reconcile-records` (the
standing two report-only findings C9/C13 only) all reproduce. Handoff §2 item 5's 27 names = the 18 born membership +
9 moved rows exactly (F5c).

## (g) Gates (captured exits, this box, `gate-exits.txt`, `gate-tails.txt`)

`check-bugs` 0 · `check-spec-anchors` 0 · `check-mem-callsites` 0 (70) · `go test ./tools/nativefrontend/` 0 · `go
test ./tools/lowerdiag/` 0 · `check-wire-boundary` 0 (11 + 46) · `check-unseq-wire` 0 (45 mutants) ·
`scripts/capped check-unseq-scheduler` 0 (35 theorems) · `scripts/capped check-core-audit` 0 · `scripts/capped lake
exe gocore-eval-tests` 0 · `check-frontend-pins` 0 (twin wire = pinned bytes `e1a87725…`; 61 stdlib files) ·
`scripts/capped lake build` 0 · `tools/reconcile-records` 0 (2 standing findings) · `check-evidence-size` 0 ·
`scripts/diff-one` on 51 rows: 33 PASS/membership (each `enumerated` = the pinned `members`), 18 PASS strict — 0 FAIL.

## PENDING [USER] items — assessed, not decided

1. **The `wide` body kind** — a real [USER] decision (a new constructor in trust surface #1). The [AGENT]
   recommendation (one closed kind mirroring `allocate`, extended by arms) is sound: coherence proved both ways in the
   same commit, no pick, the statements delegated to the legacy path; the alternatives are named honestly
   (`AllocSpec` arms — a misnomer for `copy`; a kind per built-in — four constructors for one shape; a general `exec`
   body — the nested-inductive cycle E4 rejected). Note for the ratifier: the kind's `map-lookup` arm carries F1.
2. **The trigger refinement for panic-vs-panic pairs** — a real decision (it changes RATIFIED item 2); posed, not
   taken. Alternatives are honest: keep the trigger and re-scope E6, or refine («OR against another FAILING
   occurrence», panic identity an observable). My probes agree the legacy probe realizes both members today
   (`e13` rows), so retiring it under the unrefined trigger would narrow — the lane's caution is right.
3. **Non-main units and E6's zero** — a real scope decision; the census numbers (151 of 186 emitters) are reproduced
   here. Alternatives (widen to non-main units, re-pin the twin; or re-scope E6 to the main unit) honestly named.
4. **F8: an `after` edge on a literal `allocate` decodes** — confirmed on the new `map-lit` arm (mA5, set unchanged).
   Cheap either way; the Stage E audit's own disposition (a design fact) is a fair default to ratify or overturn.
5. **E2/E12 (a) on this lane's 27 named rows** — consistent with ratified item 3's mechanism; the list matches the
   baseline exactly; every set's gc member is inside on my draws. The honest alternative is stated only implicitly
   (not ratifying = reverting nine lane moves and the eighteen born membership rows to (b) pins) — the coordinator
   should say so at the ask.

## What I did NOT check

- A full `scripts/ci --diff` / `--slow` on this box (relied on the lane's five tails + my 51-row `diff-one` + every
  standalone gate; the 5a-class pair is the train's).
- K = 80 gc draws (mine: 20 per corpus subject, 8–12 per probe subject).
- The `map` target plan's `keyType`/`valueType` against the base (F1's third possible path — code-read only).
- Whole-corpus choice traces re-run (I reproduced the census and the DIFFER/ONLY_B lists by name and traced the one
  disputed id on both sides; the 260-row outside check stands in for the byte-identity claim).
- The race detector's view of the `append` in-place store (argued by delegation to the legacy statement; not traced
  through `Race.lean`).

## Proposed dispositions

| # | class | disposition | cost |
|---|---|---|---|
| F1 | FAIL-OPEN (minor) | decode-time `base` type = `.map keyTy valTy` in the `wide map-lookup` arm AND the `map-get` head (+ the map target plan if applicable); 2 mutants; re-gate `check-unseq-wire`, `check-wire-boundary`, `lake build`, `ci --diff` | small; before merge (or the coordinator records it with the Stage E F3 precedent — a [USER] waiver, not mine) |
| F2 | RECORDS | reword `Syntax.lean` mapLit docstring, design §E5c, inventory bullet: source-order stores are a (b) PIN; cite the spec example and `maps/map-literal-duplicate-eval-order`; E12 re-envelope | records only |
| F3 | RECORDS / coverage | state the map-element multi-target widening and its trigger-dependent boundary in §E5b + ledger; two rows | records + 2 rows |
| F4 | RECORDS | correct the status-set wording (manifest admits one status); row the harness gap | records only |
| F5 | RECORDS | «3 widening sweeps» (E5c), «12 admitted / 11 differ» (E5b); the coordinator's 10/28 → 9/27 | records only |
| F6–F9 | NIT | refusal text; dead check; `ref` id check optional; none blocking | optional |

## Re-verification (fix round `28919dd6`, 2026-09-22)

**REVISED VERDICT: MERGE-CLEAN** — F1 is fixed at decode by name on all three map arms (my mW12/mW17/mE2/mW20, the
round's four mutants and my own target-plan mutant mT1 all refuse «keyType/valueType … disagree with the map base's
declared type» on the fix binary; every positive control answers identically on both binaries); F2–F5 are corrected
as claimed and honestly; F6/F7 are fixed with the census relabel exactly as claimed (147 = 97 + 36 + 8 + 5 + 1, no
sweep moved); the three born rows are correct, correctly labelled and gc's draws are inside (20/20 each, mine); the
baseline moves by exactly those three; 54 rows PASS in their lanes (the one red by design); 260 outside-family rows
are byte-identical to main's frontend + binary; every gate exits 0 on the fix tip. One RESIDUAL of F1 is named below
(R1, the mW16 class the round left OPEN): a consistently forged annotation on a SOURCE-LOCAL map base still decodes
and answers; I judge it recordable-not-blocking, with the reasons stated, for the coordinator/[USER] to overrule.

[AGENT] auditor, ordered by the [AGENT] coordinator's re-verification request (2026-09-22, relayed). Method: a second
worktree `.claude/worktrees/audit-unseq-stage-e5-fix` detached at `28919dd6` (runtime commit `263866da`; the diff
over my audited tip `403cde75` is confined to `GoLean/NativeToIR.lean` (+41/−3, `unseqCheckMapBase` + its three call
sites), a `Syntax.lean` docstring, `tools/nativefrontend/unseq.go` (+41/−3, refusal texts, one dead arm deleted),
tests, wires, three corpus rows and records); the lane's `.lake` at identical sources, `scripts/capped lake build`
EXIT=0 under the lock (golean `63e9c661…`, the lane's hash); the fix frontend built from that tree (`4586fa01…`);
the audited binary (`2159163d…`) kept for before/after. Evidence: `docs/evidence/2026-09-22_unseq-stage-e5-audit/
reverify-*` (16 files). No edit to the candidate or main; no push; the rebase onto the fix tip is the coordinator's.

### Per item

| item | what I ran | observed | verdict |
|---|---|---|---|
| **F1** the audit's mutants | `reverify-mutants.py`: mW12, mW17, mE2, mW20 on the audited vs the fix binary | audited: mW12/mW17 RAN (0), mE2/mW20 stuck late; fix: all four **REFUSED at decode** «… disagree with the map base's declared type … (audit F1)» | FIXED |
| **F1** the round's four mutants | `mut-wide-lookup-{keytype,valuetype}-vs-base`, `mut-mapget-keytype-vs-base`, `mut-map-target-keytype-vs-base` on both binaries | audited: the lookup-keytype one RAN (0), the other three stuck late; fix: all REFUSED by name (`mutants.tsv` 45 → 49; `check-unseq-wire` 49; `check-wire-boundary` 11 + 49; `Tests/UnseqWire.lean` 132 ok) | as claimed |
| **F1** the third path (`map` target plan) | my mT1: the target plan's `keyType → string` on a `$`-cell base (probe `mapCapturedKeyTargetVsWriter`, empty map) | **audited binary RAN, answered 79** — so the target-plan path was a full «decodes and answers» too, not only late-stuck as the round's own (non-empty-map) mutant showed; fix: REFUSED «map-element target plan … disagree …» | FIXED; the round's «stuck late on it» was true of its wire, the class was the whole F1 symptom |
| **F1** positive controls | `e5blookup`, `native-e5blookup`, `e2map`, `native-e2map`, `e5cmaplit`, `native-e5cmaplit`, `e5btuple`, `w1` on both binaries | identical answers (0 / 0 / 10101 / 10101 / 15 / 15 / 15 / 2) | as claimed |
| **F1** the new positive control | `enumerate.py` E5b5; the corpus row `comma-ok-map-target-vs-delete` | E5b5 `[0, 11]`, `RESULT: PASS`; row {0, 11} (`diff-one` PASS/membership enumerated=2), gc 0 on 20/20 — the lookup before the deleting call (1, true) → 11, after (0, false) → 0: both spec-permitted (a read unordered against a call), the `why` carries «[AGENT] addition» and the reason (no row or wire had exercised the arm) | correct and honestly labelled |
| **R1** the residual (mW16 class, left OPEN) | `reverify-mutants2.py` mS1–mS5 on an ADMITTED sweep whose map base is a PRIVATE source local (`commaOkPrivateMapKeyRead`: `xs[f()], ok = m[a[0]]`, m empty; `mapTargetPrivateVsCall` for the target plan) | keyType forged alone (mS2/mS5) → REFUSED (the annotation disagrees); annotation REMOVED (mS3) → REFUSED «the map base carries no static type on the wire»; **annotation AND keyType forged consistently (mS1/mS4) → decodes and RUNS on the fix binary (100 / 79)** — `unseqPayloadTy?` trusts a source local's annotation, so a consistent forgery passes; the wire does carry the local's declared type (its `define` `{"target":"declare","type":map[int]int}`), so a cross-check is possible | OPEN, recorded below |
| **F2** | `Syntax.lean` docstring, design §E5c, inventory E12/E2 bullets, handoff §2 item 6 | the (b) PIN stated with the spec example verbatim, the legacy row named, the re-envelope POSED; the core rebuilt (docstring); the trace/baseline unmoved (below) | as claimed |
| **F3** rows | `diff-one` at the fix tip; my gc draws 20/20 | `map-target-key-vs-writer` {709, 79} PASS/membership, gc 79; `map-target-nil-legacy-refusal` FAIL/frontend-export «map element as assignment target outside a single assignment», gc `wit 1` · «assignment to entry in nil map» 20/20 — the red is the quarantine's own, by design | as claimed |
| **F3** the correctness argument vs spec#Assignment_statements | probes (`reverify-probes-f3.go`, fix toolchain; gc 12 draws each): `mapTargetKeyPanicVsCall` (`m[a[9]], y = 1, wit(1)`), `mapTargetRhsDeletesKey`, `mapTargetRhsRewritesKey`, `mapTargetRhsRebindsMap`, `mapTwoTargetsVsCall`, `commaOkMapTargetVsRewrite`, `mapTargetPrivateVsCall` | {panic·``, `wit 1`·panic} (the key operand's panic is phase 1, unordered vs wit — gc `wit 1`·panic inside); **719** and **709** singletons (the store is phase 2 — a deleting or rewriting call cannot outrun it; gc =); {109, 119} (the frozen map VALUE before / after the rebinding call; gc 119); {51, 59} (two map targets, the read key vs the writing call; gc 59); {11, 15} (gc 15); {709, 79} (gc 79) | the argument holds: `Assignee.mapElem` freezes the map and key VALUES in phase 1 and checks nothing; the store is phase 2; no member outside spec#Assignment_statements' two phases |
| **F3** records | BUG-115 (Status open, Pinned-by differential, Cases = the born red + the five A3 rows — all six FAIL/frontend-export in the baseline); triage A3 5 → 6; ledger §2/§8; design §E5b + «the audit fix round» | consistent; `check-bugs` EXIT=0 | as claimed |
| **F4** | design §E5e rewritten; handoff §3 owed apparatus item; §6 note corrected | states the manifest admits one status (`diff-coverage:629`), the split was forced, the CLI path unreachable from a row; the future row's body named | as claimed |
| **F5** | design §E5c/§E5b, ledger §8ah, README, handoff §4; handoff §2 item 5 | «+3 pre-existing sweeps», «12 admitted / 11 differ»; item 5 now names **29** rows = the baseline's 20 born-membership + 9 moved vs main exactly (my recount, no surplus, no omission) and states the implicit alternative (reverting to (b) pins) | as claimed |
| **F6** | census with the fix frontend vs the audited tip's (`reverify-census-f6-relabel.txt`); my p_addr probes' refusal texts | the «unary operator &» first-reason class: audited 147 (all «address of a variable») → fix **97 element + 36 field + 8 indirection + 5 variable + 1 qualified package var = 147**, corpus + twin (corpus-only 139 = 139); no sweep moved (admitted 177 → 179 = exactly the two born graph rows; 0 lost); `*(&x)`/`&x == &y` keep the variable text, `&a[0]`/`&s.f`/`&*p` name their shape; unit tests in `go test` (EXIT=0) | as claimed |
| **F7** | `go build` of `func f(s string) string { return s[0:1:2] }` | «invalid operation: 3-index slice of string» — go/types rejects the form; the deleted arm was unreachable | as claimed |
| baseline | `reverify-baseline-delta.txt` | 3757 = 3522 / 235 → 3760 = 3524 / 236: born exactly the three rows (2 PASS/membership, 1 FAIL/frontend-export), changed 0, lost 0, PASS→non-PASS 0; header reason written | as claimed |
| trace | not re-run whole-corpus; instead: 260 outside-family rows (204 packages) with the fix frontend + binary vs main's (`reverify-outside-check.log`) and the 54 rows' sets | **260/260 identical**; the 51 audited rows' lanes and enumerated sets unchanged (35 membership + 18 strict PASS + the 1 red by design = 54); the census diff audited → fix: newly admitted 0, lost 0 beyond the born package | consistent with «3721 byte-identical, 0 DIFFER, 3 ONLY_B» |
| gates on the fix tip | `reverify-gate-exits.txt` / `-tails.txt` | check-bugs 0 · check-spec-anchors 0 · check-mem-callsites 0 (70) · go test frontend 0 · go test lowerdiag 0 · check-wire-boundary 0 (11 + 49) · check-unseq-wire 0 (49) · check-unseq-scheduler 0 · check-core-audit 0 · eval-tests 0 · check-frontend-pins 0 (twin byte-identical) · reconcile-records 0 (the standing C9/C13) · `scripts/capped lake build` 0 | green |
| probe emissions | `probes.sh` with the fix frontend | 58 corpus in 17 packages + 128 twin unchanged; `unseq` graph nodes 175 → 177 (the two born graph rows) | as claimed |
| provenance | design «the audit fix round», handoff §5, the row `why`, BUG-115, the baseline header | every choice tagged [AGENT]; «dispositions the [AGENT] coordinator's, disclosed at the merge ask»; the addition beyond the dispositions stated as such; nothing briefed as a default | honest |

### R1 — the residual of F1 on the source-local base path (the mW16 class, OPEN by the round's own record)

`unseqCheckMapBase` compares `keyType`/`valueType` with the base atom's static type: a `$` cell's DECLARED type
(authoritative — the atom's own annotation is not consulted, so mW17 refuses) or, for a SOURCE LOCAL, the atom's `type`
annotation (`unseqPayloadTy?`). The annotation is the wire's word, not the decoder's knowledge: mS1 (`wide map-lookup`)
and mS4 (`map` target plan) forge annotation and `keyType` together to `map[string]int` on a private `map[int]int`
base and the fix binary decodes and answers (100 / 79 — empty maps, no comparison). The same trust-the-annotation
rule has governed every source-local atom since Stage C (D9: «a source local's / constant's / zero value's `type`
annotation»), so this is not a regression and not new to E5; the emitter never produces it; the wire does carry the
authoritative declaration (`{"id":"m","target":"declare","type":…}` in the local's `define`), so a decoder pass that
cross-checks source-local annotations against the enclosing function's declarations would close the whole mW16 class
at once. **Judgement ([AGENT])**: recordable, not blocking — the round's record already names the class OPEN, the
residual needs a forged wire with a self-consistent lie, and the fix is a decoder-wide item rather than a map-arm
patch. What I ask the coordinator to add to the record: (i) the sentence that the F1 check on a source-local base is
only as strong as the annotation (mS1/mS4), and (ii) the follow-up item «validate source-local atom annotations
against the function's `declare` types» beside the owed apparatus item in the handoff §3. If the [USER] holds that a
forged-wire answer of any kind must not land, this becomes FIX-FIRST; I do not think doctrine requires that here,
because the trust boundary is the one Stage C set, not one this lane opened.

### Anything new

- mT1: the audited binary's `map` target plan was a full «decodes and answers» (79) on an empty map, not merely
  late-stuck — the round fixed it either way; its record should not understate the class.
- R1 (above).
- Nothing else: no new lane move, no set changed outside the born rows, no refusal text lost a cause.

### Not re-checked

The full `ci --diff` on the fix tip (the lane's tail read: EXIT=1 in 931 s on exactly the 5a pair; every standalone
gate re-run here); K = 80 draws (mine: 20 per born row, 12 per probe); the whole-corpus choice trace (the 260-row
outside check + the 54 rows' sets stand in); `check-evidence-size` and `check-spec-anchors` on the fix tip's own tree
(EXIT=0 in `reverify-gate-exits.txt`; also EXIT=0 on this branch after this commit).
