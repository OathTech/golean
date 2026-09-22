# Evidence — Stage E5 of the evaluation-order model v2.1: the residue families (lane `core/unseq-stage-e5-0922`, 2026-09-22)

[AGENT] worker. Design record `docs/2026-09-22_unseq-stage-e5-design.md` (§0 the measured residue and order, one
section per family), handoff `docs/2026-09-22_unseq-stage-e5-handoff.md`. Small tables and gate tails only (caps
256 KiB / 4 MiB — `scripts/check-evidence-size`); bulk runs are reproduced by the commands named per file. Every
gate is `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` under the box-wide lock; captured exits; a killed or
timed-out command decided nothing.

## The baseline measurements (before any family)

| file | what | producer |
|---|---|---|
| `census-before.txt` | the whole-sweep census with main `dc5de785`'s frontend (== `d76721bd`'s): 108 102 corpus sweeps, 131 admitted; legacy sweeps by unit (24 421 main / 93 753 non-main); the main-unit residue by FIRST refusal reason | `.tmp/census/run.sh <frontend> <out.tsv>` (Stage E's census tooling) + `summarize.py`; the two awk breakdowns are in the file's header |
| `probes-before.txt` | the LEGACY PROBE EMISSION census (E6's entry metric): `unseq-probe` / `unseq` nodes per emitted package wire — 70 probes in 21 corpus packages, 128 in the raft twin (0 graphs there); 25 packages refuse export (pre-existing frontend-export reds); the emitters by function and probed head | `.tmp/census/probes.sh <frontend> <out.tsv>` (emit every `Corpus/coverage/exec/**/cases.tsv` directory + the twin assembled as `scripts/check-frontend-pins` assembles it; grep the statement tags) + `probe-sites.py` (walk `funcs` + `methods`) |

## E5a — the reading-(a) built-ins `min`/`max`/`copy`/`append`

| file | what | producer |
|---|---|---|
| `census-e5a.txt` | BEFORE (main's frontend) vs AFTER (the E5a frontend): admitted 131 → 137 (+6 in 2 packages, 0 lost — by former reason `builtin copy` 3, `builtin append` 2, `builtin min` 1); the twin 10 203 / 0; the main-unit residue AFTER | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e5a.tsv` | the 6 sweeps that enter (package, unit, file:line, function, form, counts, the former reason) | `diff.py` |
| `probes-e5a.txt` | the probe emission census AFTER: 63 corpus probes in 20 packages (e13 17 → 12, copy-min 2 → 0), the twin 128 unchanged; the corpus emitters by function | `probes.sh`, `probe-sites.py` |
| `diff-one-e5a.txt` | `scripts/diff-one` on the 12 affected rows, twice: run 1 (11 PASS; `append-spread-str-vs-call` REFUTED by name — the appendSpill capacity pick of an append on a full base, site bound 30; `copy-stmt-control` admitted with one unobservable pick) and run 2 after the fix (12 PASS) | `scripts/diff-one <ids…>`; the rows quoted from `artifacts/coverage/latest.tsv` |
| `gc-draws-e5a.txt` | gc's draws for the six born subjects (20 each: 5 runs × GOMAXPROCS 1/8 × default / `-N -l`), the two fixed rows re-drawn; every draw inside its derived set, the call-first member on every membership row (15, 18, 9, 16; the controls 6 and 78) | `.tmp/e5/gc-draws.sh <pkg> <out> <subjects…>`, go1.26.5 |
| `choice-trace-main-vs-e5a.txt` | the whole-corpus choice trace, main vs E5a (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |
| `ci-diff-e5a.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |

Reference sets: `docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py` E5a1–E5a7 (regenerated `outcomes.txt`,
`RESULT: PASS`); over the wire: `Tests/UnseqWire.lean` (106 ok; 38 mutants refused by name — `mut-wide-kind`,
`mut-wide-nonatom`, `mut-wide-binds`, `mut-wide-cell-type`, `mut-min-nonatom` new), `scripts/check-unseq-wire` PASS,
`scripts/check-wire-boundary` PASS (11 byte-level + 34 unseq-node controls — the wide-copy positive control answers 9 on
the canonical tape), `scripts/check-unseq-scheduler` PASS (the hand-built `wide` graph E5a2 exact and route-α certified
{6, 15}; 35 required theorems, classical trio only), `scripts/check-mem-callsites` PASS (70), `scripts/check-core-audit`
PASS. Frontend: `go test ./tools/nativefrontend/ ./tools/lowerdiag/` ok. Explicit-target Lean builds under the lock rule:
`GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore.MachineSound GoLean.GoCore.UnseqSound GoLean.GoCore.StateWf
…` EXIT=0 (99 s); `… GoLean.NativeToIR golean UnseqWireTests UnseqSchedulerTests` EXIT=0.

**The full gate at the E5a tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the E5a tree (main `d76721bd` + the
E5a edits, the worktree dirty with exactly them; the box-wide lock 01:34:42–01:50:53Z): **EXIT=1 in 971 s, K=32; 3738 rows
3502 PASS / 236 FAIL in the run = the pinned 3503 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items** — `certificate provenance` («STALE certification: changed dependency
build/files/GoLean/GoCore/AdmissionIndices.lean» — the core inputs the `wide` kind changed) and the `baseline diff` DRIFT
block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the row's
detail the same STALE certification; under `--diff` no fresh re-certification runs — the train's step 5a installs the
candidate from its `--slow` run). Every other step ok: core build, escape-hatch scans, core totality audit, engine
isolation, check-mem-callsites (70), admission proofs, declaration + wire boundaries (11 + 34 unseq-node controls), method
identity, unseq scheduler, unseq wire (38 mutants), frontend pins (twin wire = pinned bytes), frontend / lowerdiag / harness
unit tests, eval tests, differential run, lane-validation fixtures incl. the go half, negative corpus 394 matched,
FloatVectors + inittask-std byte-exact, re-pin guard 0 PASS→non-PASS, executed library coverage; the reconciler's two
report-only findings are the standing pair (C9 = the provenance item above; C13 the doc-version note). The six born rows
reproduce their pinned states in the run (4 membership, 2 strict); the five e13 rows and `copy-min` unchanged.
`ci-diff-e5a.tail.txt` is the tail.

**Whole-corpus choice trace, main vs E5a** (`choice-trace-main-vs-e5a.txt`; main `d76721bd`'s binary `73734062…` vs the
E5a commit `732da84c`'s `4d5b3c13…`, each from its own export tree, `scripts/choice-trace-corpus --dump --jobs 5`, the two
standing exclusions; Stage D's `trace-compare.py`): **3702 ids, 3690 byte-identical, 6 DIFFER, 6 only on the E5a side** —
the 6 DIFFER ids are EXACTLY the rows of the six sweeps E5a admits (`builtins/e13-sibling-panic-order/{assert-left-append,
assert-left-copy,tgt-assert-vs-min-call,tgt-assert-vs-copy-call,tgt-assert-vs-append}`, `slices/copy-min`), the 6 ONLY_B the
born `evalorder/unseq-builtins` rows. Site census: `unseqNext` 1482 → 1609, `unseqPanic` 204 → 174 (the five e13 rows'
probes retired into graphs); every other site identical. The same 41 standing finding lines and 34 export refusals on both
sides (the tracer exits 1 on both for the summarizer's standing findings).

## E5b — multi-target assignments, blank targets, the comma-ok forms

| file | what | producer |
|---|---|---|
| `census-e5b.txt` | the E5a frontend vs the E5b frontend: admitted 137 → 154 (+12 from the widening in 10 packages — by former reason `multi-target or tuple assignment` 11, `blank target` 1; by form multi-call 6, tuple-assign 4, comma-ok 1, blank-assign 1 — and +5 the E5a package's sweeps born after its census; 0 lost); the twin 10 203 / 0 | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e5b.tsv` | the 12 sweeps that enter (the `multi-assign` family, the spec's own `eval-order-calls` example, a `recv-edge` comma-ok, two noodler rows) | `diff.py` |
| `probes-e5b.txt` | the probe emission census AFTER E5b: 60 corpus probes in 19 packages, the twin 128 unchanged | `probes.sh`, `probe-sites.py` |
| `diff-one-e5b.txt` | `scripts/diff-one` on the 65 affected rows, THREE runs: run 1 (the first E5b cut) — the spec example's two rows FAIL/differential (the lowering's E1 chain put the target's `f()` after `k()`: a WRONG ANSWER caught red-first), three born widths refuted by name, four strict rows varying across streams; run 2 (the fix) — 61 PASS, the four varying rows; run 3 (the lane moves; two widths corrected) — 4 PASS/membership | `scripts/diff-one <ids…>`; rows quoted from `artifacts/coverage/latest.tsv` |
| `gc-draws-e5b.txt` | gc's draws for the seven born subjects and the four moved rows (20 each), every one inside its set — the call-first member on every membership row | `.tmp/e5/gc-draws.sh`, go1.26.5 |
| `ci-diff-e5b.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |
| `choice-trace-main-vs-e5b.txt` | the whole-corpus choice trace, main vs E5b (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |

Reference sets: `enumerate.py` E5b1–E5b4 (`outcomes.txt` PASS); over the wire: `Tests/UnseqWire.lean` 114 ok / 41 mutants
(`mut-wide-two-binds`, `mut-recv-ok-type`, `mut-wide-assert-nonatom` new; `mut-recv-two-binds` re-pointed at the flag cell's
type — two binders are the admitted comma-ok form); `check-unseq-wire` PASS, `check-wire-boundary` PASS (11 + 38 — the
tuple positive control answers 15 on the canonical tape), `check-unseq-scheduler` PASS, `check-mem-callsites` PASS (70),
`check-frontend-pins` PASS (the twin byte-identical), `check-core-audit` PASS; `go test ./tools/nativefrontend/ ./tools/lowerdiag/`
ok; `scripts/capped lake build …` EXIT=0 (161 s).

**The full gate at the E5b tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the E5b tree, TWO runs under the
box-wide lock (`ci-diff-e5b.tail.txt`). RUN 1 (02:21–02:36Z, EXIT=1 in 936 s) was red on the 5a pair AND on `unseq wire`:
`build.py --check` found `native-e5btuple.json` / `native-e5brecv2.json` DRIFTED — the two native fixtures had been generated
before the lowering's E1-order fix (the cell numbering changed when target operands began lowering first), a stale test input
the gate caught; regenerated with the fixed frontend (the standalone wire gates PASS: 41 mutants; 11 + 38 controls). RUN 2
(02:38–02:51Z): **EXIT=1 in 765 s, K=32; 3745 rows 3509 PASS / 236 FAIL in the run = the pinned 3510 / 235 with the one
5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items** — `certificate provenance` («STALE certification: changed
dependency build/files/GoLean/GoCore/AdmissionIndices.lean») and the `baseline diff` DRIFT block's ONE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. Every other step ok (re-pin guard 0
PASS→non-PASS; the reconciler's standing two report-only findings). The seven born rows and the four moved rows reproduce
their pinned states in the run; the spec's own example PASS strict.

**Whole-corpus choice trace, main vs E5b** (`choice-trace-main-vs-e5b.txt`; main `d76721bd`'s binary `73734062…` vs the E5b commit `1a0ff398`'s binary `44a9c8e6…`, each side from its own export tree — `git archive` + `deps`, its own frontend — by `scripts/choice-trace-corpus --dump --jobs 5` and Stage D's `trace-compare.py`): 3709 ids — **3679 byte-identical, 17 DIFFER, 13 only on the E5b side**. The 17 DIFFER ids are exactly the rows of the sweeps E5a and E5b admit (`census-newly-admitted-e5{a,b}.tsv`): E5a's six (the five `builtins/e13-sibling-panic-order` built-in rows, `slices/copy-min`) and E5b's eleven DIFFERING rows (E5b admits TWELVE sweeps; `noodler/evalorder/logicalShortCircuit`'s graph never picks at bound ≥ 2, so its row is byte-identical — the audit fix round's F5b) — `channels/recv-edge/dep-index-target`, BUG-052's `multi-assign/call-write-back-order/{deref-target,slice-header-base}` and `call-write-back-order-value/deref-target`, `multi-assign/call-write-back/panic-identity`, `multi-assign/lhs-index-eval-order`, `multi-assign/target-eval-before-call`, `noodler/latitude/rhs-list-index-call-index`, `returns/multi-result-assign-order`, the spec's own example `spec-examples-stmt/eval-order-calls/{verbatim,traced-recv}`; the 13 ONLY_B ids are the born `evalorder/unseq-builtins` (6) and `evalorder/unseq-multi` (7) rows. Site census: `unseqNext` 1482 → 1903, `unseqPanic` 204 → 174 (E5a's retirements; E5b's three retired probe emissions recorded no consumption on the traced streams); every other site identical. Both sides: 34 export refusals (identical sets — the standing frontend-export reds), the exhausted-stream lists identical (strict 100, confluent 94), the two standing exclusions.

## E5c — map literals

| file | what | producer |
|---|---|---|
| `census-e5c.txt` | the E5b frontend vs the E5c frontend: admitted 154 → 165 (+3 pre-existing sweeps ENTER — the noodler and e13 map-literal rows the diff counts as «newly admitted», and `evalorder/unseq-conv-alloc/map-lit-control`, filed under «rows only in AFTER» because a comment edit shifted its line (the trace's E5c DIFFER list has it; the audit fix round's F5a corrected the former «+2»); +8 the born packages' sweeps; 0 lost — four «lost/new» pairs are those line shifts); the twin 10 203 / 0 | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e5c.tsv` | the 2 sweeps that enter | `diff.py` |
| `probes-e5c.txt` | the probe emission census AFTER E5c: 59 corpus probes in 18 packages (the noodler row's retired), the twin 128 unchanged | `probes.sh`, `probe-sites.py` |
| `diff-one-e5c.txt` | `scripts/diff-one` on the 90 affected rows: run 1 (89 PASS; `map-lit-payload-vs-call` FAIL/differential — the strict control's pin of gc's literal-first panic vs the canonical call-first tape, the F6 shape) and run 2 (the row moved to membership, PASS) | `scripts/diff-one <ids…>` |
| `gc-draws-e5c.txt` | gc's draws (20 each) for the three born subjects (6, 6, 6 — the literal at its lexical position), the two moved rows (50; the panic alone) and the `map-lit-control` control (6) | `.tmp/e5/gc-draws.sh`, go1.26.5 |
| `ci-diff-e5c.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |
| `choice-trace-main-vs-e5c.txt` | the whole-corpus choice trace, main vs E5c (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |

Reference sets: `enumerate.py` E5c1 {6, 15}, E5c2 {5, 50} (PASS); over the wire: `Tests/UnseqWire.lean` 118 ok / 43 mutants
(`mut-maplit-dup-key`, `mut-maplit-nonatom` new; E4's `mut-alloc-kind` re-pointed at `array-lit`); `check-unseq-wire` PASS,
`check-wire-boundary` PASS (11 + 41 — the map-literal positive control answers 15), `check-unseq-scheduler` PASS,
`check-mem-callsites` PASS (70), `check-frontend-pins` PASS, `check-core-audit` PASS; `go test ./tools/nativefrontend/
./tools/lowerdiag/` ok; `scripts/capped lake build …` EXIT=0 (139 s).

**The full gate at the E5c tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the E5c tree (the commit's exact content; the box-wide lock 03:03:15–03:18:24Z): **EXIT=1 in 909 s (32 cores, LEAN_NUM_THREADS=6 under the 48G cap); `differential coverage summary: cases=3748 pass=3512 fail=236` = the pinned 3513 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items** — `certificate provenance` («STALE certification: changed dependency build/files/GoLean/GoCore/AdmissionIndices.lean») and the `baseline diff` DRIFT block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. Every other step ok (unseq scheduler; unseq wire — 43 mutants, `build.py --check` no drift; frontend pins; the frontend and harness unit tests; eval tests 274; the lane-validation fixtures; the negative corpus 394 matched; re-pin guard 0 PASS→non-PASS; the reconciler's standing two report-only findings). The three born rows and the two moved rows reproduce their pinned states in the run (`ci-diff-e5c.tail.txt`).

**Whole-corpus choice trace, main vs E5c** (`choice-trace-main-vs-e5c.txt`; main `d76721bd`'s binary `73734062…` vs the E5c commit `6bf3d780`'s binary `c8613c32…`, each side from its own export tree): 3712 ids — **3676 byte-identical, 20 DIFFER, 16 only on the E5c side**. The 20 DIFFER ids are exactly the rows of the sweeps E5a (6), E5b (11) and E5c (3: `builtins/e13-sibling-panic-order/map-lit-payload-vs-call`, `noodler/latitude/map-literal-key-vs-call`, `evalorder/unseq-conv-alloc/map-lit-control` — a graph now, its one outcome unchanged) admit; the 16 ONLY_B ids are the born `unseq-builtins` (6), `unseq-multi` (7) and `unseq-maplit` (3) rows. Site census: `unseqNext` 1482 → 1958, `unseqPanic` 204 → 174 (unchanged from E5a); every other site identical. Both sides: 34 export refusals (identical sets), the exhausted-stream lists identical (strict 100, confluent 94), the two standing exclusions.

## E5e — strings

| file | what | producer |
|---|---|---|
| `census-e5e.txt` | the E5c frontend vs the E5e frontend: admitted 165 → 168 (+1 from the widening — the e13 row `bytesConvPayloadVsCall`, former reason «slice expression on a non-slice base (string)»; +2 the born package's membership sweeps; 0 lost); the twin 10 203 / 0 | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e5e.tsv` | the 1 sweep that enters | `diff.py` |
| `probes-e5e.txt` | the probe emission census AFTER E5e: 58 corpus probes in 18 packages (the e13 row's retired), the twin 128 unchanged | `probes.sh`, `probe-sites.py` |
| `diff-one-e5e.txt` | `scripts/diff-one` on the 68 affected rows (all 65 e13 rows + the born package): run 1 (67 PASS; the first `str-index-vs-call` — a status-diverse set — REFUSED BY NAME by the membership lane) and run 2 (the four redesigned / born rows, 4 PASS) | `scripts/diff-one <ids…>` |
| `gc-draws-e5e.txt` | gc's draws (20 each) for the four born subjects: 103 (the byte read after the call), `wit 5` · panic, 102 (the string slice BEFORE the call), 7 | `.tmp/e5/gc-draws.sh`, go1.26.5 |
| `ci-diff-e5e.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |
| `choice-trace-main-vs-e5e.txt` | the whole-corpus choice trace, main vs E5e (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |

Reference sets: `enumerate.py` E5e1 {102, 103}, E5e2 {102, 103}, E5e3 {7} (the forced singleton — the reference REFUTED the
first `len(s[i:]) + m()` draft), E5e4 {panic · (), panic · (wit 5)} (PASS); over the wire: `Tests/UnseqWire.lean` 120 ok / 43
mutants (no decoder change — no new mutant; the hand-built `e5estr` + native are the positive controls); `check-unseq-wire` PASS,
`check-wire-boundary` PASS (11 + 42 — the string wire answers 103 on the canonical tape); `go test ./tools/nativefrontend/
./tools/lowerdiag/` ok; `scripts/capped lake build UnseqWireTests golean` EXIT=0 under the lock (the core and the decoder unchanged).

**The full gate at the E5e tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the E5e tree (the commit's exact content; the box-wide lock 03:42:18–03:54:59Z): **EXIT=1 in 761 s (32 cores, LEAN_NUM_THREADS=6 under the 48G cap); `differential coverage summary: cases=3752 pass=3516 fail=236` = the pinned 3517 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items** — `certificate provenance` («STALE certification: changed dependency build/files/GoLean/GoCore/AdmissionIndices.lean», E5a's core change) and the `baseline diff` DRIFT block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. Every other step ok (unseq scheduler; unseq wire — 43 mutants, the string wire and its native exact; frontend pins; the frontend and harness unit tests; eval tests 274; the lane-validation fixtures; the negative corpus 394 matched; re-pin guard 0 PASS→non-PASS; the reconciler's standing two report-only findings). The four born rows reproduce their pinned states in the run; the golean binary is byte-identical to E5c's (`c8613c32…` — no decoder or core change) (`ci-diff-e5e.tail.txt`).

**Whole-corpus choice trace, main vs E5e** (`choice-trace-main-vs-e5e.txt`; main `d76721bd`'s binary `73734062…` vs the E5e commit `64b3757c`'s binary `c8613c32…` (= E5c's), each side from its own export tree): 3716 ids — **3675 byte-identical, 21 DIFFER, 20 only on the E5e side**. The 21 DIFFER ids are exactly the rows of the sweeps E5a (6), E5b (11), E5c (3) and E5e (1: `builtins/e13-sibling-panic-order/bytes-conv-payload-vs-call`) admit; the 20 ONLY_B ids are the born `unseq-builtins` (6), `unseq-multi` (7), `unseq-maplit` (3) and `unseq-strings` (4) rows. Site census: `unseqNext` 1482 → 1994, `unseqPanic` 204 → 168 (E5e retires one more probe consumption); every other site identical. Both sides: 34 export refusals (identical sets), the exhausted-stream lists identical (strict 100, confluent 94), the two standing exclusions.

## E5d — the address of a variable as an operand

| file | what | producer |
|---|---|---|
| `census-e5d.txt` | the E5e frontend vs the E5d frontend: admitted 168 → 177 (+3 from the widening — three `&x`-argument sweeps in channels/make-edge and the two multi-assign target-before-rhs packages; +5 the born package; +1 the E5e row split after its census; 0 lost); the twin 10 203 / 0 | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e5d.tsv` | the sweeps that enter | `diff.py` |
| `probes-e5d.txt` | the probe emission census AFTER E5d: 58 corpus probes in 17 packages (unchanged — the entering sweeps carried none), the twin 128 unchanged | `probes.sh`, `probe-sites.py` |
| `diff-one-e5d.txt` | `scripts/diff-one` on the 17 affected rows: run 1 (14 PASS / 3 FAIL): the five born rows PASS (4 membership, enumerated=2 each; the strict control); THREE strict rows whose sweeps enter the graph — `multi-assign/deref-target-before-rhs`, `multi-assign/selector-target-before-rhs`, `channels/make-edge/ordinary-receive-eval-order` — FAIL/nondet (the machine's adversarial streams exhibit the second member: the address-taken variable's read before the call that writes through `&x`); run 2: the three moved to membership with the reason (sets {828, 822, 181, 188}, {727, 722, 171, 177}, {170, 171, 182}; gc's call-first member inside each, 20/20), PASS | `scripts/diff-one <ids…>` |
| `gc-draws-e5d.txt` | gc's draws (20 each) for the five born subjects: call-first on every row (8, 15, 78, 8; the control 2) | `.tmp/e5/gc-draws.sh`, go1.26.5 |
| `ci-diff-e5d.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |
| `choice-trace-main-vs-e5d.txt` | the whole-corpus choice trace, main vs E5d (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |

Reference sets: `enumerate.py` E5d1 {2, 8}, E5d2 {6, 15}, E5d3 {72, 78} (PASS); over the wire: `Tests/UnseqWire.lean` 124 ok / 45
mutants (`mut-addr-payload-binder` — `ref` of a binder cell as a payload, audit F2's class; `mut-addr-head` — `ref` as a head stays
refused); `check-unseq-wire` PASS, `check-wire-boundary` PASS (11 + 46 — the address-argument wire answers 8, the address-payload
wire 15 on the canonical tape); `check-unseq-scheduler` PASS, `check-mem-callsites` PASS, `check-frontend-pins` PASS,
`check-core-audit` PASS; `go test ./tools/nativefrontend/ ./tools/lowerdiag/` ok; `scripts/capped lake build …` EXIT=0 under the
lock (the decoder changed — one payload arm; the core unchanged).

**The full gate at the E5d tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the E5d tree (the commit's exact content; the box-wide lock 04:12:42–04:27:45Z): **EXIT=1 in 902 s (32 cores, LEAN_NUM_THREADS=6 under the 48G cap); `differential coverage summary: cases=3757 pass=3521 fail=236` = the pinned 3522 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items** — `certificate provenance` («STALE certification: changed dependency build/files/GoLean/GoCore/AdmissionIndices.lean», E5a's core change) and the `baseline diff` DRIFT block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. Every other step ok (unseq scheduler; unseq wire — 45 mutants, the two address wires and their natives exact; frontend pins; the frontend and harness unit tests; eval tests 274; the lane-validation fixtures; the negative corpus 394 matched; re-pin guard 0 PASS→non-PASS; the reconciler's standing two report-only findings). The five born rows and the three moved rows reproduce their pinned states in the run; the golean binary `2159163d…` (the decoder's payload arm) (`ci-diff-e5d.tail.txt`).

**Whole-corpus choice trace, main vs E5d** (`choice-trace-main-vs-e5d.txt`; main `d76721bd`'s binary `73734062…` vs the E5d commit's binary `2159163d…`, each side from its own export tree): 3721 ids — **3672 byte-identical, 24 DIFFER, 25 only on the E5d side**. The 24 DIFFER ids are exactly the rows of the sweeps E5a (6), E5b (11), E5c (3), E5e (1) and E5d (3 — the three strict pins that became membership rows) admit; the 25 ONLY_B ids are the born rows of the five packages. Site census: `unseqNext` 1482 → 2101, `unseqPanic` 204 → 168; every other site identical. Both sides: 34 export refusals (identical sets), the exhausted-stream lists identical (strict 100, confluent 94), the two standing exclusions.

**Commit hashes.** The lane was REBASED onto main `dc5de785` (main's records-only close commit) at its end; the trace evidence files and the gate tails cite the PRE-REBASE hashes — E5a `732da84c` → `eba20f2d`, E5b `1a0ff398` → `f70903dc`, E5c `6bf3d780` → `f5903528`, E5e `64b3757c` → `6f6244f0`, E5d `50fdf05e` → `5570a190` (identical runtime content; the handoff §1 cites the post-rebase hashes).

## The gate at the rebased tip

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the rebased tip (E5d's content on main `dc5de785`; the box-wide lock 2026-09-22T04:38:01Z–2026-09-22T04:50:53Z): EXIT=1 in 772 s; `cases=3757 pass=3521 fail=236` = the pin 3522 / 235 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for `GoLean/GoCore/AdmissionIndices.lean`; the one `imported-goose/channel/google-search` drift line); every other step ok (`ci-diff-park.tail.txt`). The rebase onto main's records-only close (`dc5de785`) brought in one appended paragraph in `docs/evidence/2026-09-21_unseq-stage-e/README.md` (never touched by this lane); the runtime content is E5d's. | `ci-diff-park.tail.txt` |

## The audit fix round (2026-09-22)

The adversarial audit `docs/2026-09-22_unseq-stage-e5-audit.md` (candidate `403cde75`; FIX-FIRST — one minor decoder FAIL-OPEN, four
records corrections, no wrong answer; its evidence `docs/evidence/2026-09-22_unseq-stage-e5-audit/`) and the round's dispositions
([AGENT] coordinator, disclosed at the merge ask) are executed in the design's «The audit fix round» and the handoff §5. Producers:
the replayable scripts under the worktree's `.tmp/fix/` (handoff §6).

| file | what | producer |
|---|---|---|
| `f1-litmus.txt` | audit F1 BEFORE → AFTER: the audited tip's binary `2159163d…` vs the round's `63e9c661…` on the auditor's own mutant wires (mW12 / mW17: exit 0, value 0 → refused by name «keyType/valueType … disagree with the map base's declared type»; mE2 and the `map` target plan: stuck LATE → refused at decode; mW20 the same) and on this round's four mutants; the positive controls (`e5blookup` + native, `e2map`, `e5cmaplit` + natives) answer identically on both binaries | `.tmp/fix/f1-litmus.sh` (the audit worktree's `.tmp/mut`, read-only) |
| `gc-draws-fix.txt` | gc's draws (20 each: 5 runs × GOMAXPROCS 1/8 × default / `-N -l`, go1.26.5) for the three born subjects: `mapTargetKeyVsWriter` 79 (call-first), `commaOkMapTargetVsDelete` 0 (call-first), `mapTargetNilLegacyRefusal` `wit 1` · «assignment to entry in nil map» — every draw inside its set | `.tmp/e5/gc-draws.sh` |
| `diff-one-fix.txt` | `scripts/diff-one` on the 10 `evalorder/unseq-multi` rows at the fix-round tree: `map-target-key-vs-writer` PASS/membership enumerated=2 ({709, 79}), `comma-ok-map-target-vs-delete` PASS/membership enumerated=2 ({11, 0}), `map-target-nil-legacy-refusal` FAIL/frontend-export BY DESIGN («frontend-quarantined: map element as assignment target outside a single assignment»); the seven E5b rows unchanged | `scripts/diff-one` |
| `census-fix.txt` | the E5d frontend vs the fix-round frontend: admitted 177 → 179 (exactly the two born graph rows' sweeps; 0 lost; the F6 texts relabel the «unary operator &» first-reason class by operand shape — 147 = 97 element + 36 field + 8 indirection + 5 variable-in-a-computing-position + 1 qualified — moving no sweep); probe emissions 58 corpus + 128 twin unchanged (`unseqs` 175 → 177) | `.tmp/census/run.sh`, `summarize.py`, `diff.py`, `probes.sh` |
| `gate-exits-fix.txt` | the standalone gates' captured exits before the full gate | the scripts named per line |
| `ci-diff-fix.tail.txt` | the full gate's tail (the paragraph below) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`, ANSI stripped |
| `choice-trace-fix.txt` | the whole-corpus choice trace, the audited tip `403cde75` vs the fix round's runtime commit (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` on the round's export tree + `trace-compare.py` against the E5d trace (= `403cde75`'s content) |

Reference sets: `enumerate.py` E5b5 `xs[f()], ok = m[1]` (f deleting m[1]) {0, 11} added (`outcomes.txt` PASS); over the wire:
`Tests/UnseqWire.lean` 132 ok lines — 83 exact-set checks + 49 mutants (`mut-wide-lookup-keytype-vs-base`, `mut-wide-lookup-valuetype-vs-base`,
`mut-mapget-keytype-vs-base`, `mut-map-target-keytype-vs-base` new; the hand-built `e5blookup` + native the positive control the
`wide map-lookup` arm had lacked), `check-unseq-wire` PASS (49), `check-wire-boundary` PASS (11 + 49 — the lookup wire answers 0 on
the canonical tape; two of the mutants refuse by name through the CLI), `check-frontend-pins` PASS (the twin byte-identical
`e1a87725…`), `check-mem-callsites` PASS (70), `check-core-audit` PASS, `check-unseq-scheduler` PASS; `go test
./tools/nativefrontend/ ./tools/lowerdiag/` ok (the three F6 texts unit-tested); `scripts/capped lake build GoLean.NativeToIR golean
UnseqWireTests` EXIT=0 (122 s under the lock — the core rebuilt for the F2 docstring). Baseline 3757 = 3522 / 235 → 3760 = 3524 /
236 (two born PASS/membership, one born FAIL by design — BUG-115; nothing else moved; the header carries the reason).

**The full gate at the fix-round tree:** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the fix-round tree (`403cde75` + the round's edits, the worktree dirty with exactly them; the box-wide lock 2026-09-22T06:05:42Z–2026-09-22T06:22:36Z): **EXIT=1 in 931 s (the box-wide lock 2026-09-22T06:05:42Z–2026-09-22T06:22:36Z); `differential coverage summary: cases=3760 pass=3523 fail=237` = the re-pinned 3760 = 3524 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items — `certificate provenance` («STALE certification: changed dependency build/files/GoLean/GoCore/AdmissionIndices.lean» — the core/decoder inputs vs main's certificates) and the `baseline diff` DRIFT block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`; every other step ok (the re-pin guard 0 PASS→non-PASS; the reconciler's standing two report-only findings); the three born rows reproduce their pinned states in the run** (`ci-diff-fix.tail.txt`).

**Whole-corpus choice trace, the audited tip vs the fix round** (`choice-trace-fix.txt`; `403cde75`'s binary `2159163d…` (the E5d trace) vs the runtime commit `263866da`'s `63e9c661…`, each side from its own export tree): 3724 ids — **3721 byte-identical, 0 DIFFER, 3 only on the fix-round side** (the three born rows); site census deltas `unseqNext` 2101 → 2147, every other site identical; 34 export refusals (identical sets), the exhausted-stream lists identical, the two standing exclusions. The decoder's F1 check refuses only forged wires; the F2 docstring and the F6/F7 texts change no execution.
