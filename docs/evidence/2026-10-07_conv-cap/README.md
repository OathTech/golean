# Evidence — R3 / b6, the `[]byte(s)` / `[]rune(s)` capacity envelope (lane `lane/conv-cap-1007`, 2026-10-07)

[AGENT] build worker. Design `docs/2026-10-07_conv-cap-design.md` (D1–D8 ratified [USER] Mike 2026-10-07 «yeah agree,
build now», relayed); the measured envelope itself is `docs/evidence/2026-10-07_conv-cap-design/`. Oracle go1.26.5
(`baselines/go-oracle-pin`). Bulk scratch (`.tmp/`: the wire exports, the per-consumption dumps, the coverage artifacts)
was pruned at the lane's close; everything here regenerates from the commands below.

| File | What |
|---|---|
| `red-first-latest.tsv` | the differential of the 26 born rows `strings/conv-cap/*` at the fixtures-only commit (`3a0d22e7`, main's semantics via the primary's pre-change binary): the 4 literal controls PASS, all 22 latitude rows RED — the membership lane's singleton guard («enumerated observation set is a singleton (1 member)»: main's machine has no choice site there) |
| `red-first-witness.txt` | per row (the 6 rune rows and 4 byte rows): the pre-change machine's enumerated observation set (`observations.txt`) beside gc's draws (`draws.txt`, plain and `-race` alternating) — the observed-∉-modeled witness of BUG-118: modeled `{5}` vs gc 32 (`runes-var-nomut-5`), `{5}` vs 6 (`runes-var-esc-5`), `{33}` vs 36, `{100}` vs 104. The 4 rune rows at n ∈ {33, 100} were born as membership rows and moved to the STRICT lane at the lane tip (their envelope is a singleton, which the membership lane refuses by design); as strict rows they are plain differential mismatches on `main` (33 vs 36, 100 vs 104) — the witness above is the same program, the same observation |
| `choice-trace-compare.txt` | THE D4 CERTIFICATE: `golean choice-trace --batch` over the whole executable corpus (3882 rows exported, 34 frontend refusals; the two standing exclusions `goroutines/send-then-spin` and `strings/trimspace-repeat/repeat-bound-refused` — every corpus trace since the A-series excludes them: the former spins to the fuel cap on every stream, the latter is the tracer's native stack-overflow abort on a refused huge-repeat row, identical on both binaries) under the six standard streams, BEFORE (the primary's pre-change binary, main `5c842d1f`) vs AFTER (the lane tip), compared per (row, stream): default stream — 3750 identical, 6 observation changes (EXACTLY the 6 rune rows: the BUG-118 fix; no other row's default-tape observation moved — D4), 123 rows consume more entries with the observation unchanged (the new `convCap` consults); the three adversarial and two random streams — 19–24 observation differences (the 22 born rows and the re-laned `strings/byte-conversion-cap`, whose before-binary has no consult, plus TWO pre-existing rows, the membership rows `builtins/e13-sibling-panic-order/bytes-conv-left-len-hoist` (its `unseqNext` picks) and `stdlib-source/builder-cap/grow-after-write` (its `appendSpill` picks): their picks shift position behind a new `convCap` consult — a positional shift the membership lane does not read; corrected from «ONE» at train r74, the audit's item 4), 106–115 consumption-only differences. The 42 rows that gain a `convCap` consult at bound ≥ 2 under the default stream are listed at the end |
| `choice-trace-summary-diff.txt` | `scripts/choice-trace-summarize` before vs after: `convCap` enters the per-site census (8415 consumptions over all streams); «rows whose observation VARIES across the traced streams» 1 → 2 — the one new row is `strings/byte-conversion-cap` (the strict lane's depth guard reported it at the lane tip, `stage=nondet`: its variable operand `s` has the envelope {5, 8, 32}; re-laned strict → membership, `members=3`, default-tape observation unchanged, PASS on both lanes); the strict-lane «invisible order-sensitivity» exposure 43 → 58 rows, all data-latitude sites |
| `option-i-row-metadata.tsv` | option (i) as applied: the 17 rows' metadata before/after with each value's reason (every value the smallest that passes) |
| `timing.tsv` | the ruled condition's measurement: per-row harness walls of the 17 rows + 3 controls (before = the pre-change binary in a throwaway worktree, after = the lane tip, both at load ~10; a first before-run at load 50–80 kept for honesty), the 26 new rows as one run, and the gate: `ci --slow` 1484 s at the tip vs r72's 1487 s (−0.2%) / r71's 1301 s (+14.1%) |
| `ci-slow-run2.tail.txt` | `scripts/ci --slow` at the rebased tip `47c3972e` with option (i): RESULT FAIL on exactly the re-pin trio (bug-index: BUG-118's rows not yet in the baseline; certificate provenance STALE with an UNCHANGED SET; the baseline DRIFT = the 26 new ids + the re-lane + the 5a echo) — the 20 flips of run 1 GONE; the baseline then re-pinned and the certified record refreshed from this run's candidate |
| `ci-diff-run4.tail.txt` | the GREEN gate at the final tip `3e3c0cd7`: `scripts/ci --diff` RESULT PASS, 3916/3916 no regression, re-pin guard ok, certificate provenance ok (1061 s; run 3 at the un-repaired re-pin was refused by the baseline tool on the alternation row's `# reason:` block, repaired in `3e3c0cd7`) |
| `ci-slow-run1.tail.txt` | `scripts/ci --slow` at the lane tip `0fdcbd29` (box lock held; 1557 s): RESULT FAIL on exactly three steps — bug-index cross-check (BUG-118's six Cases rows are not in the baseline until a re-pin), certificate provenance (STALE; the fresh re-certification of `imported-goose/channel/google-search` is an UNCHANGED SET — the standing 5a pair, a provenance refresh, not a finding), and the baseline diff DRIFT: 26 new rows (all PASS), `strings/byte-conversion-cap` PASS/strict → PASS/membership (the re-lane), and 20 PASS→FAIL flips — THE DESIGN-GATE FINDING below. Every other step ok (core build warning-free, core totality audit, equations, pool spec, frontend pins — the raft twin wire byte-identical —, eval tests 298 ok, negative lane 394 no regression) |

Commands (repo root): `scripts/coverage run --prefix strings/conv-cap` (the rows); `scripts/choice-trace-corpus --jobs 4
--out <dir> --dump [--golean <binary>] --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused`
(a run without the two exclusions, as this lane's first attempt, stalls on the spinner and aborts on the refused row — chunk 3 and
the chunk-1 remainder were then traced separately by id; the union is the full corpus minus the two); the comparison script is
reproduced in `choice-trace-compare.txt`'s header line; `python3 scripts/choice-trace-summarize --manifest <dir>/manifest.tsv
<dir>/results-*.tsv`.

## The design-gate finding (STOP — D4 contradicted; not adjudicated here)

D4 asserted «every row on `main` keep their observations; no row flips» and counted the sites that gain a consult
over `Corpus/` and `raftsubject/` SOURCE files (31 `[]byte(` + 11 `[]rune(`). The full differential at the lane tip
shows 20 PASS→FAIL flips. NONE is an observation change — the default-tape observation of every pre-existing row is
identical (the certificate above: the only default-stream changes are the six rune rows, BUG-118's fix) — and none is
a wrong answer; all three classes are consequences of the NEW CONSULT POSITION on rows the count missed, chiefly the
SOURCE-THROUGH stdlib code those rows execute (`deps/go/src`, lowered by the frontend): `strings.TrimSpace`'s hot loop
`for lo, c := range []byte(s)` (strings.go:1093 — gc's zero-copy TEMP conversion, `OSTR2BYTESTMP`: cap = len, never
allocating; the machine now draws a bound-3 `convCap` at EVERY call) and `bytes.NewBufferString`'s `[]byte(s)`
(buffer.go:499).

1. 13 STRICT rows now FAIL at `stage=nondet` — the strict lane's DEPTH GUARD, not a variance: «N wide pick(s) served
   after stream [9,8,…] was exhausted at consumption 10 — the 3-stream invariance check did not cover this row; route to
   confluent, or declare depth» — `stdlib-source/builder-overlay/{grow-contract (w=11), join-large (w=200),
   repeat-doubling-loop}`, `stdlib-source/bytes-buffer/grow-contract (w=10)`, `stdlib-source/slices-sortfunc/{others,
   sort-stable-func, sortfunc-large (w=41), sortfunc-reversed-input, sortfunc-strings-by-len, sortfunc-ties-projected,
   sortfunc-ties-realized}`, `stdlib-source/strconv-parseuint/{bitsize-saturation, error-quoting, error-texts (w=17)}`.
   Their per-consumption profile under the default stream is dozens to hundreds of `convCap@3` draws (join-large: 199)
   from TrimSpace's range loop, whose capacity is UNOBSERVABLE (a range over a conversion exposes index and byte only):
   the extra members cost consults, never observations.
2. 4 MEMBERSHIP rows now FAIL at the enumerator's fail-closed guards: `builtins/e13-sibling-panic-order/
   {bytes-conv-left-len-hoist, bytes-conv-value-vs-mutating-call}` and `evalorder/unseq-conv-alloc/conv-read-vs-call`
   («site bound 3 exceeds the case's width 2 — the width assertion is REFUTED»: their fixtures convert non-literal
   strings, `[]byte(s)[7]`, `[]byte(s[i:j])[0]`, `[]byte(s)[0]`, observing bytes, not caps — the declared `width=2` is
   below the new bound), and `stdlib-source/builder-cap/grow-after-write` («work cap exceeded after 199884 step(s) …
   subtrees still unexplored»: one `convCap@3` beside its two `appendSpill` consults (bounds 31, 28) triples the tree
   past the default `work` budget).
3. `imported-goose/channel/google-search` (the CERTIFIED row): the 5a pair only — «Fresh certification: unchanged set»
   (no `convCap` consult in its profile; the claim and observations are identical; a provenance refresh).

Resolution options, for the [USER]/coordinator (a named design gate — this lane does not self-adjudicate): (i) row
metadata only, the semantics as ratified — declare depth / re-lane the 13 strict rows, `width=3` on the three e13/unseq
rows, a larger `work` on `builder-cap/grow-after-write`, then the baseline re-pin (no flip would remain; no BUGS Cases
line is owed: none is a wrong answer); (ii) narrow the consult for the unobservable range-over-conversion shape (gc's
`OSTR2BYTESTMP` is a SYNTACTIC regime the design's four regimes subsume as the zero-copy member — a bound-1 consult
there would need the frontend/decoder to mark the range operand, i.e. a wire or lowering change D3 excluded, or a
machine-side recognition of the range desugar) — a design change; (iii) both. Until ruled: the baseline is NOT
re-pinned, the 17 pre-existing rows are untouched, and the lane tip's gate stands RED on the three steps named above.

**Ruling on the finding** ([USER] Mike 2026-10-07 «Agree», relayed by the [AGENT] coordinator): option (i), conditional on the measured gate cost ≤ ~10% vs main's latest close — applied (`option-i-row-metadata.tsv`), measured (`timing.tsv`: −0.2% vs r72), re-pinned (`baselines/native-full.tsv` header, 2026-10-07 lane/conv-cap-1007). Every observation of every pre-existing row is identical before and after; the 17 rows' PASS→FAIL→PASS is a metadata story only.
