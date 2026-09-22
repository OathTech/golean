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
