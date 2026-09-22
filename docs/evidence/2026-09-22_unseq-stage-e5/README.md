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
