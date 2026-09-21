# Evidence — Stage E of the evaluation-order model v2.1: family migration (lane `core/unseq-stage-e-0921`, 2026-09-21)

[AGENT] worker. Design record `docs/2026-09-21_unseq-stage-e-design.md` (per family), handoff
`docs/2026-09-21_unseq-stage-e-handoff.md`. Small tables and gate tails only (caps 256 KiB / 4 MiB —
`scripts/check-evidence-size`); bulk runs are reproduced by the commands named per file. Every gate is
`scripts/capped scripts/ci …` under the box-wide lock; captured exits; a killed or timed-out command
decided nothing.

## E1 — package-level variables as occurrences (closes BUG-113)

| file | what | producer |
|---|---|---|
| `census-e1.txt` | the whole-sweep census BEFORE (main `74d084ad`'s frontend, built from `git archive`) and AFTER (the E1 frontend) over the 1356 corpus packages + the raft twin assembly: 107 943 sweeps; admitted 136 → 146 (+10 in 4 packages, 0 lost); the twin 10 203 sweeps, 0 admitted on both; the per-package table, the newly admitted sweeps by former reason and form, the still-legacy package-level TYPE reasons | `.tmp/census/run.sh <frontend> <out.tsv>` (`nativefrontend --unseq-census --dir <pkg>` over every `Corpus/coverage/exec/**/cases.tsv` directory and the twin assembled as `scripts/check-frontend-pins` assembles it), `summarize.py`, `diff.py` |
| `census-newly-admitted-e1.tsv` | the 10 sweeps that enter the grammar at E1 (package, unit, file:line, function, form, counts, the reason the BEFORE census printed) | `diff.py` |
| `diff-one-e1.txt` | the focused differential on all 13 affected rows (the 3 BUG-113 rows, the 4 born `evalorder/unseq-globals` rows, `spec-examples-decl/select-forms` ×3, `panic-recover/repanic-collapse/index-two-faults`, `init/stdlib-initializer-dependent`) on the E1 frontend + the E1 binary: the two flips, the four births, everything else unchanged (the init row's pre-existing frontend-export red) | `scripts/diff-one <ids…>` (the per-row `wide=` / `enumerated=` details are in `artifacts/coverage/latest.tsv` of that run and quoted in the design note §E1) |
| `ci-slow-e1.tail.txt` | the full gate's tail (the paragraph below) | `scripts/capped scripts/ci --slow`, ANSI stripped: the step / verdict / drift lines + the 5a-class row's detail |
| `gc-draws-e1.txt` | gc's draws for `evalorder/unseq-globals` (all four subjects) and `evalorder/legacy-logical-vs-call` (all three): 5 runs × GOMAXPROCS 1 / 8 × default / `-gcflags=all='-N -l'` = 20 per package, every draw inside the derived sets (2 · 11 · `wit 1` 2 · `wit 1` 2; `logical false 0` · `logical false 0` · `logical 0 true`) | `GOMAXPROCS=… go run [-gcflags=all='-N -l'] Corpus/coverage/exec/<pkg>/main.go`, go1.26.5 |

Reference sets: `docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py` E1a/E1c/E1b (regenerated
`outcomes.txt`, `RESULT: PASS`); over the wire: `Tests/UnseqWire.lean` (65 ok; 20 mutants refused by
name — `mut-deref-hidden` new), `scripts/check-unseq-wire` PASS (63 fixtures byte-identical to the
generator; 20 mutants through the CLI), `scripts/check-wire-boundary` PASS (11 byte-level + 11
unseq-node controls — the global-read positive control and the hidden-read refusal new). Frontend:
`go test ./tools/nativefrontend/...` ok (E1 witnesses admitted with their counts; `globalTypeOut`
refused by name), `go test ./tools/lowerdiag/...` ok. Explicit-target Lean builds under the lock rule:
`GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.NativeToIR golean UnseqWireTests` EXIT=0 (99
jobs).

**The full gate: `scripts/capped scripts/ci --slow` at the E1 tree** (main `14006270` + the E1 edits, the
worktree dirty with exactly them; the box-wide lock acquired 02:10:26Z after merge train r45's `ci --diff`
released it, released 02:28:29Z): **EXIT=1 in 1083 s, K=80 (`membership_draws 80`); 3709 rows 3464 PASS /
245 FAIL in the run = the pinned 3465 / 244 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items** — `certificate provenance` («STALE certification: changed dependency
build/files/GoLean/NativeToIR.lean» — the `deref` head) and the `baseline diff` DRIFT block's ONE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the same item — the
row's detail in the run: «certification: STALE certification: changed dependency build/files/GoLean/NativeToIR.lean\nFresh certification: unchanged set; seconds=169.697; candidate=/home/dev/projects/golean/.claude/worktrees/unseq-stage-e/artifacts/coverage/membership/imported-goose/channel/google-search/certification-candida»; the train installs the fresh candidate at step 5a, not a re-pin here).
Every other step ok: core build, escape-hatch scans, core totality audit (45 modules, 51 required theorems,
classical trio only — its compiled poison controls fire as designed), engine isolation, check-mem-callsites,
admission proofs, declaration + wire boundaries (11 + 11 unseq-node controls), method identity, unseq
scheduler (Stage B), unseq wire (Stage C + E1: 20 mutants), frontend pins (twin wire = pinned bytes),
frontend / lowerdiag / harness unit tests, eval tests 274 ok, differential run, lane-validation fixtures incl.
the go half, negative corpus 394 matched, FloatVectors + inittask-std byte-exact, re-pin guard 0
PASS→non-PASS, executed library coverage. `ci-slow-e1.tail.txt` is the tail (step lines, the provenance
verdict, the drift block, the row's detail). The seven rows of this family reproduce their pinned states in
the run: `or-vs-call` / `and-vs-call` PASS strict, `call-first-control` PASS, `unseq-globals/read-vs-call` and
`compound-vs-call` PASS/membership, `read-vs-unrelated-call` and `plain-target-call` PASS strict.
