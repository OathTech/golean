# Evidence — adversarial audit of Stage E5 (`core/unseq-stage-e5-0922` @ `403cde75` over main `dc5de785`), 2026-09-22

[AGENT] auditor; the note is `docs/2026-09-22_unseq-stage-e5-audit.md`. Small tables, probe sources and gate tails only
(caps 256 KiB / 4 MiB); every command is named per file. Toolchain: tip frontend built from this tree, main's frontend
from `git archive dc5de785`; tip binary `.lake/build/bin/golean` (`2159163d…`), main's binary the primary's
(`73734062…`); go1.26.5.

| file | what | producer |
|---|---|---|
| `probes-{addr,multi,builtins,maplit,strings}.go` | the auditor's probe packages (E5d/E5b/E5a/E5c/E5e) | hand-written |
| `probe.sh` | per subject: census verdict, canonical-tape run, enumerated set | `nativefrontend --unseq-census`, `golean native-json-run`, `golean coverage-observations` |
| `probe-results.txt` | every probe's census line, canonical answer and set (tip); the main-side comparisons for the E5b map-target and spec-example shapes | `probe.sh` |
| `mutants-e5.py`, `mutants-e5b.py`, `mutant-results.txt` | 44 one-edit decoder mutants through the real CLI (a mutant that RUNS is also enumerated) | the scripts |
| `gc.sh`, `gc-probe-draws.txt`, `gc-row-draws.txt` | gc draws: probes (2–3 runs × GOMAXPROCS 1/8 × default / `-N -l`), the 46 corpus subjects (5 runs each = 20 draws) | `gc.sh` |
| `row-sets.txt`, `row-sets-multivalue.txt` | the born / moved / affected corpus rows' enumerated sets (tip) | `probe.sh`; `coverage-observations` at width 8–64 for the multi-value rows |
| `diff-one-rows.tsv` | `scripts/diff-one` on the 51 rows (`artifacts/coverage/latest.tsv` rows) | `scripts/diff-one` |
| `baseline-delta.txt` | main vs tip `baselines/native-full.tsv`: born / lost / changed / PASS→non-PASS | python over `git show` |
| `census-tip-summary.txt`, `probes-tip.tsv` | the whole-sweep census and the probe-emission census with the tip frontend (packages with probes + refusals) | the lane's `.tmp/census/{run.sh,summarize.py,probes.sh}` copied |
| `outside-check.py`, `outside-check.log`, `outside-check-rows.tsv` | 260 baseline-PASS strict rows outside DIFFER ∪ born, both frontends × both binaries | the script |
| `trace-logical-short-circuit.txt` | `golean choice-trace` per row on both sides for the one admitted sweep absent from the DIFFER lists | `golean choice-trace --batch … --dump` |
| `spec-rows-main-frontend-binary.txt` | the spec example's two rows on main's frontend + binary | `probe.sh` |
| `gate-exits.txt`, `gate-tails.txt` | captured exits and tails of every gate run here | `.tmp/gates.sh` under the box-wide lock |
