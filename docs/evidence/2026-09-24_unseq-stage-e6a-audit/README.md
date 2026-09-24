# Evidence — the adversarial audit of Stage E6a (`core/unseq-stage-e6a-0924` @ `1f0dee94` over `3fb4a0d1`), 2026-09-24

[AGENT] auditor; the note is `docs/2026-09-24_unseq-stage-e6a-audit.md`. Small tables and gate tails only (caps
256 KiB / 4 MiB — `scripts/check-evidence-size`); bulk (wires, raw gc lines, the census TSVs) stays under the audit
worktree's `.tmp/` and is reproduced by the producers named per file. Toolchain: go1.26.5 (the pin); Lean per
`lean-toolchain`; the shared build box (concurrent lanes — no timing number here is load-controlled). Binaries: the
candidate's frontend built from the audit worktree (`be137623…`; path-dependent — the lane's `aead74a3…` is the same
source), main's from `git archive 3fb4a0d1` (`85e055b4…`); golean: the candidate's `bb607430…` (this worktree's
`.lake`, rsynced at identical sources and re-built as a no-op under `scripts/capped`), main's the primary's
`63e9c661…` (read-only). No edit to the candidate or main; no merge; no push.

| file | what | producer |
|---|---|---|
| `probes/p1-main.go` … `p7-main.go`, `probes/p3-sub.go` | the probe programs: p1 the trigger's scope (general vs event-mediated shapes), p2 `len`/`cap` over map / channel, p3 the unit boundary (+ a case-local `sub` package), p4 every declaration form a graph atom may name (R1) + the F8 / mS4 shapes, p5 the twin's born-graph shapes and the status-diverse body, p6 / p7 the class F1 names (a late-failing operand left of an inline built-in whose operand panics) | hand-written |
| `run-probe.sh` | lowers a probe dir with both frontends, prints the census decision per sweep, the canonical-tape run and the enumerated set (`coverage-observations --max-width 8 --max-sites 8 --cap 64 --work-cap 200000 --expect-status ok,panic`) on the matching golean | — |
| `probe-results.txt` | every probe × both sides, one line each: graphs in the function, the enumerator's summary, the members, the last legacy reason | `run-probe.sh` logs, summarized |
| `gc-draws.txt` | gc's 20 draws per subject (5 runs × GOMAXPROCS 1/8 × default / `-N -l`), tabulated `subject → {output: count}` — the 75 probe subjects and the corpus subjects of the born / moved / migrated rows (`assertLeftMinInline`, `recvOrderDeadRecvLenOperand 7`, `strIndexStatusDiverse`, the 10 `len-vs-call-order` / e13 migrations) | the lane's `gc-draws-args.sh` (copied); p3 by hand under a GOPATH layout for `sub` |
| `mutants.py`, `mutants.txt` | 27 one-edit decoder mutants over the p4 wire and two tracked fixtures through the real CLI (`native-json-run`): R1 forgeries per declaration form, the mS4 target-plan forgery, the shadow residual, the mS1 forgery THROUGH A TYPE-SWITCH BINDER (decodes and answers — F2), the F8 edges, the positive controls, a forged target id | `mutants.py` (+ two appended runs) |
| `census-repro.txt` | the whole-sweep census with both frontends (the lane's `run.sh` / `summarize.py` / `diff.py`, copied): 108 264 sweeps, 180 → 266 admitted, 93 newly admitted (= the lane's list by name), 0 lost, by former reason | `.tmp/census/all.sh` |
| `probe-census-repro.txt` | the legacy probe-emission census with both frontends: 186 → 175 (58 → 47 corpus; the twin 128 → 128, 0 → 3 graphs), the two changed packages, the emitters by function and probed head before / after | `probes.sh` + `probe-sites.py` (the lane's, copied) |
| `twin-emit.sh`, `twin-born-graphs.txt` | the twin re-assembled as `scripts/check-frontend-pins` does and emitted with both frontends (candidate = pin `1c4e7038…`, main = `e1a87725…`); the three born graphs decoded from the pin (occurrence kinds — no failing occurrence in two, F3); the census lines of the twin sweeps and of the main-unit replicas (p5) on both frontends | — |
| `customer-inventory-e6a-counts.tsv`, `customer-inventory-e6a-export.txt` | the logic team's 14 fixture units + the 8 generated `f2` variants lowered with the candidate's frontend: 22/22 export, 0 `unseq`, 0 probes (= the inventory at `3fb4a0d1`) | the inventory's `count-stmts.py` / `gen-f2-variants.py` (from `records/customer-fixture-inventory-0924`) |
| `ci-slow-tip.tail.txt` | the full gate at the candidate tip in this worktree (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` under the box-wide lock), ANSI stripped, the summary block | `.tmp/audit/gate/run-slow.sh` |
| `latest-vs-main-baseline.txt` | the gate's `artifacts/coverage/latest.tsv` against main `3fb4a0d1`'s `baselines/native-full.tsv`: every row whose result or stage differs | python over the two TSVs |
