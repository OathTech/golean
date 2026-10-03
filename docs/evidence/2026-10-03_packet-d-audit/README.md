# Evidence — pre-merge audit of window packet D at `556ab207` ([AGENT auditor], 2026-10-03)

Note: `docs/2026-10-03_packet-d-audit.md`. Branch `review/packet-d-equations-1003` (worktree
`.claude/worktrees/audit-packet-d`, fresh `.lake`, `scripts/setup-deps`), every build/gate through
`scripts/capped`, full gates under the box-wide lock.

| file | what |
|---|---|
| `ci-diff-summary.txt` | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the tip: the differential line (3821 = 3583/238), the one drift row, the reconciler's C9 line, the step summary — red on exactly the 5a pair, `semantic equations` ok, EXIT 1, 1613 s |
| `check-equations.txt` | `scripts/check-equations` standalone under the lock: EXIT 0 (229 pinned, 7 facts, no-unfold guard, both self-tests) |
| `check-core-audit.txt` | `scripts/check-core-audit` standalone under the lock: EXIT 0 (54 modules, 470 required theorems, 5 poison controls) |
| `concrete-checks.txt` | the concrete-instance checks: 78 `example`s accepted + 128 `#eval`s (53 compiled-code agreements) across all three groups, the setup equation and the projections; the refusal/terminal texts the instances produced |
| `EqCheck.lean.txt` | the check harness itself (scratch source, reproducible: `scripts/capped lake env lean` against a built tree) |
| `pins-bypass-stress.txt` | three mutated BridgeSet rows → 3 errors; the no-unfold GUARD regex probed (8 escapes, 1 false positive) and six client-style facts that prove by unfolding `stepFn` while passing it; the symbolic-shape stress (fail fast) and the `simp only [stepFn_eqns, premises]` discharge limitation with its working variants; BridgeSet's lane elaboration time |

Sizes: every file under the 256 KiB cap; the directory under the 4 MiB cap; nothing is a copy of a
tracked file (`scripts/check-evidence-size`).

## Re-verification at `7a976448` (2026-10-03; note §«Re-verification»)

| file | what |
|---|---|
| `reverify-gates.txt` | `ci --diff` at the rebased tree (red on exactly the 5a pair, 3821 = 3583/238, 944 s; the procedural dirty-tree note), `check-equations` EXIT 0 (10 self-tests), `check-core-audit` EXIT 0 (536 required) |
| `reverify-inhabitation.txt` | FACT 3's inhabitation evaluated: the eight premises at the concrete values, the boxing law's instance, the 20-step run to the abort with the store at the stop = the written store |
| `reverify-bypass-mutants.txt` | seven one-change mutants of the client against the closure no-unfold check: C1/C3/C5/C6/C9 (alias, projection, `id`, `let`, `match`-auxiliary) REFUSED; A (imported API `rfl` theorem) and B (imported test-support module, source included) PASS — finding R1 |
| `reverify-statements-and-table.txt` | BridgeSet rows 1–436/1–501 byte-identical to their predecessors, row 502, numbering; the `GoLean` diff file list and new definitions; the F4 table's flag lists and UNCHANGED-cell derivations re-run |
