# B7 context/store audit — evidence (2026-09-17)

[AGENT] auditor, branch `review/b7-context-store-0917` at the candidate tip
`d0e65182` (base main `5955e55f`). Consuming document:
`docs/2026-09-17_b7-context-store-audit.md`. Records only: small receipts of
the checks the report cites; every command was run from this worktree, every
lake/lean command through `scripts/capped`, exit codes captured. Nothing here
is a claim about Go.

| file | what | produced by |
|---|---|---|
| `statement-summary.tsv` | per changed module: declarations before/after, deleted, added, changed statements, unchanged | `.tmp/extract_stmts.py` (a Lean-declaration statement extractor: keyword … `:=`/`where`, comments stripped) over `git show 5955e55f:<f>` vs the tip |
| `statement-deltas.txt` | for EVERY changed declaration statement, the token-level delta (`-` removed tokens ‖ `+` added tokens) | `.tmp/stmt_delta.py` (difflib over the extractor's output) |
| `key-statements.txt` | the full before/after statement text of the coherence theorems and the handoff §4 items | the same extractor, named list |
| `literal-changes.txt` | every string literal (comments stripped, full files) whose multiset changed | `.tmp/lits.py` |
| `wire-compare.tsv` | 39 corpus rows lowered by the frontend, `native-json-run` on both binaries, stdout+stderr+exit compared | `.tmp/wire_compare.sh` |
| `choice-trace-subset.txt` | `scripts/choice-trace-corpus --dump --jobs 6` on 263 ids (1 in 14 manifest rows) with each binary; sorted dumps `cmp`'d; the id list | as named |
| `probe-tags-receipt.txt` | the `fun_cases stepFn ctx s c ch` probe re-run (162 arms) diffed against the lane's tracked before/after files; the 10 sampled `stepFn_sound` cases | `scripts/capped lake env lean .tmp/probe_s2.lean` (= the tracked `probe_s2.lean.txt`) |
| `unused-store-check.txt` | the 55 helpers that lost their `ExecState` binder: old-body heap-access grep through that binder | `.tmp/unused_store.py` |
| `core-audit-tail.txt` | `scripts/capped bash scripts/check-core-audit` tail, EXIT=0 | as named |
| `census.txt` | the handoff/README census numbers recomputed from git | greps listed inline |
| `perf.tsv` | probe/twin/enumeration timings on both binaries | `.tmp/perf.sh` + the dedup rows |

Binaries: main `155df5c3d7a52816…` (copied read-only from the primary's
`.lake/build/bin/golean`, the certified build at `5955e55f`), candidate
`1ea8f2ac622f3ba5…` (`scripts/capped lake build` at `d0e65182` over a plain
copy of the lane's `.lake`, EXIT=0, no-op). Frontend `9b52821a9de3831e…`
(`go build` of the untouched `tools/nativefrontend` at the tip).
