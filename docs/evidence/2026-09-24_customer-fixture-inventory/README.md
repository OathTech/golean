# Lowering the logic team's fourteen fixtures and their generated variants — the `unseq` census (2026-09-24)

[AGENT] records worker, lane `records/customer-fixture-inventory-0924`. Charter row 0 of
`docs/2026-09-23_batched-window-charter.md`, procedure as revised by the Codex review's F3
(`docs/2026-09-23_batched-window-charter-review.md`). Consuming doc:
`docs/2026-09-24_customer-fixture-inventory.md` (which cites this dir).

## Conclusion

Twenty-two units — the customer's fourteen `examples/fixtures/*` directories at their commit, plus the
eight `f2` proof variants their `tools/check_f2_proofs.py` generates by textual substitution — were
lowered by the production frontend at our `main`. All twenty-two exported successfully (exit 0, empty
stderr). The recursive statement census over the retained wires finds **0 `"stmt":"unseq"` nodes, 0
graph-body occurrences of any kind, and 0 legacy `"stmt":"unseq-probe"` statements in every unit**; the
`--unseq-census` sweep agrees (786 of 786 main-unit sweep rows decided `legacy`). The proposal's **[inf]**
hypothesis — «None of your fourteen fixtures enters a graph» (`docs/2026-09-23_proposal-to-logic-team.md`
§1 item 3) — is confirmed as measured, at these pins, for these units. It says nothing about the units
after E6's lowering changes.

## Pins

- Customer source: `/home/dev/projects/golean-logic` @ `b2c37c1492a16de317de40b2c487f478c8b9c6a1`
  (2026-09-22), clean tree; read-only to this lane (sources copied out, nothing run there).
- Our tree: `main` @ `3fb4a0d18debdc3ffd8e364e723326f475a7369f`, clean (the lane's own worktree).
  Frontend subtree pin `git rev-parse HEAD:tools/nativefrontend` = `9fe2042c4c9ac806e6bab470e1c6a4a472d19985`.
- Frontend binary sha256 `e61605f5fe2ed7f2a2fb3eb0db9cfd436a234f899915d5ab902f6347aa7c33cf`
  (`GO111MODULE=off GOCACHE=artifacts/go-build-cache go build -o .tmp/inventory/nativefrontend ./tools/nativefrontend`).
- Toolchain: `go version go1.26.5 linux/amd64` — the pin in `baselines/go-oracle-pin` (`go1.26.5`).
- Host: linux/amd64; a shared box (a train and a core lane ran concurrently). No timing number is recorded
  here, so concurrent load does not bear on the counts.

## Reproduction (from the repo root)

```sh
CUST=<path to the golean-logic checkout at b2c37c14>          # read-only
mkdir -p .tmp/inventory/{src,wires,logs,census}
for d in "$CUST"/examples/fixtures/*/; do n=$(basename "$d");
  mkdir -p .tmp/inventory/src/"$n"; cp "$d"*.go .tmp/inventory/src/"$n"/; done
python3 docs/evidence/2026-09-24_customer-fixture-inventory/gen-f2-variants.py "$CUST" .tmp/inventory/src
export GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache"
go build -o .tmp/inventory/nativefrontend ./tools/nativefrontend
for d in .tmp/inventory/src/*/; do n=$(basename "$d");
  ./.tmp/inventory/nativefrontend --dir "$d" --out .tmp/inventory/wires/"$n".json \
     2> .tmp/inventory/logs/"$n".stderr; echo "$n $?";
  ./.tmp/inventory/nativefrontend --dir "$d" --unseq-census > .tmp/inventory/census/"$n".tsv; done
python3 docs/evidence/2026-09-24_customer-fixture-inventory/count-stmts.py .tmp/inventory/wires/*.json
# positive control (our corpus, known emitters):
for c in Corpus/coverage/exec/builtins/len-vs-call-order Corpus/coverage/exec/builtins/e13-sibling-panic-order; do
  ./.tmp/inventory/nativefrontend --dir "$c" --out .tmp/inventory/control/"$(basename $c)".json; done
python3 docs/evidence/2026-09-24_customer-fixture-inventory/count-stmts.py .tmp/inventory/control/*.json
```

Wires stay under `.tmp/` (bulk); their sha256 are in `wire-sha256.tsv` and the wire carries no absolute
path, so the digests reproduce from any checkout at the pins above.

## Files

| File | What |
|---|---|
| `count-stmts.py` | the recursive walker: every JSON object with a string `"stmt"` key, whole document |
| `gen-f2-variants.py` | [AGENT] reproduction of the customer's generated `f2` proof variants (parses their table with `ast`, runs none of their code) |
| `counts.tsv` | the census for the 22 units: totals, `unseq`, legacy probes, per-body-kind, statement histogram |
| `counts-control.tsv` | the same walker on two of OUR corpus packages that DO emit — the instrument's positive control |
| `census-admitted.tsv` | `--unseq-census` admitted-column tally per unit (additional evidence; a MAIN-UNIT sweep census, not the wire) |
| `export-stderr.txt` | exit status + verbatim stderr per unit (all exit 0, all empty) |
| `wire-sha256.tsv` | digest and size of each retained scratch wire |

## Why the instrument is trusted here (the control)

An all-zero count is exactly the reading a broken counter gives. `counts-control.tsv` runs the same binary
and the same walker over `Corpus/coverage/exec/builtins/len-vs-call-order` and
`.../e13-sibling-panic-order` and reports 4 and 50 `unseq` nodes and 15 and 11 legacy probes — the numbers
the E5d census `docs/evidence/2026-09-22_unseq-stage-e5/probes-e5d.txt` records for those two packages, and
the `--unseq-census` `unseq` row counts for the same two packages (4, 50) agree with the wire.

`scripts/lower-diagnose` was NOT used: nothing failed to export, and the review's F3 restricts it to
explaining failures (it deletes its probe wire and so cannot certify absence).
