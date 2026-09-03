# Noodler probe record — semantic-edge hunting across ~30 language areas (2026-09-03)

[AGENT] Lane `noodler` ([USER]-directed 2026-09-03; the brief reached
this lane by [AGENT]-coordinator relay, not firsthand — Mike, verbatim
as relayed: «send off an agent briefed to be 'the noodler' - i.e to
write new test cases which expose semantic edges we haven't already
discovered. The noodler's job is to persistently poke and prod, find
places that our semantics either (1) doesn't match what gc does, or
(2) where our semantics does something the go semantics implies it
shouldn't do. Broad brief in a worktree, making sure to rule out of
scope all the seams we already know about. The noodler's test cases
themselves should be rolled into our suite, whether or not they found
new issues»). Consuming documents: `docs/2026-09-03_noodler-report.md`
(the lane report; cites this dir), `docs/BUGS.md` BUG-085 / BUG-086
(cite the two probe sub-dirs), the corpus packages under
`Corpus/coverage/exec/noodler/` (the rolled-in cases; every row is a
differential test, PASS rows are guards).

## Toolchain, tree and host (`docs/evidence/README.md` rules 3–5)

- Oracle: `go version` → `go version go1.26.5 linux/amd64`
  (`/usr/local/go/bin/go`), equal to `baselines/go-oracle-pin`
  (`go1.26.5`). Machine tier: Lean toolchain per `lean-toolchain`
  (`leanprover/lean4:v4.32.2`); golean binary `.lake/build/bin/golean`
  built by `scripts/capped lake build` in the noodler worktree (the
  build cache was seeded by copying the main checkout's `.lake` at the
  same commit b5abacc1, then verified by a capped `lake build`).
- Tree (rule 4): branch `noodler` off main @ b5abacc1. The gc probes are
  oracle-only and do not depend on repo state. The machine-side results
  behind every corpus row were produced by `scripts/coverage run` on the
  worktree with the probe packages committed in batches (commits
  9911bcd2 … eeb78dfd; records commit = the commit adding this README,
  `git log -1 --format=%H -- docs/evidence/2026-09-03_noodler/README.md`).
  The full gate (`scripts/capped scripts/ci --diff`) ran at the records
  tip; its tails are in `transcripts/gate-tail-1-prepin.txt` (the drift run
  at eeb78dfd) and `transcripts/gate-tail-2-records.txt` (RESULT: PASS at
  the records commit 67629805). No GoLean/, tools/,
  scripts/ file was modified on this lane.
- Host (rule 5): linux/amd64, shared build box with several agents'
  lanes running concurrently. The only timing-sensitive numbers here are
  the budget cliffs in `scratch-notes.md` (single measurements under
  load, order-of-magnitude only; the corpus rows were sized to pass
  well inside the runner's 30 s Lean timeout).

## Reproduction (rule 2; copy-paste from the repo root)

```sh
# F1 — gc's two panic texts for a value-receiver method on a nil *T (BUG-085)
GO111MODULE=off go run docs/evidence/2026-09-03_noodler/probes/gc-wrapper-text/main.go
GO111MODULE=off go run -gcflags='-N -l' docs/evidence/2026-09-03_noodler/probes/gc-wrapper-text/main.go
#   -> transcripts/gc-wrapper-text.txt (both flag sets, byte-identical)

# F2 — FormatInt-without-FormatUint shim injection refusal (BUG-086)
for v in a b c d e both; do
  d=$(mktemp -d artifacts/fi-$v.XXXX)
  cp docs/evidence/2026-09-03_noodler/probes/formatint-bisect/fi-$v.go.txt $d/main.go
  printf 'fi-%s: ' $v; GO111MODULE=off go run ./tools/nativefrontend --dir $d --out $d/wire.json 2>&1 | head -1; echo
done
#   -> transcripts/formatint-bisect.txt (a..e refused; 'both' exports)

# The corpus rows (machine vs gc for every probe)
scripts/coverage run --prefix noodler/
# The full gate at the records tip
scripts/capped scripts/ci --diff
```

## What was measured (rule 6) and the conclusion

~560 new differential rows in 90 packages under `Corpus/coverage/exec/
noodler/` across: conversions, integer arithmetic, name resolution
(predeclared-identifier shadowing), bounds-check panic texts,
interfaces, function-local types, closures / Go 1.22 loop variables,
defer/recover, maps, evaluation order (spec-ordered AND spec-unordered
axes), select/switch, generics (incl. Go 1.24 generic aliases),
struct/array/pointer equality, methods on non-struct types, literals
and constant arithmetic, builtins (min/max/clear/copy/append), forced
goroutine programs, init order and init-time panics, strings and the
modeled stdlib subset, membership-lane envelope rows, a frontier hunt
over the frontend's own refusal strings, floats, assertion-text matrix,
append aliasing, range semantics, sync misuse fatals, go-statement
evaluation timing, type-switch clause selection, integer-kind index
operands, resource budgets.

Conclusion the report relies on: the executable core matched gc on
every deterministic program that lowered — zero wrong VALUES, zero
wrong panic KINDS, zero termination mismatches, and the membership
rows' admitted sets were exactly the spec-bounded sets (no upper-bound
violation found). The two new fidelity findings are both at the
edges of the trusted surface: F1 a panic-TEXT divergence where gc's
own text is optimizer-dependent (BUG-085), F2 a whole-program
spurious refusal inside the frozen stdlib-shim allowlist (BUG-086).
The frontier hunt found refusal families on legal Go that no ledger
row names (report §4). All other refusals hit were already-recorded
seams (`scratch-notes.md`, "known seams re-hit").

## Incident (rule 7, [AGENT], honest reporting)

At ~02:40 on 2026-09-03 this lane stopped its own background gate with
a machine-wide `pgrep -f 'scripts/c[i] --diff'` pattern kill. That
pattern matched every `scripts/ci --diff` on the shared box, and
`../atomics-w1/artifacts/coverage/latest.meta.tsv` was written at
02:40 — the atomics-w1 lane's gate was very likely killed by this
lane. Reported to the coordinator in the lane report; the atomics-w1
lane must be told to re-run its gate. Lesson recorded: kill only PIDs
you launched (the retry used `nohup … & echo $! > ci.pid`).

## Files

- `probes/gc-wrapper-text/main.go` — the F1 gc probe (7 call shapes).
- `transcripts/gc-wrapper-text.txt` — its output at default flags and `-N -l`.
- `probes/formatint-bisect/fi-{a..e,both}.go.txt` — the F2 bisect programs.
- `transcripts/formatint-bisect.txt` — the native frontend's verdict per program.
- `transcripts/gate-tail-1-prepin.txt` — the pre-pin `scripts/capped scripts/ci --diff` tail (drift = the 562 new ids).
- `transcripts/gate-tail-2-records.txt` — the final `scripts/capped scripts/ci --diff` tail (RESULT: PASS).
- `per-area-table.tsv` — package → rows / PASS / FAIL / born-FAIL ids (generated from the gate's `artifacts/coverage/latest-full.tsv`; producer named in its header).
- `scratch-notes.md` — the running triage notes: known seams re-hit (with the record found for each), findings, could-not-probe items, budget cliff measurements.
