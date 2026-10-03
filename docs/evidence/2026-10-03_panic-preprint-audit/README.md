# Pre-merge audit probes and measurements — lane `core/panic-preprint-1003`, the preprint phase (2026-10-03)

[AGENT auditor], branch `review/panic-preprint-1003`. Consuming doc: `docs/2026-10-03_panic-preprint-audit.md` (which cites
this directory). Candidate = `517f9883` (the lane tip, one commit over `main` @ `aeab81c5`); main = `git archive aeab81c5`
built fresh under `.tmp/main-aeab81c5/` with `deps/` symlinked to the audit worktree's. Trees clean at the recorded SHAs (the
probe fixtures below were UNTRACKED scratch under `Corpus/coverage/exec/panic-recover/audit-preprint{,-stdlib,-2}/`, present
only while the probe runs ran; moved out before the gate). Toolchain: `go version go1.26.5 linux/amd64` (= the pin,
`baselines/go-oracle-pin`); Lean per `lean-toolchain`; the machine binary `.lake/build/bin/golean` built by
`GOLEAN_MEM_MAX=48G scripts/capped lake build golean gocore-eval-tests` on each side. Host: linux/amd64, a shared box carrying
other projects' builds (load average 2.8–9 during the timing runs — see `elab-ab.tsv`'s load column).

## Conclusion

68 probes beyond the lane's 21 rows (51 in set 1, 5 stdlib, 12 method-set corners in set 2): the candidate matches gc exactly
on every strict row, admits gc's draw inside every enumerated set (whose other members are gc-realizable box-identity
assignments — e.g. three identical entries → the 4 observations in `membership-sets.txt`), and refuses by name everywhere
else (BUG-099 runtime-error fatals, unpinned pointer/basic fatal payloads, the address-form struct payloads, `fmt`/`runtime`
quarantine). `main` refuses every row. One set-2 row (`two-goroutines-panic-error`) is undecided on BOTH sides: gc's stderr
carries two concurrent panic reports and the harness refuses to classify it (not a machine answer). Elaboration A/B: no module over 1.5×; `PrefixFacts` 1.48× on both runs. The gate at the tip: red on exactly the 5a pair.

## Files

- `probes-set1-main.go`, `probes-set1-cases.tsv` — set 1 (51 rows; one per attack shape, comments name the gc behaviour each
  targets). `probes-stdlib-main.go`, `probes-stdlib-cases.tsv` — the `errors`/`fmt`/`runtime` rows (5).
  `probes-set2-main.go`, `probes-set2-cases.tsv` — method-set corner cases (12).
- `probe-results.tsv` — set 1 + stdlib: id, candidate result/stage, main result/stage, candidate detail (truncated).
  `probe-results-set2.tsv` — set 2, same columns.
- `gc-first-lines.tsv`, `gc-first-lines-2.tsv` — gc's first `panic:`/`fatal error:` line per row (from the harness's `oracle.stderr`).
- `membership-sets.txt` — the enumerated observation sets of the collision rows (the machine's members; the harness checked
  gc's exhibited member ∈ set).
- `empty-result-adhoc.txt` — the one row the harness cannot express (an EMPTY rewritten text): the hand-run machine answer.
- `elab-ab.tsv` — the isolated elaboration A/B (two runs per module per side) with ratios and the `PrefixFacts` profiler split.
- `statement-check.txt` — the byte-wise statement comparison main vs candidate for the coherence theorems and the exact
  old → new of the three posed changes; `bridgeset-mutants.txt` — the two mutated rows and their type-mismatch errors.
- `ci-diff-tip-tail.txt` — the tail of `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the tip.

## Reproduction (from the audit worktree root, binary built as above)

```
# probe sets (each side; the fixture dirs copied under Corpus/coverage/exec/panic-recover/ first, removed after)
scripts/coverage run --prefix panic-recover/audit-preprint            # set 1 + stdlib (+ set 2 once its dir is present)
cp artifacts/coverage/latest.tsv <side>.tsv; artifacts/coverage/membership/<id>/observations.txt = the member sets
# the empty-text row by hand
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run ./tools/nativefrontend \
  --dir artifacts/coverage/go-run/panic-recover__audit-preprint__method-returns-empty --out .tmp/adhoc/empty.json
.lake/build/bin/golean native-json-run --input .tmp/adhoc/empty.json --function methodReturnsEmpty
# elaboration A/B (under the lock, alternating sides, two runs)
GOLEAN_MEM_MAX=48G scripts/capped lake env lean GoLean/GoCore/<module>.lean      # timed with date +%s.%N
GOLEAN_MEM_MAX=16G scripts/capped lake env lean -Dprofiler=true -Dprofiler.threshold=500 GoLean/GoCore/PrefixFacts.lean
# BridgeSet mutants: a scratch copy of GoLean/GoCore/BridgeSet.lean with the two edits named in bridgeset-mutants.txt
GOLEAN_MEM_MAX=16G scripts/capped lake env lean .tmp/BridgeSetMut.lean
# the gate
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff
```
