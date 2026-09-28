# Pre-merge audit of the step-label reshape — evidence (2026-09-28)

[AGENT auditor]. Consuming doc: `docs/2026-09-28_step-label-audit.md`. Candidate `61bdc65d` (lane `core/step-label-0928`),
compared against `main` @ `84f0a9e4` (its merge base; `fd1135ff` differs by one records-only doc). Host linux/amd64, the
shared box; builds and the gate under the box-wide lock; everything under `scripts/capped`.

| File | What | Producer |
|---|---|---|
| `main-vs-lane-summary.txt` | 1804 ids × (5 streams `native-json-run` / lane-param `coverage-observations`), main binary vs candidate binary, byte-for-byte: 0 DIFF | `compare-main-vs-lane.py` (run from `.tmp/cmp/`, capped 40G) |
| `sampled-ids.txt` | the sampled manifest ids | same |
| `compare-main-vs-lane.py` | the comparison script (own wire export, identical argv to both binaries) | [AGENT auditor] |
| `google-search-reenumeration.txt` | the certified slow-tier row re-enumerated on both binaries with the certificate's argv: identical output and statistics, = the certified set | `coverage-observations` ×2 under `/usr/bin/time -v` |
| `probes.txt` | BridgeSet mutation controls (rows 34, 15 → elaboration fails) and the TryLock pick-record probe (modulo, empty tape, bound 1) | `scripts/capped lake env lean` |
| `theorem-inventory.txt` | theorem names and statements, main vs candidate: none removed, 6 added, no premise added | `git grep` + a statement extractor |
| `gate-tail.txt` | `ci --diff` at the candidate tip: EXIT=1 red on exactly the 5a pair; 3768 = 3531/237 | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` |
