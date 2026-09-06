# O2 terminal and customer integration

[AGENT], 2026-09-06. Accepted integration of `f3971190` into
`39235f658326dd26a85d0e590ff9d6e1b796c3be`. The accompanying merge commit
names this checkpoint. Main remains at `47195683`.

All 3,952 selected input hashes in `source.json` were revalidated after the
three gates completed. The manifest SHA-256 is
`8eff45c52710b67cc22971dc0517562cc517286854279cacb4b7d9d146a2dcd3`.
Independent source-union review `352d09f9` is attached in the adjacent
`2026-09-06_o2-terminal-union-independent` packet. The accepted feature's
239 inputs differ only in the additive CI/Lake union and nine member pins.
Each pin changes only its apparatus source inventory; all other fields
match both parents. The combined inventory has 172 inputs.

| Fresh gate | Result | Evidence |
|---|---|---|
| Ordinary CI | Exit 0 | `ci.log`, `ci.exit` |
| Nine string-panic member cases | 9 PASS, exit 0 | `members.log`, `members.exit`, `members-latest.tsv`, nine certificates |
| Iris customer gate | Exit 0; both complete native artifacts and all 8 differential cases pass | `customer.log`, `customer.exit`, `native-artifacts/`, customer/shared result tables |

The interface audit checks 160 exports and 15,448 declarations; the terminal
audit checks 32 exports and 15,146 declarations; the customer audit checks
143 exports and 15,605 declarations. The gates retain compiled forbidden
declaration controls, including unused declarations. `terminal-claims.json`
records the actual terminal theorem types. Earlier semantic review remains
attached through feature tip `f3971190`; the additive-union review does not
replace that review or claim an independent Lean replay.

The three raw artifact archives retain all files from their focused runs
except each reproducible `bin/coverageharness`. The corresponding inventories
include the omitted binaries' hashes and sizes. Certificate source maps and
pin hashes were checked against the integrated files. Both whole native
artifact hashes were also matched against the customer log. Reproduction
commands and resource settings are in `provenance.json` (16 GiB, three Lean
threads, two differential workers).

The ordinary CI's full 3,635-case executable and 394-case negative records
remain **cached** from the accepted R1 run. They are not fresh full-corpus
evidence for this integration. The eight fresh customer rows and nine fresh
membership rows have separate raw records. Final B7/I1 migration, the
integrated `uintptr` repair, final full/slow gates, final review and the
sprint closing packet remain owed. This checkpoint does not complete O4/O5
or the sprint.
