# Project gate audit evidence

[AGENT] evidence at source SHA `75dcb6d14c279fc7149ee626063b24ab76e2fa1f`, 2026-09-05. See `../../2026-09-05_project-gate-audit.md` for the assessment and scope limitations.

- `gate-tail.txt`: completed `scripts/capped scripts/ci --diff` summary, RESULT PASS. The executable run had 3,593 rows, 3,347 PASS and 246 FAIL; the baseline comparison passed without regression. This includes cached slow-tier sets, not fresh `--slow` certification.
- `differential-meta.tsv`, `negative-meta.tsv`: harness attribution records. Clean source tree; pinned oracle.
- `artifact-hashes.json`: SHA-256 fingerprints of the full local log, current results, baseline, twin wire, and probe wire. The larger files remain in the primary checkout; a hash alone is not a substitute for retaining them for a distributed audit.
- `ContractProbes.lean`, `contract-probes.txt`: compiled evaluation of the core's continuation-sensitive `recoverResult` and address-only `StateWf`. The output is nil, an interface containing the panic payload, and `true`. These are probes, not exported theorems.
- `printprobe.go`, `print-driver.json`, `print-dedup.txt`: current frontend and driver produce the output prefix; the dedup engine exits 1 explicitly refusing the output event. This investigated suspicion was rejected as a finding.

Replay from the primary checkout, with this evidence directory substituted for `EVIDENCE`:

```sh
scripts/capped lake env lean EVIDENCE/ContractProbes.lean
```

For the printing probe, copy `printprobe.go` into a unique scratch package as `main.go`, build the native frontend from the audited source, emit with `--dir PACKAGE --out WIRE`, then run:

```sh
scripts/capped .lake/build/bin/golean native-json-run --input WIRE --function subject
scripts/capped .lake/build/bin/golean coverage-observations --input WIRE --function subject --engine dedup
```

The first command must return integer 7 with output `audit-output\n`; the second must fail naming an output event. Do not use an old unversioned `artifacts/nativefrontend` binary: the first exploratory attempt did, and its obsolete println refusal was excluded from the audit evidence.
