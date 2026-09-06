# Command and result ledger

Source worktree: `/home/dev/projects/golean/.claude/worktrees/typed-preflight`.
All entries ran from that root. Environment:
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2`.
The following lists executable entrypoints; log redirection and status-file
shell wrappers do not alter their arguments. Published metadata and the
per-case capture JSON retain the effective parameters and actual CLI argv.

| Entrypoint | Log / recorded exit | Scope |
|---|---|---|
| `scripts/capped scripts/ci --diff` | `ci-diff.log` / `ci-diff.exit` = 0 | Full fresh preflight, including interface gate. |
| `bash spikes/gate-a1/check` | `a1-gate.log` / `a1-gate.exit` = 0 | Gate self-caps every Lean invocation. |
| `bash scripts/check-admission` | `admission-gate.log` / `admission-gate.exit` = 0 | Proof commands self-capped; initial final differential tail lacked outer cap, explicitly corrected below. |
| `bash spikes/iris-customer/check` | `a2-gate.log` / `a2-gate.exit` = 0 | Proof commands self-capped; initial final differential tail lacked outer cap, explicitly corrected below. |

The corrected targeted differential tails used `scripts/capped` around
`scripts/diff-coverage`, the gate-generated admission/A2 manifests, and
separate `artifacts/admission-capped` and `artifacts/a2-capped` output
directories. Their unaltered metadata records the exact manifest paths and
hashes; the logs and exit files show 1/1 and 3/3 PASS. The recommended future
invocations cap the whole scripts, as shown in the README.

The full additional capture ran:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped python3 artifacts/typed-preflight/capture-replay.py \
  --root "$PWD" --coverage artifacts/coverage \
  --manifest artifacts/typed-preflight/full-manifest.tsv \
  --out artifacts/typed-preflight/capture-full --jobs 2
```

It exited 0 after all requested attempts had records, including five
timeouts on one case. `capture-full.log` and `.exit` preserve completion.
All 17,926 subprocess argv and timeout/exit verdicts are in the archived
per-case JSON. The final producer is byte-identical to `capture-replay.py`
here and to the hash in `capture-provenance.json`.

The full comparator check was:

```sh
python3 artifacts/typed-preflight/compare-replay.py \
  artifacts/typed-preflight/capture-full artifacts/typed-preflight/capture-full
```

It intentionally exited 1 for the explicit `INCOMPLETE` record;
`capture-full-selfcheck.json` records that sole finding. This is a failed
whole-capture completeness assertion, not evidence of source divergence.
The final A2 smoke capture and comparator corruptions preserve their own
commands/provenance in `capture-controls.tar.gz` and the final control log.

Archives were generated with deterministic relative tar member names,
mtime zero, uid/gid zero, mode 0644 and gzip mtime zero. Each was reread in
full and every extracted member's hash matched its inventory. No file was
extracted over a worktree. All original source hashes were rechecked after
the runs; no baseline, dependency pin or semantic source changed.
