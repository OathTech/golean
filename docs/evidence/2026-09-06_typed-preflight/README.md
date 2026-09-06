# Typed-consumer sprint preflight

[AGENT], 2026-09-05–06. Starting source:
`10fefeb3e6fbb3f7cb6630b8b559a9a7e7915e97` on `typed-preflight`.
This is initial sprint evidence, not the final integrated sprint gate.

## Executable and proof gates

All completed gates exited zero:

| Evidence | What actually ran |
|---|---|
| `ci-diff.log` | Fresh full executable differential: 3,598 cases, 3,353 PASS and 245 known FAIL; 202 interpreter eval checks; 394 fresh negative Go-oracle checks; normal CI checks and compiled gate-integrity controls. |
| Interface section of `ci-diff.log` | Full `scripts/check-interface`: fresh promoted/interface/contract/audit elaboration, 19 required exports, 526 audited constants, three compiled poison rejections. |
| `admission-gate.log` | Full admission gate: fresh elaboration, 14 required theorems, 375 audited constants, three compiled poison rejections, exact fresh native artifact comparison and 1/1 differential witness. |
| `a1-gate.log` | Full A1 gate: fresh spike elaboration, 12 required exports, 862 audited constants and three compiled poison rejections. |
| `a2-gate.log` | Full Iris customer gate: fresh spike elaboration, 18 required exports, 1,274 audited constants, three compiled poison rejections, exact fresh native artifact comparison and 3/3 differential controls. |

The full executable and negative runs match the tracked baselines. The
executable runner itself exits 1 because 245 cases are known failures; CI
exits 0 after comparing that failing set with the baseline. Neither a
refusal nor an unsupported case is counted as conformance. The existing
`channels/select-select/beside-loop` FAIL-stage alternation remains explicit
in the baseline; this run records `lean-observation`.

One slow-tier row, `imported-goose/channel/google-search`, is explicitly
**CERTIFIED-CACHED**. This run freshly checks its Go samples and driver
coupling against the tracked set; it does not re-certify that set. The two
existing report-only reconciler findings (C13 and C5) remain visible in the
CI log. The 394 negative checks establish Go-oracle rejection, not GoLean
frontend rejection of invalid source.

`full.tsv`, `full.meta.tsv`, `negative.tsv`, and `negative.meta.tsv` are
unaltered copies of the published records. `full-manifest.tsv` has the same
SHA256 as the manifest recorded in `full.meta.tsv`; its complete case-id set
is checked against `full.tsv`. Some generic metadata fields say `unknown`
because CI invokes `diff-coverage` directly. Full scope is established by
the actual 3,598-row manifest and result-id equality, not by rewriting those
metadata fields. `admission.tsv` and `a2.tsv` keep the opt-in fixtures separate.

## Source and bootstrap provenance

`source-sha256.json` binds all 5,485 tracked files at the starting revision.
`source-recheck.json` confirms that every one was unchanged after CI and the
spike gates completed, with a clean worktree at that checkpoint.
`source-final-recheck.json` confirms the same original files remain unchanged
after capture; its later revision contains only the independent Boolean
helper review documents. Subsequent changes in this lane are evidence and
documentation only. The earlier
`source-status.txt` records an untracked bootstrap `deps` symlink; it was
moved into artifacts and replaced by a real gitignored `deps/` directory
before differential provenance was recorded. No semantic source changed.

Lean is pinned at 4.32.2, Go at 1.26.5, and the Iris package at
`e7a0a43814c4f1154ca0c8049883ca56c2288b86`. The version files, reference
revision files, gate fingerprints and dependency checks retain the exact
measurements. Root `.lake` was independently copied from the primary
checkout; each spike `.lake` was independently copied from the reviewed
`gate-a2-iris` worktree. No writable build cache was shared between worktrees.
The main checkout's pinned `deps/go` and `deps/goose` were only read through
reference symlinks. This is an incremental build plus the gates' explicit
fresh elaborations, not a clean network bootstrap or full upstream rebuild.

All proof elaborations, full CI, and model replay used `scripts/capped`,
`GOLEAN_MEM_MAX=16G` and `LEAN_NUM_THREADS=3`; differential concurrency was 2.
Packaging identified a gap in the documented opt-in invocation: admission
and A2's scripts cap their proof commands, but their final `diff-coverage`
call does not self-wrap its Lake build. The initial `bash .../check`
invocations therefore did not establish a cap for those four differential
witness tails. `admission-capped-diff.log` and `a2-capped-diff.log` retain
fresh targeted reruns under an outer `scripts/capped`, without repeating
the already capped proof work. Their metadata records the untracked
evidence documents present at that time; the original source inventory
remained unchanged. Use the corrected whole-script commands below.
`cap-readback.txt` records `memory.max=17179869184` and `memory.swap.max=0`.
No pin, baseline, resource cap or sandbox permission changed.

## Before/after observations and choice consumption

The ordinary differential harness retains Go stdout/stderr, wire artifacts,
membership observation sets and summary records, but its strict-stream
choice reports are shell variables. `capture-replay.py` supplements that
evidence using the existing `choice-trace --batch --dump` implementation.
It records full model observation bytes and every labeled consumption;
it does not modify the model, harness, corpus or acceptance conditions.

Each available wire is replayed with the default stream and the three fixed
CI streams. Strict `depth=N` rows additionally use the same three explicit
LCG31 streams as CI. The tracer's separate `rand:` syntax uses a different
generator and is deliberately not substituted. Fuel is 10,000,000 except
the following four rows, whose existing manifests explicitly declare
`nonterm=200`; those captures use fuel 200 and record that exception:

- `atomics/spin/flag-wait`
- `goroutines/send-then-spin`
- `race/atomics-free/cas-failure-acquires`
- `sync/trylock/spin-until-trylock`

These are bounded captured paths, not an all-choices theorem or an
unbounded termination claim. The full conformance run remains separate.
Missing wire and lowering/setup refusals are recorded explicitly. A
successful subprocess is not by itself a successful model execution.

All 3,598 manifest ids have final capture records:

| Capture classification | Cases | Meaning |
|---|---:|---|
| `RECORDED` | 3,558 | All requested observation and trace commands completed; includes explicit model refusals and other outcomes, not only success. |
| `RECORDED_WITH_FINDINGS` | 1 | `arrays/materialization-budget/over-budget`: BUG-078's existing lowering refusal; four error observation records and one tracer `ERROR`, with no consumption. |
| `NO_WIRE` | 38 | Existing known failures with no emitted wire; each full-run status/stage/detail remains in its case record. No PASS case lacks a wire. |
| `INCOMPLETE` | 1 | `strings/trimspace-repeat/repeat-bound-refused`: the existing BUG-090 timeout gap, described below. |

The capture retains 14,362 completed native observation commands and 3,559
completed trace batches. There are 14,359 trace rows: 14,358 with driver
agreement and the one explicit lowering error. The dumps retain 21,326
labeled consumptions; no trace alarm or choice-bound violation was reported.
`capture-summary.json` derives these counts and separately lists every
native observation status, including unsupported, stuck and fuel-out.

**The BUG-090 gap is unresolved, not an observation or a measured choice
trace.** This case timed out in full CI at its existing 30-second limit.
Capture allowed 240 seconds for each native command and 240 seconds for
the entire per-case tracer batch. Its default stream, three fixed streams,
and tracer batch all timed out at fuel 10,000,000: five timed-out commands,
empty observation outputs, and no completed trace row or consumption row.
The case's `incomplete_commands=6` is a diagnostic count that additionally
counts absent trace rows; it is not six subprocess timeouts. No rerun,
reduced-fuel substitute, or prefix was promoted to a completed capture.

This is the same named budget pin documented in
[`docs/BUGS.md`, BUG-090](../../BUGS.md) and previously left unmeasured in
the [C2 choice-trace exclusion record](../2026-09-05_c-arc-c2/choice-trace/excluded.tsv).
That older run stopped its first stream after more than 30 minutes. The
current source already uses a dense heap; the old bug entry's association-list
mechanism prose is historical and is not a fresh diagnosis of this timeout.
This preflight preserves the resource evidence without asserting a new cause.

The collector exits zero because every requested attempt now has a record.
The whole-corpus comparator **deliberately fails self-comparison** solely
on this `INCOMPLETE` case: `capture-full-selfcheck.json` and `.exit` retain
that result (35,852 captured files checked). Thus the package does not yet
establish the charter's whole-corpus byte-identity criterion for B7. Whether
a future formal correspondence plus this explicitly retained timeout record
satisfies the intended measurement claim remains for review; no automatic
exclusion or acceptance exception has been added.

The existing batch tracer is unsafe to resume when requesting a dump:
`runBatch` skips ids already present in the report but rewrites the dump.
The capture therefore uses a fresh directory for every case and never
resumes either output. No existing helper was changed. Every command,
exit/timeout verdict, input hash, output hash, stream and fuel is retained
in the capture's per-case JSON records.

`compare-replay.py` compares full observation stdout/stderr and report/dump
bytes without normalization; it also checks manifest coverage, file hashes,
stream/fuel settings and command verdicts. Reuse the same frozen coverage
input directory on both sides so diagnostic input paths also remain equal.
Keep a separately fresh full CI run for status/stage conformance. If an
isolated fidelity repair precedes B7, capture that repaired source as B7's
before-state; do not relabel intentional repair differences as representation
equivalence. I1's declared earlier-stage refusals also remain a separate arc.

`check-capture-controls.py` exercises real A2 captures and corruptions. The
final control log records rejection of changed observation bytes,
changed consumption bytes, a missing case and a missing dump. The earlier
`capture-controls.log` records a script-placement command error (exit 2),
followed by the corrected, successful invocation in the `-verified` log;
it is not counted as a comparator rejection. The tiny A2 capture and all
controls were rerun after the producer reached its final source; those
final outputs are retained in `capture-controls.tar.gz`.

## Reproduction

From a checkout with the exact pinned dependencies available:

```sh
export GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2
scripts/capped scripts/ci --diff
scripts/capped bash scripts/check-admission
scripts/capped bash spikes/gate-a1/check
scripts/capped bash spikes/iris-customer/check
```

The interface gate is already invoked in CI. For a fresh capture:

```sh
SPRINT_SCRATCH="$(mktemp -d "${TMPDIR%/}/golean-preflight.XXXXXX")"
scripts/coverage-manifest > "$SPRINT_SCRATCH/manifest.tsv"
scripts/capped python3 docs/evidence/2026-09-06_typed-preflight/capture-replay.py \
  --root "$PWD" --coverage artifacts/coverage \
  --manifest "$SPRINT_SCRATCH/manifest.tsv" \
  --out "$SPRINT_SCRATCH/capture" --jobs 2
```

Pass the two resulting capture-directory paths to `compare-replay.py` for
the before/after comparison. Keep the original wire-input directory fixed
when performing that comparison, as described above.

`coverage-artifacts.tar.gz` retains 22,510 raw published/input/oracle files,
excluding rebuildable binaries; `coverage-artifact-sha256.json` indexes their
uncompressed bytes. `capture-full.tar.gz` retains every per-case capture,
including timeout outputs and exact command records. `capture-controls.tar.gz`
retains the final A2 smoke capture and the intentional corruptions used to
challenge the comparator. Each archive has a SHA256 inventory and a full
member-by-member verification record. Extract only into fresh directories;
none of these archives claims every recorded program succeeds. Check
`SHA256SUMS` from this directory before consuming the evidence.
