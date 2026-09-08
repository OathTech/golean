# I1 declaration landing — validation evidence (2026-09-08)

[AGENT] 2026-09-08. Scope: the separate L1b declaration boundary under
[`land/i1-declarations`' charter](../../2026-09-08_i1-declaration-landing-charter.md).
The [landing record](../../2026-09-08_i1-declaration-landing.md) consumes this
evidence. These are compact records, not source or corpus copies.

[AGENT] First-review correction round: the [review response](../../2026-09-08_i1-review-response.md)
records the new work and second-review stop. `coordinator-review.md` is the
supplied independent FIX-FIRST report at `8b4a1aec`, copied byte-exactly;
its source SHA is recorded in that response. Initial validation below remains
bound to its historical source. New correction-gate records are identified
separately when complete.

Toolchains: `go version go1.26.5 linux/amd64`; Lean pinned by
`lean-toolchain` to `leanprover/lean4:v4.32.2`. Gates ran on linux/amd64 with
a verified 32 GiB cgroup cap, three Lean threads, eight differential workers
and the primary checkout's box-wide full-build lock. No performance claim
is inferred from timings.

- `source-selection.tsv`: fifteen original committed blobs at `7ac3eb46`.
- `candidate-gate.txt`: tail of the corrected full `--diff` gate, captured
  exit 0; dirty candidate at `31ecd39d`, frozen index tree
  `91c21fbbc0773ad375561adc478c9a7a5dbbe83f`. Its runtime source equals
  implementation commit `3e393be5d7f72d3be2dd57e45872e9fcc4a90518`; only
  documentation/evidence changed between that gate and the commit.
- `author-controls.json`: eight actual fixture-reader challenges and their
  named refusals; these are author checks, not independent review.
- `candidate-measurements.json`: freshly derived counts, comparison of
  results and allowed stages against the baselines, source-bound log hashes
  and fixture identity. The existing `beside-loop` stage alternation is
  retained; no baseline was re-pinned.
- `committed-slow-gate.txt` and `committed-slow-measurements.json`: final
  clean-source `--slow` PASS at `3e393be5`, actual exit 0; 3,654 executable
  rows (3,403 PASS / 251 expected FAIL), 394 negative PASS, no drift, and
  the freshly enumerated six-member certified set and wire byte-identical.
  The statistics were published at 2026-09-08 01:17:23 UTC. The compact
  tail includes the exact slow-mode banner to distinguish this run from a
  gate using cached certification. Later completion edits are records only.

The first full run was interrupted for the reproduced named-constraint bug
(exit 143, 1,010 partial published rows); it is not a full PASS. Full logs,
red-first outputs and the dead-owned-lock recovery record remain in ignored
`artifacts/i1-landing/` in the worktree. Findings and resolutions are explained
in the landing record. Independent audit disposition is recorded there.

## Reproduction

From an isolated checkout of the implementation commit, run
`scripts/setup-deps --from /path/to/prepared/sibling`. Take the box-wide lock
as described in `docs/operational-lessons.md` before a full gate; the original
runner held `/home/dev/projects/golean/artifacts/build-lock.d` with a PID and
worktree owner record and released only its own lock on completion.
The gate's exact inner commands were:

```sh
mkdir -p .tmp/i1 artifacts/i1-landing
export TMPDIR="$PWD/.tmp/i1"
export GOLEAN_MEM_MAX=32G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=8
scripts/capped scripts/ci --diff > artifacts/i1-landing/ci-diff-corrected.log 2>&1
scripts/capped scripts/ci --slow > artifacts/i1-landing/ci-slow-committed.log 2>&1
```

Capture each actual exit status; do not treat a log's partial success as a
completed gate. Original candidate metadata records `git_dirty=true`; the
committed-source rerun records its own SHA and `git_dirty=false`. Full logs
include run-specific paths; their recorded hashes identify these particular
runs and are not deterministic golden outputs. Compact gate tails remove
ANSI SGR escapes and retain the text from `══ scripts/ci summary` to the end.

The focused producer, parser, equality, pin and poison checks are reproduced
by `scripts/capped scripts/check-declarations`. Frontend regressions were run
with `GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off go test
./tools/nativefrontend ./tools/lowerdiag -count=1`. To reproduce the additional
fixture-reader challenges after the declaration target has built:

```sh
GOLEAN_DECLARATION_FIXTURE="$PWD/artifacts/i1-landing/declarations.json" \
  GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off \
  go test ./tools/nativefrontend -run '^TestDeclarationDecoderFixture$' -count=1
python3 - <<'PY'
from pathlib import Path
import copy, json, subprocess
base = Path('artifacts/i1-landing/declarations.json').read_bytes()
data = json.loads(base)
folder = Path('.tmp/i1/reader-challenges')
folder.mkdir(exist_ok=True)
controls = [
    ('duplicate-schema', b'{"schema":"i1-declaration-test-v1",' + base[1:], 'duplicate JSON object key'),
    ('escaped-duplicate-schema', b'{"\\u0073chema":"i1-declaration-test-v1",' + base[1:], 'duplicate JSON object key'),
    ('invalid-utf8', b'\xff' + base, 'JSON input is not valid UTF-8'),
]
for label, name in [('uintptr-collapse', 'up'), ('generic-argument-collapse', 'ib'), ('raw-tag-collapse', 's1')]:
    m = copy.deepcopy(data)
    row = next(r for r in m['types'] if r['name'] == name)
    twin = {'up': 'u', 'ib': 'i', 's1': 's2'}[name]
    row['type'] = next(r['type'] for r in m['types'] if r['name'] == twin)
    controls.append((label, json.dumps(m).encode(), 'Go/Lean declaration identity differs'))
m = copy.deepcopy(data)
m['pairs'][1] = m['pairs'][0]
controls.append(('repeated-pair', json.dumps(m).encode(), 'duplicate, missing or reordered identity pair'))
m = copy.deepcopy(data)
m['nominals'] = []
controls.append(('missing-nominals', json.dumps(m).encode(), 'unknown nominal declaration'))
results = []
for label, body, reason in controls:
    p = folder / (label + '.json')
    p.write_bytes(body)
    r = subprocess.run(['scripts/capped', 'lake', 'env', 'lean', '--run',
        'tools/check-declaration-wire.lean', str(p)], stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, timeout=120)
    (folder / (label + '.log')).write_text(r.stdout)
    assert r.returncode != 0 and reason in r.stdout, (label, r.returncode, r.stdout)
    results.append({'control': label, 'exit': r.returncode, 'reason': reason})
Path('artifacts/i1-landing/reader-challenges.json').write_text(json.dumps(results, indent=2) + '\n')
PY
```

`author-controls.json` is the resulting JSON record. Source-selection blob
identities can be re-derived with `git rev-parse
7ac3eb46bb3e2fe9c15b86b509569ef086327453:<path>` for each listed path.
The fixture hash is `sha256sum artifacts/i1-landing/declarations.json` and
must equal the tracked declaration fixture pin. The measurements' log hashes
are `sha256sum` of their named paths. Counts and allowed-stage comparisons
use the full native and negative TSV records, excluding comment/header rows;
the actual standing checks are:

```sh
scripts/coverage-baseline-diff --full --baseline baselines/native-full.tsv artifacts/coverage/latest.tsv
scripts/coverage-baseline-diff --full --baseline baselines/negative-full.tsv artifacts/coverage/negative-latest.tsv
python3 tools/reconcile-records
```
