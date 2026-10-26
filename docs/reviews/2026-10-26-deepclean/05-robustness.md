# Robustness and release hygiene review

[AGENT Codex / robustness] 2026-10-26. Independent source review and small reproductions against
base `62bb461463d94c9eb4f3d003aa441db653bd77c3`, worktree `deepclean-1026`. Product sources,
tests, baselines and charter were not edited. No other review report was read before forming
these findings. After the seed finding was sent, the coordinator reported independent
corroboration; the analysis below remains this reviewer's own.

## Result and scope

Six findings: four medium defects and two low defects/documentation corrections. No new
wrong Go execution result was established. The strongest measurement issue is a successful
auxiliary trace report that can conceal a fresh tracer error behind stale results. This
runner is explicitly auxiliary tooling, **not a gate**; this finding does not establish a
false green of `scripts/ci` or the differential baseline.

Reviewed the CLI's arguments, file wrappers, observation decoder, seed parser/allocation,
runtime allocation guards, setup and trace scripts, strict JSON parser, and release/setup
documentation. Used the prepared `.tmp/nativefrontend` and `.lake/build/bin/golean` binaries.
Every actual frontend/interpreter/trace run was inside `capped`, normally with a deliberately
small `CAPPED_MEM_MAX=256M`; no uncapped stress run, full build, corpus, or gate was performed.
The coordinator owns the full gate. Scratch stayed under `.tmp/deepclean-robustness/`; no
Go compilation or download was needed. The isolated script harness sets local Go cache and
temporary paths and `GOPROXY=off`.

Findings and proposed dispositions below have [AGENT Codex / robustness] provenance. They
are proposals, not changes to standing practices or accepted product scope.

## R1 — Medium: stale trace chunks can replace a fresh ERROR with an old success

**Locations:** `scripts/choice-trace-corpus:131-135,151`; `scripts/choice-trace-summarize:62-75`.

The corpus runner removes only `results-0.tsv` through `results-(JOBS-1).tsv`, then passes
**every** `results-*.tsv` in the reused output directory to the summarizer. Old higher-index
chunks remain after reducing `--jobs`. The summarizer deliberately merges multiple runs,
with later successful entries superseding earlier entries and ERROR entries ignored whenever
the same id has any successful entry. That merge policy is inappropriate for the runner's
claim about this run.

Reproduced using unchanged copies of both scripts, a synthetic one-row manifest and exporter,
and the **real golean tracer**. The exporter copies a prepared valid wire, so no Go build or
whole-corpus run is needed. First record a valid trace, retain its result as `results-99.tsv`,
then rerun with `--jobs 1` and an invalid-schema wire. The fresh `results-0.tsv` contains
`probe/one`, status `ERROR`, and `native lowering: unexpected schema broken`. Nevertheless,
the runner exits **0** and reports one traced id, one stream, and **zero ERROR ids**. A valid
fresh trace with no stale files is the held control and also exits 0.

`results-99.tsv` is just a compact stand-in for a surviving chunk from a prior larger job
count; the defect does not require 100 processes. Other valid stale rows can also inflate the
reported scope beyond the current manifest. This is a measurement defect, not merely untidy
temporary files.

**Acceptance:** summarize only the exact chunk paths produced by the current invocation, or
start in a fresh per-run directory. A fresh ERROR must remain visible and fail the runner,
regardless of old successes. Keep the summarizer's explicit multi-input behavior if useful;
do not silently use it as current-run evidence. The complete shared reproduction is in §7.

## R2 — Medium: seed array types bypass materialization limits and allocate before validation

**Locations:** `GoLean/SeedFile.lean:184-195`; `GoLean/GoCore/Seed.lean:267-295`.

The seed type grammar accepts an arbitrary decimal array length directly as `Ty.array`.
Unlike native-wire type decoding, it applies no `arrayLenBudget` or nested-footprint check.
`seedCells` first invokes `seedAllocFrom`, which constructs and allocates the default value
of every declared cell, and only afterwards checks the supplied seed values in
`seedStoreFrom`. A tiny malformed seed can therefore force a massive allocation before
the expected value-length diagnostic is reached.

With the ordinary `arrayLenCap` wire and an unused seed cell, `[3]int` with value `[]`
returns exit 1 and a well-formed observation:

```text
status: stuck
message: seed: cell 0: expected array(3), got 0 element(s)
```

Changing only the type string to `[1073741824]int` kills the process at the 256 MiB cap
in under one second: **exit 137, the cap's KILLED diagnostic, no observation JSON**.
This is a failure, not an explicit seed refusal. It requires neither a large seed file nor
execution of a large Go program. The underlying array request greatly exceeds the wire's
per-dimension limit; the small reproduction cap limits review cost rather than claiming
that 256 MiB is a supported production budget.

```sh
python3 - <<'PY'
from pathlib import Path
import json
p = Path('.tmp/deepclean-robustness')
p.mkdir(parents=True, exist_ok=True)
for name, size in [('small', 3), ('huge', 1073741824)]:
    (p / ('seed-' + name + '.json')).write_text(json.dumps({
        'schema': 'golean-seed-v1',
        'cells': [{'type': '[' + str(size) + ']int', 'value': []}]}))
PY
CAPPED_MEM_MAX=256M capped .tmp/nativefrontend \
  --dir Corpus/coverage/exec/arrays/array-len-cap \
  --out .tmp/deepclean-robustness/simple.wire.json
CAPPED_MEM_MAX=256M capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-robustness/simple.wire.json --function arrayLenCap \
  --seed .tmp/deepclean-robustness/seed-small.json --no-choice-report
# Expected control exit 1; run the following separately if the shell has errexit.
CAPPED_MEM_MAX=256M capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-robustness/simple.wire.json --function arrayLenCap \
  --seed .tmp/deepclean-robustness/seed-huge.json --no-choice-report
```

Additional held control: seed types `[0][3]int` and `[0][1073741824]int`, both with value `[]`,
completed successfully with an empty array seed and result 6. Thus the tested failure is
materializing a positive-length array, not simply parsing a large number. No claim is made
about a semantic error on zero-length arrays.

**Acceptance:** reject over-budget seed shapes by name before allocation, including nested
and named-type footprints, and perform cheap shape checks before materializing obviously
invalid seeds. Preserve cycles/sharing and small valid seed behavior. This finding is
separate from the acknowledged append/string-conversion allocation limitations in BUG-131.

## R3 — Medium: observation comparison accepts lossy JSON and impossible byte values

**Locations:** `GoLean/CLI.lean:983-984` and `933-938`; contract `docs/cli.md:245,394,442`.

`decodeObservation` calls `Lean.Json.parse`, not the project's lossless parser. Duplicate
keys disappear before exact-key validation. A left observation containing `status:"panic"`
followed by `status:"ok"` compares equal to a clean `ok` observation, **exit 0 with no
diagnostic**. This contradicts the documented strict decoding boundary and permits a
conflicting raw result to become a successful comparison. The string-value arm also checks
only that each byte is a natural number, so `bytes:[256]` self-compares successfully even
though it is not a byte sequence.

This is a schema/validation defect. No claim is made that today's generated Go observer or
model outputs produce either malformed form. Valid comparisons still work, and an unknown
ordinary object key is rejected with exit 2, establishing that the defect is specifically
lossless parsing and incomplete scalar validation rather than absent validation altogether.

Complete short probe (prints exit codes; all comparisons capped):

```sh
python3 - <<'PY'
import json, os, subprocess
env = dict(os.environ, CAPPED_MEM_MAX='256M')
ok = dict(schema='golean-observation-v1', status='ok', output='', values=[])
good = json.dumps(ok)
duplicate = ('{"schema":"golean-observation-v1","status":"panic",'
             '"status":"ok","output":"","values":[]}')
bad_byte = json.dumps(dict(ok, values=[dict(tag='string', bytes=[256])]))
cases = [('valid', good, good), ('duplicate-status', duplicate, good),
         ('byte-256', bad_byte, bad_byte),
         ('unknown-key', json.dumps(dict(ok, typo=0)), good)]
for name, left, right in cases:
    r = subprocess.run(['capped', '.lake/build/bin/golean', 'observation-eq',
                        '--left', left, '--right', right], env=env,
                       capture_output=True, text=True)
    print(name, r.returncode, r.stderr.strip())
PY
```

Observed exit codes: `valid 0`, `duplicate-status 0`, `byte-256 0`, `unknown-key 2`.

**Acceptance:** lossless, bounded observation parsing rejects duplicate keys, including
escaped equivalents, and invalid Unicode escapes before equality; string bytes must be in
0–255. Ordinary valid observations must retain their existing equality behavior. Reusing
the existing parser is a small boundary repair, not a request for a new adversarial gate.

## R4 — Medium: a failed trace summarizer still produces runner exit 0

**Locations:** `scripts/choice-trace-corpus:145-157`.

The script enables `pipefail` but does not check the exit status of the summary/`tee`
pipeline. It searches the resulting report for certain finding lines and then unconditionally
exits 0. A failed summarizer that emits no such lines is therefore a success to the caller.

The §7 harness leaves a malformed old `results-99.tsv` with contents `junk\nbroken\n`.
The fresh trace succeeds, the summarizer raises `KeyError: 'status'`, and the runner exits
**0**. Its stderr shows the traceback; the visible failure is not entirely hidden, but the
success exit code violates the script's stated infrastructure/finding contract. This defect
is distinct from R1: even with chunk selection fixed, any summarizer or `tee` failure must
not become success.

**Acceptance:** check the summary pipeline's status and return the documented infrastructure
failure exit code. A real report finding should continue to return the finding code. No
new gate is needed; a focused script self-test is sufficient. Full reproduction: §7.

## R5 — Low: an absolute `choice-trace-corpus --out` path breaks wire loading

**Locations:** `scripts/choice-trace-corpus:110,117`.

`w` is `$OUT/wire/...`; the batch manifest always records `$ROOT/$w`. When `--out` is
absolute, the exporter correctly writes the wire to the absolute directory, but the batch
path gains a second root prefix. The real tracer then cannot load it and the runner reports
an ERROR. No relative-only restriction appears in the option's contract.

In §7, `--out out` succeeds. Changing only to `--out <absolute scratch path>/absout` returns
exit 1 and an unreadable doubled-prefix path. This is an ordinary supported-looking CLI
input, with no unusual filename or permission condition.

**Acceptance:** resolve output paths once, or preserve already-absolute wire paths. Both
relative and absolute output directories should produce identical trace results. The
failure must remain loud until repaired. Full reproduction: §7.

## R6 — Low: current release-facing documentation carries stale limits and theorem counts

**Locations:** `docs/release.md:160-164`; `README.md:142`; compare
`GoLean/GoCore/Machine.lean:1694-1703`, `docs/BUGS.md:9023`, and `comparator.json`.

The release document still says variable-length `make` past the footprint budget allocates
until a memory kill and that the core guard awaits a decision. BUG-131 and the actual
machine implement that guard as of 2026-10-25. The published limit now misstates the
shipped behavior and makes a completed release item appear open. The README also describes
349 comparator theorems while `comparator.json` contains 383, agreeing with the charter.

The runtime behavior was verified with the existing corpus source:

```sh
CAPPED_MEM_MAX=256M capped .tmp/nativefrontend \
  --dir Corpus/coverage/exec/arrays/materialization-budget-runtime \
  --out .tmp/deepclean-robustness/runtime.wire.json
CAPPED_MEM_MAX=256M capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-robustness/runtime.wire.json --function makeOverBudget \
  --no-choice-report
# Separate command after the intended nonzero refusal:
CAPPED_MEM_MAX=256M capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-robustness/runtime.wire.json --function makeSmallElem \
  --no-choice-report
python3 -c 'import json; print(len(json.load(open("comparator.json"))["theorem_names"]))'
```

The first interpreter run immediately reports `unsupported` with the named runtime-footprint
budget (33,554,432 requested leaves versus 16,777,216 allowed). The small-element control
reports `ok`, value 32784. The count command prints 383. This was not an expensive at-budget
materialization run.

**Acceptance:** update the release limit to describe the runtime guard and accurately retain
the still-open allocation routes documented under BUG-131, rather than deleting all resource
limits. Correct or remove the redundant README theorem count. No standing-rule change is
necessary.

## 7. Complete isolated reproduction for R1, R4 and R5

Run R2's frontend command first to create `simple.wire.json`. Save the following as
`.tmp/deepclean-robustness/probe-runner.py`, then run
`python3 .tmp/deepclean-robustness/probe-runner.py` from the repository root.

The two reviewed scripts are copied byte-for-byte into a scratch miniature checkout. Only
the manifest and `go run` export step are substituted; the real interpreter generates both
the good and ERROR trace rows. This keeps the actual repository's fixed artifact/cache paths
untouched and avoids building Go or tracing the corpus. The script deletes only its own
scratch `runner` directory before repeating. All runner processes run inside the 256 MiB
cap. Observed in approximately two seconds:

| Case | Exit | Result |
| --- | --- | --- |
| Relative path, fresh output | 0 | One traced id, zero errors |
| Absolute output path | 1 | Real tracer ERROR from duplicated root path |
| Malformed stale higher chunk | 0 | Summarizer traceback, `KeyError: 'status'` |
| Current ERROR plus stale success | 0 | Fresh ERROR row exists; summary says zero ERROR ids |

```python
import os
from pathlib import Path
import shutil
import subprocess

repo = Path.cwd()
root = repo / '.tmp/deepclean-robustness/runner'
if root.exists():
    shutil.rmtree(root)
(root / 'scripts').mkdir(parents=True, exist_ok=True)
(root / 'bin').mkdir(exist_ok=True)
for name in ('choice-trace-corpus', 'choice-trace-summarize'):
    shutil.copy2(repo / 'scripts' / name, root / 'scripts' / name)
(root / 'scripts/coverage-manifest').write_text(
    '#!/usr/bin/env python3\n'
    'print("probe/one\\tunused\\tarrayLenCap\\t-\\tok\\t-\\t-\\tstrict\\t-\\t-")\n')
(root / 'bin/go').write_text(
    '#!/usr/bin/env python3\n'
    'import os,shutil,sys\n'
    'shutil.copyfile(os.environ["PROBE_WIRE"],sys.argv[sys.argv.index("--out")+1])\n')
for p in (root / 'scripts/coverage-manifest', root / 'bin/go'):
    p.chmod(0o755)
env = {**os.environ, 'PATH': str(root / 'bin') + ':' + os.environ['PATH'],
       'PROBE_WIRE': str(repo / '.tmp/deepclean-robustness/simple.wire.json'),
       'CAPPED_MEM_MAX': '256M', 'GOPROXY': 'off',
       'TMPDIR': str(repo / '.tmp/deepclean-robustness/gotmp'),
       'GOTMPDIR': str(repo / '.tmp/deepclean-robustness/gotmp'),
       'GOCACHE': str(repo / '.tmp/deepclean-robustness/gocache')}
cmd = ['capped', str(root / 'scripts/choice-trace-corpus'), '--jobs', '1',
       '--golean', str(repo / '.lake/build/bin/golean'), '--streams', 'default']
def run(name, out):
    p = subprocess.run(cmd + ['--out', out], env=env, text=True, capture_output=True)
    print(name, 'exit', p.returncode)
    print(p.stderr.strip())
    print('\n'.join(line for line in p.stdout.splitlines()
                    if 'rows traced:' in line or 'ERROR' in line))
run('relative control', 'out')
run('absolute path', str(root / 'absout'))
(root / 'out/results-99.tsv').write_text('junk\nbroken\n')
run('stale malformed file', 'out')
shutil.copyfile(root / 'out/results-0.tsv', root / 'out/results-99.tsv')
(root / 'invalid.json').write_text('{"schema":"broken"}')
env['PROBE_WIRE'] = str(root / 'invalid.json')
run('current ERROR hidden by stale success', 'out')
print('CURRENT:', (root / 'out/results-0.tsv').read_text().splitlines()[-1])
```

## Held controls, acknowledged limits and gaps

- The README arrayLenCap example lowers and runs; the inspected case has a main function, so its lack of --subject is not a defect.
- Small malformed seeds refuse by name, and both tested zero-length outer array seeds succeed. Runtime-sized make now refuses excessive footprints; a small-element control succeeds.
- Valid observation equality and unknown-key rejection work. The review does not establish malformed observations emitted by current producers.
- The trace runner itself is auxiliary tooling; no claim about the main gate follows from its false successes. Its real tracer was exercised, but its corpus discovery and Go export were replaced only inside the isolated harness.
- Existing limitations around append/string-conversion materialization, Go observer pointer/slice/map/channel comparison, raw seeded addresses, runtime Go defaults and pre-main aborts are documented; they are not promoted here into newly discovered defects.
- No full numerical differential, fresh dependency installation, permission-denial reproduction, or host-portability run was attempted. Setup/network behavior was inspected statically. No inference of a nono denial was needed.
- Existing charter text contains verbatim historical user quotations. It was left untouched; any cleanup of those quotations is the owner's call, not authorization implied by this audit.
- Reproduction artifacts are ephemeral. The reviewer removes only .tmp/deepclean-robustness after recording these reproducible conclusions; this report is the retained artifact.
