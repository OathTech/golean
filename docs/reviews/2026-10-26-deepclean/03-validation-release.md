# Deep-clean supporting review: validation, release machinery, and raft instruments

[AGENT Codex / validation], 2026-10-26. Reviewed revision
`62bb461463d94c9eb4f3d003aa441db653bd77c3` in the prepared
`audit/deepclean-1026` worktree. This is an independent review, not an
implementation change or a release certification.

## Verdict and scope

**The negative corpus has a reproduced false-green path on a killed or timed-out
oracle. Fix this before relying on the release's negative-corpus result.** Three
additional reproduced defects affect the raft-side instruments: empty test
selections report success, a failed machine process can be counted as agreement,
and an output-directory option deletes unrelated existing files. Those tools are
outside the main gate; that limits the reach of their defects but does not make
their results reliable.

Starting points were the differential harness, observation comparison, baseline
accounting, Lean trust checks, CI, and release reproducibility. I read the
implementation of `scripts/ci`, `coverage`, `diff-coverage`, `coverage-negative`,
`coverage-baseline-diff`, `coverage-cause`, the timeout wrapper, cap wrapper,
kernel replay, core audit, Lake check/comparator wrappers, relevant observation
code, workflow, and raft tools. I followed the raft assurance chain into
`raftharness`, derivation, and auxiliary instruments. No earlier review verdict
was used as a premise.

The coordinator owns the fresh full gate; this review did not run another full
build or corpus. Focused program runs and the derivation check used `capped`.
Probes and local Go build state were confined to this worktree's
`.tmp/deepclean-validation/`; no baseline, source, charter, shared dependency,
or machine-global setting was changed. Probe sources needed for reproduction
are included below, so scratch can be removed.

Priorities here are proposals: **P1** is a release-blocking trust-surface defect;
**P2** is a concrete defect to fix before promoting the affected tool or its
evidence; **P3** is documentation or reproducibility debt that can be explicitly
scoped out of a release. The coordinator may consolidate these with other
review findings.

| ID | Priority | Finding | Evidence |
|---|---|---|---|
| V1 | P1 | Negative corpus counts a killed/timed-out compiler as successful rejection | Unmodified runner, real frontend, injected exit controls; actual self-SIGKILL and actual timeout both publish PASS |
| V2 | P2 | `raftharness` reports all green when no scenario ran | Exact `main.go` compiled with a failing fixture scenario; typo, zero and negative iteration controls exit 0 |
| V3 | P2 | Raft probe accepts matching stdout from a machine that died by SIGKILL | Unmodified `runprobe.py`, subprocess controls, actual self-SIGKILL; runner exits 0 |
| V4 | P2 | Raft `--out` recursively deletes an existing directory without ownership checks | Unrelated scratch sentinel disappears even with `--keep` |

## V1 — P1: the negative oracle's process status is discarded

**Location:** `scripts/coverage-negative:310–324`. Contrast its frontend leg at
`248–285` and the positive runner's `undecided_cause` handling.

The negative runner checks whether `go build` succeeded. After any nonzero exit,
it forgets the exit code, searches the captured text for the case's expected
substring, and proceeds to the frontend leg. A successful frontend rejection
then publishes `PASS`. This treats an infrastructure death as a completed
compiler verdict whenever the process emitted a plausible diagnostic first.

This is an ordinary partial-output failure mode, not a requirement to defend
against a malicious compiler. In particular, the timeout wrapper correctly
distinguishes timeout and signal death, but this caller throws away precisely
that information. Memory pressure and interruption are explicitly relevant to
the shared build environment.

**Observed:** the real corpus case
`arrays/array-compare-different-length`, with the real prepared native frontend,
reported `cases=1 pass=1 fail=0` and runner exit **0** for oracle exits **2, 124,
137, and 143**, as well as the expected exit-1 control. A second probe made the
oracle process actually SIGKILL itself after writing the diagnostic, and made it
actually exceed `GO_TIMEOUT_SECONDS=1`; both still produced the same PASS.
The wrapper's timeout/signal behavior is therefore not merely inferred from an
arbitrary exit-code mock.

The diagnosis does **not** establish that any recorded real negative run was
killed. It establishes that a green result cannot exclude that failure mode.
The negative baseline pins result/stage only, so it cannot recover a discarded
status from a PASS row.

**Proposed repair:** retain `go build`'s exit code; only its deliberate compiler
rejection exit may proceed to the diagnostic and frontend checks. Timeout,
signal death, inability to execute, and other non-verdict exits need explicit
red classifications. Preserve the existing successful rejection check. A few
controls exercising a normal rejection, timeout-after-diagnostic, and
SIGKILL-after-diagnostic are sufficient; no new adversarial gate is needed.

**Acceptance:** each non-verdict control produces no PASS row and a nonzero
runner result, names its process cause, and cannot match the all-PASS negative
baseline. The real rejected case still passes.

### Reproduction

Run from the repository root after building the normal frontend, or use the
prepared `.tmp/nativefrontend`. This uses a scratch miniature root with symlinks
to the unmodified script and read-only corpus. The frontend build is replaced by
a copy of that prepared real frontend; only the compiler-oracle subprocess is
controlled. Nothing is written to the real `artifacts/` or corpus.

```sh
python3 - <<'PY'
from pathlib import Path
import os, shutil, subprocess, tempfile

root = Path.cwd()
scratch = root / '.tmp'
scratch.mkdir(exist_ok=True)
p = Path(tempfile.mkdtemp(prefix='negative-status-', dir=scratch))
try:
    for name in ('scripts', 'bin', 'tmp'):
        (p / name).mkdir()
    for name in ('coverage-negative', 'run-with-timeout.sh'):
        (p / 'scripts' / name).symlink_to(root / 'scripts' / name)
    for name in ('Corpus', 'baselines'):
        (p / name).symlink_to(root / name)
    (p / 'manifest.tsv').write_text(
        'arrays/array-compare-different-length\t'
        'Corpus/coverage/negative/compile/arrays/array-compare-different-length\t'
        'mismatched types\tarrays,comparability,compile_error\n')
    (p / 'bin/go').write_text('''#!/usr/bin/env python3
import os, shutil, signal, sys, time
args = sys.argv[1:]
if args == ['version']:
    os.execv(os.environ['PROBE_REAL_GO'], ['go'] + args)
if args and args[0] == 'build' and args[-1] == './tools/nativefrontend':
    shutil.copy2(os.environ['PROBE_FRONTEND'], args[args.index('-o') + 1])
    sys.exit(0)
if args and args[0] == 'build' and args[-1].startswith('./Corpus/'):
    print('main.go:4: invalid operation: a == b (mismatched types [1]int and [2]int)',
          file=sys.stderr, flush=True)
    mode = os.environ['PROBE_MODE']
    if mode == 'killed':
        os.kill(os.getpid(), signal.SIGKILL)
    if mode == 'timeout':
        time.sleep(10)
    sys.exit(int(mode))
sys.exit('unexpected probe invocation: ' + repr(args))
''')
    (p / 'bin/go').chmod(0o755)
    env = dict(os.environ,
        PATH=str(p / 'bin') + ':' + os.environ['PATH'],
        PROBE_REAL_GO=shutil.which('go'),
        PROBE_FRONTEND=str(root / '.tmp/nativefrontend'),
        TMPDIR=str(p / 'tmp'), GO_TIMEOUT_SECONDS='1',
        GOLEAN_COVERAGE_ARTIFACTS=str(p / 'out'))
    for mode in ('1', '2', '124', '137', '143', 'killed', 'timeout'):
        env['PROBE_MODE'] = mode
        r = subprocess.run(['capped', 'bash', str(p / 'scripts/coverage-negative'),
                            str(p / 'manifest.tsv')], cwd=p, env=env,
                           text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
        print('oracle mode:', mode, 'runner exit:', r.returncode)
        print(r.stdout)
finally:
    shutil.rmtree(p)
PY
```

## V2 — P2: `raftharness` has a vacuous-success path

**Location:** `raftharness/main.go:15–19,31–54`.

An unknown `-scenario` matches no entry. `-iters 0` or a negative value enters
no iteration. The driver checks only its failure counter, which remains zero,
and announces `raftharness: all green`. A typo or a computed zero-sized campaign
therefore looks like successful testing, even though the documented exercise
floors and safety checker never ran.

**Observed:** the exact tracked `main.go`, compiled with one fixture scenario
that always fails, returned:

| Arguments | Exit | Result |
|---|---:|---|
| `-scenario typo -iters 1 -seed 1` | 0 | all green; no scenario run |
| `-scenario basic -iters 0 -seed 1` | 0 | all green; no scenario run |
| `-scenario basic -iters -1 -seed 1` | 0 | all green; no scenario run |
| `-scenario basic -iters 1 -seed 1` | 1 | fixture failure reported |

The fixture controls the scenario body, not the driver under review. I also
attempted the full harness with project-local Go caches and network disabled;
it failed before execution because `google.golang.org/protobuf v1.36.11` is not
in the available module cache. Thus these are isolated driver results, **not**
a full raft campaign result.

**Proposed repair:** validate the scenario against the configured names,
require a positive iteration count, reject unexpected positional arguments,
and assert a nonzero number of completed runs before printing success. Report
the count in the conclusion. The checks belong in this driver, not in an
additional top-level gate.

**Acceptance:** typo, zero, and negative controls exit nonzero by name; a
selected real scenario runs and a deliberately failing fixture still fails.

### Reproduction without the unavailable protobuf dependency

```sh
python3 - <<'PY'
from pathlib import Path
import os, shutil, subprocess, tempfile
root = Path.cwd()
(root / '.tmp').mkdir(exist_ok=True)
p = Path(tempfile.mkdtemp(prefix='raft-main-', dir=root / '.tmp'))
try:
    shutil.copyfile(root / 'raftharness/main.go', p / 'main.go')
    (p / 'fixture.go').write_text('''package main
import ("context"; "fmt"; "time")
var scenarios = []struct {
    Name string
    Budget time.Duration
    Run func(context.Context, uint64) error
}{{"basic", time.Second, func(context.Context, uint64) error {
    return fmt.Errorf("scenario executed")
}}}
''')
    (p / 'tmp').mkdir()
    env = dict(os.environ, GO111MODULE='off', GOCACHE=str(p / 'cache'),
               GOTMPDIR=str(p / 'tmp'), TMPDIR=str(p / 'tmp'))
    subprocess.run(['capped', 'go', 'build', '-o', str(p / 'probe'),
                    str(p / 'main.go'), str(p / 'fixture.go')], env=env, check=True)
    for scenario, iterations in [('typo', '1'), ('basic', '0'),
                                  ('basic', '-1'), ('basic', '1')]:
        r = subprocess.run(['capped', str(p / 'probe'), '-scenario', scenario,
                            '-iters', iterations, '-seed', '1'],
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(scenario, iterations, 'exit', r.returncode)
        print(r.stdout)
finally:
    shutil.rmtree(p)
PY
```

## V3 — P2: raft evidence instruments ignore a failed machine process

**Locations:** `tools/raftsubject/runprobe.py:169–175,203–225`,
`codeccheck.py:753–775`, and `tracereplay.py:426–447`.

`runprobe.py` parses the final stdout line without checking the machine
process's return code. `codeccheck.py` rejects a failed process only when it has
no stdout. `tracereplay.py` does not retain the machine return code in its
resumable record. Consequently matching partial output from a crashed machine
can be presented as agreement.

**Observed:** an unmodified `runprobe.py` invocation with a successful oracle
control and a machine control that flushes the matching normal observation,
then **SIGKILLs itself**, exits **0** and prints
`runprobe: PASS — both oracles agree: 111035`. The killed program is a deliberate
subprocess fault control, not a claim that the real interpreter crashed.
The analogous `codeccheck.py` and `tracereplay.py` branches were inspected
statically; no long real raft campaign was rerun.

There is a related negative-mode weakness: `runprobe.py:129–140` interprets
every nonzero Go exit as an expected refusal/abort before validating any
process-level cause. A missing dependency or a killed oracle is not evidence
that a logger stub or runtime panic was reached.

**Proposed repair:** validate process exits before accepting stdout, preserving
the distinction between successful observations, deliberate modeled stops, and
infrastructure death. Store status in resumable trace records; a record that
never stored a status cannot certify successful execution. For negative probes,
check the intended terminal diagnostic and deliberate exit rather than generic
nonzero status. Reuse the existing main apparatus's process-status discipline
where practical, without turning these optional instruments into new gates.

**Acceptance:** partial matching output followed by SIGKILL is red; a normal
matching execution passes; intended negative probes still pass for their
actual terminal cause but fail for an unrelated compiler or process failure.

## V4 — P2: `--out` owns more than it creates

**Locations:** `tools/raftsubject/runprobe.py:109–110` and
`codeccheck.py:715–716`.

Both scripts recursively delete the user-supplied output directory before doing
the work. There is no marker, containment check, or refusal for unrelated
existing contents; deletion errors are suppressed. `--out` therefore behaves
as an undocumented recursive erase command. A mistaken parent directory can
remove other agents' artifacts or source. This is especially unsuitable for a
tool presented to someone who has just cloned the project.

**Observed:** a scratch directory containing `unrelated.txt` was supplied to
`runprobe.py --keep --out ...`. The command exited 0, replaced the directory
with its program tree, and the unrelated file was gone. `--keep` ruled out
end-of-run cleanup as the cause; the deletion happens before the run.
No non-scratch directory was used in the experiment.

**Proposed repair:** create a unique child work directory under the chosen
output root, or refuse an existing nonempty directory unless it contains an
unambiguous ownership marker for this tool. Delete only that owned child.
Report failed cleanup instead of silently swallowing it. A refusal for a
nonempty foreign directory and one normal repeat-run test are enough.

**Acceptance:** a foreign sentinel survives, the command either refuses by
name or writes solely to its own child, and normal automatic cleanup removes
only material that invocation created.

### Shared reproduction for V3 and V4

This invokes the real Python driver with three tiny subprocess controls. The
machine prints a matching result and then actually dies by SIGKILL. It does
not exercise raft semantics. All directories and deliberate deletions are
confined to a newly allocated `.tmp` subtree.

```sh
python3 - <<'PY'
from pathlib import Path
import os, shutil, subprocess, tempfile
root = Path.cwd()
(root / '.tmp').mkdir(exist_ok=True)
p = Path(tempfile.mkdtemp(prefix='raft-status-', dir=root / '.tmp'))
try:
    (p / 'go').write_text(
        '#!/usr/bin/env python3\nimport sys\nprint("111035", file=sys.stderr)\n')
    (p / 'frontend').write_text(
        '#!/usr/bin/env python3\nimport pathlib,sys\n'
        'pathlib.Path(sys.argv[sys.argv.index("--out")+1]).write_text("{}")\n')
    (p / 'golean').write_text('''#!/usr/bin/env python3
import os, signal
print('{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":111035}]}', flush=True)
os.kill(os.getpid(), signal.SIGKILL)
''')
    for tool in ('go', 'frontend', 'golean'):
        (p / tool).chmod(0o755)
    out = p / 'existing-output'
    out.mkdir()
    sentinel = out / 'unrelated.txt'
    sentinel.write_text('review sentinel\n')
    env = dict(os.environ, PATH=str(p) + ':' + os.environ['PATH'],
               PYTHONDONTWRITEBYTECODE='1')
    r = subprocess.run(['capped', 'python3', 'tools/raftsubject/runprobe.py',
                        '--keep', '--out', str(out),
                        '--frontend', str(p / 'frontend'),
                        '--golean', str(p / 'golean')], env=env,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print('runner exit:', r.returncode, 'foreign file survives:', sentinel.exists())
    print(r.stdout)
finally:
    shutil.rmtree(p)
PY
```

## Scope and reproducibility debts

These are separate from the reproduced defects. They should enter the release
limits or a modest repair task; the evidence does not justify claiming a new
semantic failure.

1. **The raft subject's source and the convenience checkout have different
   pin policies.** `scripts/setup-deps:88–103` deliberately floats `deps/raft`;
   `raftharness/go.mod` uses that directory through a local replacement. The
   derived subject is read against `56e32004b1af3a4cb625fbfe5dbca24fb6023d09`.
   Current local `deps/raft` is `638f42739b77572b5708eb0d8a776a272ade71ed`.
   Importantly, `derive.py:2389–2406` checks each source digest before writing;
   the current derived tree passed that check despite the revision difference.
   A fresh setup cannot promise the same concurrent raft reference or even a
   successful regeneration against a future floating checkout. Pin the
   executable reference or make its explicitly floating status prominent.

2. **The main gate is narrower than the family of raft instruments.**
   `scripts/ci:390–395` runs nativefrontend, lowerdiag and coverageharness Go
   tests. It does not run `raftharness`, the derived-code upstream differential,
   or the long raft semantic probes. `check-frontend-pins` compares the assembled
   twin's lowered wire; it does not execute the twin. The toolkit README
   explicitly says these instruments are outside `scripts/ci`. That separation
   is legitimate if release readers can see it: a green gate is not a fresh
   raft end-to-end result. If such a result is claimed, rerun the relevant
   instrument after repairing V2/V3 and state its exact schedules and budget.

3. **Retired proof tooling still appears executable and supported.**
   `tracereplay.py:400–418,473–476` advertises a verified fast engine and defaults
   to `proofs/.lake/build/bin/fastreplay`, while the source and transfer theorems
   it cites are no longer in this product. Remove the obsolete route, or
   identify an external compatible producer and the exact version contract.
   It should not remain an unexplained default path in a live tool's help.

4. **The standalone raft instruments do not apply the cap or main runner's
   timeout/status policy themselves.** Their README says they are uncapped,
   while some documented runs take tens of minutes. Use an explicit outer cap
   under this box's rules; for release documentation, state this cost and apply
   the project `cap` convention where it can be reused simply. This review ran
   no unbounded real raft campaign.

5. **Observation parsing has a separately reproduced strictness gap.**
   `GoLean/CLI.lean:983` uses `Json.parse` for `observation-eq`; duplicate
   `status` keys with an earlier refusal and a later `ok` compare equal to the
   plain `ok` object (exit 0). The frontend/CLI review owns this finding and its
   additional Unicode control. I do not count it twice here or claim current
   corpus emitters produce duplicate keys.

## What held, and the limits of this review

- The positive differential runner explicitly handles timeout, signal death,
  undecided comparisons, missing observations, and empty enumerations. Its
  comments and implementation distinguish membership evidence from proof that
  every modeled behavior is Go-realizable. V1 is a concrete asymmetry in the
  negative lane, not a conclusion that every runner has the same hole.
- Baseline causes are derived before comparison; the positive result reader
  refuses duplicate IDs and malformed row shapes. Full comparisons require
  baseline presence. Cached and partial fast-tier results are visibly captioned
  in `judge_record`; they are not presented as new corpus executions.
- The kernel-replay wrapper compares source, on-disk olean, and replayed module
  sets and checks checker status. Core audit enumerates modules recursively and
  checks their declaration closure. The reviewed code has substantive trust
  checks beyond a successful build. I did not independently establish their
  complete correctness, run a separate replay, or prove any theorem here.
- The Lake check/comparator wrappers report sandbox mode and checker failure,
  and the project's release procedure distinguishes these from the owner's
  claim-point run. This review supplies no outside-sandbox or paranoid result.
- `TMPDIR=<own scratch> PYTHONDONTWRITEBYTECODE=1 capped python3
  tools/raftsubject/derive.py --check` completed with exit **0** and a clean
  derivation comparison. It also visibly reported the upstream revision
  difference discussed above.
- The full `raftharness` execution attempt failed with
  `module lookup disabled by GOPROXY=off` for protobuf v1.36.11. No network
  fetch, shared-cache modification, or substitute dependency was attempted.
  The isolated CLI controls do not certify raft's safety properties.
- No browser-dependent hosted CI observation, fresh-clone network setup,
  external consumer repository, full codec differential, or long trace replay
  was reached. No claim is made that those surfaces are clean.

The proposed repair order is V1 first, then the comparator strictness finding
owned by the frontend review, then V2/V3 before citing fresh raft evidence, and
V4 before encouraging arbitrary output-directory use. Release notes should
separate the main corpus, the wire pin, historical raft experiments, and the
remaining optional instruments. The defects above are left unfixed in accordance
with this review's read-only product scope.
