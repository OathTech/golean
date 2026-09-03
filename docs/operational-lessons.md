# Operational lessons — build, memory, and tool incidents (measured remedies)

Moved out of CLAUDE.md at the W0 landing (2026-08-27): the charter
states rules; this file holds the incidents that earned them and the
measured remedies. Add entries incident-first: what happened, what
was measured, the remedy. (Agent-guidance style: incident-derived
lines only — the BRiCk lesson.)

## Memory: every lake/lean invocation goes through scripts/capped

A `by decide +kernel` on a FALSE proposition reached 60 GB in ~2 min
and killed the session twice (the OOM killer's badness score picks
the multiplexer). The cause was a false goal, not an expensive one —
with the fuel bug fixed the same line checked in 1.2 s. Habit:
`#eval` the Bool before asking the kernel to prove it. Two caps that
DON'T work, measured: `lean -M` is not enforced during kernel
reduction (VmRSS 4953 MiB at t=10s under `-M 4096`, no diagnostic);
`prlimit --as` kills Lean spuriously (address space reserved per
thread). RSS via cgroup (`systemd-run --user --scope` +
`MemoryMax`) is the only honest knob. The cap is a blast radius,
not a budget.

## The cap without the bus: cgroup-direct placement (2026-09-01)

INCIDENT. After a session relaunch under a nono sandbox profile that
did not grant the systemd user-bus socket (`/run/user/$UID/bus`),
`scripts/capped` — then built on `systemd-run --user --scope` — failed
closed everywhere at once (`Failed to connect to bus: Operation not
permitted`, exit 4): every gate, every worker's build, the fuzz
campaign. Diagnosis by `nono why --profile claude-local --path
/run/user/1000/bus --op write` → `path_not_granted`. The process's
`snap.zellij` AppArmor label was a red herring (complain mode; the
user's own shell inside zellij reached the bus fine). Granting the bus
to the sandbox had been tried and rolled back in the sibling
cerberus-lean project (profile history 1.9–1.11).

REMEDY ([USER]-directed port of cerberus-lean's `scripts/capped`,
mainline `bbdbacaff`). The cap never needed systemd: under cgroup v2
delegation (`user@.service`, `Delegate=yes`) the process's PARENT
cgroup (`app.slice`) is writable by the user and has the memory
controller enabled for children. `scripts/capped` now creates a
SIBLING child cgroup there (the same shape `systemd-run` would make),
writes `memory.max` + `memory.swap.max=0`, migrates itself in, and
RE-ENTERS ITSELF — so the existing readback (`GOLEAN_CAPPED=1` →
prove `memory.max` → `=verified`) certifies the cap exactly as before;
placement changed, verification did not. `systemd-run` remains the
fallback when cgroupfs isn't writable; an unavailable cap is still an
error (exit 4/127), never a silent uncapped run. New: a KILLED banner
on exit 137/143 (a cgroup kill must shout — the sibling project's
tail-pipe/exit-code misreadings earned it).

SANDBOX PREREQUISITE (the one grant): filesystem write under
`/sys/fs/cgroup/user.slice/user-$UID.slice/user@$UID.service/app.slice`
(nono profile `claude-local` 1.13.0). Narrow: cgroupfs writes within
the user's own slice only. GOTCHA: `nono why` without `--profile
<name>` evaluates the default profile and reports the slice DENIED even
when the live one grants it — always pass `--profile claude-local`.

VERIFY after any change (seconds each):
  GOLEAN_MEM_MAX=32G scripts/capped cat /proc/self/cgroup
      # ends in .../app.slice/capped-<pid>-<ts>
  GOLEAN_MEM_MAX=32G scripts/capped env | grep GOLEAN_CAPPED   # =verified
  GOLEAN_MEM_MAX=256M scripts/capped python3 -c 'x=bytearray(1<<30)'
      # must die: exit 137 + the KILLED banner
  scripts/capped sh -c 'exit 42'; echo $?                        # 42
All four measured green at the port (2026-09-01), plus: no leftover
`capped-*` cgroups after runs; `GOLEAN_MEM_MAX=64GB` refuses (exit 2);
`none` still warns.

## Concurrency OOM: threads × per-module peaks, not single modules

Full parallel builds of trees with heavy modules breach any sane cap
via AGGREGATE RSS (measured: 6–8 concurrent window-kernel modules
breached 96 G; per-module peaks modest; kills present as exit 143 —
kernel SIGKILLs a worker, systemd SIGTERMs the scope — mimicking an
external killer; two units chased a phantom "reaper"). Remedies,
measured: sequential warm (per-Audit-root explicit targets at
LEAN_NUM_THREADS=2) then the full build at scaled threads; cold
worktree full builds need 64G+; `scripts/ci` scales
LEAN_NUM_THREADS to the cap (honors an explicit caller value).
Diagnose kills with `systemctl --user show <scope> -p Result` —
`Result=oom-kill` settles it in seconds; check timestamps before
believing a failed-units list (stale entries linger until
reset-failed).

## The box-wide build lock

Two capped builds from different lanes over-committed the 125 G box
and the OOM killer took the session. FULL builds/gates are exclusive
box-wide: `mkdir artifacts/build-lock.d` (atomic; owner file;
trap-protected release; wait-retry 120 s). Explicit-target builds
≤48G are exempt. Takeover of a stale lock requires evidence (age +
zero running builds), logged.

## Masked kills and artifact-less verification

Piping compiler output through `grep|head` swallows cgroup kills —
mid-unit "greens" were SIGTERMs. Judge every build by its CAPTURED
EXIT CODE (`> log 2>&1; echo EXIT=$?`), never by absence of grepped
errors. And `lake env lean` produces NO oleans — it verifies but
caches nothing; cache-warming verification uses `lake build
<target>`. An interface-hot edit owes a sequential warm before any
full build.

## The comparator-judge Solution build

The judge's confined unit does a fresh-clone cold build; after the
proofs tree grew, that build breached the box (122.8 G peak,
swap-thrash). Remedy (wrapper-side, trust-neutral — the confined
unit still exports and kernel-replays everything): pre-build the
Solution closure in the clone, sequential warm then scaled full
build, alongside the existing Challenge/core pre-builds. External
trust tools stay pristine; version skew is resolved by user-chosen
pins (the landrun cli-v2 window incident: the working pin
self-reports the wrong version — identify with `go version -m`).

## CI runners and caps

A runner VM that dies uploads no logs and saves no cache —
"disposable, let it die" is the wrong frame. CI wraps gate steps in
SYSTEM-scope cgroup caps and PROVES the cap via readback
(`GOLEAN_CAPPED=1` + size; `scripts/ci` refuses if the kernel
disagrees).

## Diagnosing async results

A backgrounded job that buffers can show empty stdout mid-run —
check the artifact it writes, not stdout. A Workflow `<failures>`
line is a single branch, not the run: read the journal and the
usage counts before reporting failure; say what survived. (Recorded
because it misfired twice; the same discipline applies to
infrastructure theories — the phantom-reaper incident survived two
units because nobody ran the mundane systemctl check.)

## Desugar coupling: helper lemmas married to the compiler's do-elaboration

The U0 toolchain bump (Lean 4.31→4.32.2, 2026-08-28) had to edit
PROOF-LAYER STATEMENTS, not just proofs: ~9 helper lemmas
(`setLoopG`, `scan_generic`/`scan_genericV`/`scan_genericW`,
`forIn_find_none/some`, Lens `setLoop`, DriftApply/DriftOps sim
`body :=` arguments, FastEval `show`-terms) are stated against the
LITERAL packing of the do-desugar — loop-state tuple type/order,
junk `pure PUnit.unit` binds, trailing `let x ← e; pure x` — and
the 4.32 elaborator changed all three (MProd→Prod in declaration
order; junk binds gone; trailing binds kept in compiled functions
but COLLAPSED in hand-written `show` terms, forcing explicit
`>>=`). Measured blast radius this bump: 24 files (2 core + 22
proofs). Lesson: any lemma whose statement names the compiled
shape of a `for`/do-block is TOOLCHAIN-COUPLED — expect statement
edits at every Lean bump, budget them, and prefer stating over a
named function (the `setLoopG` idiom) so the coupling is one
definition per loop rather than scattered patterns.

## Sandbox conventions

Repo-local caches for ad hoc Go probes (`GOCACHE=$PWD/artifacts/…`);
`/tmp` may be write-only under the profile (nono
`insufficient_access` on read) — keep scratch in `artifacts/`. On
any sandbox denial: stop and hand the user exact commands; never
vendor or copy around restrictions. Do not `rm -rf` scratch dirs
without approval.

## Huge array types: a native stack overflow presented as a process abort

`golean` on issue34395's `[100<<20]byte` global died with exit 134
("Stack overflow detected. Aborting.") — a fail-noisy abort, but not a
cause-naming refusal (the gotest-triage INFRA note, 2026-09-01, which
mis-described the program as "deep recursion"; the recursion was the
normalizer's over the array's elements). Remedy (BUG-078): the wire
decoder refuses array TYPES past `arrayLenBudget` (GoLean/
NativeToIR.lean) by name — every array type flows through that one
decode; runtime-length allocations are slices, which normalize by
reference (probed: `make([]byte, 100<<20)` grinds but never aborts).

MEASURE THE PATH THE BUG NAMES (audit fix round 2026-09-01): the first
budget, 1<<20, was derived from numbers taken on the DEFAULT-VALUE path
(`var a [N]byte`, `Array.replicate` — linear: 0.06 s at 1<<20), but
the pathology BUG-078 names is the element-wise normalize
(`normalizeListWith`, GoLean/GoCore/Ops.lean — non-tail recursion +
quadratic `#[h] ++ t`), reached by the LITERAL initializer
(`var a = [N]byte{42}`) and by an ELEMENT STORE into a default array
(`a[0] = 42`) — both QUADRATIC: 0.13 s at 10^4, 2.7 s at 5×10^4,
5.0 s at 1<<16, 11.4 s at 10^5, 20.5 s at 1<<17, 46 s at 2×10^5,
224 s at 4×10^5 (auditor), ≈25 min extrapolated at 1<<20 — against
the gate's 30 s per-case wall (`LEAN_TIMEOUT_SECONDS`). The 1<<20
budget therefore admitted shapes that could only die as wall-clock
kills. Re-derived budget: 1<<16 (≈5–5.5 s worst flat path, >5×
margin; 500× the largest corpus array type, 128). The budget is a
PER-TYPE FLAT bound, not a value-size bound: nested
`[1024][1024][128]byte` is admitted and its default value is cheap
(1.1 s, persistent-array sharing), but ONE element store into it
measured 46 s (the store re-normalizes through the nesting) — a
recorded residual, honest wall-clock kill, lifted with the owed
linear normalize. Lesson: a budget's docstring states WHICH path
each number was measured on; a number without its path is not a
derivation.

## ARG_MAX is a cliff whose height is set by TMPDIR length; one dead fan-out must not look like N dead workers

`scripts/diff-coverage` fanned rows out as `ls "$ROWDIR"/*.in | xargs
-P N …`: the glob expanded inside bash but reached `ls` as ONE execve
argument vector. Linux bounds that vector by ARG_MAX (2 MiB here,
`getconf ARG_MAX`; strings + NUL + an 8-byte pointer each, environment
included), so the runner had a hidden row ceiling that MOVED WITH THE
LENGTH OF TMPDIR: 19,999 rows under a 130-byte TMPDIR is ~3.5 MB of
argv and died `ls: Argument list too long` (grossmith campaign,
2026-09-02, verified by its auditor; red-first record
`docs/evidence/2026-09-02_diffcov-argmax/`); main's 2,526 rows at this
box's 68-byte per-file paths were ~190 KB (2526 × 77 B) — safe by accident: the
cliff is 11,817 rows at a 130-byte TMPDIR (168-byte per-file paths;
bisection, the evidence dir's mechanism.log) and ≈27k at 68 bytes
(27,235 by ARG_MAX/(path+1+8); 27,166 measured at the audit), and nothing checked either
number. Three fail-open behaviours composed on top: GNU xargs
without `-r` runs its command ONCE on empty stdin, so `run_case ""`
FABRICATED a manifest-error row for id "" and mv'd a stray `.out` into
the repo root; `|| echo WARNING` absorbed the pool's exit; and the
assembler wrote `FAIL <id> … worker produced no result` for every row
and PUBLISHED them — a single global failure attributed per case,
row-for-row indistinguishable from 19,999 independent worker deaths.
Remedies: never pass a file list through execve — `find -print0 |
xargs -0 -r` streams it; capture every pipeline status (`PIPESTATUS`)
and record it in the meta rather than discarding it; and make the
assembler tell "NO row has a result" (one infrastructure failure: exit
2, nothing published) from "SOME rows have none" (per-row fail-closed
rows). Lesson: a per-case fail-closed row is only honest when the
failure was per-case; a global failure rendered as N local ones is a
misattribution, and an `xargs` without `-r` is a fabrication waiting
for an empty pipe. Fixture: `scripts/test-lane-validation` G5.

## A killed command has decided nothing: timeouts must name themselves

`run_with_timeout` in `scripts/diff-coverage` exits 124 silently, and
four of its consumers read the killed command's EMPTY capture as a
verdict (noodler-lane finding, confirmed by its auditor, fixed
2026-09-03): the strict-lane Lean run reported `lean-observation:
expected status ok, got ` (nothing after "got"); the oracle-invariance
re-run reported "observation varies with iteration order" with
`variant=` empty; the membership driver-coupling pin reported
"copied-driver drift"; and the Go-sample membership loop raised the
too-narrow soundness alarm — one cause-blind, three cause-WRONG, all
of them fail-closed (a timeout never passed) and therefore invisible
as defects until someone read a detail column. The three enumerator
paths already did it right ("enumerator TIMED OUT after Ns …"), which
is how the rest were caught. Remedy: every consumer tests exit 124
BEFORE it reads the capture, and reports at the stage of the check
that could not complete with `… TIMED OUT after Ns (<KNOB>) — <what
was NOT established>` (stage words unchanged — the strict run stays
at `lean-observation` because `tools/reconcile-records` and
`scripts/check-bugs.sh` count that stage as fidelity-bearing and
`lean-run` would have left the ratchet); `lean observation-eq` moved
behind `obs_eq`, whose 124 is distinct from "not equal"; and the alarm
handler announces itself on stderr so a `2>&1` capture carries the
cause even in a consumer that forgets the test. Lesson: a fail-closed
path can still lie about WHY; a wrapper that returns a bare exit code
delegates the naming to every caller, and every caller that reads
"$output" before "$?" will attribute the silence to whatever it was
checking. Test it by forcing the kill: `scripts/test-lane-validation
--with-go` T1-T4 run the real runner from a fake root whose `golean`
shim `exec sleep`s on exactly one targeted call under a 1 s budget
(red-first record: `docs/evidence/2026-09-03_timeout-cause/`).
RESIDUAL (audit F1 on the fix, 2026-09-03; DISCHARGED the same day on
branch `runner-exitcode`): the first slice named only 124. Three other
non-verdict exit codes were still read as verdicts — `observation-eq`
exit 2 (runObservationEq's undecodable-observation refusal,
GoLean/CLI.lean) as "not equal" by every `obs_eq` caller, with
`obs_eq`'s `>/dev/null 2>&1` discarding the decode message; 137/143
(SIGKILL/SIGTERM through the wrapper's `128 + signal` — a cgroup/OOM
kill, or scripts/capped's) as "not equal" by `obs_eq`, as `expected
status ok, got ` (empty) on the strict Lean-run path, and as "expected
Go panic, got: " (empty) through `go_run_oracle`. Same fix shape as
124's: `undecided_cause` / `signal_cause` / `obs_eq_cause` in
`scripts/diff-coverage` classify the code BEFORE the capture is read —
0 and 1 are the only verdict codes (equal/not-equal; ok/error
observation; go run green/red), 124 is the wall clock, 137/143 and any
other 128+n are `KILLED (exit N — …; did not decide)`, exit 2 from the
comparator is `could not decode the observation (exit 2 — did not
decide; comparator said: <decode message>)` (obs_eq now keeps the
comparator's stderr in `OBS_EQ_STDERR`) — except at the two SELF-
comparison sites (`obs_eq "$go_observation" "$go_observation"`), where
exit 2 IS the decision and the accurate `Go output is not a valid
observation` wording stays, now with `(comparator said: <message>)`
(audit F1 on this slice) — and any other code is `failed with exit N
(did not decide)`. Stage words, budgets, criteria and the
baseline are unchanged (ci --diff: 3195/3195 rows, zero drift — so no
real did-not-decide had been hiding under a labelled failure). The
three enumerator sites, lake build, harness generation and both native
exports name 137/143 too (`signal_cause` only: `go run` collapses every
child exit — a panic, the harness's os.Exit(2) — to 1 with a trailing
"exit status N" line, and only a `go` tool usage error yields 2, so
codes 2..128 there are a tool's refusal with its message, not a kill;
audit F2 corrected the first draft's "the harness exits 2" claim). runObservationEq's codes are documented,
not changed. Fixtures T5-T8 (`scripts/test-lane-validation --with-go`;
red-first record `docs/evidence/2026-09-03_runner-exitcode/`): a
genuine exit 2 from the real comparator, a `kill -9` on the strict
Lean run, a `kill -TERM` on the differential-stage comparison, and a
fake `go` that `kill -9`s itself on the oracle call. Second lesson,
caught red by T7 during the fix: a classifier's exit status must be
the classification and nothing else — `[[ -n "$stderr" ]] && printf`
as the LAST line of the namer returned 1 on an empty capture, and a
SIGTERM (which leaves no stderr) read as a verdict again.

## An exact-match guard on a two-valued oracle is a coin-flip gate

`scripts/coverage-baseline-diff` compares `RESULT/stage` per row exactly,
and one red row's STAGE is decided by gc, not by the machine:
`channels/select-select/beside-loop` returns 5 or 90 in gc; the strict
lane's differential check runs before the oracle-invariance re-run and
returns early, so gc=5 gives equality then `FAIL/nondet` (the adversarial
streams hit the refusal) while gc=90 gives `FAIL/differential` (Lean=5,
Go=90). The pinned row said `nondet`; a full `ci --diff` therefore drifted
on that one row on whichever runs gc sampled 90 — a red that was FAIL
either way, reported as a regression. Remedy ([USER] ruling (a),
2026-09-03, a gate change — quote relayed by the [AGENT] coordinator,
primary record `docs/assessment/decisions-2026-08-31.md` 2026-09-03
addendum): the row's stage column carries the set
`nondet|differential`, matched by membership, RESULT still exact, with a
`# reason:` comment naming the mechanism; the form is refused (exit 2)
on a PASS row, on an unknown stage word, or without the reason line, and
every other stage-column consumer either handles the set or fails loudly
(`check-bugs.sh` (6), `reconcile-records` C1); the re-pin guard checks
the alternation SURVIVES a regeneration (`scripts/check-alternation-survival`),
because no column-3 reader existed among the guards. Two lessons from the fix
itself: (a) gawk exits 2 on its OWN fatals (an unreadable input), so a
script that means "exit 2 = refused" must give the awk refusal a distinct
code (3) or an I/O failure reads as a record refusal; (b) under
`set -euo pipefail`, `printf | grep '^REFUSED' | sort` with no match kills
the script at exit 1 before the intended `exit 2` — the refusal path
itself needs `|| true`. Both were caught by running the fixtures, not by
reading the code. Red-first record: `docs/evidence/2026-09-03_guard-stage-alt/red-first.txt`;
fixtures `scripts/test-lane-validation` Part A4.
## A sampling budget is a claim about the caption, not the verdict: make it a recorded number and put the perturbation first

The membership lane's Go-side budget was an implicit 10 (`samples=5`,
drawn as 5 plain `go run` then 5 under `-race`) and the PASS caption
said `exhibited=E` as if that were the oracle's support. Two 80-draw
runs (`docs/2026-09-01_membership-depth.md` §4.2) showed the order was
the worst possible for a small budget: on the scheduling rows plain
`go run` is a point-mass and every late member came from `-race`, which
the gate order reached only at draw 6 — 6 of 22 ten-draw rows captioned
`exhibited=1` for a row the oracle demonstrably moves on, and saturation
of two-member rows took up to 52–66 alternating draws when it came at
all. Remedy ([USER]-ruled 2026-09-03, memo §4.3 / P2, implemented on
`sampling-budget`): alternate plain/`-race`; stop early when the
distinct observations reach the row's `members=` pin; otherwise stop at
K, with K set by RUN MODE (32 on the gate path, 80 under `--slow`) and
printed in the run header + `latest.meta.tsv`; report `draws=` beside
`exhibited=` so the budget spent is a recorded number, never an implicit
default. Distinctness is decided by the comparator, and an undecided
comparison (timeout/kill/exit 2) fails the row as "saturation NOT
decided" — the cause-naming discipline of the entry above applies to
the stopping rule too, or a killed comparator would read as "new
observation" (an early stop that never fires) or as "repeat" (a
saturation the oracle did not show). Two lessons. (1) A budget that
lives only in a per-row default is invisible to the reader of the
result; make the spent budget part of the caption and the cap part of
the run's provenance. (2) When a per-row param stops being read by the
code (`samples=` here), REFUSE it by name in both the manifest and the
harness rather than accept-and-ignore: an author who writes
`samples=20` expecting more draws would otherwise get a green row and
nothing. The rule cannot flip a RESULT — membership PASS/FAIL is "every
draw ∈ the enumerated set" and the baseline stores result/id/stage
only — which is what made it a caption-honesty change rather than a
baseline re-pin; measured cost and the before/after exhibition table:
`docs/evidence/2026-09-03_sampling-budget/`. Audit follow-up (F1, same
day): the first cost reading blamed the draws; the real critical path
was a per-(draw, member) comparator spawn in the membership check with
no memo — a 300-member row whose gc observation is member #124 went
from ~248 to ~3,968 `observation-eq` processes (1:57 for one row), and
the retired `samples=1` turned out to have been an unstated cost cap on
exactly that loop. Lesson: when a budget rises by 3× and the wall
rises by 3×, check what ELSE scales with the budget before attributing
the cost to the budgeted thing; and a per-row knob that "happens" to
keep one row cheap is a hidden cost cap — name it or remove it.
