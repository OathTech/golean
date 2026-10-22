# Operational lessons — build, memory, and tool incidents (measured remedies)

Moved out of CLAUDE.md at the W0 landing (2026-08-27): the charter
states rules; this file holds the incidents that earned them and the
measured remedies. Add entries incident-first: what happened, what
was measured, the remedy. (Agent-guidance style: incident-derived
lines only — the BRiCk lesson.)

## Memory: every heavy invocation goes through `cap` (the box tool when present)

**Since 2026-10-21 the cap is detected, never shipped** (box-independence,
release-readiness row 46; [USER] 2026-10-21, paraphrased: the project must
build and check on an ordinary machine with the documented commands and no
extra setup; `capped` is box tooling, used through the function
`cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }`
and sized by `CAPPED_MEM_MAX`, never `-m`; where it is absent the build runs
uncapped, silently; `scripts/capped` goes). `scripts/cap.sh` defines `cap`
and the thread derivation (`LEAN_NUM_THREADS` = cap/8G, floor 2, from
`CAPPED_MEM_MAX`, default 32G — the box default, kept as the project's
choice with or without the tool); every gate script sources it and runs its
heavy commands through `cap`; `scripts/ci` no longer re-execs itself through
a wrapper, and prints the cap in force as its first note. The former shim
`scripts/capped` (its fallback body a near-copy of the box tool) is gone,
with the names `GOLEAN_MEM_MAX` and `GOLEAN_CAPPED`. The one measured reason
to raise the limit: a COLD full build / cold `scripts/ci` in a fresh
worktree needs 64G+ («Concurrency OOM», below) — `CAPPED_MEM_MAX=64G
scripts/ci`, said where it is run; `scripts/ci` prints that note itself when
it sees a cold tree under a small cap. The box-wide build lock (below)
stays. (2026-10-11 to 2026-10-21 the shim translated the legacy names onto
the box tool, after `capped scripts/ci` had re-wrapped itself into a sibling
cgroup at 64 G and silently escaped the certified 32 G; before that the
project wrapper below WAS the cap. The history is kept as written; the box
tool was ported from it. The full account of the 2026-10-21 change:
«Box-independence», at the end of this file.)

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
SYSTEM-scope cgroup caps and PROVES the cap via readback: the in-scope
shell reads its own cgroup's `memory.max` and refuses (exit 3) if the
kernel says `max` (the readback moved from the project wrapper into the
workflow when the wrapper went, 2026-10-21); the size goes in as
`CAPPED_MEM_MAX`, which sizes `scripts/ci`'s thread pool. A runner has
no `capped`, so the gate's own steps run bare inside that scope.

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
without approval. INCIDENT (2026-09-04, lane `c-arc-gu`, [AGENT]): a
`sort FILE > /tmp/x && mv /tmp/x FILE` chain, routed through `/tmp`
against this rule, DESTROYED three evidence dump copies — the redirect
was denied, but zsh ran the `mv` anyway and a cross-device `mv` whose
source it cannot read had already unlinked the destination. The copies
were regenerated from the intact `artifacts/` runs (the auditor
re-verified the regeneration byte-for-byte); the lesson is the rule
above, plus: never `mv` over a file you cannot regenerate, and keep
sort scratch beside the output (`sort -o FILE FILE` needs no scratch).

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
2026-09-03, a gate change — relayed by the [AGENT] coordinator,
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

**Addendum (2026-09-04, lane `flaky-panic-wait` [AGENT]): a deferred
`Done` (or any wake) in a PANICKING goroutine makes the oracle
schedule-dependent — membership lane, never strict.** The deferred call
runs during the unwind and wakes main; main can print and exit 0 before
the runtime's `exit(2)` lands (gc: printed-then-abort 52/280 under
`-race`, exit-0 seen once under gate load). The machine already admits
both members (`l5ExitWindow` + the B1 post-op boundary), so the row, not
the semantics, was the defect: `noodler/goroutines/goroutine-panic-
under-wait` re-laned to `membership members=2 statuses=ok+panic` (the
`goroutines/wake-then-abort` precedent) with a deterministic no-Done
twin pinning the unconditional panic
(`docs/evidence/2026-09-04_flaky-panic-wait/`).
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

## A cached certification is owed a re-run the moment the wire schema moves — and the cache key cannot tell you when the machine moved

The one `tier=slow` row (`imported-goose/channel/google-search`,
`engine=dedup`, members=6) carries CERTIFIED-CACHED standing on the
gate path: `scripts/ci --diff` replays the tracked record in
`baselines/certified/` after checking its wire sha and params, and
only `scripts/ci --slow` re-enumerates. Between 2026-09-01 and
2026-09-04 thirteen commits moved the wire schema (exact-key
discipline, make-map `hint`, `atomic-op`, stdlib source-through,
`sync-op`/TryLock, …) and `tools/reconcile-records` C9 said so on
every gate ("the wire schema moved after the certification date") —
three days of a MEDIUM that nobody discharged, while the fast gate
stayed green because THIS fixture's wire bytes happened not to
contain any of the moved node kinds (its sha never went STALE). Two
lessons. (1) **The rule: any wire-schema move ⇒ C9 fires ⇒ run
`scripts/capped scripts/ci --slow` at the clean tip and refresh the
record BEFORE the next claim that leans on the cached set.** The
discharge is cheap — the 2026-09-04 re-cert was 709 s wall for the
whole `--slow` gate on the loaded shared box (the dedup enumeration
is ~160 s of that) — so there is no cost argument for letting C9
stand; the reason it stood was that a report-only MEDIUM reads as
someone else's problem. It is the slice's problem that moved the
wire. (2) **The wire sha is a key for the PROGRAM, not for the
MACHINE.** It detects a frontend change to this fixture's emit and
nothing else: an interpreter change (a new `GoCore` op, a scheduler
boundary, a stamp) can move the enumerated set with the sha
bit-identical, and the fast gate's four driver-coupling runs sample
that surface, they do not close it. So "the cached row's sha still
matches" is never an argument against re-certifying; only the fresh
enumeration is. A same-day subtlety, recorded so the next re-cert
does not trip on it: C9 tests `git log --since <certified>` over the
wire files, and `--since` on a bare date means midnight — a re-cert
run on the same calendar day as the last wire commit would leave C9
firing on a current record. The header therefore carries the run's
full ISO instant (`# certified: 2026-09-04T01:02:30+00:00  commit:
…`), which both the harness (`sed 's/^# certified: //'`) and the
reconciler (`(\S+)\s+commit:`) already accept. Evidence and the K=80
exhibition table: `docs/evidence/2026-09-04_slow-recert/`.

**Addendum (2026-09-04, second re-cert the same day — the re-cert is a
standing post-train step, not a one-off).** The 01:02 re-cert cleared
C9 for exactly one merge train. The round-11 train (hygiene A3/A4/A8,
fr22-fr23 + its audit round, lower-diagnose) landed five more commits
to `wire.go`/`NativeToIR.lean` by 16:40Z and C9 fired again on the
very next gate; the second re-cert (`slow-recert-2`, run 17:24Z at the
clean tip aceb0dcb, 516 s wall under a 1-min load peak of 54 —
dedup set AND graph reproduced bit-for-bit, wire sha still 2f1d639f)
is recorded in `docs/evidence/2026-09-04_slow-recert-2/`. Two
observations. (a) **C9 re-fires after EVERY frontend-touching round**,
because `NativeToIR.lean` is on nearly every semantics slice's path
(three of the five round-11 commits were machine-side refactors —
payload cells, address-free globals — that touched the decoder without
changing a wire byte). Treating the re-cert as a lane someone spawns
after noticing the MEDIUM means the record is stale for the whole
window between the train and the noticing; twice today that window
was long enough for other lanes to gate against it. (b) The discharge
is mechanical when the set is identical (header instant + commit,
delta class DATE/COMMIT-ONLY) and only becomes a decision when a set
MOVES — which is precisely when it must not be buried in a train. So
the honest shape is a **standing post-train step**: whoever lands a
train whose merged branches touched `tools/nativefrontend/wire.go` or
`GoLean/NativeToIR.lean` (`git log <old-tip>..<new-tip> -- <the two
files>` non-empty) runs `scripts/capped scripts/ci --slow` at the new
clean tip before the train is declared landed, refreshes the header if
IDENTICAL, and STOPS with a finding if not. PROPOSAL ONLY, [AGENT]:
the merge train is today a coordinator procedure, not a script, so
this is a rule for that procedure (or a one-line check in the train's
landing checklist), not a tool change; whether to adopt it — and
whether a same-day K=80 exhibition (this run: 5 of 6 vs the morning's
6 of 6 on `google-search`) is worth the extra ~8 minutes per train — is
a [USER] call. Until ruled on, C9 stays the signal and the re-cert
stays owed on every fire.

**Addendum (2026-09-04): the standing post-train step — ADOPTED
[USER].** C9 re-fired the same day after the round-11 train landed
five more commits to `wire.go`/`NativeToIR.lean`; lane `slow-recert-2`
(`docs/evidence/2026-09-04_slow-recert-2/README.md`, not yet merged to
main as of this entry) ran the second re-cert and proposed making it a
standing post-train step rather than a re-cert someone spawns after
noticing the MEDIUM: whenever a merge train's landed branches touched
`tools/nativefrontend/wire.go` or `GoLean/NativeToIR.lean`, run
`scripts/ci --slow` at the merged tip and refresh the certification
record before the train is declared landed — an identical set
refreshes the header only, a changed set is a finding reported before
the train continues, never a silent re-pin. **ADOPTED [USER]
2026-09-04** (Mike, relayed by the [AGENT] coordinator; cited as
relayed): (adopted) — adopting the
proposal as written. Recorded as merge protocol step 5a, `CLAUDE.md`
"The merge protocol".

## A comparator that projects a field away on one side is fail-open on that field (2026-09-05)

The choice tracer's driver-agreement check (`GoLean/ChoiceTrace.lean`
`traceStream`) compares the real engine's observation with the
enumerator driver's. The engine's is a `RunResult` — a `Stop` paired
with the output printed before it; the enumerator's refusal was a bare
`Stop`, rendered through `observationOfRun` with an EMPTY output field.
So on every refusal path the check compared status + message only. It
showed up as a false positive — `builtins/float-bits/roundtrip-payloads`
prints two lines before its BUG-094 refusal and was reported as an
engine/enumerator MISMATCH on all six streams on every whole-corpus
trace this lane ran, `main`'s own binary included, until the c-arc-b4
pre-merge audit read the two JSONs side by side — but the false
positive was the benign half: a REAL pre-refusal output divergence between the two
drivers would have printed «ok». Fix: `CLI.enumPoolRun`/`enumRunProgram`
return `Except (Stop × GoString) …`, pairing every refusal with the
pre-step fold exactly as `execProgLoopOut` does, and the tracer compares
the whole observation on both paths (the float-bits row went to 0
mismatches with no other line of the whole-corpus summary moving —
`docs/evidence/2026-09-05_c-arc-b4/choice-trace/fix-summary.txt`). Two
lessons. (1) **When a comparator's two sides have different types, the
conversion is part of the comparator's trust surface**: a `mapError (·,
empty)` is a projection, and a projection on one side means the field
is not compared — audit the conversions, not just the `!=`. (2) **A
standing MISMATCH that "everyone knows" is a finding nobody read**: the
row was listed as "pre-existing, not this lane's" in the lane's
records before anyone opened the two observations; the audit's
side-by-side read diagnosed it.
Lane tooling ([AGENT] fix, records-only audit round); the eval-test F5
pins still compare `.ok` members only — a refusal-path eval pin is
noted in TODO.md, not claimed.

## The method-identity audit's 180 s budget has thin headroom under shared-box load (2026-10-07)

`tools/typed_audit.py`'s 180 s per-compile budget for the method-identity
poison copy has thin headroom under shared-box load. Measured 162 s
(lane), 195 s (r71), 201 s (isolated, load ~50), and >180 s under load
~50–60 in r72's first `ci --slow`, which failed closed (the step
refused by name, «audit subprocess timeout», and `executed library
coverage` echoed the failed receipt); the fresh re-run, started at
1-min load ~37, measured 150 s and passed. A budget change is a [USER]
decision; until then, re-run under lower load (check `uptime` first).
Train r72 ([AGENT] train worker; the re-run-not-retune ruling [AGENT]
coordinator, 2026-10-07).
**Raised 180 → 360 s** in train r73 ([USER] Mike 2026-10-07 (items 1 and 2 agreed), relayed). The budget is `run_logged`'s per-subprocess timeout, so
it also governs the core-audit harness/poison compiles and the
method-identity dispatch subprocesses. Measured alone 150–201 s, so
360 s still catches a hang; under load, still check `uptime` first.

The same holds for the per-run `LEAN_TIMEOUT_SECONDS`: the 30 s
`LEAN_TIMEOUT_SECONDS` on heavy budget rows (e.g.
`noodler/budget/map-20k`'s oracle-invariance re-runs: 4.7 s / 9.6 s
alone) has thin headroom under shared-box load. r72's first `ci --diff`
at load 17/34/43 timed out on it, failing closed (PASS → FAIL/nondet,
«a killed run is not an observed variance»); the fresh re-run (start
load 30/40/46) passed. A budget change is a [USER] decision. Train r72
([AGENT] train worker; the re-run ruling [AGENT] coordinator,
2026-10-07).
**Default raised 30 → 60 s** in train r73 ([USER] Mike 2026-10-07
(items 1 and 2 agreed), relayed): only the default in `scripts/diff-coverage`;
the derived tracer budget `LEAN_TRACE_TIMEOUT_SECONDS` (8 ×) moves
240 → 480 s with it. map-20k measures 4.7–9.6 s alone, so 60 s still
catches a hang.

## A long gate is itself the defect (2026-10-12)

The gate cull (`docs/2026-10-12_gate-cull-plan.md`, [USER]-ruled D1–D9): of
44 classified rows only 17 guarded the trust surface; the rest were self-tests
of checkers, compiled poison/mutant controls, a cache certificate and a receipt
registry. Recorded cost before the cull: 850–1034 s per warm `--diff`, of
which ~430 s was the post-build control steps plus the certificate check; one
mutant self-test cost 3912 s cold. The certificate apparatus (§«A cached
certification is owed a re-run…» above) certified a cache for ONE row whose
fresh enumeration takes ~94–160 s single-core: deleting the cache deleted the
need for the proof. Lessons: a cache on the trust path needs a validity proof
that grows until every edit invalidates it — run the thing instead; a check
that tests a CHECKER (poison, mutant, receipt, self-test) adds no evidence
about the product and belongs in a hand-run `scripts/test-*`; and the global
rule now says it outright — a slow gate is a reason to examine and trim.

## The kernel replay gate: the checker's peak is threads × import closures (2026-10-13)

The zero-context review (`docs/2026-10-13_codex-zero-context-pass.md`, F4)
found that the gate built and audited axioms but never replayed the built
oleans through the kernel into a fresh environment, so a metaprogram that skipped the kernel
(`debug.skipKernelTC`, `addDeclWithoutChecking`) would pass the build, the
escape-hatch scan AND the axiom audit (a scratch `bogus : False :=
True.intro` built that way printed «does not depend on any axioms»; only
`leanchecker` refused it: «(kernel) declaration type mismatch»). Ruled
[USER] Mike 2026-10-13, relayed: (item 4 ruled a critical finding and a core trust gap, to be fixed). Since lane `gate/kernel-replay-1013`
`scripts/check-kernel-replay` runs `lake env leanchecker --verbose GoLean`
in both tiers after the build and fails on any nonzero exit (a kill
included) and on a replayed set that is not the on-disk module set (the
checker replays whatever oleans it FINDS: a missing olean is skipped in
silence).

**Stale oleans of DELETED modules fail the replay, not the build** (lane
`core/retire-relation-1020`, 2026-10-21, the relational retirement). Lake never
deletes an olean whose source is gone, and `lake build` never looks at it, so a
`.lake` copied from before a deletion still holds e.g. `PoolStep.olean`; the
checker finds and replays it, and it fails on the first constant its imports no
longer provide («(kernel) unknown constant 'GoLean.GoCore.Machine.Step'») before
the set comparison could name it STALE. Since that lane the script prints the
set diff with its remedy ALSO when the checker fails. The remedy: delete the
deleted modules' artifacts (`find .lake/build -path '*GoLean/GoCore/<Module>.*'
-delete`, `.olean/.ilean/.hash/.trace/.c/.o`) or build cold; a fresh clone never
has them. (The toolchain lane hit the same on its branch; its note there confirms this.)

The hosted runner is the case that never builds cold ([AGENT] 2026-10-22, lane
`ci/prune-stale-oleans-1022`): the workflow restores `.lake` from the Actions
cache through a restore-keys FALLBACK every run (the primary key embeds the run
id, so it never hits) and saves the whole tree back `always()`, so a deleted
module's artifacts ride the cache lineage forever — 79 dead modules (the
typed-profile facade parked 2026-09-16, the relational layer retired 2026-10-21)
failed every push run on main from the retirement to 2026-10-22, refused by the
gate, while the same gate passed on every local tree. The remedy is now a script,
`scripts/prune-stale-oleans` (self-test `scripts/test-prune-stale-oleans`): it
deletes every artifact under `.lake/build/lib/lean/` and `.lake/build/ir/` whose
module has no `<path>.lean` at the root, names each one, passes a cold tree, and
refuses a lakefile with a `srcDir` (the rule would be wrong). The workflow runs it
right after the cache restore; by hand it replaces the `find … -delete` above.
`scripts/ci` prints only the last 25 lines of a failed check, so the runner log
named 23 of the 79 under its «129 oleans vs 50 modules» count — the full list is
in the check's own output, not the gate's tail.

The cost law is the build's («Concurrency OOM», above): the checker runs
one task per module on Lean's thread pool, each importing the module's
closure, and the peak is the SUM over the concurrent tasks. Measured
2026-10-13 (warm tree at `2e69dd86`, 68 modules, box load ~16, GNU time
`%M` on the checker process, under the box lock, each run exit 0 with
all 68 replayed):

| `LEAN_NUM_THREADS` | wall | peak RSS |
|---|---|---|
| unset (toolchain default = hardware concurrency, 32 here; ~35 OS threads seen) | 27.3 s | 31.2 GB (29.8 GiB) — 2 GiB under the 32 G cap |
| 8 (what `scripts/ci` exports under a 64 G cap) | 13.8 s | 11.2 GB |
| 4 (what `scripts/ci` exports under the 32 G default) | 17.8 s | 6.7 GB |
| 2 | 30.7 s | 3.1 GB |
| 1 | 49.0 s | 2.3 GB |

The coordinator's earlier «21 s, ~30 GB» was the unset case. Per-process
per-module replay was also measured: the 66 leaf modules peak at 1.5 GB
(`GoLean.GoCore.StepErrors`, 2.8 s) and sum to 58 s, but the checker
matches targets by NAME PREFIX, so `leanchecker GoLean` and `leanchecker
GoLean.GoCore` each replay their whole subtree (68 and 58 modules, 28 GB
at the default threads) and a per-module loop through the CLI cannot
isolate those two; the thread knob reaches the same peak reduction in one
process. Inside the gate (fast tier, same tree, `LEAN_NUM_THREADS=4` from
the cap): 15.0 s wall, 7.1 GB peak, of a 106 s fast tier.
So: the gate's replay inherits `scripts/ci`'s `LEAN_NUM_THREADS`
(cap/8G), the script sets 4 when run by hand with it unset ([AGENT]
2026-10-13; faster and five times lighter than the default), and the line
it prints names the thread count, the wall and the peak. A cgroup kill
reaches the script as the checker's exit 137 (GNU time: «Command
terminated by signal 9»); the script's own FAIL line is the signal
(«KILLED (exit 137 …); a killed replay has checked nothing») and it exits
1, so `capped`'s KILLED banner does NOT print on this path — self-tested
under `capped -m 1G`. The same kernel in a fresh environment, not an
independent verifier, and the imports are trusted as loaded (a dependency
package would be trusted, not replayed; none today). `@[extern]` is
outside its reach by construction — the kernel checks the Lean body, the
executable runs the named symbol — so the escape-hatch text scan carries
that guard (`META_HATCH_RE` in `scripts/lean-scan.sh`, `extern` added in
the fix round, review F1). `lake check` (toolchains ≥ 4.35) is the
stronger form when the Lean pin moves; the pin moved to 4.35.0 on 2026-10-21 (entry
«Lean 4.35» below: what `lake check` can and cannot do on this lakefile).

## Lean 4.35: the bump's breakage classes, and what the gate is at this toolchain (2026-10-21)

[USER] 2026-10-20 (release-readiness row 42, paraphrased): bump to Lean
`v4.35.0` now, as a priority — it blocks using GoLean upstream — in
parallel with the relational retirement lane. Lane `toolchain/lean-4.35-1020`
([AGENT]). Lake 5.0.0 (4.35.0) accepted the tracked `lake-manifest.json`
unchanged (byte-identical after `lake env` and every build; no packages).

**The whole tree compiled with zero errors in the executable modules**; the
breakage was in proofs and in one CLI definition, six classes:

1. *Deprecated lemma names* (warnings; the gate demands warning-free):
   `if_neg`/`if_pos`/`dif_pos`/`dif_neg`/`if_false` → `ite_eq_right`/
   `ite_eq_left`/`dite_eq_left`/`dite_eq_right`/`ite_false` — drop-in
   (identical statements), a word-boundary `sed`. 90 sites in the kept
   modules; 117 more in the retirement set, left to the retirement lane.
2. *A core source position pinned in a proof*: two `StateWf` proofs rewrote
   the literal `panicWithPosWithDecl "Init.Data.Array.Basic" "Array.eraseIdx!"
   1820 47 …`; the panic moved to line 1867. Fixed by the position-agnostic
   `Array.panicWithPosWithDecl_eq_empty` (`rfl` over any position). Lesson:
   never match a toolchain source position; state the lemma over the
   function (`panic!` computes to `default`).
3. *A stale `Decidable` instance after `simp only`*: a `simp only [foo]`
   unfold rewrites an `if`'s condition but leaves its instance stated over
   the OLD condition (type-correct only up to unfolding; the toolchain's new
   `linter.tacticCheckInstances` names it), and the following `split` or
   `rw [ite_eq_right …]` misses the `if` («Did not find an occurrence of
   the pattern if ?m then ?m else ?m»; `split`: «failed to simplify target
   using new hypotheses»). Fix: `dsimp only` for the definitional rewrites
   (`Loc.rootPath`; the rfl lemma `Int.zero_emod`) — it rewrites inside the
   instance too. Two sites, both in `MachineSound`, which left the tree the
   same day with the relational retirement (the re-homed `StepFnFacts` carries
   neither site); the idiom is the lesson.
4. *`constructor` warns when a later constructor also unifies* (the
   generic `Step` sweep: `Step.callStart` vs `callImmediate`, the literal
   arms vs `evalStrictNullary`): `constructor!` (= `constructor +first`)
   is the previous behaviour, chosen where the sweep's subgoals decide (one
   site, also in `MachineSound`, gone the same day).
5. *`letFun` deprecated*: `have` is a non-dependent `let` now and `simp`
   zeta-reduces it; drop `letFun` from `simp only` sets (one site).
6. *`given` (with `requires`, `ensures`) is a forbidden binder name in a
   `def` signature* («unexpected identifier; expected '_' or forbidden
   token»): one `CLI` binder renamed; fields keep the name.

Not a breakage but a gate expectation that moved: the core totality
audit's «constructive abort-text helpers» rule. Its axiom-level form,
axioms ⊆ {`propext`, `Quot.sound`}, is DROPPED at 4.35 — not restated —
because the toolchain's `BEq` instances on `Int` and `UInt8`
(`instBEqOfLawfulEqOrd` through `Int.instLinearOrderPackage` /
`instLinearOrderPackageUInt8` → `Std.LinearOrderPackage.ofLE._proof_2` →
`Classical.propDecidable`; `UInt8.instLawfulEqOrd`, a theorem, →
`Classical.not_not`) carry `Classical.choice` in PROOF fields. Precisely
(the reviewer's probes): `==`/`!=` on `Int`/`UInt8` reach choice;
`decide (a ≤ b)`, `<`, `compare`, `max`, `min` carry none; so
`firstLine`'s `(· != 10)` is itself a data path with the trio, and every
one of the five helpers is computable (`Lean.isNoncomputable env n =
false`). What replaces the bound (`Tests/GoCoreAudit.lean`,
`checkOwnedNoClassical`) is a HYGIENE check, not an axiom boundary: the
classical trio; computability of every helper; and, over the constants
DEFINED IN GoLean/Tests MODULES within a helper's closure (ownership by
`env.getModuleIdxFor?`, not by name root — 43 constants in GoLean modules
carry another root today), no direct `Classical.*` name and no citation of
a non-instance toolchain theorem whose axioms reach `Classical.choice`
(memoised `collectAxioms`). Owned code may rely on the toolchain's
instances and definitions, whose classical proof fields are the
toolchain's; every classical entry point of the five helpers today is such
an instance (`instLinearOrderPackageUInt8`, `Int.instLinearOrderPackage`,
`UInt8.instLawfulEqOrd`, `UInt8.instLawfulOrderOrd`). Inherent to a
reference check: a toolchain instance that is itself a classical theorem
is allowed, so this is hygiene over what the repository writes, not a
proof that no classical fact is used. The owner decides between this and
trio-only. The trace that found the entry points: walk a declaration's
used constants and follow the ones whose axioms contain `Classical.choice`
(a dozen-line `MetaM` loop).

**Measured at 4.35** (this box, under the lock; the module set named per row):

| what | figure |
|---|---|
| cold full build, `LEAN_NUM_THREADS=8`, `capped -m 64G`, main's module set (169 jobs) | 499 s wall; aggregate cgroup peak 3.2 GiB; largest process 3.1 GB (the 4.32.2 cold build of 2026-10-12: 163 jobs, 8 min 37 s) |
| cold full build, same cap, the post-retirement tip (126 jobs; rebased onto `ea629cc8`) | 315 s wall; aggregate cgroup peak 3.1 GiB; largest process 3.1 GB; zero warnings |
| fast tier (`capped scripts/ci`, warm) | 99 s; 2026-10-22, library-only defaults (12 targets built by name, the split check, no `lake check`): 89 s |
| kernel replay (`scripts/check-kernel-replay`, 4 threads) | main's set, 68 modules: 12.9 s, 5.9 GB peak (4.32.2: 17.8 s, 6.7 GB); the post-retirement tip, 47 modules: 8.2 s, 3.5 GB; 2026-10-22, 50 modules: 9.1 s, 4.4 GB |
| `lake env leanexport GoLean` (the `GoLean` library's closure with its Init/Std/Lean imports) | main's set: 33 s, 2.7 GB, a 1.0 GB, 18.1 M-line export; the tip (47 modules, reviewer's run): 34.7 s, 942 MB, 16.37 M lines |
| `lake check --from-export <that> --inadvisably-no-sandbox` | main's set: 133 s, 1.6 GB; the tip: 150 s; both «Lean default kernel accepts the solution; Uses axioms: propext, Quot.sound, Classical.choice» |
| `capped lake check --inadvisably-no-sandbox`, the library-only defaults (2026-10-22, lane `gate/lake-check-1021`; 32G cap, by hand) | probe: 212 s wall, largest process 2.7 GB; the by-hand run at the tip: 204.6 s wall, largest process 2.7 GB (2,749,232 KB); both «Lean default kernel accepts the solution», «Uses axioms: propext, Quot.sound, Classical.choice», rc 0 |
| the same inside `CAPPED_MEM_MAX=64G capped scripts/ci --diff` (the `--diff`-tier speedbump) | wall 203.7 s; largest process 2,687 MB; PASS — «Lean default kernel accepts the solution», «Uses axioms: propext, Quot.sound, Classical.choice», no sandbox (bwrap: «loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted»); the whole merge tier 710 s wall at LEAN_NUM_THREADS=8 on a warm tree (the fresh corpus runs included), RESULT: PASS, no red speedbump |
| the export alone (`LAKE_CHECK_EXPORT=1 capped lake check > export.ndjson`, Lake's build-and-export half) and the four working bundled kernels on it by hand, as Lake invokes them (`LEAN_ABORT_ON_PANIC=1`, the export path last; the box default cap) | export 34.6 s, 2.7 GB, 0.95 GB / 16.5 M lines; `leanchecker-paranoid --silent --from-export` 224.8 s, 1.7 GB, exit 0 (silent); `lean4lean --import` 235.6 s, 1.4 GB, «checked 178476 declarations»; `con-leche` 26.8 s, 6.6 GB, «accepted 178479 declarations (--verified)»; `con-ron` 17.6 s, 3.4 GB, «accepted 178479 declarations (--verified)»; the default kernel `leanchecker --silent --from-export` 154.0 s, 1.5 GB, exit 0 — about 9 min for the export plus the four, `docs/release.md` §3 (a) |
| `CAPPED_MEM_MAX=64G capped lake check --paranoid --inadvisably-no-sandbox` (the five external kernels; the cap raised deliberately for the measurement) | 975.6 s wall; largest process 42.2 GB (44,257,920 KB — OVER the 32G box default, which would kill it: run it under 64G); Lean's paranoid kernel, lean4lean (178,476 declarations), con-leche and con-ron (178,479 each, --verified) and the default kernel all accept; nanoda REJECTS by crashing — «thread 'thread_3' has overflowed its stack; fatal runtime error: stack overflow, aborting», «error: nanoda exited with 134» — a crash in nanoda's own worker thread on this export, not a kernel rejection of a named declaration; rc 1 overall. Not chased (the lane brief: do not loop on it); whether it reproduces outside the sandbox is the owner's run to say |

**`lake check` at this project — LANDED 2026-10-22 (lane
`gate/lake-check-1021`; [USER] 2026-10-21, release-readiness row 42's
open half, paraphrased: the check must run, as the in-sandbox speedbump
and as the owner's claim-point gate; the default targets become the
libraries only).** The toolchain's `lake check` builds the default
targets, exports them, replays the export through the kernel and refuses
non-standard axioms (`--paranoid` adds five external kernels), in a
`bwrap` sandbox that needs unprivileged user namespaces, which a sandboxed
agent session does not have (here: «setting up uid map: Permission
denied»). Its export half (`Lake/CLI/Main.lean`, `checkExport`) imports
EVERY default module into one environment, so on the 2026-10-12 lakefile
— every library and executable a default target; `Main.lean`,
`Tests.GoCoreEval`, `Tests.StrictJsonParse`, … each with a top-level
`main` for `lean --run` — it stopped at the second `main` («import
Tests.GoCoreEval failed, environment already contains 'main' from Main»),
sandboxed or not. The landed arrangement: `defaultTargets` is the
main-free LIBRARIES only — `GoLean`, `TestsData`, `AdmissionTests`,
`GoCoreAuditTests` — and the gate builds every declared target by name
(`scripts/ci` parses `lakefile.toml` for the list and FAILS the build step
on a shape it cannot parse: an unknown key, a wildcard glob, a nameless
section); the two executables and the six `main`-bearing test libraries
(`EvalTests`, `DeclarationTests`, `MethodIdentityTests`,
`UnseqSchedulerTests`, `UnseqWireTests`, `EquationTests`) are outside the
defaults. The split is checked both ways after a green build from each
module's built `.ilean` (the elaborated constant names, so a namespaced
`Tests.X.main` is not `main`; an unreadable or reshaped `.ilean` is a FAIL,
never «main-free»): a main-free library that is not default, a default
executable or `main`-bearing library, a default name no target declares —
each a FAIL. The COVERAGE GAP this leaves (review F3, 2026-10-22): ten
modules are outside BOTH kernel checks — not default targets, so not in
`lake check`'s export, and not `GoLean.*`, so not in the replay's prefix:
`Main`, `Tests.GoCoreEval`, `Tests.DeclarationWire`,
`Tests.StrictJsonParse`, `Tests.DeclarationUnicode`, `Tests.MethodIdentity`,
`Tests.UnseqHarness`, `Tests.UnseqScheduler`, `Tests.UnseqWire`,
`Tests.EquationClient`. Two of them carry theorems:
`Tests/EquationClient.lean` (296 equation pins and 12 facts, plus two
witnesses, under its `main`; built and run by `scripts/check-equations`)
and `Tests/MethodIdentity.lean` (12: `requirement_identity_is_semantic`,
`method_identity_is_semantic`, `private_same_package_accepted`,
`private_cross_package_rejected`, `pointer_inherits_private_value`,
`value_does_not_inherit_private_pointer`, `variadic_is_part_of_signature`,
`nil_text_ignores_foreign_declaration`,
`nil_text_promoted_entry_outside_family`,
`nil_text_requires_matching_package`, `private_targets_are_distinct`,
`utf8_target_vector`; run by `scripts/check-method-identity`). Those are
kernel-checked at elaboration (the build) but NOT replayed against
tampering by either check. The remedy is a follow-up, not made here: turn
the `lean --run` `main`s into build-time checks (as the enrollment `#eval`
in `Tests/EquationClient.lean` already is), after which the libraries
become main-free and default, and `lake check` covers them. Also:
`scripts/diff-coverage`'s up-front build names `golean`, which is no
longer a default (a bare `lake build` now builds the libraries only — the
README's cold-build line says so).
`scripts/check-lake-check` is the SPEEDBUMP, in the `--diff` tier only
(about four minutes): it probes `bwrap` with Lake's own flags, runs
sandboxed where that starts and `--inadvisably-no-sandbox` where it does
not (the toolchain prints «this run is not trustworthy»), says which, and
passes only on the toolchain's acceptance line AND the axiom verdict (both
carried on its PASS line with the wall and the largest-process RSS); the
owner's `lake check` outside the sandbox is the gate at claim points,
`--paranoid` at the release claim point (CLAUDE.md «The gates»,
`docs/release.md` §3). The measurements are in the table above.

**Both kernel checks stay, one reason each.** `scripts/check-kernel-replay`
(fast tier; 50 modules: 9.1 s, 4.4 GB at 4 threads, 6.8 s, 9.1 GB at 8) replays the ON-DISK
`GoLean` olean set and checks it equal to the module set on disk — an
unbuilt or stale olean is named with its remedy, which `lake check`
(exporting what the default targets import) cannot see — and needs no
bwrap. `lake check` covers the default test libraries' modules —
`Tests/GoCoreContract.lean`'s pins, the audit harness
`Tests/GoCoreAudit.lean`, the admission facts — which the `GoLean`-prefix
replay does not, plus the export path and, under `--paranoid`, the five
external kernels. The olean path the replay uses is unchanged at 4.35
(`leanchecker --verbose <prefix>`, `replaying <module>` lines; no `--help`
— flags are partitioned by a leading dash and anything else is a module
name); 4.35 adds `--from-export` and `--silent`, the export path `lake
check` drives. Since the fix round the script compares the oleans on disk
with the module set BEFORE the replay, so a stale olean of a deleted
module is named with its remedy rather than surfacing as the kernel's
rejection of its first importer.

**After a rebase that deletes modules, wipe `.lake/build` before the gate.**
Lake never removes the olean of a deleted module, and `leanchecker GoLean`
replays every olean it finds under the prefix: after this lane rebased onto
the relational retirement, the fast tier's kernel replay failed on the stale
`GoLean.GoCore.PoolStep` olean («(kernel) unknown constant
'GoLean.GoCore.Machine.Step'», 18 s, 26 GB peak at 4 threads from the retired
closures loading) — the gate failing closed on the build tree, not the
source. `scripts/check-kernel-replay` names a stale olean by path only when
the replay itself succeeds (the set comparison runs after it); a kernel
rejection in a module that no longer has a source is the same remedy:
`rm -rf .lake/build` and rebuild cold (`CAPPED_MEM_MAX=64G capped lake build`).

## Box-independence: the cap is detected, never shipped; the tools are declared (2026-10-21)

THE RULE ([USER] 2026-10-21, paraphrased; release-readiness row 46): the
project must work outside the Oath boxes — a clone on an ordinary machine
builds and checks with the documented commands and no extra setup; nothing
box-specific is hard-coded (home paths, install locations, cache layouts,
hostnames, the sandbox's name, box-only tools); dependencies are declared in
the project's files and optional box tooling is detected at run time; the
memory cap is used through `cap()` (above), sized by `CAPPED_MEM_MAX`, never
`-m`, and where `capped` is absent the build runs uncapped, silently —
`scripts/capped` removed, the README's promise that the gate refuses to run
uncapped withdrawn.

WHAT CHANGED ([AGENT] lane apparatus/box-independence-1021). `scripts/cap.sh`
(sourced, beside `lean-scan.sh` and `typed-gate-scratch.sh`): `cap`, the
thread derivation, `cap_argv` (the same choice as an argv prefix, for a site
that hands its command to `run_with_timeout`, which execs its argv) and a
one-line cap note that says only what THIS script does — without the tool
it applies no cap itself; an outer cgroup (the workflow's systemd scope, a
`capped` further up) may still be in force, which it cannot see. Every
heavy call site — `scripts/ci` (the build, the eval tests, the two corpus
runs), the ten check scripts (`check-frontend-pins`' `lake build golean`
among them, after the fix round), `scripts/diff-coverage`'s own `lake
build` (`$(cap_argv)` inside its timeout, so the README's `scripts/diff-one`
route is capped too), `scripts/grossmith-run` (its `gengo()`),
`scripts/go-version-diversity` (its two corpus runs), `tools/admission-
check.py` and `tools/core-audit.py` (`shutil.which("capped")`) — goes
through it: 29 `cap`/`cap_argv` sites in 15 shell scripts plus the two
Python tools (27 in 13 before the fix round); the two self-wrapping scripts
(`ci`, `grossmith-run`) no longer re-exec. The GitHub workflow passes
`CAPPED_MEM_MAX` and keeps the proven-cap readback in its own in-scope
shell. `scripts/check-lake-check` probes `bwrap` with Lake's own base flag
set (`Lake/CLI/Check.lean`, `buildSandboxArgs`: `--ro-bind / /`, the tmpfs
covers, `--dev`, `--proc`, `--clearenv`, `--unshare-all`,
`--die-with-parent`, `--new-session`; the binary from `COMPARATOR_BWRAP`,
Lake's own override) and runs `lake check` sandboxed where that starts,
with `--inadvisably-no-sandbox` where it does not, saying which — the first
round's weaker probe (`--ro-bind / / --dev /dev`) would have labelled a run
«sandboxed» in an environment that opens a user namespace but cannot
unshare the network; here, inside the agent sandbox, Lake's set fails on
«loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted»
(every time, also under `env -i`; the «setting up uid map» error was the
weaker probe's), so the no-sandbox form.
`scripts/check-wire-boundary` runs under `set -Ee` so the scratch file's
ERR trap still names a failing command inside `cap`. Hostnames,
`~/projects/...` and `/usr/local/go` left the living docs and the Lean
comments (dated records, baseline re-pin notes and the gc traceback
fixtures keep theirs: they say what was run and where).

TOOLS, MEASURED. The declared set is now the README's list: elan/Lean,
go1.26.5, Python ≥ 3.11, git, bash ≥ 5, GNU coreutils or compatible;
`capped`, `bwrap` and `/usr/bin/time` optional — perl is no longer on it
(below). `jq` was declared but used only in a `docs/cli.md` example:
dropped. `shasum -a 256` (the full `perl` package, not perl-base) became
`sha256sum` (coreutils) at its five sites. bash ≥ 5, not 4 (fix round
finding 2): `scripts/diff-coverage`'s per-row timer reads
`${EPOCHREALTIME/./}` (bash 5.0+), which under `set -u` would kill `timed`
on bash 4, so «bash 4» was a false promise; the alternatives buy nothing
(`date +%s%N` is GNU/uutils-only; a python3 call per row is ≈10 ms twice a
row), and every Linux this project can run on has shipped bash 5 since
2019.

`run_with_timeout` (one sourced definition, `scripts/run-with-timeout.sh`,
since the fix round; the four scripts that each carried the perl one-liner
— `diff-coverage`, `coverage-negative`, `detector-soundness`,
`oracle-386-static` — source it). CORRECTION of the first round's record
and of the lane commit `268f7776`'s message, which said GNU `timeout` gives
124 on the ignored-TERM probe: that figure was asserted from memory, not
measured, and is WRONG. Measured on this box: GNU 9.7
(`/usr/bin/gnutimeout`) and uutils 0.8.0 BOTH exit **137** on
`timeout --kill-after=1 1 sh -c 'trap "" TERM; sleep 30'` (GNU documents
137 for a KILL after the timeout); the one genuine divergence is a TERM
death, `timeout 5 sh -c 'kill -TERM $$'`: GNU 143, uutils 15. The
wrapper's own figures: 124 / 143 / 124 (plain timeout) / 137 (SIGKILL) /
127 (no such command). So the real reasons the project keeps its own
wrapper are (a) the CONTRACT — 124 on a timeout, which `diff-coverage`
relies on to tell a timeout from a cgroup kill (137 → the `killed:` cause
family, `undecided_cause`) — and (b) the uutils/GNU divergence, which
makes coreutils' exit codes box-dependent. The host is now Python, not
perl ([AGENT], fix round): Python ≥ 3.11 is already declared and perl was
not; the port keeps the contract exactly, eight probes measured through
the sourced file — ignored TERM 124, TERM death 143, plain timeout 124,
SIGKILL 137, no such command 127, `exit 3` → 3, a non-numeric or zero
timeout → 2 with a message (the perl `alarm 0` silently disabled the
guard; the callers' own checks stay, naming the knob) — at +7.7 ms a call
(`python3 -I -S`: 9.6 ms; perl: 1.9 ms). The cost of a full run, anchored:
`artifacts/coverage/timings.tsv` of the lane's `--diff` run at `6ded1f4b`
has 64,539 timed phases, every one a `run_with_timeout` call, so
64.5k × 7.7 ms ≈ 500 s of CPU ≈ 16 s of wall over 32 workers — consistent
with the gate's 488 s (perl) → 499 s (Python). (The first record here said
«on the order of 20k calls»; the second review counted.) Two behaviours
are new, both deliberate: the command runs in its own process group — set
from both sides of the fork, so a signal forwarded in the first instant
finds it — and the TERM-then-KILL goes to the group (a timed-out `go run`
takes its compiled child with it; a capped build — `run_with_timeout …
$(cap_argv) lake build`, the box tool between the wrapper and lake — dies
whole, where the perl wrapper killed the direct child only and would have
left lake running), and HUP, INT, QUIT and TERM to the wrapper are
forwarded to the group (exit 128+N), so a hangup or Ctrl-C still reaches a
command that is no longer in the terminal's group (the second review found
HUP missing from the first port: the wrapper died 129 and the command
lived on, its alarm gone — the perl child shared the caller's group and
died with it). ONE LEAK, KNOWN AND LEFT ([AGENT], second fix round): on
the bare route — `scripts/diff-one` or `scripts/diff-coverage` by hand on
a box with `capped` on PATH and no outer `CAPPED_STATE` — a `lake build`
that times out inside the wrapper leaves an empty cgroup directory behind:
the group TERM kills the box tool's outer shell, which keeps itself outside
the cgroup, has no trap, and never reaches its `rmdir`. Ordering the kill
(the direct child first, the group a moment later) would not help — that
shell dies on TERM at once, before any cleanup, and excluding it from the
group kill would make the wrapper depend on the tool's internals. The
cleanup belongs to the tool (a trap around its `rmdir`), proposed to the
owner as box-tool hygiene; under `scripts/ci --diff` the route does not
arise (the outer `cap` makes the inner `capped` a plain exec). The stderr announcement is opt-in
(`RUN_WITH_TIMEOUT_ANNOUNCE=1`, set by `diff-coverage` as before; the other
three keep stderr clean, as before). THE SELF-TEST CAUGHT THE PORT'S FIRST
CUT: `scripts/test-lane-validation --with-go` failed every fixture with a
real oracle run («go run oracle failed with exit 78»), and `scripts/diff-one`
on a case the full gate had just passed failed the same way, while the
oracle's exact command shape passed by hand under both wrappers. The cause
was not the wrapper's semantics but its transport: `diff-coverage` hands
`run_case` and `run_with_timeout` to its `xargs` workers with `export -f`;
the perl one-liner lived inline in the function body and travelled with it,
whereas the Python program lived in a plain shell variable that did not — so
every worker ran `python3 -c ""`, which exits 0 having run NOTHING. The
harness step «succeeded» without writing its directory and the oracle's
crash-file reset then failed with 78 (`GOLEAN_COVERAGE_JOBS=1`, the
sequential path, passed — the bisection that named it). Remedy: the program
is exported with the function (`export RUN_WITH_TIMEOUT_PY`, and the
announce flag likewise), and the function REFUSES when the program is empty
(exit 70, a code no consumer reads as a verdict) rather than run nothing —
a silent `exit 0` from an empty program is the fail-open the charter
forbids. Lesson: a function that is exported to workers may only depend on
state that is exported with it, and a wrapper must fail closed when its
own body is missing. The self-test's own fake root (a scratch `scripts/`
holding only a link to `diff-coverage`, so that a fake `golean` can sit
beside it) then needed links to the two files diff-coverage now sources
beside itself (`cap.sh`, `run-with-timeout.sh`): without them the runner
died at the source line before any row, and sixteen fixtures reported
«row: <none>». With both fixes `scripts/test-lane-validation --with-go` is
green: 151 ok, 0 FAIL (2026-10-21). (The A/B run of the self-test at main's tree that was
tried first was itself a mistake: its worktree shared this lane's `.lake`
by symlink while its sources differed, so its `lake build` rebuilt this
lane's oleans against the other source set while this lane used them —
`lake build failed` mid-investigation; the orphaned workers were stopped by
PID and `.lake/build` was wiped and rebuilt cold, 293 s. Never share a
build tree between worktrees whose sources differ.)

`deps/go`: the pin allows a shallow clone (tag `go1.26.5` is the pinned
SHA; measured locally: 37 MB of `.git` and 186 MB checked out against
474 MB of history; the gate's consumers read files at HEAD and run
`rev-parse`/`diff --quiet HEAD`, which a shallow clone satisfies — the
workflow already clones that way), but `scripts/mine-spec-archaeology`
walks history and the network clone path cannot be tested from the
sandbox, so `scripts/setup-deps` keeps the full clone; the README says what
it costs.

ACCEPTANCE (the clean-clone test the lane brief set, run 2026-10-21 at the
lane commit `dc95dea6`; the result lines are the runs' own). A clean clone
(`git clone --no-hardlinks` of the lane worktree into its `.tmp/`, the
branch checked out, `scripts/setup-deps --from <the primary's deps/>` — a
fresh machine runs `scripts/setup-deps` with the network), then ONLY the
README's commands, under the box-wide build lock:
  1. with `capped` on PATH and `CAPPED_MEM_MAX=64G`:
     `capped lake build` (cold) — EXIT=0 in 294 s;
     `scripts/ci --diff` — `RESULT: PASS`, 488 s; «memory cap: capped on PATH
     (/usr/local/bin/capped); CAPPED_MEM_MAX=64G; CAPPED_STATE=unset» (the
     bare `scripts/ci` capped each heavy step itself), LEAN_NUM_THREADS=8;
     differential 4025/4025 and negative 415/415, no regression; the one
     speedbump RED is `lake check` (environment already contains 'main' from
     Main — row 42 territory, as before), its line reading «no sandbox (bwrap
     cannot start here: bwrap: setting up uid map: Permission denied)».
  2. the same clone, PATH stripped of the directory holding `capped`,
     `CAPPED_MEM_MAX` unset, `LEAN_NUM_THREADS=4` (the derivation's value for
     32G): `scripts/ci` — `RESULT: PASS`, 82 s (warm); «memory cap: capped NOT
     on PATH: heavy steps run uncapped (the cap is box tooling; CAPPED_MEM_MAX=
     unset, so 32G still sizes LEAN_NUM_THREADS)»; the same speedbump RED.
     (That note's wording was corrected in the fix round — «capped not on
     PATH: this script applies no cap itself» — because an outer cgroup can
     still be in force; the line quoted is the run's own at `268f7776`.)
Reproduce: the two command lists above in a fresh clone; the logs are
ephemeral.
