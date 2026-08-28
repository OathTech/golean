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
