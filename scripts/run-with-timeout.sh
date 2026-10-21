# scripts/run-with-timeout.sh — run_with_timeout <seconds> <cmd...>, SOURCED by
# the differential runner and its siblings (scripts/diff-coverage,
# coverage-negative, detector-soundness, oracle-386-static). One definition
# since 2026-10-21 (box-independence fix round, release-readiness row 46;
# before, each script carried the same perl one-liner).
#
# THE EXIT-CODE CONTRACT, which every consumer tests before reading a killed
# command's output as a verdict (docs/operational-lessons.md, «A killed
# command has decided nothing»):
#   124          the wall clock fired (TERM to the command's process group, one
#                second, then KILL) — distinct from 137, a cgroup/OOM kill;
#   128+N        the command died of signal N (137 SIGKILL, 143 SIGTERM);
#   127          the command could not be exec'd;
#   2            the timeout is not a positive integer: refused loudly, never
#                a disabled guard (the callers validate their knobs first);
#   else         the command's own exit status.
# Why not coreutils `timeout`, measured 2026-10-21: GNU 9.7 and uutils 0.8.0
# both exit 137 when the KILL after --kill-after was needed (the contract's
# 124), and they differ from each other on a TERM death (143 vs 15); an exit
# code that depends on which coreutils is installed is box-dependence. Why
# Python and not perl (the 2026-08..10 one-liner): Python ≥ 3.11 is already a
# declared dependency and perl is not; the port keeps the contract exactly
# (eight probes in the lessons entry) at +8 ms a call (9.6 vs 1.9 ms).
#
# The command runs in its OWN PROCESS GROUP and the kill goes to the group, so
# a timed-out `go run` takes its compiled child with it and a capped build
# (`run_with_timeout 60 $(cap_argv) lake build`: the box tool between the
# wrapper and lake) dies whole — the perl wrapper killed the direct child only
# and left grandchildren running. SIGTERM/SIGINT to the wrapper are forwarded
# to the group the same way (exit 128+N), so Ctrl-C still reaches a command
# that is no longer in the terminal's group.
#
# RUN_WITH_TIMEOUT_ANNOUNCE=1 (diff-coverage sets it) makes the timeout
# announce itself on stderr — «run_with_timeout: TIMED OUT after Ns — killing:
# …» — belt and braces for a consumer that captures 2>&1 and forgets the exit
# code; the other sources keep stderr clean, as before.
#
# EXPORTED, and guarded, because diff-coverage hands its functions to `xargs`
# workers with `export -f`: the function travels, a plain shell variable does
# not, and `python3 -c ""` exits 0 having run NOTHING — the first port did
# exactly that in every worker (the harness step «succeeded» without writing
# its directory and the oracle's reset then failed with 78), which
# scripts/test-lane-validation caught (2026-10-21). So the program is exported
# with the function, and a shell where it is empty refuses (exit 70, a code no
# consumer reads as a verdict) instead of running nothing.

RUN_WITH_TIMEOUT_PY='
import os, signal, sys, time
try:
    t = int(sys.argv[1]); assert t > 0
except Exception:
    sys.stderr.write("run_with_timeout: the timeout must be a positive integer (seconds), got %r\n" % (sys.argv[1:2] or [""])[0]); os._exit(2)
announce = sys.argv[2] == "1"
argv = sys.argv[3:]
if not argv:
    sys.stderr.write("run_with_timeout: no command\n"); os._exit(2)
pid = os.fork()
if pid == 0:
    os.setpgid(0, 0)
    try:
        os.execvp(argv[0], argv)
    except OSError as e:
        sys.stderr.write("run_with_timeout: cannot exec %s: %s\n" % (argv[0], e)); os._exit(127)
def group(sig):
    try: os.killpg(pid, sig)
    except ProcessLookupError: pass
def on_alarm(*_):
    if announce:
        sys.stderr.write("run_with_timeout: TIMED OUT after %ds — killing: %s\n" % (t, " ".join(argv)))
    group(signal.SIGTERM); time.sleep(1); group(signal.SIGKILL); os._exit(124)
def forward(signum, *_):
    group(signum); time.sleep(1); group(signal.SIGKILL); os._exit(128 + signum)
signal.signal(signal.SIGALRM, on_alarm)
signal.signal(signal.SIGTERM, forward)
signal.signal(signal.SIGINT, forward)
signal.alarm(t)
_, st = os.waitpid(pid, 0)
os._exit(128 + os.WTERMSIG(st) if os.WIFSIGNALED(st) else os.WEXITSTATUS(st))
'

export RUN_WITH_TIMEOUT_PY

run_with_timeout() {
  local seconds="$1"
  shift
  if [ -z "${RUN_WITH_TIMEOUT_PY:-}" ]; then
    echo "run_with_timeout: the wrapper program is not defined in this shell (scripts/run-with-timeout.sh not sourced, or not exported to this worker) — refusing to run nothing" >&2
    return 70
  fi
  python3 -I -S -c "$RUN_WITH_TIMEOUT_PY" "$seconds" "${RUN_WITH_TIMEOUT_ANNOUNCE:-0}" "$@"
}
