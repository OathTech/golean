# scripts/cap.sh — the memory cap, SOURCED (`. "$ROOT/scripts/cap.sh"`) by every
# script that runs a heavy command: lake, lean, leanchecker, the differential
# runner. Box-independence (release-readiness row 46, [USER] 2026-10-21): the
# memory-capping wrapper `capped` is box tooling, detected at run time and
# never copied into the project. Scripts run heavy commands through `cap`,
# size the limit with CAPPED_MEM_MAX (never `-m`, which only `capped`
# understands), and where `capped` is absent the command runs UNCAPPED,
# silently: the cap is enforced on the Oath boxes only, and other machines
# must not depend on it. The former shim `scripts/capped` was removed the
# same day; GOLEAN_MEM_MAX and GOLEAN_CAPPED are retired names
# (docs/operational-lessons.md, «Box-independence»).
#
# Nesting: the box tool execs straight through under CAPPED_STATE=verified,
# so `capped scripts/ci` runs the whole gate in one cgroup and the inner
# `cap` calls add nothing; a bare `scripts/ci` caps each heavy step by
# itself. CAPPED_MEM_MAX=none is the box tool's loud opt-out and means
# nothing where the tool is absent.
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }

# cap_argv: the same choice as an argv PREFIX, for a site that hands its
# command to another wrapper which execs its argv (run_with_timeout), where a
# shell function cannot go: `run_with_timeout 60 $(cap_argv) lake build`
# (unquoted on purpose: empty when the tool is absent).
cap_argv() { if command -v capped >/dev/null 2>&1; then echo capped; fi; }

# cap_lean_threads: scale Lean's thread pool to the cap (a performance knob,
# not a check). The pool bounds the concurrent `lean` workers AND the
# per-file elaboration; peak memory is a sum of per-thread peaks, 8G a
# thread measured (docs/operational-lessons.md, «Concurrency OOM»). Exports
# LEAN_NUM_THREADS = cap/8G (floor 2) from CAPPED_MEM_MAX — default 32G, the
# box default, a project choice that applies with or without the tool —
# unless the caller set it. Sets CAP_THREADS_NOTE either way, and CAP_MEM_GB
# to the integer size in G (empty when the cap is not an integer size, e.g.
# `none`, or uses a K/T suffix).
cap_lean_threads() {
  local mem num unit jobs
  CAP_MEM_GB=""
  mem="${CAPPED_MEM_MAX:-32G}"
  case "$mem" in
    none)  num=""; unit="" ;;
    *[Gg]) num="${mem%[Gg]}"; unit=G ;;
    *[Mm]) num="${mem%[Mm]}"; unit=M ;;
    *)     num="$mem"; unit=B ;;
  esac
  case "$num" in ''|*[!0-9]*) num="" ;; esac
  if [ -n "$num" ]; then
    case "$unit" in G) CAP_MEM_GB="$num" ;; M) CAP_MEM_GB=$(( num / 1024 )) ;; B) CAP_MEM_GB=$(( num / 1073741824 )) ;; esac
  fi
  if [ -n "${LEAN_NUM_THREADS:-}" ]; then
    CAP_THREADS_NOTE="LEAN_NUM_THREADS=$LEAN_NUM_THREADS (set by the caller — honoured as-is)"
  elif [ -z "$CAP_MEM_GB" ]; then
    CAP_THREADS_NOTE="LEAN_NUM_THREADS unset (cap '$mem' is not an integer size — toolchain default)"
  else
    jobs=$(( CAP_MEM_GB / 8 )); [ "$jobs" -lt 2 ] && jobs=2
    export LEAN_NUM_THREADS="$jobs"
    CAP_THREADS_NOTE="cap $mem -> LEAN_NUM_THREADS=$jobs (cap/8G, floor 2)"
  fi
}

# cap_note: one line saying what this script does about the cap, for a
# gate's record (honest measurement: a run says what it ran under). Without
# the tool the script applies no cap ITSELF — an outer cgroup (the GitHub
# workflow's systemd scope, a `capped` further up) may still be in force,
# which this script cannot see; the thread sizing is cap_lean_threads's own
# line.
cap_note() {
  local mem state tool
  mem="${CAPPED_MEM_MAX:-unset}"; state="${CAPPED_STATE:-unset}"
  if tool="$(command -v capped 2>/dev/null)"; then
    echo "capped on PATH ($tool); CAPPED_MEM_MAX=$mem; CAPPED_STATE=$state"
  else
    echo "capped not on PATH: this script applies no cap itself (the cap is box tooling); CAPPED_MEM_MAX=$mem"
  fi
}
