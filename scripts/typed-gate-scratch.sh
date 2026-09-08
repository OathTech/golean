# [AGENT] 2026-09-08. Source only from a restored typed gate after ROOT is set.
# Every allocation belongs to this invocation, including on abrupt failure.
export TMPDIR="$ROOT/.tmp"
mkdir -p "$TMPDIR"
gate_scratch=$(mktemp -d "$TMPDIR/typed-gate.XXXXXX")
printf 'Gate has not completed: %s\n' "$0" > "$gate_scratch/failure.txt"
typed_gate_error() {
  local rc=$1 command=$2
  printf 'Command failed (exit %s): %s\n' "$rc" "$command" >> "$gate_scratch/failure.txt"
}
finish_scratch() {
  local rc=$?
  if [[ $rc = 0 ]]; then
    rm -rf -- "$gate_scratch"
  else
    printf 'Gate %s failed with exit %s; see the calling log.\n' "$0" "$rc" >> "$gate_scratch/failure.txt"
    printf 'Failed gate scratch retained: %s\n' "$gate_scratch" >&2
  fi
}
trap 'typed_gate_error "$?" "$BASH_COMMAND"' ERR
trap finish_scratch EXIT
