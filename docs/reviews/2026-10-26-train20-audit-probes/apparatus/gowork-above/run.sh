#!/usr/bin/env bash
# Gate-survival under a go.work ABOVE the checkout: the negative corpus (full) and a positive
# subset, run from a symlinked view of the worktree whose logical parent carries go.work
# (`go 1.26` / `godebug panicnil=1`, no `use`: module-mode gc without GOWORK=off refuses
# «no modules were found in the current workspace»; the frontend without GOWORK=off refuses
# the directory by name). SKIP_NEGATIVE=1 skips the negative pass.
set -u
WS="$(cd "$(dirname "$0")" && pwd -P)"
LOCK=/home/mike/projects/golean/artifacts/build-lock.d
until mkdir "$LOCK" 2>/dev/null; do sleep 15; done
printf 'audit20-app-1026 %s %s\n' "$$" "$(date -Is)" > "$LOCK/owner"
trap 'rm -rf "$LOCK"' EXIT
cd "$WS/repo"
echo "pwd(logical)=$PWD"; echo "go.work above: $(ls -la ../go.work | cut -c1-60)"
if [ "${SKIP_NEGATIVE:-0}" = 1 ]; then
  echo "== negative corpus skipped (already run) =="
else
  start=$(date +%s)
  echo "== negative corpus (full) =="
  env -u GOWORK -u GOFLAGS capped scripts/coverage-negative > "$WS/negative.log" 2>&1; echo "negative rc=$? ($(( $(date +%s) - start ))s)"
  grep -v '^#' artifacts/coverage/negative-latest.tsv | cut -f1 | sort | uniq -c
fi
echo "== positive subset =="
start=$(date +%s)
env -u GOWORK -u GOFLAGS capped scripts/coverage run \
  --id comparisons/nil-left-operand/pointer --id comparisons/nil-left-operand/switch-case \
  --id pointers/struct-through-conversion-value/eq-literal --id directives/debug-panicnil \
  --id noodler/defers/panic-nil-recovered --id panic-recover/repanic-collapse/nil-passthrough \
  > "$WS/positive.log" 2>&1; echo "positive rc=$? ($(( $(date +%s) - start ))s)"
grep -v '^#' artifacts/coverage/latest.tsv | cut -f1-4
grep -E '^(manifest_cases|filters|git_commit)' artifacts/coverage/latest.meta.tsv
