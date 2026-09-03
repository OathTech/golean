#!/usr/bin/env bash
# gc-draws — 20 `go run` draws of one row's harness, plain and -race
# ALTERNATING (membership-depth memo §4.3 order), each observation
# checked against a certified observation set with `golean observation-eq`.
#   gc-draws.sh <harness-dir> <certified-observations.txt> <out-dir> [golean-bin]
# Oracle invocation mirrors scripts/diff-coverage's go_run_oracle
# (GO111MODULE=off, GODEBUG=panicnil=0, repo-local GOCACHE, run from the
# harness dir). Exit 0 iff every draw is a member; 1 otherwise.
set -uo pipefail
hdir="$1"; cert="$2"; out="$3"; bin="${4:-.lake/build/bin/golean}"
ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
mkdir -p "$out"; : > "$out/draws.tsv"
bad=0
for i in $(seq 1 20); do
  mode=plain; flag=()
  if (( i % 2 == 0 )); then mode=race; flag=(-race); fi
  obs="$(cd "$hdir" && GO111MODULE=off GODEBUG=panicnil=0 GOCACHE="$ROOT/artifacts/go-build-cache" go run "${flag[@]}" . 2>&1)"; rc=$?
  member=NOT-A-MEMBER
  if [[ $rc -eq 0 ]]; then
    while IFS= read -r m; do
      if "$bin" observation-eq --left "$m" --right "$obs" >/dev/null 2>&1; then member=member; break; fi
    done < <(grep -v '^#' "$cert" | grep .)
  fi
  printf '%d\t%s\trc=%d\t%s\t%s\n' "$i" "$mode" "$rc" "$member" "$obs" >> "$out/draws.tsv"
  [[ "$member" == member ]] || bad=1
done
echo "distinct observations: $(cut -f5 "$out/draws.tsv" | sort -u | wc -l); non-members: $(grep -c 'NOT-A-MEMBER' "$out/draws.tsv")"
exit $bad
