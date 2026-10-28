#!/usr/bin/env bash
set -u
export LC_ALL=C
resolve() {
  local u; u=$(git diff --name-only --diff-filter=U); [ -z "$u" ] && return 0
  local f
  while IFS= read -r f; do
    case "$f" in
      baselines/native-full.tsv|baselines/negative-full.tsv) python3 -I tools/stage/baseline-union3.py "$f" || return 1;;
      docs/BUGS.md|docs/changelog/20d3946d-WINDOW.md|docs/defect-shapes.md|docs/spec-divergence-ledger.md) python3 -I tools/stage/keep-both.py "$f" || return 1;;
      Tests/GoCoreEval.lean) git checkout --theirs -- "$f" && echo "$f: theirs (the fix lane's pins replace the sweep's)";;
      *) echo "STOP: unexpected conflict in $f"; return 1;;
    esac
  done <<< "$u"
  git add $u && GIT_EDITOR=true git cherry-pick --continue 2>&1 | tail -1
}
for c in "$@"; do echo "=== $c ==="; git cherry-pick "$c" 2>&1 | grep -i 'conflict'; resolve || { echo "stopped at $c"; exit 1; }; done
