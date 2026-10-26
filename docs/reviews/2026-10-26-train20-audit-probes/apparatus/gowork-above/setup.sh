#!/usr/bin/env bash
# Builds the symlinked view: <worktree>/.tmp/ws/go.work above <worktree>/.tmp/ws/repo/, whose
# entries are symlinks to the worktree's (artifacts/ and .tmp/ real and empty). The scripts
# resolve ROOT with `pwd -P` of their own directory, which stays inside the view (a real dir);
# every `cd Corpus/...` keeps the logical path, so gc's walk (base.Cwd = $PWD) and the frontend's
# (filepath.Abs) both see ../go.work unless GOWORK=off is pinned. Then: run.sh (this directory).
set -eu
ROOT="$(git rev-parse --show-toplevel)"; WS="$ROOT/.tmp/ws"
rm -rf "$WS"; mkdir -p "$WS/repo/artifacts/coverage" "$WS/repo/.tmp"
cp "$(dirname "$0")/go.work" "$WS/go.work"
for e in $(ls -A "$ROOT" | grep -vx -e artifacts -e .tmp); do ln -s "$ROOT/$e" "$WS/repo/$e"; done
cp "$(dirname "$0")/run.sh" "$WS/run.sh"; chmod +x "$WS/run.sh"
echo "view at $WS/repo; now: $WS/run.sh (the negative corpus, then the positive subset)"
