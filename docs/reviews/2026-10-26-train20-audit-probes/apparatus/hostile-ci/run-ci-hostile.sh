#!/usr/bin/env bash
# The fast tier under a hostile Go environment: any gate step that inherits GOFLAGS fails
# loudly (-toolexec names a missing binary); any module-mode go or any unpinned frontend
# run sees GOWORK naming a missing workspace file.
set -u
cd "$(dirname "$0")/.."
LOCK=/home/mike/projects/golean/artifacts/build-lock.d
until mkdir "$LOCK" 2>/dev/null; do sleep 15; done
printf 'audit20-app-1026 %s %s\n' "$$" "$(date -Is)" > "$LOCK/owner"
trap 'rm -rf "$LOCK"' EXIT
start=$(date +%s)
GOFLAGS=-toolexec=/nonexistent/toolexec GOWORK=/nonexistent/go.work capped scripts/ci > .tmp/ci-hostile.txt 2>&1
echo "rc=$? seconds=$(( $(date +%s) - start ))" >> .tmp/ci-hostile.txt
