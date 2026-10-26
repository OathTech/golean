#!/usr/bin/env bash
# Run one race-location probe on both sides: the machine enumerates every
# schedule (`coverage-observations --expect-status <race|ok>`: a member outside
# the expected status fails the run), gc runs `go run -race`. Usage:
#   docs/reviews/2026-10-26-equality-probes/race.sh <probe-name> <race|ok>
# Same prerequisites as probe.sh.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
ROOT="$(cd "$HERE/../../.." && pwd -P)"
name="$1"; expect="$2"
d="$HERE/$name"
echo "=== $name (expect $expect) ==="
if ! (cd "$ROOT" && "$ROOT/.tmp/nativefrontend" --dir "$d") > "$d/wire.json" 2> "$d/fe.err"; then
  echo "[frontend REFUSED] $(head -c 500 "$d/fe.err")"
else
  "$ROOT/.lake/build/bin/golean" coverage-observations --input "$d/wire.json" --function run --expect-status "$expect" --backedge full > "$d/enum.out" 2> "$d/enum.err"; rc=$?
  echo "[machine enum rc=$rc] $(tail -c 300 "$d/enum.err" | tr '\n' '|')"
  echo "[machine members] $(sort -u "$d/enum.out" | cut -c1-160 | tr '\n' '|')"
fi
( cd "$d" && GO111MODULE=off GOFLAGS= GODEBUG=panicnil=0 GOTRACEBACK=none go run -race . > go.stdout 2> go.stderr; echo "rc=$?" > go.rc )
if grep -q "WARNING: DATA RACE" "$d/go.stderr"; then gr=RACE; else gr="no-race"; fi
echo "[gc -race] $gr ($(cat "$d/go.rc"))"
