#!/usr/bin/env bash
# twin-emit.sh <frontend> <out.json> — assemble the twin as scripts/check-frontend-pins does and emit
set -uo pipefail
FE="$1"; OUT="$2"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"; cd "$ROOT"
TW="$ROOT/.tmp/audit/twin-prog-$(basename "$FE")"; rm -rf "$TW"; mkdir -p "$TW"
for pkg in quorum raftpb tracker proto confchange raft; do cp -r "raftsubject/$pkg" "$TW/"; done
for f in twin-lib.go twin-chdriver.go twin-chdriver-main.go; do cp "tools/raftsubject/$f" "$TW/"; done
"$FE" --dir "$TW" --out "$OUT"; echo "EXIT=$?"; sha256sum "$OUT"
