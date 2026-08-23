#!/usr/bin/env bash
# u5-manifest.sh — recompute the U5 run manifest FROM THE BUILD ARTIFACTS
# (never restated): segment -> done/pending, done iff the olean exists and
# is newer than its generated source. Writes the manifest TSV and appends
# one dated summary line to the manifest log.
set -u
cd "$(dirname "$0")/../.." || exit 9
SRC=proofs/GoLeanProofs/Specs
OL=proofs/.lake/build/lib/lean/GoLeanProofs/Specs
MAN=docs/campaign-arc2-probes/records/u5-manifest.tsv
LOG=docs/campaign-arc2-probes/records/u5-manifest-log.txt
{
  echo -e "# U5 run manifest — recomputed $(date -u +%FT%TZ) from oleans under $OL"
  echo -e "# kind\tmodule\tstatus"
  done_n=0; tot=0
  for kind in TwinCkpts TwinSegs; do
    for f in "$SRC/$kind"/*.lean; do
      [ -e "$f" ] || continue
      b=$(basename "$f" .lean); tot=$((tot+1))
      o="$OL/$kind/$b.olean"
      if [ -f "$o" ] && [ "$o" -nt "$f" ]; then s=done; done_n=$((done_n+1)); else s=pending; fi
      echo -e "$kind\t$b\t$s"
    done
  done
  echo -e "# done/total: $done_n/$tot"
} > "$MAN.tmp" && mv "$MAN.tmp" "$MAN"
summary=$(tail -1 "$MAN")
echo "$(date -u +%FT%TZ) $summary" >> "$LOG"
echo "$summary"
