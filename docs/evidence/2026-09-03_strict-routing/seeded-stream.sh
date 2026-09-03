#!/usr/bin/env bash
# seeded-stream.sh <seed> <N> — the depth= guard's seeded stream: a 31-bit
# LCG (glibc constants 1103515245/12345), value = bits 16..31 (0..65535),
# printed as the explicit comma list `--choices`/`--stream` accept.
seed="$1"; n="$2"; x="$seed"; out=""
for ((i = 0; i < n; i++)); do
  x=$(( (x * 1103515245 + 12345) & 0x7fffffff ))
  v=$(( (x >> 16) & 0xffff ))
  out+="${out:+,}$v"
done
printf '%s\n' "$out"
