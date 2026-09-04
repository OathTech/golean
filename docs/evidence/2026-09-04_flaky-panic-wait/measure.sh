#!/usr/bin/env bash
# usage: measure2.sh <bin> <n> <label>   — classify (rc, stdout-has-ok-json, stderr-has-panic)
bin=$1; n=$2; label=$3
out="dist-$label.tsv"; : > "$out"
for i in $(seq 1 "$n"); do
  so=$("$bin" 2>err.tmp); rc=$?
  okj=$(printf '%s' "$so" | grep -c '"status":"ok"'); pn=$(grep -c '^panic: under-wait' err.tmp)
  printf '%s\t%s\t%s\t%s\n' "$i" "$rc" "okjson=$okj" "panic=$pn" >> "$out"
done
echo "== $label ($n runs of $bin)"; cut -f2- "$out" | sort | uniq -c
