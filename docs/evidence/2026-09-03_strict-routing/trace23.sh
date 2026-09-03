#!/usr/bin/env bash
set -uo pipefail
M=artifacts/strict-routing
ids="fmt/fprintf-builder/describe-shape fmt/fprint-writers/fprintf-buffer-shape fmt/sprintf-dyn/logger-shape fmt/sprintf-dyn/sprint-space-rule fmt/sprintf-dyn/verb-kinds fmt/sprintf-verbs/d-width multipkg/mini-raft-twin/duel multipkg/mini-raft-twin/elect-propose-commit multipkg/mini-raft-twin/perturb-picks multipkg/mini-raft-twin/perturb-rev multipkg/mini-raft-twin/starve-node strconv/format-parse/format-int-vals strconv/format-parse/format-uint-bases strconv/format-parse/parse-uint-errors strconv/format-parse/parse-uint-range-value spec-examples-stmt/prime-sieve/five spec-examples-stmt/prime-sieve/eight goroutines/worker-pool/shared-feed sync/waitgroup-workers-join/workers-join imported-goose/channel/parallel-search-replace/search-replace fmt/sprintf-verbs/d-int fmt/sprintf-verbs/d-uint spec-examples-stmt/go-statements/named-call"
: > $M/rows23.tsv
for id in $ids; do awk -F'\t' -v id="$id" '$1==id{print $1"\t"$3"\t"$4}' $M/manifest.tsv >> $M/rows23.tsv; done
S1=$($M/seeded-stream.sh 1 256); S2=$($M/seeded-stream.sh 2 256); S3=$($M/seeded-stream.sh 3 256)
S1L=$($M/seeded-stream.sh 1 2048); S2L=$($M/seeded-stream.sh 2 2048); S3L=$($M/seeded-stream.sh 3 2048)
: > $M/trace23.tsv; : > $M/trace23.err
while IFS=$'\t' read -r id fn args; do
  a=(); if [ "$args" != "-" ]; then IFS=',' read -ra xs <<< "$args"; for x in "${xs[@]}"; do a+=(--arg-int "$x"); done; fi
  case "$id" in spec-examples-stmt/prime-sieve/*) A=$S1L; B=$S2L; C=$S3L;; *) A=$S1; B=$S2; C=$S3;; esac
  .lake/build/bin/golean choice-trace --input artifacts/coverage/native/$id/wire.json --function "$fn" "${a[@]}" --stream default --stream 9,8,7,6,5,4,3,2,1,0 --stream 1,3,5,7,9,2,4,6,8,0 --stream 5,5,5,5,5,5,5,5 --stream "$A" --stream "$B" --stream "$C" 2>>$M/trace23.err | tail -n +2 | awk -F'\t' -v id="$id" '{s=$2; if (length(s)>40) s="seeded" NR-4 "/len" split(s,t,","); print id"\t"s"\t"$3"\t"$4"\t"$5"\t"$6"\t"$7"\t"$8"\t"$15}' >> $M/trace23.tsv
done < $M/rows23.tsv
