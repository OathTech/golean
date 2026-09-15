# Static sweep census over lowered wires — spike for the evaluation-order model (2026-09-15)

[AGENT] Disposable estimate for `docs/2026-09-15_evaluation-order-model.md` §6
(«can the machine express an unordered operand pair through the tape without the
choice-stream count exploding across the corpus»). Static only: no Lean build,
no machine run, no baseline touched. Counts are UPPER BOUNDS on the probe/use
pairs the model would emit (the wire cannot tell a captured local from a private
one, nor a constant divisor from a variable one) and say nothing about stream
POPS, which under the model's consult-on-difference rule occur only when a
sibling event changes an operand's outcome.

- Commit: main `a7d553f7` (worktree clean; the frontend binary built from this tree).
- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`).
- Host: linux/amd64, no timing-sensitive numbers.

## Reproduction (repo root)

    mkdir -p .tmp/gocache .tmp/wires
    GO111MODULE=off GOCACHE=$PWD/.tmp/gocache go build -o .tmp/nativefrontend ./tools/nativefrontend
    for tsv in $(find Corpus/coverage/exec -name cases.tsv | sort); do d=$(dirname "$tsv"); id=${d#Corpus/coverage/exec/}
      f=(); case "$id" in init/hidden-dep*) f+=(--allow-hidden-dep-init-order);; esac
      GO111MODULE=off GOCACHE=$PWD/.tmp/gocache .tmp/nativefrontend "${f[@]}" --dir "$d" --out ".tmp/wires/${id//\//__}.json" 2>/dev/null || true; done
    # 1330 of 1353 case directories lower; the 23 refusals are the designed reds (BUG-102 and kin).
    python3 docs/evidence/2026-09-15_eval-order-model-spike/count.py baselines/pins/twin-chdriver.wire.json
    python3 docs/evidence/2026-09-15_eval-order-model-spike/count.py .tmp/wires/*.json

## Definitions (count.py)

- sweep: a run of hoisted statements (`$c` temps, statement-form hoists, `unseq-probe`) plus the residual statement that closes it; nested bodies are their own sweeps.
- event: a hoisted call / call-value / receive / `len` / `cap` / `min` / `max` / `recover` / `append` / `copy` / `make` / `new` (the spec's ordered operations, built-ins included).
- panicky_in_event_sweeps: residual `index-get`/`index-addr`/`deref`/`slice`/`type-assert`/`map-get`/`field-addr`/`\/`/`%` nodes in event-bearing sweeps (today's `probeKind` census, approximated on the wire — the operands the model pairs in slice 1).
- plain_in_event_sweeps: residual non-temp `ident`/`field-get`/`globaladdr` reads in event-bearing sweeps (the mutable-read widening of slice 2; upper bound).
- bug104_early_once_temps: compound/IncDec targets whose address is a hoisted temp, plus every `map-compound-assign` (BUG-104's early "once"-temps).
- e2_call_rhs_addr_target: non-define assigns with a call RHS and an addressed (index/deref/field) target (E2's shape).

Check: the twin's `probes` = 128, the count the e13-b design §10 recorded — the segmentation reproduces the tracked number.
