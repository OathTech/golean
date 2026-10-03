# The re-pin offer (window unit 7b) — evidence (2026-10-03)

[AGENT] unit 7b worker, branch `docs/repin-offer-1003`. Consuming documents: `docs/2026-10-03_offer-to-logic-team.md`
(the offer note) and the frozen «Offer summary» of `docs/changelog/61958f2e-WINDOW.md`. Authority: [USER] Mike 2026-10-03
«prepare the offer, do the dry run», relayed by the [AGENT] coordinator. Bulk (wires, the dry-run clone, build logs) stayed
in gitignored scratch and was deleted at the end; what is kept here reproduces from the pins below.

## Pins

| Pin | Value |
|---|---|
| Our tree | `main` @ `20d3946de2a8a8ffdbc462268180103351224fe7` (the offer's content commit; this records branch adds docs only); `HEAD:tools/nativefrontend` = `d2a644207098ccfcb14f466f53e9e61924742440` |
| Frontend binary | sha256 `6641453ac06a92afb0c04b292dfb63fdee586726596709ab6d562509c74c61c3` (`GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go build -o .tmp/inventory/nativefrontend ./tools/nativefrontend`) |
| Go toolchain | `go1.26.5 linux/amd64` = `baselines/go-oracle-pin` |
| Logic repository | `/home/dev/projects/golean-logic` @ `8a572d2412bb986fe7f8a90a6b9b1562ba96b2c8` (`main`, 2026-10-03 16:27 UTC, clean) — READ-ONLY to this lane (sources copied out; the dry run ran in a separate clone) |
| Their pins | `provenance/pins.json`: golean `61958f2e…` (their pin), iris `e7a0a438…`, batteries `023ce7d6…`, Qq `38d591e7…`, lean `v4.32.2`, go `c19862e5…` (= our `deps/go`) |

## Files

| File | What |
|---|---|
| `inventory-counts.tsv` | the recursive statement-node census (the 2026-09-24 walker `count-stmts.py`, unchanged) over the 31 retained wires: totals, `unseq` nodes, legacy probes, per-body-kind occurrences, statement histogram |
| `inventory-counts-control.tsv` | the same walker over two of OUR emitting packages (`len-vs-call-order`, `e13-sibling-panic-order`) — the instrument's positive control |
| `inventory-export-status.tsv` | exit status and stderr size per unit (all 0 / 0) |
| `inventory-census-admitted.tsv` | `--unseq-census` admitted-column tally per unit (a MAIN-UNIT sweep census; additional evidence, not the wire) |
| `inventory-wire-sha256.tsv` | digest and size of each retained scratch wire (the wire carries no absolute path) |
| `dryrun-module-status.tsv` | every enrolled logic module (242 of `provenance/audit.json` + the 4 consumer libraries): `ok` (built), `failed` (its own errors), `blocked` (a transitive import failed — the first failing import named) |
| `dryrun-error-census.tsv` | the 1864 error blocks grouped by CAUSE, with example `module:line:col`, the answering changelog row and the answering BridgeSet pins |
| `dryrun-errors-per-module.tsv` | per failing module: generated artifact vs hand-written, error blocks, whether Lean's `maxErrors` (100) truncated it, causes |
| `dryrun-differential.txt` | their gate's `differential` step (`scripts/diff-coverage` over their `examples/fixtures/manifest.tsv`, 18 rows) run in the dry-run workspace against our `main` — see the offer note §6 |

## Reproduction

Inventory (from the repo root; `CUST` = the logic checkout at the commit above, read-only):

```sh
mkdir -p .tmp/inventory/{src,wires,logs,census,control}
for d in "$CUST"/examples/fixtures/*/; do n=$(basename "$d"); mkdir -p .tmp/inventory/src/"$n"; cp "$d"*.go .tmp/inventory/src/"$n"/; done
python3 docs/evidence/2026-09-24_customer-fixture-inventory/gen-f2-variants.py "$CUST" .tmp/inventory/src   # their 8 f2 variants, reproduced
export GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache"; go build -o .tmp/inventory/nativefrontend ./tools/nativefrontend
for d in .tmp/inventory/src/*/; do n=$(basename "$d"); ./.tmp/inventory/nativefrontend --dir "$d" --out .tmp/inventory/wires/"$n".json 2> .tmp/inventory/logs/"$n".stderr; echo "$n $?";
  ./.tmp/inventory/nativefrontend --dir "$d" --unseq-census > .tmp/inventory/census/"$n".tsv; done
python3 docs/evidence/2026-09-24_customer-fixture-inventory/count-stmts.py .tmp/inventory/wires/*.json
```

Dry run (an isolated clone under OUR gitignored `deps/`; their repository untouched; no network):

```sh
git clone --local --no-hardlinks /home/dev/projects/golean-logic deps/golean-logic-dryrun
# the ONE edit in the clone: provenance/pins.json golean.rev := 20d3946de2a8a8ffdbc462268180103351224fe7
python3 tools/setup.py --golean-source /home/dev/projects/golean --reference-root "$PWD/deps" \
  --dependency-seed /home/dev/projects/golean-logic/packages/golean-iris/.lake/packages      # local clones + copied caches only
# under the box-wide lock (mkdir artifacts/build-lock.d), capped:
cd packages/golean-iris && GOLEAN_MEM_MAX=48G LEAN_NUM_THREADS=6 scripts/capped lake build GoLeanIris GoLeanIrisExamples GoLeanIrisAudit GoLean.NativeToIR
```

The build ran 142 s (lock taken 22:25:05 UTC, EXIT=1 at 22:27:27): 26 GoLean modules built with ZERO errors (`Machine`,
`StepFn`, `MachineSound`, `MultiSound`, `NativeToIR` among them; iris/batteries/Qq replayed from the copied caches); of their
modules 6 built, 28 failed on their own errors, 212 were blocked (189 through `GoLeanIris.Language`). Lake stops a failed
module's dependents, so the census is the import FRONTIER, not a whole-tree count; 16 modules hit Lean's `maxErrors` (100),
so their counts are lower bounds. No fix was attempted on their code.
