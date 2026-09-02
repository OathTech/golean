# BUG-082 fix evidence — the `make(map[K]V, hint)` hint lowered, gc vs machine (2026-09-02)

[AGENT] Worker record for the `bug082-maphint` lane. Consuming docs
(rule 8): `docs/BUGS.md` BUG-082 (Status: fixed), the baseline re-pin
headers `baselines/native-full.tsv` / `baselines/negative-full.tsv`,
latitude inventory R16 (`docs/2026-08-11_latitude-inventory.md`),
`docs/language-coverage-ledger.md` (Making_slices_maps_and_channels
row, §8), `docs/coverage-ledger.md` (Builtins row). Corpus:
`Corpus/coverage/exec/builtins/make-map-hint-eval/` (13 rows),
`Corpus/coverage/exec/builtins/make-maxalloc/map-hint-eval-order`
(the born-red witness, flipped), `Corpus/coverage/negative/compile/
maps/make-map-{float,string,negative-const,overflow-const}-hint`.

## Authorization (provenance, rule 7)

[USER] Mike, 2026-09-02, relayed to this worker by the [AGENT]
coordinator — NOT firsthand: «Issue (2) sounds like a clear win, it's
a bug fix right? do it», where issue (2) was the coordinator's item
"BUG-082 frontend fix: authorizes moving the twin-wire pin". The
twin-wire pin move below is authorized for THIS reason only. All
other decisions in this directory are [AGENT].

## Toolchain, tree, host (rules 3–5)

- Oracle: `go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`.
- Machine: Lean toolchain per `lean-toolchain` (`leanprover/lean4:
  v4.32.2`), golean binary `.lake/build/bin/golean` built by
  `scripts/capped lake build golean` from the tree named next.
- Tree (rule 4): every run below was made on the `bug082-maphint`
  worktree at `fa4fce58` (branch base = main at the time) with the
  slice's changes UNCOMMITTED (`git_dirty=true` in the saved meta
  files); they were committed unchanged as the commit that adds this
  directory (`git log -1 --format=%H -- docs/evidence/2026-09-02_bug082-maphint/README.md`).
  The "pre-fix frontend" replication uses `emit.go` at `fa4fce58`
  exactly (`git show fa4fce58:tools/nativefrontend/emit.go`).
- Host: linux/amd64; nothing here is timing- or load-sensitive.

## The question

The Go spec lists the map hint among a `make` call's ordinary size
operands (spec#Making_slices_maps_and_channels) and orders operand
calls and panics left to right (spec#Order_of_evaluation); gc's
runtime then CLAMPS a negative or over-limit hint to 0 and never
panics on it (`deps/go/src/runtime/map.go` `makemap`, `maps.NewMap`).
BUG-082: the native frontend's `emitMake` never visited `c.Args[1]`
for a map, so the hint's EVALUATION (side effects, panics, exactly-
once) was dropped end-to-end. Does the fixed frontend + decoder
realize gc's observable behavior — effects yes, value no?

## What changed (the fix under test)

- `tools/nativefrontend/emit.go` `emitMake`, `*types.Map` arm: emits
  the hint as the `make-map` node's `hint` field EXACTLY when the Go
  source has a second argument; absent otherwise.
- `GoLean/NativeToIR.lean`: the strict key list for `"make-map"` gains
  `hint` (nothing else widened — any other key still refuses); the
  decoder passes `hint` as `Stmt.makeMap`'s `initialSpace`.
- NO GoCore change: `applyStmtOpCore`'s `makeMap` arm already
  evaluated an optional hint operand and ignored its value.
- WHERE THE HINT IS EVALUATED (two halves, both in operand order):
  calls inside the hint are hoisted by the frontend into `$c` temps
  BEFORE the `make-map` statement (the path every effectful operand
  takes; `probe.wire.json` shows `hint` as an ident naming the hoisted
  temp); the residual call-free expression is evaluated by the machine
  arm as the operand after the target address. The corpus rows
  `index-panic-*` (a call-free out-of-range index as the hint) witness
  the machine-side half: the panic is raised there, before the map
  exists.

## Artifacts

| file | what |
| --- | --- |
| `probe/main.go` | the side-effect probe family (the maxAlloc auditor's `make(map, bump())` shape and four more: two bumps in one hint, negative-from-call, panicking hint with a `created` flag, order vs neighbouring calls) |
| `gc-transcript.txt` | gc (`go run`) values: 31 / 50 / -677 / 1 / 12341 |
| `probe.wire.json` | the FIXED frontend's wire for `probe/` (5/5 make-map nodes carry `hint`) |
| `machine-transcript.txt` | the fixed golean on `probe.wire.json`: 31 / 50 / -677 / 1 / 12341 — equal to gc on every probe |
| `probe.wire.prefix-frontend.json` | the PRE-FIX frontend's wire for `probe/` (0/5 make-map nodes carry `hint`; the hint's calls are not hoisted either) |
| `machine-transcript-prefix-frontend.txt` | the fixed golean on the pre-fix wire: 11 / 10 / -877 / 11 / 1341 — the red-first; the whole delta is the frontend |
| `focused-diff-one.tsv` (+ `focused-diff-one.meta.tsv`, `focused-diff-one-2.meta.tsv`) | `scripts/diff-one` over the 17 map-hint rows (the 13 new, the flipped witness, the two gc-truth rows, `builtins/make-map-hint`): 17/17 PASS; two invocations merged (the index-panic rows were added after the first) |
| `twin-pin-structural-diff.txt` | old vs new `baselines/pins/twin-chdriver.wire.json`: no method/func added or removed, no other top-level key moved; exactly two make-map nodes gain `hint` — `tracker.Config.Clone$lit0` (`make(map[uint64]struct{}, len(m))`) and `raft.lockedRand.Intn` (`make(map[int]struct{}, n)`) — and each changed unit is byte-identical once the `hint` fields are removed |

## Findings

1. Effects yes, value no. On all five probes the fixed machine equals
   gc; the pre-fix frontend through the same decoder differs on all
   five, each by exactly the dropped hint evaluation (the bump not
   applied; the panic not raised — `probeHintPanic` returns the
   "created" value 11 instead of the recovered 1; the log digit 2
   missing from `probeOrder`).
2. A negative hint from a call is evaluated and clamped: `-677` on
   both sides (n bumped from -9 to -7, map holds 2 entries).
3. Non-integer / non-representable constant hints never reach the
   lowering: the frontend refuses them at its go/types type-check with
   gc's own messages (transcript below); the negative rows pin the
   compile-time rejection (`go build` oracle, 394/394 PASS).
4. Pins: the deviation pin `hidden-dep-order` is UNCHANGED ("ok
   [hidden-dep-order]"); the twin-wire pin moved `b4ef84e433c1…` →
   `eef32142627a…` and `scripts/check-frontend-pins` reports "ok
   [twin-wire] — fresh emit = pinned wire (eef32142627a…)" at the
   re-pinned tree.

## Frontend refusal transcript (finding 3)

```
$ GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/negative/compile/maps/make-map-float-hint --out /dev/null
nativefrontend: type-check: Corpus/coverage/negative/compile/maps/make-map-float-hint/main.go:4:24: 1.5 (untyped float constant) truncated to int
$ ... --dir Corpus/coverage/negative/compile/maps/make-map-string-hint ...
nativefrontend: type-check: .../main.go:4:24: cannot convert "8" (untyped string constant) to type int
$ ... --dir Corpus/coverage/negative/compile/maps/make-map-negative-const-hint ...
nativefrontend: type-check: .../main.go:4:24: invalid argument: index -1 (constant of type int) must not be negative
$ ... --dir Corpus/coverage/negative/compile/maps/make-map-overflow-const-hint ...
nativefrontend: type-check: .../main.go:4:24: 1 << 64 (untyped int constant 18446744073709551616) overflows int
```
(each exits 1; the `--out` path was a scratch file, nothing written).

## Reproduction (rule 2; from the repo root)

```
export GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache"
E=docs/evidence/2026-09-02_bug082-maphint
# gc side
{ echo "# producer: go run ./$E/probe (GO111MODULE=off; $(go version))"; go run ./$E/probe; } > $E/gc-transcript.txt
# fixed frontend + fixed machine
scripts/capped lake build golean
go run ./tools/nativefrontend --dir $E/probe --out $E/probe.wire.json
for f in probeBump probeBumpTwice probeNegBump probeHintPanic probeOrder; do printf '%s\t' $f; .lake/build/bin/golean native-json-run --input $E/probe.wire.json --function $f; echo; done   # = machine-transcript.txt body
# pre-fix frontend (emit.go at fa4fce58) + fixed machine
S=$(mktemp -d "$TMPDIR/oldfe.XXXXXX"); cp -r tools/nativefrontend/. $S/; git show fa4fce58:tools/nativefrontend/emit.go > $S/emit.go
(cd $S && go build -o ../oldfe.bin .); $S/../oldfe.bin --dir $E/probe --out $E/probe.wire.prefix-frontend.json
for f in probeBump probeBumpTwice probeNegBump probeHintPanic probeOrder; do printf '%s\t' $f; .lake/build/bin/golean native-json-run --input $E/probe.wire.prefix-frontend.json --function $f; echo; done   # = machine-transcript-prefix-frontend.txt body
# focused differential (17 rows)
scripts/capped scripts/diff-one builtins/make-map-hint-eval/{panic-map-never-created,panic-uncaught,index-panic-map-never-created,index-panic-uncaught,evaluated-once,negative-from-call,zero,named-int-type,uint8-var,untyped-const,typed-const,eval-order-with-neighbors,eval-order-in-expression} builtins/make-maxalloc/{map-hint-eval-order,map-hint-over,map-hint-negative} builtins/make-map-hint
# pins (the twin re-pin = copying check-frontend-pins' fresh emit over the pinned file, then re-running)
scripts/capped scripts/check-frontend-pins
# twin pin structural diff: the python block below, old = git show fa4fce58:baselines/pins/twin-chdriver.wire.json
python3 - > $E/twin-pin-structural-diff.txt <<'PYEOF'
import json, subprocess
old = json.loads(subprocess.run(["git","show","fa4fce58:baselines/pins/twin-chdriver.wire.json"],capture_output=True,text=True).stdout)
new = json.load(open("baselines/pins/twin-chdriver.wire.json"))
om={(m.get("recvType"),m.get("name")): m for m in old["methods"]}; nm={(m.get("recvType"),m.get("name")): m for m in new["methods"]}
ofm={f.get("name"):f for f in old.get("funcs",[])}; nfm={f.get("name"):f for f in new.get("funcs",[])}
print("method keys only-in-old:", sorted(set(om)-set(nm))); print("method keys only-in-new:", sorted(set(nm)-set(om)))
print("funcs only-in-old:", sorted(set(ofm)-set(nfm))); print("funcs only-in-new:", sorted(set(nfm)-set(ofm)))
for k in sorted(set(old)|set(new)):
    if k not in ("methods","funcs") and old.get(k)!=new.get(k): print("top-level differs:", k)
def nodes(o,acc,path=""):
    if isinstance(o,dict):
        if o.get("stmt")=="make-map": acc.append((path,o))
        for k,v in o.items(): nodes(v,acc,path+"."+k)
    elif isinstance(o,list):
        for i,v in enumerate(o): nodes(v,acc,path+f"[{i}]")
def strip(z):
    if isinstance(z,dict):
        if z.get("stmt")=="make-map": z.pop("hint",None)
        for v in z.values(): strip(v)
    elif isinstance(z,list):
        for v in z: strip(v)
def unit(label,o,n):
    print("===== changed", label); oa=[];na=[]; nodes(o,oa); nodes(n,na); print("  make-map nodes old/new:", len(oa), len(na))
    for (pp,x),(qq,y) in zip(oa,na):
        if x!=y: print("  make-map at", qq); print("    old keys:", sorted(x)); print("    new keys:", sorted(y)); print("    new hint:", json.dumps(y.get("hint"),sort_keys=True))
    o2=json.loads(json.dumps(o)); n2=json.loads(json.dumps(n)); strip(o2); strip(n2); print("  identical once hint fields are removed:", o2==n2)
for name in sorted(n for n in set(ofm)&set(nfm) if ofm[n]!=nfm[n]): unit("func "+name, ofm[name], nfm[name])
for k in sorted(k for k in om if k in nm and om[k]!=nm[k]): unit("method "+str(k), om[k], nm[k])
PYEOF
```

## Gate (appended after the full run)

`scripts/capped scripts/ci --diff` on this worktree with the slice's
changes uncommitted (tree `fa4fce58` + changes, `git_dirty=true`;
the full summary is `gate-tail.txt`): **RESULT: PASS** — core build
warning-free; frontend pins ok (deviation observation unchanged, twin
wire = re-pinned bytes); eval tests 146 ok; differential FULL
2572/2572, no regression against the re-pinned `native-full.tsv`
(so the drift vs the PREVIOUS pin is exactly the 14 rows its header
lists: 13 born-PASS + 1 FAIL→PASS flip, verified row-by-row with
`diff` of the data rows); negative 394/394 matched; re-pin guard 0
PASS→non-PASS flips; `tools/reconcile-records` 0 HIGH (3 report-only
findings, pre-existing); `scripts/check-spec-anchors` ok (590 spec# +
164 mem# resolve at pin c19862e5f). [AGENT] No source file was
edited after the gate started; the commit that adds this directory
is the gated tree.
