# Twin-wire pin structural diff — the qrow-syncval re-pin's inspection record (2026-09-01)

[AGENT] The Q-SYNCVAL slice's re-pin commit (`b16738d3`) moved
`baselines/pins/twin-chdriver.wire.json` and asserted the delta was
"exactly the inspected sync-stub delta". This directory is that
inspection, per the docs/evidence convention (D-9): a structural JSON
diff of the old pin vs the new one, showing the delta is confined to
SIX method entries and NOTHING else — no method added or removed, no
func added/removed/changed, no other top-level key moved. [Count
corrected FIVE→SIX at the audit fix round (F5): the list below always
had six.]

The six changed entries (`structural-diff.txt` has the exact old/new
field values):

- `sync.Mutex.Lock`, `sync.Mutex.Unlock`: `unsupported` reason
  REPLACED BY a `body` — the P-S2-6 one-statement sync-op body
  (`{"stmt":"sync-op","op":"lock"/"unlock","args":[$recv]}`), the
  same wire node the direct statement lowering emits (the identity
  principle, `docs/2026-08-31_qrow-rulings.md` row 6).
- `sync.Mutex.TryLock`: stays declaration-only; the `unsupported`
  reason reworded (cause-naming, P-S2-6-aware).
- `raft.MemoryStorage.{Lock,Unlock,TryLock}` (the promoted stubs):
  stay declaration-only; reasons reworded (dispatch-on-the-embedding-
  type is the remaining refusal; method values and statement/defer
  ops adjust to the embedded primitive at their sites).

No `$syncOnceDone` appears: the twin uses `sync.Mutex` only, and the
completer is emitted only when `sync.Once` reaches the wire.

## Reproduction

From the repo root (commit `b3a89593`, clean tree; the diff compares
the pin's parent `b16738d3~1` against the tracked pin):

```
python3 - > docs/evidence/2026-09-01_qrow-syncval-twin-repin/structural-diff.txt <<'PYEOF'
import json, subprocess
old = json.loads(subprocess.run(["git","show","b16738d3~1:baselines/pins/twin-chdriver.wire.json"],capture_output=True,text=True).stdout)
new = json.load(open("baselines/pins/twin-chdriver.wire.json"))
print("# structural diff: old pin (pre-b16738d3) vs re-pinned twin-chdriver.wire.json")
print("# producer: docs/evidence/2026-09-01_qrow-syncval-twin-repin/README.md Reproduction block")
om={(m.get("recvType"),m.get("name")): m for m in old["methods"]}
nm={(m.get("recvType"),m.get("name")): m for m in new["methods"]}
print("method keys only-in-old:", sorted(set(om)-set(nm)))
print("method keys only-in-new:", sorted(set(nm)-set(om)))
of={f.get("name") for f in old.get("funcs",[])}; nf={f.get("name") for f in new.get("funcs",[])}
print("funcs only-in-old:", sorted(of-nf)); print("funcs only-in-new:", sorted(nf-of))
ofm={f.get("name"):f for f in old.get("funcs",[])}; nfm={f.get("name"):f for f in new.get("funcs",[])}
print("changed funcs:", sorted(n for n in of&nf if ofm[n]!=nfm[n]))
for k in sorted(set(old)|set(new)):
    if k in ("methods","funcs"): continue
    if old.get(k)!=new.get(k): print("top-level differs:", k)
for k in sorted(k for k in om if k in nm and om[k]!=nm[k]):
    print("===== changed method", k)
    o,n=om[k],nm[k]
    for field in sorted(set(o)|set(n)):
        if o.get(field)!=n.get(field):
            print("  field:", field)
            print("    old:", json.dumps(o.get(field), sort_keys=True))
            print("    new:", json.dumps(n.get(field), sort_keys=True))
PYEOF
```

The re-pinned wire itself was produced by the check-frontend-pins
assembly (fresh emit over the canonical twin program) and verified
byte-identical by `scripts/check-frontend-pins` at the re-pin tree
("ok [twin-wire] — fresh emit = pinned wire (b4ef84e433c1…)").

## Toolchain / host

- `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`)
- linux/amd64; repo at `b3a89593` (this record's commit adds only
  this directory), tree clean at generation.
