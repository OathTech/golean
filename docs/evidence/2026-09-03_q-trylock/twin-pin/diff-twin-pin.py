#!/usr/bin/env python3
"""diff-twin-pin.py — enumerate the STRUCTURAL diff between the twin wire
pin at a git revision and the working-tree pin (or a fresh emit).
Usage (repo root):
  python3 docs/evidence/2026-09-03_q-trylock/twin-pin/diff-twin-pin.py [OLD_REV] [NEW_FILE]
Defaults: OLD_REV = c22e367a (main before the q-trylock re-pin),
NEW_FILE = baselines/pins/twin-chdriver.wire.json. Prints every top-level
key whose value differs and, for equal-length lists, each changed entry
with its recvType/name and the keys that differ."""
import json, subprocess, sys
old_rev = sys.argv[1] if len(sys.argv) > 1 else "c22e367a"
new_file = sys.argv[2] if len(sys.argv) > 2 else "baselines/pins/twin-chdriver.wire.json"
old = json.loads(subprocess.check_output(["git", "show", f"{old_rev}:baselines/pins/twin-chdriver.wire.json"]))
new = json.load(open(new_file))
print("top-level keys equal:", list(old.keys()) == list(new.keys()))
changed = 0
for k in old:
    if old[k] != new[k]:
        if isinstance(old[k], list) and len(old[k]) == len(new[k]):
            for i, (a, b) in enumerate(zip(old[k], new[k])):
                if a != b:
                    changed += 1
                    print(f"CHANGED {k}[{i}]: recvType={a.get('recvType')} name={a.get('name')}")
                    for kk in sorted(set(a) | set(b)):
                        if a.get(kk) != b.get(kk):
                            print(f"   key {kk}: old={json.dumps(a.get(kk))[:200]} | new={json.dumps(b.get(kk))[:400]}")
        else:
            changed += 1
            print("CHANGED", k, "(length or scalar)")
print("changed entries:", changed)
