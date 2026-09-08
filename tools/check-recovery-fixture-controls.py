#!/usr/bin/env python3
"""Pin the native controls' different results after real differential checks."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
records = root / "artifacts/recovery-typing/differential/go-run"
expected = {
    "shared-false": True,
    "shared-true": False,
    "outside": True,
    "reversed-true": True,
    "direct-true": True,
}
for case, value in expected.items():
    path = records / ("recovery-typing__" + case) / "oracle.stdout"
    observation = json.loads(path.read_text())
    if observation != {
        "schema": "golean-observation-v1", "status": "ok",
        "values": [{"tag": "bool", "value": value}],
    }:
        raise SystemExit(f"recovery fixture control {case}: expected Boolean {value}, got {observation}")
    print(f"Recovery native control: {case} returns {str(value).lower()}")
print("Recovery native controls: input dependence, defer order, and directness all distinguish results")
