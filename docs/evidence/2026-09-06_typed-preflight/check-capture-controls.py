#!/usr/bin/env python3
"""Exercise the replay comparator against real captured evidence and corruptions."""
import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("capture", type=Path)
parser.add_argument("--comparator", type=Path, required=True)
parser.add_argument("--scratch-root", type=Path, required=True)
args = parser.parse_args()
scratch = Path(tempfile.mkdtemp(prefix="capture-controls-", dir=args.scratch_root))


def compare(path, expected, label):
    result = subprocess.run(["python3", str(args.comparator), str(args.capture), str(path)],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (scratch / f"{label}.log").write_text(result.stdout)
    if result.returncode != expected:
        raise SystemExit(f"{label}: expected exit {expected}, got {result.returncode}: {result.stdout}")
    decoded = json.loads(result.stdout)
    if expected and not decoded["findings"]:
        raise SystemExit(f"{label}: rejected without named findings")
    print(f"{label}: expected exit {expected}; {len(decoded['findings'])} finding(s)", flush=True)


compare(args.capture, 0, "intact")
for label in ["observation-byte", "consumption-byte", "missing-case", "missing-dump"]:
    target = scratch / label
    shutil.copytree(args.capture, target)
    if label == "observation-byte":
        path = next(target.glob("*/observation-0.stdout"))
        path.write_bytes(path.read_bytes() + b"corrupted-observation")
    elif label == "consumption-byte":
        path = next(target.glob("*/consumptions.tsv"))
        path.write_bytes(path.read_bytes() + b"corrupted-consumption\n")
    elif label == "missing-case":
        path = target / "index.tsv"
        path.write_text("\n".join(path.read_text().splitlines()[:-1]) + "\n")
    else:
        path = next(target.glob("*/consumptions.tsv"))
        path.rename(path.with_suffix(".withheld"))
    compare(target, 1, label)
print(f"Control evidence retained at {scratch}")
