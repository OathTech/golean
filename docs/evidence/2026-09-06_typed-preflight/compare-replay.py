#!/usr/bin/env python3
"""Compare captured model observations and choice consumptions without normalization.

Use the same frozen --coverage input directory for both capture-replay runs.
The full, independently rerun CI result/stage comparison is a separate gate.
This script does not convert setup refusal, model refusal or fuel-out to PASS.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path


def read_index(root):
    with (root / "index.tsv").open() as file:
        rows = list(csv.DictReader(file, delimiter="\t"))
    if len({r["id"] for r in rows}) != len(rows):
        raise ValueError("duplicate id in capture index")
    return {r["id"]: r for r in rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()
    left, right = read_index(args.before), read_index(args.after)
    issues = []
    compared = 0
    lp = json.loads((args.before / "provenance.json").read_text())
    rp = json.loads((args.after / "provenance.json").read_text())
    for root, index, provenance in [(args.before, left, lp), (args.after, right, rp)]:
        manifest = (root / "manifest.tsv").read_bytes()
        expected = {r[0] for r in csv.reader(manifest.decode().splitlines(), delimiter="\t") if r and not r[0].startswith("#")}
        if expected != index.keys() or hashlib.sha256(manifest).hexdigest() != provenance["manifest_sha256"]:
            issues.append({"scope": str(root), "field": "manifest/index integrity"})
    for field in ["manifest_sha256", "capture_script_sha256", "fuel_policy", "stream_policy"]:
        if lp[field] != rp[field]:
            issues.append({"scope": "provenance", "field": field})
    if left.keys() != right.keys():
        issues.append({"scope": "ids", "before_only": sorted(left.keys() - right.keys()),
                       "after_only": sorted(right.keys() - left.keys())})
    for cid in sorted(left.keys() & right.keys()):
        ld = args.before / left[cid]["directory"]
        rd = args.after / right[cid]["directory"]
        lc = json.loads((ld / "case.json").read_text())
        rc = json.loads((rd / "case.json").read_text())
        for directory, case in [(ld, lc), (rd, rc)]:
            for name, digest in case.get("files_sha256", {}).items():
                path = directory / name
                if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                    issues.append({"scope": cid, "field": f"capture integrity: {name}"})
        for field in ["manifest_row", "capture_status", "wire_sha256", "fuel", "fuel_exception", "streams"]:
            if lc.get(field) != rc.get(field):
                issues.append({"scope": cid, "field": field})
        if lc["capture_status"] == "INCOMPLETE" or rc["capture_status"] == "INCOMPLETE":
            issues.append({"scope": cid, "field": "incomplete capture"})
        command_verdicts = lambda c: [(x["name"], x["exit"], x["timeout"]) for x in c["commands"]]
        if command_verdicts(lc) != command_verdicts(rc):
            issues.append({"scope": cid, "field": "command verdicts"})
        names = lambda d: {p.name for p in d.iterdir() if p.name in {"trace.tsv", "consumptions.tsv"}
                           or p.name.startswith("observation-") and p.suffix in {".stdout", ".stderr"}}
        ln, rn = names(ld), names(rd)
        if ln != rn:
            issues.append({"scope": cid, "field": "captured file inventory"})
        for name in sorted(ln & rn):
            compared += 1
            if (ld / name).read_bytes() != (rd / name).read_bytes():
                issues.append({"scope": cid, "field": name})
    print(json.dumps({"result": "IDENTICAL" if not issues else "DIFFERENT_OR_INCOMPLETE",
                      "case_ids": len(left), "compared_files": compared,
                      "scope": "exact captured bytes and verdicts only, not conformance or all-choice equivalence",
                      "findings": issues}, indent=2))
    raise SystemExit(bool(issues))


if __name__ == "__main__":
    main()
