"""Recheck sealed integration rows, manifests, source inputs and stage changes."""
import collections
import csv
import hashlib
import json
from pathlib import Path

evidence = Path(__file__).resolve().parent
root = evidence.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def baseline(text):
    lines = [line for line in text.splitlines() if line and not line.startswith("#")]
    rows = list(csv.DictReader(lines, delimiter="\t"))
    assert len(rows) == len({row["id"] for row in rows})
    return {row["id"]: row for row in rows}


sources = json.loads((evidence / "sources.json").read_text())
for name, digest in sources.items():
    assert sha(root / name) == digest, name
for name, digest in json.loads((evidence / "build-config-addendum.json").read_text())["sources"].items():
    assert sha(root / name) == digest, name

proof = {"source_inputs_revalidated": len(sources)}
for label, count, path in [
    ("full", 3627, "baselines/native-full.tsv"),
    ("negative", 394, "baselines/negative-full.tsv"),
]:
    rows = list(csv.DictReader((evidence / (label + ".tsv")).open(), delimiter="\t"))
    ids = [row["id"] for row in rows]
    manifest = [line.split("\t") for line in (evidence / (label + ".manifest.tsv")).read_text().splitlines()
                if line and not line.startswith("#")]
    meta = dict(list(csv.reader((evidence / (label + ".meta.tsv")).open(), delimiter="\t"))[1:])
    assert len(ids) == len(set(ids)) == len(manifest) == count
    assert set(ids) == {row[0] for row in manifest}
    assert sha(evidence / (label + ".manifest.tsv")) == meta["manifest_sha256"]
    pinned = baseline((root / path).read_text())
    assert set(pinned) == set(ids)
    for row in rows:
        expected = pinned[row["id"]]
        assert row["result"] == expected["result"], row
        assert row["stage"] in expected["stage"].split("|"), (row, expected)
    proof[label] = {
        "cases": count,
        "counts": dict(collections.Counter(row["result"] for row in rows)),
        "unique_complete_inventory": True,
        "manifest_sha_matches_original_metadata": True,
        "baseline_status_and_allowed_stage_match": True,
    }

before = baseline((root / "docs/evidence/2026-09-06_observer-classification/hybrid-baseline-before.tsv").read_text())
after = baseline((root / "baselines/native-full.tsv").read_text())
delta = {
    "new": {key: after[key] for key in sorted(after.keys() - before.keys())},
    "removed": sorted(before.keys() - after.keys()),
    "changed": {key: {"before": before[key], "after": after[key]}
                for key in sorted(before.keys() & after.keys()) if before[key] != after[key]},
}
assert len(delta["new"]) == 11 and not delta["removed"]
assert all(row["result"] == "PASS" for row in delta["new"].values())
assert list(delta["changed"]) == ["sync/mutex-unlock-fatal/during-panic-unwind"]
proof["reviewed_classifier_delta"] = delta
(evidence / "validation.json").write_text(json.dumps(proof, indent=2) + "\n")
print("PASS: 3627 executable and 394 negative rows; complete unique inventories, original manifest hashes, allowed stages and exact reviewed classifier delta.")
