from decimal import Decimal
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path.cwd()
P = ROOT / "docs/evidence/2026-09-06_i1-json-independent"
expected = json.loads((P / "cases.json").read_text())
actual_rows = [json.loads(line, parse_float=Decimal, parse_int=Decimal)
               for line in (P / "independent-probes.jsonl").read_text().split("\n") if line]
actual = {row["name"]: row for row in actual_rows}
assert len(expected) == len(actual_rows) == len(actual) == 107
assert not (P / "independent-probes.stderr").read_text()
for case in expected:
    row = actual[case["name"]]
    assert row["bytes"]["ok"] == case["ok"], (case, row)
    if case["ok"]:
        value = json.loads(bytes.fromhex(case["raw_hex"]),
                           parse_float=Decimal, parse_int=Decimal)
        assert row["bytes"]["value"] == row["text"]["value"] == value, (case, row)
    elif "reason" in case:
        assert case["reason"] in row["bytes"]["error"], (case, row)

for name in ["schema-extra-valid-json", "schema-incomplete-valid-json"]:
    assert actual[name]["bytes"]["ok"] and not actual[name]["declarationBytes"]
assert actual["declaration-bool"]["declarationBytes"]
row = actual["declaration-escaped-duplicate"]
assert row["oldParsedDeclaration"] and not row["declarationBytes"]
row = actual["surrogate-07"]
assert row["oldParsedNominal"] and not row["nominalBytes"]
row = actual["nominal-explicit-replacement"]
assert row["nominalBytes"] and row["oldParsedNominal"]
assert '$["outer"][0]' in actual["dup-inside-array"]["bytes"]["error"]
invalid = [case for case in expected if case.get("invalid_utf8")]
assert len(invalid) == 10
assert all(actual[case["name"]]["text"]["ok"] and
           not actual[case["name"]]["bytes"]["ok"] for case in invalid)

log = (P / "declaration-gate.log").read_text()
assert "Declaration gate: PASS;" in log
assert "1712 imported/local declarations checked" in log
assert log.count("Declaration negative audit:") == 6
fixture = Path(re.search(r"Declaration gate: PASS; fresh fixture retained at (.+)", log).group(1))
shutil.copyfile(fixture, P / "fresh-go-fixture.json")
raw = fixture.read_bytes()
parsed = json.loads(raw)
assert len(parsed["types"]) == 24 and len(parsed["pairs"]) == 576
schema = json.dumps(parsed["schema"], ensure_ascii=False, separators=(",", ":")).encode()
at = raw.index(b"{") + 1
variants = {
    "valid-fixture": raw,
    "duplicate-schema": raw[:at] + b'"schema":' + schema + b"," + raw[at:],
    "escaped-duplicate-schema": raw[:at] + b'"sch\\u0065ma":' + schema + b"," + raw[at:],
}
serialized = json.dumps(parsed, ensure_ascii=False, separators=(",", ":")).encode()
types = json.dumps(parsed["types"], ensure_ascii=False, separators=(",", ":")).encode()
variants["duplicate-types"] = b'{"types":' + types + b"," + serialized[1:]
controls = P / "fixture-controls"
controls.mkdir(exist_ok=True)
fixture_results = {}
for name, value in variants.items():
    path = controls / (name + ".json")
    path.write_bytes(value)
    result = subprocess.run(["scripts/capped", "lake", "env", "lean", "--run",
                             "tools/check-declaration-wire.lean", str(path)],
                            cwd=ROOT, text=True, capture_output=True, timeout=90)
    output = result.stdout + result.stderr
    (controls / (name + ".log")).write_text(output)
    expected_exit = 0 if name == "valid-fixture" else 1
    assert result.returncode == expected_exit, (name, result.returncode, output)
    if expected_exit:
        assert "duplicate JSON object key" in output, output
    fixture_results[name] = {"exit": result.returncode,
                             "sha256": hashlib.sha256(value).hexdigest()}

result = {
    "independent_input_cases": 107,
    "PASS": 107,
    "valid_exact_JSON_tree_checks": sum(case["ok"] for case in expected),
    "duplicate_refusals": sum(case.get("reason") == "duplicate JSON object key" for case in expected),
    "invalid_UTF8_refusals": 10,
    "text_API_scope": "All 10 malformed UTF8 strings refuse parseBytes. A deliberately lossy Python conversion outside the candidate creates replacement-containing String inputs that parse accepts; parse cannot validate erased byte provenance.",
    "parsed_API_scope": "Old parsed duplicate basic and replacement nominal are accepted by decode; strict decodeBytes refuses the original malformed inputs. Explicit U+FFFD is accepted.",
    "fresh_gate": "PASS: 47 original checks; 24 Go types; 576 identity pairs; 1712 declaration audit; 6 compiled poisons rejected",
    "whole_fixture_controls": fixture_results,
    "harness_corrections": "Initial independent harness used String.fromUTF8! for malformed bytes and emitted its own panic diagnostics; preserved separately, replaced by explicitly generated lossy companion files. JSONL split now uses LF only to retain valid literal U+2028/U+2029 inside JSON strings. No candidate source changed.",
}
(P / "probe-checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
