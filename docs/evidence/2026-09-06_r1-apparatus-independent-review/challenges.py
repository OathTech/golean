"""Independent bounded R1 apparatus challenges; no conformance claim."""
import copy
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
SNAPSHOT = json.loads((OUT / "snapshot.json").read_text())
ROOT = Path(SNAPSHOT["scratch"])
sys.path.insert(0, str(ROOT / "tools"))
import string_member as check
from string_member_runner import Run, FUEL, STREAMS

results = []


def refuses(label, operation):
    try:
        operation()
    except check.Refusal as exc:
        results.append({"label": label, "result": "refused", "cause": str(exc)})
    else:
        raise AssertionError(f"{label}: accepted malformed input")


pins = sorted((ROOT / "baselines/string-members").rglob("*.json"))
for path in pins:
    p = check.read_json(path)
    check.validate_pin(p, p["case"], p["subject"]["function"], p["subject"]["arguments"])
    assert len(p["controls"]) == 13
results.append({"label": "all-nine-pins", "result": "valid", "roles_each": 13,
                "streams": [list(s) for s in STREAMS]})
pin = check.read_json(ROOT / "baselines/string-members/panic-recover/string-members/equal.json")
for label, mutate in [
    ("missing-role", lambda p: p["controls"].pop("invalid-after-lf")),
    ("foreign-role", lambda p: p["controls"].update(waived=True)),
    ("duplicate-invocation", lambda p: p["controls"]["normal-control"].update(
        function=p["controls"]["direct-recovery"]["function"],
        arguments=p["controls"]["direct-recovery"]["arguments"])),
    ("missing-exit", lambda p: p["controls"]["equal-repanic"]["expectation"]["go"].pop("childExit")),
    ("bool-exit", lambda p: p["controls"]["equal-repanic"]["expectation"]["go"].update(childExit=True)),
    ("typed-bool-argument", lambda p: p["controls"]["normal-control"].update(arguments=[{"tag":"int","value":True}])),
    ("escaping-control-package", lambda p: p["binding"].update(control_package="Corpus/controls/string-members/../foreign")),
    ("noncanonical-control-package", lambda p: p["binding"].update(control_package="Corpus//controls/string-members/explicit")),
    ("unknown-scope", lambda p: p.update(scope="all-programs-typed")),
    ("forged-verdict-field", lambda p: p.update(forced_half_ok=True)),
]:
    bad = copy.deepcopy(pin)
    mutate(bad)
    refuses(label, lambda: check.validate_pin(bad, pin["case"], "Equal", []))

# The wire files here are explicitly synthetic inputs to the binding checker.
# This checks refusals; it does not claim fresh frontend execution.
wire, controls = ROOT / "review-subject-wire", ROOT / "review-control-wire"
wire.write_bytes(b"synthetic subject wire\n")
controls.write_bytes(b"synthetic control wire\n")
bound = copy.deepcopy(pin)
bound["binding"]["native_wire_sha256"] = check.sha(wire)
bound["binding"]["control_wire_sha256"] = check.sha(controls)
subject = "Corpus/coverage/exec/panic-recover/string-members"
oracle = ROOT / "baselines/go-oracle-pin"


def binding(p, version="go1.26.5"):
    check.check_source_binding(ROOT, p, subject, wire, controls, version, oracle)


binding(bound)
results.append({"label": "synthetic-wire-source-binding-positive", "result": "valid"})
for label, mutate in [
    ("missing-go-source", lambda p: p["binding"]["go_sources"].clear()),
    ("changed-go-source", lambda p: p["binding"]["go_sources"].update({subject + "/main.go": "0" * 64})),
    ("missing-apparatus", lambda p: p["binding"]["apparatus_sources"].pop("GoLean/CLI.lean")),
    ("changed-apparatus", lambda p: p["binding"]["apparatus_sources"].update({"GoLean/CLI.lean": "0" * 64})),
    ("missing-control-copy", lambda p: p["binding"]["control_sources"].pop("Corpus/controls/string-members/explicit/main.go")),
    ("stale-subject-wire", lambda p: p["binding"].update(native_wire_sha256="0" * 64)),
    ("stale-control-wire", lambda p: p["binding"].update(control_wire_sha256="0" * 64)),
    ("stale-oracle-pin", lambda p: p["binding"].update(go_oracle_pin_sha256="0" * 64)),
    ("forged-rationale", lambda p: p["rationale"].update(sha256="0" * 64)),
    ("absent-rationale-section", lambda p: p["rationale"].update(section="No such reviewed section")),
]:
    bad = copy.deepcopy(bound)
    mutate(bad)
    refuses(label, lambda: binding(bad))
refuses("wrong-live-toolchain", lambda: binding(bound, "go1.26.4"))

# Exercise the production parser and member checker together with synthetic
# process outputs. No substituted executable is accepted as a corpus run.
record = {"schema":"golean-string-abort-witness-v1", "admitted":True,
          "fuel":FUEL, "choices":[],
          "observation":{"schema":"golean-observation-v1", "status":"panic",
                         "message":"orig [recovered]", "output":""},
          "chain":[{"bytes":[111,114,105,103], "recovered":True},
                   {"bytes":[111,114,105,103], "recovered":False}]}
raw = {"schema":"golean-raw-panic-v1", "status":"panic", "childExit":2,
       "messageBytes":[103,99], "outputBytes":[]}
stdout, stderr = ROOT / "synthetic-witness.json", ROOT / "synthetic-stderr"
stderr.write_bytes(b"")


def witness(data, code=1):
    stdout.write_text(json.dumps(data))
    runner = Run.__new__(Run)
    runner.golean = "unused-synthetic-parser-control"
    runner.lean_timeout = 1
    runner.execute = lambda *args: (code, stdout, stderr)
    machine, chain = runner.model("parser-control", wire, "Equal", [], "panic", witness=True, typed=True)
    check.check_actual_member(machine, raw, chain)


witness(record)
for label, mutate in [
    ("missing-chain", lambda p: p.pop("chain")),
    ("null-chain", lambda p: p.update(chain=None)),
    ("empty-chain", lambda p: p.update(chain=[])),
    ("incomplete-later-chain-entry", lambda p: p["chain"][1].pop("bytes")),
    ("bool-payload-byte", lambda p: p["chain"][1].update(bytes=[True])),
    ("non-byte-payload", lambda p: p["chain"][1].update(bytes=[256])),
    ("numeric-recovered-flag", lambda p: p["chain"][1].update(recovered=0)),
    ("wrong-member", lambda p: p["observation"].update(message="fabricated")),
    ("changed-output", lambda p: p["observation"].update(output="\x00")),
    ("admission-refused", lambda p: p.update(admitted=False)),
    ("numeric-admitted", lambda p: p.update(admitted=1)),
    ("different-fuel", lambda p: p.update(fuel=FUEL-1)),
    ("different-choices", lambda p: p.update(choices=[1])),
    ("foreign-record-field", lambda p: p.update(trusted=True)),
]:
    bad = copy.deepcopy(record)
    mutate(bad)
    refuses(label, lambda: witness(bad))
for code in [0,124,137,143]:
    refuses(f"witness-process-exit-{code}", lambda: witness(record,code))
results.append({"label":"metadata-member-parser-positive", "result":"valid"})
(OUT / "challenges.json").write_text(json.dumps(results,indent=2)+"\n")
print(json.dumps({"records":len(results), "refusals":sum(r["result"]=="refused" for r in results)},indent=2))
