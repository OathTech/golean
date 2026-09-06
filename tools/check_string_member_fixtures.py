#!/usr/bin/env python3
"""Fresh native/CLI witness checks plus meaningful compiling Go mutations.

Mutation programs are explicit adversarial controls, not corpus verdicts.
Their altered bytes are recorded; no stale binding is called a semantic
control failure. The tested outcome itself must change after Go compiles.
"""
import hashlib
import csv
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import sys

from string_member import check_actual_member, require, sha, Refusal
from string_member_runner import Run

ROOT = Path(__file__).resolve().parents[1]


def main():
    scratch = Path(tempfile.mkdtemp(prefix="string-member-fixtures-", dir=ROOT/".tmp"))
    helper = scratch/"coverageharness"
    env = os.environ.copy()
    env.update(GO111MODULE="off", GOCACHE=str(ROOT/"artifacts/go-build-cache"))
    subprocess.run(["go", "build", "-o", str(helper), "./tools/coverageharness"], cwd=ROOT, env=env, check=True, timeout=180)
    run = Run(scratch/"runs", ROOT/".lake/build/bin/golean", helper, 60, 60)
    source = "Corpus/coverage/exec/panic-recover/string-members"
    controls = "Corpus/controls/string-members/explicit"
    wire = run.emit("subject", source)
    control_wire = run.emit("controls", controls)
    record = {"scratch": str(scratch), "source_hashes": {}, "native": [], "mutations": []}
    for directory in (source, controls):
        record["source_hashes"].update({str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT/directory).glob("*.go"))})

    # Every byte of the reported payload/flag derives from the real driver.
    # Compare erasure through the actual CLI too, including fuel refusal.
    expected = {
        "Equal": (b"orig", True, "orig [recovered]"),
        "InvalidBefore": (b"\xff\x00\\\nZ", False, '"\\xff\\x00\\x5c\\x0a\\x5a"'),
        "InvalidAfter": (b"a\n\xff", False, '"\\x61\\x0a\\xff"'),
        "InvalidRecovered": (b"\xff\x00\\\nZ", True, '"\\xff\\x00\\x5c\\x0a\\x5a" [recovered]'),
        "Unicode": ("界🙂".encode(), False, "界🙂"),
        "Controls": (b"a\x00\x01\t\r\nZ", False, "a\x00\x01\t\r"),
    }
    for i, (function, (payload, recovered, text)) in enumerate(expected.items()):
        machine, chain = run.model("witness-"+function, wire, function, [], "panic", witness=True, typed=True)
        require(chain[0] == {"bytes": list(payload), "recovered": recovered}, "actual reached head bytes/flag differ")
        require(machine["message"] == text, "selected member differs from explicit regression pin")
        original, _ = run.model("ordinary-"+function, wire, function, [], "panic")
        run.compare("erasure-"+function, machine, original)
        go = run.go("native-"+function, source, function, [], "panic", race=i % 2 == 1)
        check_actual_member(machine, go, chain)
        record["native"].append({"function": function, "go": go, "machine": machine, "chain": chain})
    for function in ("Equal", "Normal"):
        pair = []
        for command in ("native-json-run", "native-json-string-run"):
            code, out, err = run.execute(f"zero-{function}-{command}", [run.golean, command, "--input", str(wire), "--function", function, "--fuel", "0"], 60)
            require(code == 1, "zero fuel was not a refusal")
            value = json.loads(out.read_bytes())
            if command.endswith("string-run"):
                require(value["chain"] is None and value["fuel"] == 0, "zero fuel manufactured abort provenance")
                value = value["observation"]
            pair.append(value)
        require(pair[0] == pair[1], "CLI erasure changed zero-fuel outcome")

    base_main = (ROOT/controls/"main.go").read_text()
    base_controls = (ROOT/controls/"controls.go").read_text()
    # Each mutation compiles as Go. Except for the dedicated kind/occurrence
    # probes, its exact Boolean/order/output control itself must change.
    mutations = [
        ("replace-invalid-byte", "main.go", 'panic("\\xff\\x00\\\\\\nZ")', 'panic("\\xef\\xbf\\xbd\\x00\\\\\\nZ")', "ControlInvalidBefore", "false"),
        ("drop-nul", "main.go", 'panic("\\xff\\x00\\\\\\nZ")', 'panic("\\xff\\\\\\nZ")', "ControlInvalidBefore", "false"),
        ("drop-invalid-after-lf", "main.go", 'panic("a\\n\\xff")', 'panic("a\\n")', "ControlInvalidAfter", "false"),
        ("direct-indirect", "controls.go", "result = indirectRecovery() == nil", "result = recover() == nil", "ControlIndirect", "false"),
        ("reverse-defers", "controls.go", "func ControlOrder() (result int) {\n\tdefer func() { result = result*10 + 1 }()\n\tdefer func() { result = result*10 + 2 }()", "func ControlOrder() (result int) {\n\tdefer func() { result = result*10 + 2 }()\n\tdefer func() { result = result*10 + 1 }()", "ControlOrder", "not-21"),
        ("duplicate-defer", "controls.go", "func ControlOrder() (result int) {", "func ControlOrder() (result int) {\n\tdefer func() { result = result*10 + 1 }()", "ControlOrder", "not-21"),
        ("change-output", "controls.go", "func ControlNormal() bool {", 'func ControlNormal() bool {\n\tprint("\\x00")', "ControlNormal", "output"),
        ("suppress-final-panic", "main.go", 'func equalHandler() {\n\t_ = recover()\n\tpanic("orig")', 'func equalHandler() {\n\t_ = recover()\n\treturn', "ControlDynamic", "false"),
    ]
    for label, filename, old, new, function, expected_change in mutations:
        mutant = scratch/label
        mutant.mkdir()
        for name, contents in (("main.go", base_main), ("controls.go", base_controls)):
            if name == filename:
                require(old in contents, f"{label}: mutation target missing")
                # InvalidBefore and InvalidRecovered share the literal;
                # mutate the first intended occurrence only, record all bytes.
                contents = contents.replace(old, new, 1)
            (mutant/name).write_text(contents)
        # An independently successful compile precedes the observed control.
        compiled = subprocess.run(["go", "build", "-o", str(mutant/"program"), "."], cwd=mutant, env=env, capture_output=True, timeout=60)
        (mutant/"compile.stdout").write_bytes(compiled.stdout)
        (mutant/"compile.stderr").write_bytes(compiled.stderr)
        require(compiled.returncode == 0, f"{label}: mutant did not compile: {compiled.stderr!r}")
        go = run.go("mutation-"+label, str(mutant), function, [], "ok")
        original, _ = run.model("model-mutation-"+label, control_wire, function, [], "ok")
        require(go != original, f"{label}: meaningful exact control did not change")
        if expected_change == "false":
            require(go["values"] == [{"tag": "bool", "value": False}], f"{label}: wrong reason for changed control")
        elif expected_change == "not-21":
            require(go["values"][0]["value"] != 21, f"{label}: order probe stayed blind")
        else:
            require(go["output"] == "\x00" and original["output"] == "", "output mutation was not byte-exact")
        record["mutations"].append({"label": label, "compiled": compiled.returncode,
                                    "go": go, "original_model": original,
                                    "sources": {p.name: sha(p) for p in mutant.glob("*.go")}})
        print(f"String fixture negative: {label} compiled; exact control changed", flush=True)

    # Wrong dynamic kind remains legal Go, but cannot forge string-chain
    # metadata or typed admission even when its decimal text looks simple.
    mutant = scratch/"wrong-kind"
    mutant.mkdir()
    (mutant/"main.go").write_text('package main\nfunc WrongKind(){ panic(42) }\nfunc main(){}\n')
    kind_wire = run.emit("kind-mutant", str(mutant))
    code, out, err = run.execute("kind-witness", [run.golean, "native-json-string-run", "--input", str(kind_wire), "--function", "WrongKind"], 60)
    value = json.loads(out.read_bytes())
    require(code == 1 and value["chain"] is None and value["admitted"] is False,
            "non-string panic became actual string provenance")
    native_kind = run.go("native-kind", str(mutant), "WrongKind", [], "panic")
    require(native_kind["messageBytes"] == [52, 50], "wrong-kind native control did not actually panic with 42")
    record["mutations"].append({"label": "wrong-kind", "native": native_kind, "actual_witness": value})

    # The real runner must refuse a non-verdict process exit BEFORE it can
    # inspect otherwise valid panic evidence. These are synthetic apparatus
    # controls, not additional Go/model conformance observations.
    native_go = next(c for c in run.commands if c["label"] == "native-Equal-go")
    native_crash = run.records["native-Equal"]["crash"]
    native_ack = run.records["native-Equal"]["registration"]
    fakebin = scratch/"fakebin"
    fakebin.mkdir()
    fakego = fakebin/"go"
    fakego.write_text(f'''#!{sys.executable}
import os, pathlib, sys
base = pathlib.Path({str(run.directory)!r})
pathlib.Path("oracle.crash").write_bytes((base / {native_crash!r}).read_bytes())
pathlib.Path("oracle.registered").write_bytes((base / {native_ack!r}).read_bytes())
sys.stderr.buffer.write((base / {native_go['stderr']!r}).read_bytes())
raise SystemExit(int(os.environ["STRING_MEMBER_FAKE_EXIT"]))
''')
    # This is a new test-owned executable, not a permission repair.
    fakego.chmod(0o700)
    old_path = run.env["PATH"]
    run.env["PATH"] = str(fakebin)+os.pathsep+old_path
    for code in (0, 124, 137, 143):
        run.env["STRING_MEMBER_FAKE_EXIT"] = str(code)
        try:
            run.go(f"nonverdict-{code}", source, "Equal", [], "panic")
        except Refusal as exc:
            require(f"exit {code}, expected 1" in str(exc), "non-verdict control refused for an unrelated cause")
            record.setdefault("apparatus_refusals", []).append({"exit": code, "cause": str(exc)})
        else:
            raise Refusal("otherwise valid panic files hid a non-verdict process exit")
    run.env["PATH"] = old_path
    run.env.pop("STRING_MEMBER_FAKE_EXIT")

    # Exercise the real shell caller's re-validation on rows that bypass
    # coverage-manifest. A missing-pin failure is not enough: these must
    # fail at manifest, before any certificate or Go subject is considered.
    bypass = scratch/"bypass.tsv"
    bad_fields = [
        ("wrong-status", "ok", "panic", "-", "why", "-"),
        ("text-predicate", "panic", "panic", "orig", "why", "-"),
        ("missing-rationale", "panic", "panic", "-", "-", "-"),
        ("arbitrary-params", "panic", "panic", "-", "why", "skip-controls=1"),
        ("nondet", "panic", "panic,nondet", "-", "why", "-"),
        ("fatal", "fatal", "panic", "-", "why", "-"),
    ]
    bypass.write_text("".join("\t".join(["r1-boundary-"+label, source, "Equal", "-", status, features,
                                        reason, "string-member", why, params])+"\n"
                              for label, status, features, reason, why, params in bad_fields))
    bypass_artifacts = scratch/"bypass-artifacts"
    env = run.env.copy()
    env.update(GOLEAN_COVERAGE_ARTIFACTS=str(bypass_artifacts), GOLEAN_COVERAGE_JOBS="2",
               GOLEAN_COVERAGE_RESULTS=str(bypass_artifacts/"latest.tsv"),
               GOLEAN_COVERAGE_META=str(bypass_artifacts/"latest.meta.tsv"))
    code, _, cause = run.execute("manifest-bypass", [str(ROOT/"scripts/diff-coverage"), str(bypass)], 180, env=env)
    require(code == 1, f"manifest bypass gate did not finish with six classified failures: {code}/{cause.read_bytes()!r}")
    with (bypass_artifacts/"latest.tsv").open() as captured:
        rows = list(csv.DictReader(captured, delimiter="\t"))
    require(len(rows) == len(bad_fields) and all(r["result"] == "FAIL" and r["stage"] == "manifest" for r in rows),
            "malformed string-member row escaped the shell manifest boundary")
    record["manifest_bypass"] = rows

    (scratch/"evidence.json").write_text(json.dumps(record, indent=2)+"\n")
    for p, digest in record["source_hashes"].items():
        require(sha(ROOT/p) == digest, "fixture source changed during gate")
    print(f"String fixtures PASS: 6 raw-native/actual-driver controls, 2 zero-fuel erasures, 9 compiling semantic mutations, 4 non-verdict capture refusals, 6 manifest-bypass refusals; evidence {scratch}", flush=True)


if __name__ == "__main__":
    main()
