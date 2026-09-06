#!/usr/bin/env python3
"""Fresh actual-emitter package envelopes and real Lean input refusal controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("source", "imported", "sync", "format", "atomic")


def run(command, log, *, env=None):
    result = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=240)
    log.write_bytes(result.stdout)
    return result


def main():
    parent = Path(os.environ.get("TMPDIR", ROOT / ".tmp"))
    parent.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="declaration-package-gate-", dir=parent))
    print(f"Package declaration evidence retained: {directory}", flush=True)
    env = os.environ.copy()
    env.update(GO111MODULE="off", GOCACHE=str(ROOT / "artifacts/go-build-cache"),
               GOLEAN_DECLARATION_PACKAGE_FIXTURE=str(directory / "fixtures"))
    produced = run(["go", "test", "./tools/nativefrontend", "-run",
                    "^TestDeclarationPackageFixture$", "-count=1", "-v"],
                   directory / "producer.log", env=env)
    if produced.returncode:
        raise SystemExit(produced.stdout.decode())
    manifest = json.loads((directory / "fixtures/manifest.json").read_bytes())
    assert [r["name"] for r in manifest] == list(NAMES), "actual fixture inventory differs"
    assert [r["queries"] for r in manifest] == [23, 0, 0, 0, 0], "Go query inventory differs"
    lean = [str(ROOT / "scripts/capped"), "lean", "--run", "tools/check-declaration-package.lean"]
    programs = {}
    for name in NAMES:
        fixture = directory / "fixtures" / name
        result = run(lean + [str(fixture / "program.json"), str(fixture / "queries.json")],
                     fixture / "lean.log")
        if result.returncode or b"Package declarations: PASS" not in result.stdout:
            raise SystemExit(result.stdout.decode())
        programs[name] = json.loads((fixture / "program.json").read_bytes())
        print(name + ": " + result.stdout.decode().strip(), flush=True)

    # Source/ABI and role coverage are measured from actual final arrays. These
    # assertions prevent a vacuous fixture after producer/source changes.
    function_roles, method_roles, helpers = set(), set(), set()
    for program in programs.values():
        for f in program["declarations"]["funcs"]:
            function_roles.add(f["kind"])
            if f["kind"] == "synthetic":
                helpers.add(f["helper"])
        method_roles.update(m["kind"] for m in program["declarations"]["methods"])
    assert function_roles == {"source", "closure", "synthetic"}
    assert method_roles == {"source", "promoted", "interface", "imported", "sync", "model"}
    assert helpers == {"pkginit", "fmt", "fmt-composite", "fmt-slice", "defer-recover",
                       "defer-close", "once-done", "once-do", "defer-sync", "sync-once-done"}
    original = programs["source"]
    envelope = original["declarations"]
    ci = next(i for i, f in enumerate(envelope["funcs"]) if f["kind"] == "closure")
    si = next(i for i, f in enumerate(envelope["funcs"]) if f["id"] == "F")
    mi = next(i for i, m in enumerate(envelope["methods"]) if m["kind"] == "source")
    assert envelope["funcs"][ci]["signature"] != envelope["funcs"][ci]["sourceSignature"]
    promoted = next(m for m in envelope["methods"] if m["kind"] == "promoted")
    assert promoted["receiver"] != promoted["sourceReceiver"]
    assert {n["id"]: n["arity"] for n in envelope["nominals"]}["main.UnusedOrigin"] == 2

    # Every malformed fixture starts from the actual complete native document.
    # Each must reach its intended decoder diagnostic, not merely any exception.
    controls = []

    def control(name, mutate, reason):
        value = copy.deepcopy(original)
        mutate(value)
        controls.append((name, json.dumps(value, ensure_ascii=False).encode(), reason))

    def set_at(path, value):
        def change(document):
            for key in path[:-1]:
                document = document[key]
            document[path[-1]] = value
        return change

    D = "declarations"
    control("absent-envelope", lambda x: x.pop(D), "expected exactly keys")
    control("unknown-envelope-key", lambda x: x[D].update(guess=True), "expected exactly keys")
    control("wrong-version", set_at([D, "schema"], "guess"), "wrong envelope schema")
    control("missing-function", lambda x: x[D]["funcs"].pop(), "inventory differs")
    control("extra-function", lambda x: x[D]["funcs"].append(x[D]["funcs"][0]), "inventory differs")
    control("missing-method", lambda x: x[D]["methods"].pop(), "inventory differs")
    control("changed-function-index", set_at([D, "funcs", si, "index"], 900), "declaration index differs")
    control("reordered-function-bindings", lambda x: x[D]["funcs"].reverse(), "declaration index differs")
    control("changed-function-id", set_at([D, "funcs", si, "id"], "other"), "declaration identity differs")
    control("changed-native-id", set_at(["funcs", si, "name"], "other"), "declaration identity differs")
    control("empty-native-id", set_at(["funcs", si, "name"], ""), "empty identity")
    control("unknown-function-role", set_at([D, "funcs", si, "kind"], "guessed"), "unknown function declaration role")
    control("duplicate-function-id", lambda x: (x["funcs"][si].update(name="G"), x[D]["funcs"][si].update(id="G")), "duplicate function identity")
    control("refused-arity", set_at(["funcs", si, "arity"], 2), "refused function arity differs")
    control("source-abi-confusion", set_at([D, "funcs", si, "sourceSignature", "variadic"], True), "variadic signature needs")
    control("source-abi-type-disagreement", set_at([D, "funcs", si, "sourceSignature", "params", 0],
            {"kind": "basic", "basic": "complex64"}), "source and ABI signatures differ")
    control("missing-capture", set_at([D, "funcs", ci, "captures"], []), "capture/source prefix does not equal")
    control("capture-is-value", set_at([D, "funcs", ci, "captures", 0],
            {"kind": "basic", "basic": "int"}), "capture ABI is not a pointer")
    control("capture-wrong-pointer", set_at([D, "funcs", ci, "captures", 0],
            {"kind": "pointer", "elem": {"kind": "basic", "basic": "bool"}}), "capture/source prefix does not equal")
    control("closure-source-is-abi", set_at([D, "funcs", ci, "sourceSignature"],
            envelope["funcs"][ci]["signature"]), "capture/source prefix does not equal")
    hi = next(i for i, f in enumerate(envelope["funcs"]) if f["kind"] == "synthetic")
    control("unknown-helper", set_at([D, "funcs", hi, "helper"], "future-helper"), "unknown synthetic helper role")
    control("helper-with-source", lambda x: x[D]["funcs"][hi].update(sourceSignature=envelope["funcs"][hi]["signature"]), "expected exactly keys")
    control("changed-method-index", set_at([D, "methods", mi, "index"], 901), "declaration index differs")
    control("reordered-method-bindings", lambda x: x[D]["methods"].reverse(), "declaration index differs")
    control("changed-method-id", set_at([D, "methods", mi, "id"], "other"), "declaration identity differs")
    control("changed-receiver-id", set_at([D, "methods", mi, "receiverId"], "other"), "adapter receiver identity differs")
    control("changed-member-name", set_at([D, "methods", mi, "member", "name"], "other"), "method member identity differs")
    control("unknown-method-role", set_at([D, "methods", mi, "kind"], "guessed"), "unknown method declaration role")
    control("source-receiver-confusion", set_at([D, "methods", mi, "sourceReceiver"],
            {"kind": "basic", "basic": "bool"}), "source receiver differs")
    control("method-native-receiver-shape", set_at(["methods", mi, "recv"], True), "expected")
    control("method-variadic-disagreement", lambda x: x["methods"][mi].update(variadic=not x["methods"][mi]["variadic"]), "variadic marker differs")
    control("missing-interface", set_at([D, "interfaces"], []), "incomplete or reordered interface inventory")
    control("duplicate-interface", lambda x: x[D]["interfaces"].append(x[D]["interfaces"][0]), "incomplete or reordered interface inventory")
    control("missing-interface-method", set_at([D, "interfaces", 0, "type", "methods"], []), "incomplete interface requirement set")
    control("duplicate-interface-method", lambda x: x[D]["interfaces"][0]["type"]["methods"].append(x[D]["interfaces"][0]["type"]["methods"][0]), "duplicate interface method")
    control("interface-index-range", set_at([D, "interfaces", 0, "index"], 902), "interface type index out of range")
    control("missing-nominal", lambda x: x[D]["nominals"].pop(next(i for i,n in enumerate(x[D]["nominals"]) if n["id"] == "main.R")), "unknown nominal declaration")
    control("changed-referenced-arity", lambda x: next(n for n in x[D]["nominals"] if n["id"] == "main.Box").update(arity=2), "expects 2 arguments")
    control("duplicate-nominal", lambda x: x[D]["nominals"].append(x[D]["nominals"][0]), "duplicate nominal identity")
    control("unused-extra-nominal", lambda x: x[D]["nominals"].append({"id": "invented", "arity": 0}), "nominal origin inventory does not equal")
    control("missing-required-source-origin", lambda x: x[D]["nominals"].pop(next(i for i,n in enumerate(x[D]["nominals"]) if n["id"] == "main.UnusedOrigin")), "nominal origin inventory does not equal")
    control("duplicate-source-origin", lambda x: x[D]["sourceNominals"].append(x[D]["sourceNominals"][0]), "duplicate source nominal origin")
    control("unknown-package-role", set_at([D, "packages", 0], "other"), "package unit order differs")
    control("empty-packages", set_at([D, "packages"], []), "empty or duplicate package unit inventory")
    control("duplicate-packages", lambda x: x[D]["packages"].append(x[D]["packages"][0]), "empty or duplicate package unit inventory")
    raw = json.dumps(original).encode()
    controls.extend([
        ("raw-duplicate-root", b'{"schema":"golean-native-v1",' + raw[1:], "duplicate JSON object key"),
        ("raw-escaped-duplicate", b'{"schem\\u0061":"golean-native-v1",' + raw[1:], "duplicate JSON object key"),
        ("raw-invalid-utf8", raw.replace(b'"F"', b'"\xff"', 1), "UTF-8"),
        ("raw-lone-surrogate", raw.replace(b'"F"', b'"\\ud800"', 1), "surrogate"),
    ])
    out = directory / "controls"
    out.mkdir()
    records = []
    for name, data, reason in controls:
        path = out / (name + ".json")
        path.write_bytes(data)
        result = run(lean + [str(path)], out / (name + ".log"))
        assert result.returncode != 0 and reason in result.stdout.decode(), (
            name, result.returncode, result.stdout.decode())
        records.append({"name": name, "sha256": hashlib.sha256(data).hexdigest(),
                        "exit": result.returncode, "diagnostic": reason})

    # These remain well-formed positive metadata. Their source meaning is wrong,
    # so the fresh Go observations must detect them after successful decoding.
    # This distinguishes schema validation from the tested compiler arrow.
    meaning_controls = []

    def meaning(name, mutate, reason):
        value = copy.deepcopy(original)
        mutate(value)
        meaning_controls.append((name, json.dumps(value).encode(), reason))

    meaning("unused-origin-wrong-arity", lambda x: next(n for n in x[D]["nominals"] if n["id"] == "main.UnusedOrigin").update(arity=3), "Go/Lean nominal arity differs")
    meaning("well-formed-wrong-source-signature", lambda x: (x[D]["funcs"][si]["signature"]["params"][0].update(basic="complex64"), x[D]["funcs"][si]["sourceSignature"]["params"][0].update(basic="complex64")), "Go/Lean source signature differs")
    ri = next(i for i,m in enumerate(envelope["methods"]) if m["id"] == "main.R.M")
    meaning("well-formed-wrong-receiver", lambda x: (x[D]["methods"][ri]["receiver"].update(id="main.Wrapper"), x[D]["methods"][ri]["sourceReceiver"].update(id="main.Wrapper")), "Go/Lean adapter receiver differs")
    meaning("well-formed-wrong-member-package", lambda x: x[D]["methods"][ri]["member"].update(package="other"), "Go/Lean selected method satisfaction differs")
    meaning("well-formed-wrong-interface-signature", lambda x: x[D]["interfaces"][0]["type"]["methods"][0]["signature"]["results"][0].update(basic="complex64"), "Go/Lean selected method satisfaction differs")
    meaning_records = []
    for name, data, reason in meaning_controls:
        path = out / (name + ".json")
        path.write_bytes(data)
        valid = run(lean + [str(path)], out / (name + "-decode.log"))
        assert valid.returncode == 0, (name, valid.stdout.decode())
        challenged = run(lean + [str(path), str(directory / "fixtures/source/queries.json")], out / (name + "-go.log"))
        assert challenged.returncode != 0 and reason in challenged.stdout.decode(), (name, challenged.stdout.decode())
        meaning_records.append({"name": name, "sha256": hashlib.sha256(data).hexdigest(),
                                "decode_exit": valid.returncode, "query_exit": challenged.returncode, "diagnostic": reason})
    (directory / "meaning-controls.json").write_text(json.dumps(meaning_records, indent=2) + "\n")
    (directory / "controls.json").write_text(json.dumps(records, indent=2) + "\n")
    (directory / "coverage.json").write_text(json.dumps({"function_roles": sorted(function_roles),
        "method_roles": sorted(method_roles), "helpers": sorted(helpers), "fixtures": manifest}, indent=2) + "\n")
    print(f"Package declaration gate: PASS; {len(NAMES)} actual pipeline fixtures, 23 Go observations, {len(records)} real-input refusals, {len(meaning_records)} valid-metadata Go challenges", flush=True)


if __name__ == "__main__":
    main()
