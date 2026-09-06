#!/usr/bin/env python3
"""Strict source/pin/record checks for the versioned R-1 string envelope.

This module never accepts a caller's claim that controls passed. The runner
executes them and supplies its own checked observations; persisted records
are evidence, not an alternate trusted input or a cache of verdicts.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re

SCHEMA = "golean-string-member-pin-v1"
ENVELOPE = "golean-r1-explicit-string-v1"
MATRIX = "golean-r1-string-controls-v1"
ROLES = (
    "dynamic-kind-and-bytes", "normal-control", "direct-recovery",
    "indirect-recovery", "defer-order", "reversed-defer-control",
    "equal-repanic", "unequal-repanic", "multiple-repanic", "rethrow", "computed-equal",
    "invalid-before-lf", "invalid-after-lf",
)
ABORT_ROLES = {"equal-repanic", "unequal-repanic", "multiple-repanic", "rethrow", "computed-equal"}
APPARATUS_FILES = (
    "Main.lean",
    "GoLean.lean",
    "tools/nativefrontend/inittask-std.tsv",
    "tools/nativefrontend/stdlib-substitutions.tsv",
    "tools/nativefrontend/stdlib-overlay.tsv",
    "baselines/stdlib-pin.tsv",
    "scripts/diff-coverage", "scripts/coverage-manifest", "tools/string_member.py",
    "tools/string_member_runner.py", "scripts/check-string-members.py",
    "scripts/coverage-baseline-diff", "scripts/ci", "tools/test_string_member.py",
    "tools/check_string_member_fixtures.py",
    "scripts/check-interface", "scripts/check-interface.py", "Tests/InterfaceAudit.lean",
    "Tests/StringPanicMembers.lean", "Tests/PanicRendering.lean",
    "lean-toolchain", "lakefile.toml",
)
APPARATUS_ROOTS = {"GoLean": ".lean", "tools/nativefrontend": ".go", "tools/coverageharness": ".go"}


class Refusal(ValueError):
    """An explicitly unestablished membership obligation."""


def require(condition, cause):
    if not condition:
        raise Refusal(cause)


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, f"duplicate JSON key: {key}")
        obj[key] = value
    return obj


def read_json(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_object,
                          parse_float=lambda s: (_ for _ in ()).throw(Refusal(f"non-integer JSON number outside this schema: {s}")),
                          parse_constant=lambda s: (_ for _ in ()).throw(Refusal(f"non-JSON constant: {s}")))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise Refusal(f"invalid JSON file {path}: {exc}") from exc


def keys(obj, wanted, label):
    require(type(obj) is dict, f"{label}: expected object")
    require(set(obj) == set(wanted), f"{label}: exact keys required; missing={sorted(set(wanted)-set(obj))}, unknown={sorted(set(obj)-set(wanted))}")


def byte_array(value, label):
    require(type(value) is list and all(type(v) is int and 0 <= v <= 255 for v in value),
            f"{label}: expected integer byte array (Booleans are not bytes)")
    return bytes(value)


def text(value, label):
    require(type(value) is str, f"{label}: expected text")
    try:
        return value.encode("utf-8", errors="strict")
    except UnicodeError as exc:
        raise Refusal(f"{label}: invalid Unicode scalar text") from exc


def relative(value, label):
    require(type(value) is str and value != "" and "\\" not in value,
            f"{label}: expected nonempty relative POSIX path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and all(x not in (".", "..") for x in value.split("/")) and
            str(p) == value, f"{label}: noncanonical/escaping path")
    return value


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inventory(root, directory, suffix):
    directory = relative(directory, "inventory directory")
    base = root / directory
    require(base.is_dir() and not base.is_symlink(), f"missing/non-owned source directory: {directory}")
    result = {}
    for p in sorted(base.rglob("*")):
        require(not p.is_symlink(), f"source inventory does not admit symlink: {p}")
        if p.is_file() and p.suffix == suffix:
            result[p.relative_to(root).as_posix()] = sha(p)
    require(result, f"empty source inventory: {directory}")
    return result


def apparatus_inventory(root):
    result = {}
    for directory, suffix in APPARATUS_ROOTS.items():
        result.update(inventory(root, directory, suffix))
    for name in APPARATUS_FILES:
        require((root / name).is_file() and not (root / name).is_symlink(), f"missing apparatus source: {name}")
        result[name] = sha(root / name)
    return dict(sorted(result.items()))


def check_inventory(actual, pinned, label):
    require(type(pinned) is dict and pinned, f"{label}: expected nonempty inventory")
    for path, digest in pinned.items():
        relative(path, label)
        require(type(digest) is str and re.fullmatch(r"[0-9a-f]{64}", digest), f"{label}: invalid SHA256")
    require(actual == pinned, f"{label}: missing, extra or changed source (pin is stale)")


def arguments(value, label):
    require(type(value) is list, f"{label}: expected typed argument array")
    for arg in value:
        keys(arg, ("tag", "value"), label)
        # The current CLI/harness has integer arguments. Do not coerce 0/1
        # to Boolean or invent an O2 admission judgment for them.
        require(arg["tag"] == "int" and type(arg["value"]) is int, f"{label}: unsupported argument type")


def observation(value, status=None):
    require(type(value) is dict, "observation: expected object")
    require(value.get("schema") == "golean-observation-v1", "observation: wrong schema")
    require(value.get("status") in ("ok", "panic"), "observation: refusal/non-conformance status")
    if status is not None:
        require(value["status"] == status, f"observation: expected {status}")
    if value["status"] == "panic":
        keys(value, ("schema", "status", "message", "output"), "panic observation")
        text(value["message"], "panic message")
    else:
        keys(value, ("schema", "status", "values", "output"), "successful observation")
        require(type(value["values"]) is list, "successful observation: expected values array")
        # The actual Lean observation comparator checks all nested values;
        # this is schema validation before it, not an alternate comparator.
    text(value["output"], "program output")


def raw_panic(value):
    keys(value, ("schema", "status", "childExit", "messageBytes", "outputBytes"), "raw panic")
    require(value["schema"] == "golean-raw-panic-v1" and value["status"] == "panic" and
            type(value["childExit"]) is int and value["childExit"] == 2, "raw panic: wrong terminal/exit")
    byte_array(value["messageBytes"], "raw panic message")
    byte_array(value["outputBytes"], "raw panic output")


def selected_members(payload, recovered):
    """The two proved representations, before the shared first-LF projection.

    A direct candidate exists only if it byte-round-trips. The escape
    candidate is reversible for every byte sequence. The complete actual
    machine pin still selects ONE member; this does not accept arbitrary
    rendering text or reconstruct payload from the Go first line.
    """
    require(type(recovered) is bool, "recovered flag: expected Boolean")
    candidates = ['"' + "".join(f"\\x{b:02x}" for b in payload) + '"']
    try:
        direct = payload.decode("utf-8", errors="strict")
        require(direct.encode("utf-8") == payload, "direct UTF8 byte round trip failed")
        candidates.append(direct)
    except UnicodeError:
        pass
    suffix = " [recovered]" if recovered else ""
    return {(candidate + suffix).split("\n", 1)[0] for candidate in candidates}


def check_actual_member(machine, raw_go, actual_chain):
    observation(machine, "panic")
    raw_panic(raw_go)
    require(type(actual_chain) is list and actual_chain, "actual terminal witness: missing nonempty string chain")
    for entry in actual_chain:
        keys(entry, ("bytes", "recovered"), "actual string chain entry")
        byte_array(entry["bytes"], "actual payload")
        require(type(entry["recovered"]) is bool, "actual recovered flag: expected Boolean")
    head = actual_chain[0]
    require(machine["message"] in selected_members(bytes(head["bytes"]), head["recovered"]),
            "machine text is not a prescribed member of the actual payload/flag")
    require(text(machine["output"], "machine output") == bytes(raw_go["outputBytes"]),
            "program output changed across R-1 membership")


def validate_pin(pin, case, function, args):
    keys(pin, ("schema", "envelope", "case", "subject", "binding", "scope", "machine", "matrix", "controls", "rationale"), "pin")
    require(pin["schema"] == SCHEMA and pin["envelope"] == ENVELOPE and pin["matrix"] == MATRIX,
            "pin: unknown schema/envelope/control matrix")
    require(pin["case"] == case, "pin: case identity differs")
    relative(case, "case id")
    keys(pin["subject"], ("function", "arguments"), "subject")
    require(pin["subject"]["function"] == function and pin["subject"]["arguments"] == args,
            "pin: actual subject/arguments differ")
    arguments(args, "subject arguments")
    require(pin["scope"] in ("typed-explicit-string", "reviewed-broader-string-control"), "pin: unknown evidence scope")
    observation(pin["machine"], "panic")
    keys(pin["binding"], ("go_sources", "native_wire_sha256", "go_toolchain", "go_oracle_pin_sha256", "apparatus_sources", "control_package", "control_sources", "control_wire_sha256"), "binding")
    for name in ("native_wire_sha256", "go_oracle_pin_sha256", "control_wire_sha256"):
        require(type(pin["binding"][name]) is str and re.fullmatch(r"[0-9a-f]{64}", pin["binding"][name]), f"binding: invalid {name}")
    control_package = relative(pin["binding"]["control_package"], "control package")
    require(control_package.startswith("Corpus/controls/string-members/"), "control package outside fixed source area")
    keys(pin["rationale"], ("path", "section", "sha256"), "rationale")
    relative(pin["rationale"]["path"], "rationale path")
    require(type(pin["rationale"]["section"]) is str and pin["rationale"]["section"].strip(), "rationale section missing")
    require(type(pin["rationale"]["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", pin["rationale"]["sha256"]), "rationale SHA256 invalid")
    keys(pin["controls"], ROLES, "mandatory controls")
    invocations = set()
    for role, control in pin["controls"].items():
        keys(control, ("function", "arguments", "expectation"), f"control {role}")
        require(type(control["function"]) is str and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", control["function"]), f"control {role}: invalid function")
        arguments(control["arguments"], f"control {role} arguments")
        invocation = (control["function"], json.dumps(control["arguments"], sort_keys=True))
        require(invocation not in invocations, "mandatory roles duplicate the same invocation")
        invocations.add(invocation)
        pair = control["expectation"]
        keys(pair, ("kind", "go", "machine"), f"control {role} observations")
        status = "panic" if role in ABORT_ROLES else "ok"
        observation(pair["machine"], status)
        if status == "panic":
            require(pair["kind"] == "string-member", f"control {role}: abort requires explicit string membership")
            keys(pair["go"], ("status", "childExit", "outputBytes"), f"control {role} forced Go fields")
            require(pair["go"]["status"] == "panic" and type(pair["go"]["childExit"]) is int and pair["go"]["childExit"] == 2,
                    f"control {role}: wrong Go terminal/exit pin")
            byte_array(pair["go"]["outputBytes"], f"control {role} Go output")
        else:
            require(pair["kind"] == "exact", f"control {role}: non-rendering control requires exact equality")
            observation(pair["go"], "ok")
            require(pair["go"] == pair["machine"], f"control {role}: non-rendering control pins differ")
    require(pin["controls"]["defer-order"]["expectation"]["machine"] !=
            pin["controls"]["reversed-defer-control"]["expectation"]["machine"],
            "defer-order/reversed control must distinguish results")


def check_source_binding(root, pin, subject_directory, wire, control_wire, go_version, oracle_pin):
    binding = pin["binding"]
    subject_sources = inventory(root, subject_directory, ".go")
    controls = inventory(root, binding["control_package"], ".go")
    check_inventory(subject_sources, binding["go_sources"], "subject Go inventory")
    check_inventory(controls, binding["control_sources"], "control Go inventory")
    # Every exact subject source, including its main/init declarations, is
    # present byte-for-byte in the separate control package. The semantic
    # frontend still sees only the original subject package for admission.
    for name, digest in subject_sources.items():
        copied = str(PurePosixPath(binding["control_package"]) / PurePosixPath(name).relative_to(subject_directory))
        require(controls.get(copied) == digest, f"control package changes/omits subject source: {name}")
    check_inventory(apparatus_inventory(root), binding["apparatus_sources"], "apparatus inventory")
    require(sha(wire) == binding["native_wire_sha256"] and sha(control_wire) == binding["control_wire_sha256"],
            "fresh native subject/control wire differs from pin")
    require(go_version == binding["go_toolchain"] and sha(oracle_pin) == binding["go_oracle_pin_sha256"],
            "Go toolchain/oracle pin differs")
    rationale = pin["rationale"]
    require(sha(root / rationale["path"]) == rationale["sha256"], "reviewed rationale changed")
    headings = re.findall(r"^#{1,6} " + re.escape(rationale["section"]) + r"$",
                          (root / rationale["path"]).read_text(), flags=re.MULTILINE)
    require(len(headings) == 1, "rationale section is missing or ambiguous")
