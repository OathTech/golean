"""Adversarial contract tests; the acceptance runner never imports this file."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import string_member as check


def ok(value=True):
    observed = {"tag": "bool", "value": value} if type(value) is bool else {"tag": "int", "kind": "int", "value": value}
    return {"schema": "golean-observation-v1", "status": "ok", "values": [observed], "output": ""}


def panic(message, output=""):
    return {"schema": "golean-observation-v1", "status": "panic", "message": message, "output": output}


def raw(message=b"gc report", output=b""):
    return {"schema": "golean-raw-panic-v1", "status": "panic", "childExit": 2,
            "messageBytes": list(message), "outputBytes": list(output)}


def sample_pin():
    controls = {}
    for role in check.ROLES:
        if role in check.ABORT_ROLES:
            expected = {"kind": "string-member", "machine": panic("orig [recovered]"),
                        "go": {"status": "panic", "childExit": 2, "outputBytes": []}}
        else:
            value = 21 if role == "defer-order" else 12 if role == "reversed-defer-control" else True
            expected = {"kind": "exact", "go": ok(value), "machine": ok(value)}
        controls[role] = {"function": role.replace("-", "_"), "arguments": [], "expectation": expected}
    return {"schema": check.SCHEMA, "envelope": check.ENVELOPE, "matrix": check.MATRIX,
            "case": "panic-recover/string-members/equal", "subject": {"function": "Equal", "arguments": []},
            "scope": "typed-explicit-string", "machine": panic("orig [recovered]"), "controls": controls,
            "binding": {"go_sources": {}, "native_wire_sha256": "0"*64, "go_toolchain": "go1.26.5",
                        "go_oracle_pin_sha256": "0"*64, "apparatus_sources": {},
                        "control_package": "Corpus/controls/string-members/explicit", "control_sources": {},
                        "control_wire_sha256": "0"*64},
            "rationale": {"path": "docs/argument.md", "section": "Explicit subject", "sha256": "0"*64}}


class StringMemberContracts(unittest.TestCase):
    def validate(self, pin):
        check.validate_pin(pin, "panic-recover/string-members/equal", "Equal", [])

    def test_positive_matrix(self):
        self.validate(sample_pin())

    def test_matrix_and_schema_refusals(self):
        transforms = [
            lambda p: p.update(forced_half_ok=True),
            lambda p: p.update(envelope="arbitrary-predicate"),
            lambda p: p.update(matrix="caller-optional-controls"),
            lambda p: p["subject"].update(arguments=[{"tag": "int", "value": 1}]),
            lambda p: p["controls"].pop("dynamic-kind-and-bytes"),
            lambda p: p["controls"].update(extra=p["controls"]["normal-control"]),
            lambda p: p["controls"]["normal-control"].update(function=p["controls"]["direct-recovery"]["function"]),
            lambda p: p["controls"]["defer-order"].update(expectation=p["controls"]["reversed-defer-control"]["expectation"]),
            lambda p: p["controls"]["equal-repanic"]["expectation"].update(kind="exact"),
            lambda p: p["controls"]["direct-recovery"]["expectation"].update(kind="string-member"),
            lambda p: p["controls"]["indirect-recovery"]["expectation"].update(go=ok(False)),
            lambda p: p["controls"]["normal-control"]["expectation"]["machine"].update(status="unsupported"),
            lambda p: p["rationale"].update(path="../outside"),
            lambda p: p["binding"].update(control_package="Corpus/unreviewed"),
            lambda p: p["machine"].update(message="\ud800"),
        ]
        for i, mutate in enumerate(transforms):
            with self.subTest(mutation=i):
                pin = sample_pin()
                mutate(pin)
                with self.assertRaises(check.Refusal):
                    self.validate(pin)

    def test_exact_bytes_and_member_forms(self):
        payload = b"a\n\xff"
        chain = [{"bytes": list(payload), "recovered": True}]
        expected = '"\\x61\\x0a\\xff" [recovered]'
        check.check_actual_member(panic(expected), raw(b"a"), chain)
        # Invalid bytes after LF cannot disappear merely because gc's
        # observed line itself was decodable.
        for wrong in ("a", '"\\x61\\x0a\\xef\\xbf\\xbd" [recovered]', '"\\x61\\x0a\\xff"', "any text"):
            with self.subTest(wrong=wrong), self.assertRaises(check.Refusal):
                check.check_actual_member(panic(wrong), raw(b"a"), chain)
        # The suffix is formatted before LF projection; CR and controls
        # remain payload bytes. R1 does not claim gc printed our member.
        check.check_actual_member(panic("a\x00\x01\r"), raw(b"a\x00\x01\r"),
                                  [{"bytes": list(b"a\x00\x01\r\nZ"), "recovered": True}])
        check.check_actual_member(panic("orig [recovered]"), raw(b"orig [recovered, repanicked]"),
                                  [{"bytes": list(b"orig"), "recovered": True},
                                   {"bytes": list(b"orig"), "recovered": False}])

    def test_no_kind_exit_output_or_chain_waiver(self):
        machine, go, chain = panic("x", "\x00before\n"), raw(b"x", b"\x00before\n"), [{"bytes": [120], "recovered": False}]
        check.check_actual_member(machine, go, chain)
        variants = []
        for field, value in (("status", "fatal"), ("childExit", True), ("childExit", 137),
                             ("outputBytes", list(b"before\n")), ("messageBytes", [True]),
                             ("messageBytes", [256])):
            changed = copy.deepcopy(go); changed[field] = value
            variants.append((machine, changed, chain))
        variants.extend([(machine, go, None), (machine, go, []),
                         (machine, go, [{"bytes": [121], "recovered": False}]),
                         (machine, go, [{"bytes": [120], "recovered": False}, {"value": 3}]),
                         (machine, go, [{"bytes": [120], "recovered": 0}])])
        for i, args in enumerate(variants):
            with self.subTest(mutation=i), self.assertRaises(check.Refusal):
                check.check_actual_member(*args)

    def test_duplicate_keys_and_integer_typing(self):
        for value in ('{"a": 1, "a": 2}', '{"a": {"b": 1, "b": 2}}'):
            with self.assertRaises(check.Refusal):
                json.loads(value, object_pairs_hook=check.unique_object)
        for args in ([{"tag": "int", "value": True}], [{"tag": "bool", "value": True}],
                     [{"tag": "int", "value": 0, "trusted": True}]):
            with self.assertRaises(check.Refusal):
                check.arguments(args, "probe")

    def test_inventory_is_complete_and_content_bound(self):
        # No cleanup: scratch is retained under the session/repo temp root.
        root = Path(__file__).resolve().parents[1]
        directory = Path(tempfile.mkdtemp(prefix="string-inventory-", dir=root/".tmp"))
        (directory / "subject").mkdir()
        (directory / "subject/main.go").write_text("package main\n")
        (directory / "subject/second.go").write_text("package main\nfunc second() {}\n")
        actual = check.inventory(directory, "subject", ".go")
        check.check_inventory(actual, dict(actual), "source")
        for bad in ({"subject/main.go": actual["subject/main.go"]},
                    {**actual, "subject/extra.go": "0"*64},
                    {**actual, "subject/second.go": "0"*64}):
            with self.assertRaises(check.Refusal):
                check.check_inventory(actual, bad, "source")

    def test_executable_entrypoints_are_content_bound_and_required(self):
        root = Path(__file__).resolve().parents[1]
        directory = Path(tempfile.mkdtemp(prefix="string-entrypoints-", dir=root/".tmp"))
        for name, suffix in check.APPARATUS_ROOTS.items():
            source = directory / name / ("InventoryProbe" + suffix)
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("inventory probe\n")
        # These two obligations are independent of the implementation's
        # list, so removing an entry from APPARATUS_FILES cannot remove
        # its negative control as well.
        entrypoints = ("Main.lean", "GoLean.lean")
        for name in set(check.APPARATUS_FILES) | set(entrypoints):
            source = directory / name
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("original source\n")
        pinned = check.apparatus_inventory(directory)
        for name in entrypoints:
            source = directory / name
            with self.subTest(entrypoint=name, mutation="changed"):
                source.write_text("changed executable entrypoint\n")
                with self.assertRaises(check.Refusal):
                    check.check_inventory(check.apparatus_inventory(directory), pinned, "apparatus")
                source.write_text("original source\n")
            with self.subTest(entrypoint=name, mutation="missing"):
                retained = source.with_suffix(".retained")
                source.rename(retained)
                with self.assertRaises(check.Refusal):
                    check.apparatus_inventory(directory)
                retained.rename(source)


if __name__ == "__main__":
    unittest.main()
