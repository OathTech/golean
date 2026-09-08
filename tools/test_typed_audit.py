#!/usr/bin/env python3
"""Scratch lifecycle and write-through controls; compiled poisons run per gate."""
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import typed_audit as audit


class AuditScratchTests(unittest.TestCase):
    def setUp(self):
        self.root = self.parent / self._testMethodName
        self.root.mkdir()

    def test_success_ignores_foreign_tmpdir_and_removes_only_own_tree(self):
        foreign = self.root / "foreign"
        (self.root / ".tmp/old").mkdir(parents=True)
        with patch.dict(os.environ, {"TMPDIR": str(foreign)}):
            with audit.scratch(self.root, "control") as directory:
                self.assertEqual(directory.parent, self.root / ".tmp")
                (directory / "result").write_text("success")
        self.assertFalse(directory.exists())
        self.assertFalse(foreign.exists())
        self.assertTrue((self.root / ".tmp/old").is_dir())

    def test_failed_subprocess_keeps_output_and_reason(self):
        with self.assertRaisesRegex(RuntimeError, "exited 17"):
            with audit.scratch(self.root, "control") as directory:
                audit.run_logged([sys.executable, "-c", "print('named failure'); raise SystemExit(17)"],
                                 directory / "audit.log", cwd=self.root)
        self.assertIn("named failure", (directory / "audit.log").read_text())
        self.assertIn("exited 17", (directory / "failure.txt").read_text())

    def test_overlay_excludes_poison_and_every_sidecar(self):
        package = self.root / ".lake/build/lib/lean/Tests"
        package.mkdir(parents=True)
        before = {}
        for name in ["Poison.olean", "Poison.olean.private", "Poison.ir", "Poison.ilean",
                     "Poison.setup.json", "Poison.olean.server", "Sibling.olean", "PoisonExtra.olean"]:
            before[name] = ("original " + name).encode()
            (package / name).write_bytes(before[name])
        fixture = self.root / "overlay"
        audit.link_package(self.root, fixture, "Tests.Poison")
        for name in before:
            target = fixture / "Tests" / name
            if name.startswith("Poison."):
                self.assertFalse(target.exists(), name)
                target.write_text("private compiled output")
                self.assertFalse(target.is_symlink())
            else:
                self.assertTrue(target.is_symlink(), name)
        self.assertEqual(before, {p.name: p.read_bytes() for p in package.iterdir()})

    def test_missing_real_build_is_named_failure(self):
        with self.assertRaisesRegex(RuntimeError, "no built olean: Tests.Missing"):
            audit.link_package(self.root, self.root / "overlay", "Tests.Missing")

    def test_shell_gate_failure_records_the_failed_command(self):
        command = ['bash', '-c', 'set -Eeuo pipefail; ROOT=$1; . "$2"; false',
                   'scratch-control', str(self.root), str(audit.ROOT / 'scripts/typed-gate-scratch.sh')]
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        directories = list((self.root / '.tmp').glob('typed-gate.*'))
        self.assertEqual(len(directories), 1)
        self.assertIn('Command failed (exit 1): false',
                      (directories[0] / 'failure.txt').read_text())


if __name__ == "__main__":
    with audit.scratch(audit.ROOT, "typed-audit-controls") as directory:
        AuditScratchTests.parent = directory
        result = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(AuditScratchTests))
        if not result.wasSuccessful():
            sys.exit("Audit scratch self-tests failed")
