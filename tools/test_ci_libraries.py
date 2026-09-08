#!/usr/bin/env python3
"""Ownership/receipt controls, including a real Lean build-bypass probe."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import Mock, patch

import ci_libraries as ci
from typed_audit import scratch


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.root = self.parent / self._testMethodName
        (self.root / "Tests").mkdir(parents=True)
        (self.root / "scripts").mkdir()
        (self.root / "Tests/A.lean").write_text("example : True := True.intro\n")
        self.config = self.root / "lakefile.toml"
        self.config.write_text('[[lean_lib]]\nname = "ATests"\nglobs = ["Tests.A"]\n')
        self.registry = self.root / "scripts/ci-libraries.json"
        self.registry.write_text(json.dumps({"a": {"libraries": ["ATests"], "executables": []}}))

    def test_complete_ownership_and_actual_targets(self):
        _, stats = ci.coverage(self.root)
        self.assertEqual(stats["test_modules"], 1)
        run = ci.initialize(self.root)
        runner = Mock(return_value=subprocess.CompletedProcess([], 0))
        self.assertEqual(ci.run_step(self.root, run, "a", [], runner=runner), 0)
        self.assertEqual(runner.call_args.args[0],
                         [str(self.root / "scripts/capped"), "lake", "build", "ATests:leanArts"])
        self.assertEqual(len(ci.verify(self.root, run)["receipts"]), 1)

    def test_empty_default_facets_cannot_skip_a_broken_test(self):
        self.config.write_text('name="GateCoverageControl"\n' + self.config.read_text()
                               + 'defaultFacets=[]\n')
        (self.root / 'lean-toolchain').write_bytes((ci.ROOT / 'lean-toolchain').read_bytes())
        (self.root / 'Tests/A.lean').write_text('def broken : Nat := "not a natural number"\n')
        capped = self.root / 'scripts/capped'
        capped.write_text('#!/bin/sh\nexec "' + str(ci.ROOT / 'scripts/capped') + '" "$@"\n')
        capped.chmod(0o755)
        run = ci.initialize(self.root)
        def actual_build(args, **kwargs):
            result = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, **kwargs)
            (self.root / 'actual-build.log').write_text(result.stdout)
            return result
        with patch.dict(os.environ, {'GOLEAN_MEM_MAX': '4G', 'LEAN_NUM_THREADS': '1'}):
            code = ci.run_step(self.root, run, 'a', [], runner=actual_build)
        self.assertEqual(code, 1, 'empty defaultFacets hid the broken test')
        output = (self.root / 'actual-build.log').read_text()
        self.assertIn('Tests/A.lean', output)
        self.assertIn('not a natural number', output)
        self.assertIn('type mismatch', output.lower())
        with self.assertRaisesRegex(ValueError, 'failed, stale or mismatched'):
            ci.verify(self.root, run)

    def test_untracked_nested_test_cannot_disappear(self):
        (self.root / "Tests/Nested").mkdir()
        (self.root / "Tests/Nested/New.lean").write_text("-- new regression\n")
        with self.assertRaisesRegex(ValueError, "unowned=.*Tests.Nested.New"):
            ci.coverage(self.root)

    def test_symlink_directory_cannot_hide_tests(self):
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "Hidden.lean").write_text("-- hidden\n")
        (self.root / "Tests/hidden").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "aliased Tests source"):
            ci.coverage(self.root)

    def test_alternate_source_root_cannot_fake_ownership(self):
        self.config.write_text(self.config.read_text() + 'srcDir="elsewhere"\n')
        with self.assertRaisesRegex(ValueError, "srcDir needs explicit coverage support"):
            ci.coverage(self.root)

    def test_executable_root_also_needs_library(self):
        self.config.write_text(self.config.read_text() +
                               '\n[[lean_exe]]\nname="eval"\nroot="Tests.Run"\n')
        (self.root / "Tests/Run.lean").write_text("def main : IO Unit := pure ()\n")
        with self.assertRaisesRegex(ValueError, "unowned=.*Tests.Run"):
            ci.coverage(self.root)

    def test_library_without_ci_step(self):
        self.config.write_text(self.config.read_text() +
                               '\n[[lean_lib]]\nname="BTests"\nglobs=["Tests.B"]\n')
        (self.root / "Tests/B.lean").write_text("-- test\n")
        with self.assertRaisesRegex(ValueError, "lack named CI steps.*BTests"):
            ci.coverage(self.root)

    def test_missing_named_step_receipt(self):
        run = ci.initialize(self.root)
        with self.assertRaisesRegex(ValueError, "named CI step did not run: a"):
            ci.verify(self.root, run)

    def test_failed_build_cannot_mint_passing_receipt(self):
        run = ci.initialize(self.root)
        runner = Mock(return_value=subprocess.CompletedProcess([], 7))
        self.assertEqual(ci.run_step(self.root, run, "a", ["must-not-run"], runner=runner), 7)
        self.assertEqual(runner.call_count, 1)
        with self.assertRaisesRegex(ValueError, "failed, stale or mismatched"):
            ci.verify(self.root, run)

    def test_failed_audit_fails_named_step(self):
        run = ci.initialize(self.root)
        runner = Mock(side_effect=[subprocess.CompletedProcess([], 0), subprocess.CompletedProcess([], 9)])
        self.assertEqual(ci.run_step(self.root, run, "a", ["check"], runner=runner), 9)
        with self.assertRaisesRegex(ValueError, "failed, stale or mismatched"):
            ci.verify(self.root, run)

    def test_previous_run_receipt_is_stale(self):
        first, second = ci.initialize(self.root), ci.initialize(self.root)
        ci.run_step(self.root, first, "a", [], runner=Mock(return_value=subprocess.CompletedProcess([], 0)))
        (second / "a.json").write_bytes((first / "a.json").read_bytes())
        with self.assertRaisesRegex(ValueError, "failed, stale or mismatched"):
            ci.verify(self.root, second)

    def test_wrong_build_targets_are_rejected(self):
        run = ci.initialize(self.root)
        ci.run_step(self.root, run, "a", [], runner=Mock(return_value=subprocess.CompletedProcess([], 0)))
        receipt = json.loads((run / "a.json").read_text())
        receipt["targets"] = ["SomeOtherLibrary"]
        (run / "a.json").write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, "failed, stale or mismatched"):
            ci.verify(self.root, run)

    def test_configuration_change_during_run(self):
        run = ci.initialize(self.root)
        self.config.write_text(self.config.read_text() + "\n# edited during CI\n")
        with self.assertRaisesRegex(ValueError, "coverage changed"):
            ci.verify(self.root, run)

    def test_missing_declared_source(self):
        (self.root / "Tests/A.lean").unlink()
        with self.assertRaisesRegex(ValueError, "missing or aliased source"):
            ci.coverage(self.root)

    def test_unsupported_glob_cannot_silently_underreach(self):
        self.config.write_text(self.config.read_text().replace('"Tests.A"', '"Tests.*"'))
        with self.assertRaisesRegex(ValueError, "unsupported module glob"):
            ci.coverage(self.root)

    def test_duplicate_registry_key(self):
        self.registry.write_text('{"a": {}, "a": {}}')
        with self.assertRaisesRegex(ValueError, "duplicate registry key"):
            ci.coverage(self.root)

    def test_undeclared_library(self):
        self.registry.write_text(self.registry.read_text().replace('"ATests"', '"MissingTests"'))
        with self.assertRaisesRegex(ValueError, "undeclared library MissingTests"):
            ci.coverage(self.root)

    def test_ambiguous_library_ownership(self):
        self.config.write_text(self.config.read_text() +
                               '\n[[lean_lib]]\nname="BTests"\nglobs=["Tests.A"]\n')
        self.registry.write_text('{"a":{"libraries":["ATests","BTests"],"executables":[]}}')
        with self.assertRaisesRegex(ValueError, "belongs to multiple libraries"):
            ci.coverage(self.root)


if __name__ == "__main__":
    with scratch(ci.ROOT, "ci-library-controls") as directory:
        CoverageTests.parent = directory
        result = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(CoverageTests))
        if not result.wasSuccessful():
            sys.exit("Library coverage self-tests failed")
