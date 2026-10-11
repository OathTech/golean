#!/usr/bin/env python3
"""Adversarial storage lifecycle tests; all deletion is in test-owned roots."""
import concurrent.futures
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from audit_scratch import AuditRun, sha
from storage import Budget, StorageError, allocated, go_cache


class StorageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="golean-storage-test-", dir=os.environ.get("TMPDIR"))
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repo"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Storage Test", "-c", "user.email=test@example.invalid",
                        "commit", "--allow-empty", "-qm", "test"], check=True)
        (self.root / "lean-toolchain").write_text("test-toolchain\n")
        self.base = Path(self.temp.name) / "budget"
        self.budget = Budget(self.root, base=self.base, scratch_limit=4*1024**2,
                             evidence_limit=4*1024**2, free_reserve=0)
        self.package = self.root / "package"
        self.package.mkdir()
        (self.package / "A.olean").write_bytes(b"original compiler output")

    def run_context(self):
        return AuditRun(self.root, "test", budget=self.budget,
                        scratch_bytes=1024**2, evidence_bytes=1024**2)

    def command(self, run, code, timeout=5):
        return run.run([sys.executable, "-c", code], cwd=self.root,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)

    def test_sequential_copies_and_exact_logs(self):
        original = sha(self.package / "A.olean")
        with self.run_context() as run:
            for i in range(3):
                with run.fixture(str(i)) as fixture:
                    run.copy_package(self.package, fixture / "P")
                    (fixture / "P/A.olean").write_bytes(b"poison")
                    (fixture / "P/A.lean").write_text("axiom namedHole : False\n")
                    self.assertEqual(self.command(run, "print('compiled')").returncode, 0)
                    result = self.command(run, "print('forbidden axiom namedHole'); exit(1)")
                    self.assertEqual(result.returncode, 1)
                    self.assertIn("namedHole", result.stdout)
                    run.confirm("namedHole")
                self.assertFalse(fixture.exists())
                self.assertEqual(sha(self.package / "A.olean"), original)
        self.assertFalse(run.path.exists())
        self.assertFalse(list(self.budget.claims.iterdir()))
        record = json.loads((run.evidence / "run.json").read_text())
        self.assertEqual([c['returncode'] for c in record['commands']], [0,1]*3)
        self.assertTrue((run.evidence / "0/P/A.lean").exists())
        self.assertFalse((run.evidence / "0/P/A.olean").exists())
        for name, digest in json.loads((run.evidence / "SHA256SUMS.json").read_text()).items():
            self.assertEqual(sha(run.evidence / name), digest)

    def test_failed_compile_remains_failure_and_is_preserved(self):
        with self.assertRaisesRegex(RuntimeError, "compiler failed"):
            with self.run_context() as run:
                with run.fixture("bad") as fixture:
                    run.copy_package(self.package, fixture / "P")
                    result = self.command(run, "print('parse error'); exit(3)")
                    self.assertEqual(result.returncode, 3)
                    raise RuntimeError("compiler failed")
        record = json.loads((run.evidence / "run.json").read_text())
        self.assertEqual(record['state'], 'failed-or-interrupted')
        self.assertEqual(record['commands'][0]['returncode'], 3)
        self.assertFalse(run.path.exists())

    def test_evidence_write_failure_preserves_fixture_and_reservation(self):
        with self.assertRaises(StorageError):
            with self.run_context() as run:
                with patch.object(run, '_preserve', side_effect=OSError('disk full')):
                    with run.fixture('fail') as fixture:
                        run.copy_package(self.package, fixture / 'P')
                        run.confirm('marker')
        self.assertTrue((fixture / 'P/A.olean').exists())
        self.assertEqual(len(list(self.budget.claims.glob('*.json'))), 1)

    def test_cleanup_failure_is_not_a_pass(self):
        with self.assertRaises(StorageError):
            with self.run_context() as run:
                with patch.object(run, '_remove', side_effect=OSError('cannot unlink')):
                    with run.fixture('fail') as fixture:
                        run.copy_package(self.package, fixture / 'P')
                        run.confirm('marker')
        self.assertTrue((run.evidence / 'fail/files.json').exists())
        self.assertTrue(fixture.exists())
        self.assertTrue(list(self.budget.claims.iterdir()))

    def test_symlink_and_foreign_cleanup_refused(self):
        with self.run_context() as run:
            with self.assertRaises(StorageError):
                run._remove(self.package)
            with self.assertRaises(StorageError):
                run._remove(run.path / '..' / '..' / '..' / 'repo/package')
            with self.assertRaises(StorageError):
                with run.fixture('../escape'):
                    pass
        self.assertTrue((self.package / 'A.olean').exists())

    def test_timeout_kills_child_and_preserves_actual_exit(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            with self.run_context() as run:
                self.command(run, "import time; print('started', flush=True); time.sleep(30)", timeout=.3)
        record = json.loads((run.evidence / 'run.json').read_text())
        self.assertEqual(record['commands'][0]['returncode'], -signal.SIGKILL)
        self.assertEqual(record['state'], 'failed-or-interrupted')
        self.assertFalse(run.path.exists())

    def test_concurrent_admission_serializes(self):
        def reserve(i):
            budget = Budget(self.root, base=self.base, scratch_limit=100, evidence_limit=100, free_reserve=0)
            try:
                return budget.reserve({'pid': os.getpid(), 'lane': i}, 80, 80)
            except StorageError:
                return None
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            claims = list(pool.map(reserve, [1,2]))
        self.assertEqual(sum(c is not None for c in claims), 1)
        # A dead/unknown owner is not silently dropped on the next admission.
        self.assertIsNone(reserve(3))

    def test_sigterm_preserves_interruption_and_kills_child(self):
        with self.assertRaises(KeyboardInterrupt):
            with self.run_context() as run:
                self.command(run, 'import os,signal,time; os.kill(os.getppid(), signal.SIGTERM); time.sleep(30)')
        record = json.loads((run.evidence / 'run.json').read_text())
        self.assertEqual(record['commands'][0]['returncode'], -signal.SIGKILL)
        self.assertEqual(record['state'], 'failed-or-interrupted')
        self.assertFalse(run.path.exists())

    def test_fast_gate_growth_is_failure_with_files_preserved(self):
        from storage_watch import watch
        (self.root / '.tmp').mkdir()
        cache = self.root / 'cache'
        cache.mkdir()
        target = self.root / '.tmp' / 'new-output'
        with patch('storage_watch.inherited', return_value=False), patch('storage_watch.cache_admission', return_value=str(cache)):
            status = watch(self.root, [sys.executable, '-c',
                           'from pathlib import Path; import sys; Path(sys.argv[1]).write_bytes(bytes(8192))', str(target)],
                           budget=self.budget, limit=4096)
        self.assertEqual(status, 2)
        self.assertTrue(target.exists())

    def test_guard_stops_detached_descendant(self):
        from storage_processes import stop_tree
        marker = self.root / 'detached-pid'
        parent = subprocess.Popen([sys.executable, '-c',
            'import subprocess,sys,time; from pathlib import Path; '
            'p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"],start_new_session=True); '
            'Path(sys.argv[1]).write_text(str(p.pid)); time.sleep(60)', str(marker)])
        try:
            deadline = time.monotonic()+5
            while not marker.exists() and time.monotonic() < deadline:
                time.sleep(.01)
            descendant = int(marker.read_text())
            handle = os.pidfd_open(descendant)
            try:
                stop_tree(parent.pid)
                parent.wait(timeout=5)
                import select
                poll = select.poll()
                poll.register(handle, select.POLLIN)
                self.assertTrue(poll.poll(5000), 'detached child survived cleanup')
            finally:
                os.close(handle)
        finally:
            if parent.poll() is None:
                stop_tree(parent.pid)
                parent.wait()

    def test_retained_output_budget_survives_completed_runs(self):
        paths = [self.root / 'artifacts']
        paths[0].mkdir()
        cache = self.root / 'cache'
        cache.mkdir()
        limited = Budget(self.root, base=self.base, scratch_limit=1024**2,
                         evidence_limit=1024**2, free_reserve=0, output_limit=10000)
        limited.register_outputs(paths, cache)
        first = limited.reserve({'output_bytes': 4096}, 1, 1)
        (paths[0] / 'first').write_bytes(bytes(4096))
        limited.release(first)
        second = limited.reserve({'output_bytes': 4096}, 1, 1)
        (paths[0] / 'second').write_bytes(bytes(4096))
        limited.release(second)
        # Reconstructing the coordinator cannot forget retained output.
        next_run = Budget(self.root, base=self.base, scratch_limit=1024**2,
                          evidence_limit=1024**2, free_reserve=0, output_limit=10000)
        with self.assertRaises(StorageError):
            next_run.reserve({'output_bytes': 4096}, 1, 1)
        self.assertEqual(next_run.output_bytes(), 8192)

    def test_unknown_bytes_and_evidence_stop_admission(self):
        (self.budget.scratch / 'unknown').mkdir()
        (self.budget.scratch / 'unknown/big').write_bytes(bytes(4*1024**2))
        with self.assertRaises(StorageError):
            self.budget.reserve({'pid': os.getpid()}, 1, 1)
        self.assertTrue((self.budget.scratch / 'unknown/big').exists())

    def test_shared_cache_and_explicit_override(self):
        linked = Path(self.temp.name) / 'linked'
        subprocess.run(['git', '-C', str(self.root), 'worktree', 'add', '--detach', str(linked)], check=True, capture_output=True)
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual(go_cache(self.root), go_cache(linked))
        explicit = str(Path(self.temp.name) / 'explicit')
        with patch.dict(os.environ, {'GOCACHE': explicit}, clear=True):
            self.assertEqual(go_cache(self.root), explicit)
        with patch.dict(os.environ, {'GOCACHE': 'relative'}, clear=True):
            with self.assertRaises(StorageError):
                go_cache(self.root)


if __name__ == '__main__':
    unittest.main()
