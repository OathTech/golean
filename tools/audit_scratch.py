"""Owned mutation scratch: seal evidence, then release isolated build copies.

No audit verdict is inferred here. Callers keep their compiler-exit and named
rejection assertions; this layer records actual commands and returns results.
"""
from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
import functools
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tarfile
import time

from storage import Budget, GIB, StorageError, allocated, atomic_json, go_cache

_active = ContextVar("golean_audit_run")
ENV_KEYS = ("LEAN_PATH", "LEAN_SYSROOT", "LEAN_NUM_THREADS", "GOLEAN_MEM_MAX",
            "GOLEAN_CAPPED", "GOCACHE", "GOLEAN_SHARED_GOCACHE", "GO111MODULE")
COMPILED = (".olean", ".olean.private", ".olean.server", ".ilean", ".trace", ".hash", ".c", ".o")


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for part in iter(lambda: f.read(1024 * 1024), b""):
            h.update(part)
    return h.hexdigest()


def active_run():
    return _active.get()


def managed_audit(root, label):
    def decorate(fn):
        @functools.wraps(fn)
        def wrapped(*args, **kwargs):
            with AuditRun(root, label) as run:
                token = _active.set(run)
                try:
                    return fn(*args, **kwargs)
                finally:
                    _active.reset(token)
        return wrapped
    return decorate


class AuditRun:
    def __init__(self, root, label, *, budget=None, scratch_bytes=GIB,
                 evidence_bytes=128 * 1024 ** 2):
        self.root = Path(root).resolve()
        self.label = label
        self.budget = budget or Budget(self.root)
        self.scratch_bytes, self.evidence_bytes = scratch_bytes, evidence_bytes
        self.copied = {}
        self.commands = []
        self.fixture_open = False
        self.peak = 0

    def __enter__(self):
        self.claim = self.budget.reserve(
            {"worktree": str(self.root), "label": self.label, "pid": os.getpid()},
            self.scratch_bytes, self.evidence_bytes)
        self.path = self.budget.scratch / self.claim["id"]
        self.evidence = self.budget.evidence / self.claim["id"]
        self.path.mkdir()
        self.evidence.mkdir()
        self.identity = self.path.stat().st_dev, self.path.stat().st_ino
        self.record = dict(self.claim, state="running", commands=self.commands,
                           toolchain=(self.root / "lean-toolchain").read_text().strip(),
                           go_cache=go_cache(self.root), fixtures=[])
        compiler = shutil.which("lean")
        if compiler:
            resolved = Path(compiler).resolve()
            self.record["lean_executable"] = {"path_entry": compiler, "resolved": str(resolved), "sha256": sha(resolved)}
        atomic_json(self.evidence / "run.json", self.record)
        self._snapshot()
        self.old_term = signal.getsignal(signal.SIGTERM)
        signal.signal(signal.SIGTERM, self._terminate)
        print(f"Audit storage: {self.path}; evidence: {self.evidence}", flush=True)
        return self

    def _snapshot(self):
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.root), *args],
                                           env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"})
        self.record["head"] = git("rev-parse", "HEAD").decode().strip()
        (self.evidence / "git-status.txt").write_bytes(git("status", "--porcelain", "--untracked-files=normal"))
        # Include dirty/untracked compiler and gate sources, not gigabytes of
        # historical evidence. The actual bytes, not just HEAD, bind the run.
        paths = set(git("ls-files", "-z").decode().split("\0"))
        paths.update(git("ls-files", "--others", "--exclude-standard", "-z").decode().split("\0"))
        inputs = {}
        with tarfile.open(self.evidence / "inputs.tar.gz", "w:gz") as archive:
            for name in sorted(paths - {""}):
                p = self.root / name
                if name.startswith(("GoLean/", "Tests/", "tools/", "scripts/", "spikes/")) or name in {
                    "GoLean.lean", "Main.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"}:
                    if p.is_file() and not p.is_symlink() and "/docs/" not in name:
                        inputs[name] = sha(p)
                        archive.add(p, arcname=name, recursive=False)
        atomic_json(self.evidence / "input-hashes.json", inputs)
        self.input_hashes = inputs
        self._check()

    def _terminate(self, signum, frame):
        raise KeyboardInterrupt(f"signal {signum}")

    def _check(self):
        self.peak = max(self.peak, allocated(self.path))
        self.budget.check(self.claim)

    def copy_package(self, source, destination):
        source, destination = Path(source), Path(destination)
        if (not self.fixture_open or destination.resolve() != destination
                or not destination.is_relative_to(self.current_fixture)):
            raise StorageError("package copy is outside the owned fixture")
        size = allocated(source)
        if allocated(self.path) + size > self.scratch_bytes:
            raise StorageError("complete package would exceed run reservation")
        records = {}
        for p in sorted(source.rglob("*")):
            if p.is_symlink():
                raise StorageError(f"compiled package contains a symlink: {p}")
            if p.is_file():
                records[str(p.relative_to(source))] = sha(p)
                self.copied[str(p)] = records[str(p.relative_to(source))]
        shutil.copytree(source, destination)  # independent files, never links
        for name, expected in records.items():
            if sha(destination / name) != expected:
                raise StorageError("compiled package copy verification failed")
        self.fixture_record["packages"].append({"source": str(source), "destination": str(destination), "hashes": records})
        self._check()

    @contextmanager
    def fixture(self, label):
        if self.fixture_open or not label or Path(label).name != label or label in {".", ".."}:
            raise StorageError("invalid or overlapping fixture")
        self.fixture_open = True
        path = self.path / label
        path.mkdir()
        self.current_fixture = path
        self.fixture_record = {"label": label, "packages": [], "state": "running"}
        self.record["fixtures"].append(self.fixture_record)
        try:
            yield path
        except BaseException:
            self.fixture_record["state"] = "failed-or-interrupted"
            raise
        else:
            if "expected_rejection" not in self.fixture_record:
                raise StorageError("fixture returned without recording its checked rejection")
            self.fixture_record["state"] = "checks-returned"
        finally:
            self._preserve(path, self.evidence / label)
            atomic_json(self.evidence / "run.json", self.record)
            self._check()
            self._remove(path)
            self.fixture_open = False

    def confirm(self, marker):
        self.fixture_record["expected_rejection"] = {"exit": 1, "text": "forbidden axiom", "marker": marker}

    def run(self, args, *, cwd=None, env=None, text=True, stdout=None, stderr=None, timeout=180):
        if text is not True or stdout != subprocess.PIPE or stderr != subprocess.STDOUT:
            raise StorageError("audited commands require text and merged captured output")
        number = len(self.commands)
        log = self.evidence / f"command-{number:03}.log"
        environment = env if env is not None else os.environ
        record = {"args": [str(a) for a in args], "cwd": str(cwd or self.root),
                  "environment": {k: environment[k] for k in ENV_KEYS if k in environment},
                  "timeout_seconds": timeout, "log": log.name, "returncode": None}
        self.commands.append(record)
        atomic_json(self.evidence / "run.json", self.record)
        with log.open("xb") as output:
            process = subprocess.Popen(args, cwd=cwd, env=env, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            deadline = time.monotonic() + timeout
            try:
                while process.poll() is None:
                    self._check()
                    if time.monotonic() >= deadline:
                        raise subprocess.TimeoutExpired(args, timeout)
                    time.sleep(0.2)
            except BaseException as exc:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                record["exception"] = repr(exc)
                raise
            finally:
                record["returncode"] = process.returncode
                output.flush()
                os.fsync(output.fileno())
                atomic_json(self.evidence / "run.json", self.record)
        self._check()
        return subprocess.CompletedProcess(args, process.returncode, log.read_text())

    def _preserve(self, path, destination):
        destination.mkdir(exist_ok=True)
        inventory = {}
        for p in sorted(path.rglob("*")):
            if p.is_symlink():
                raise StorageError(f"unexpected symlink in owned fixture: {p}")
            if p.is_file():
                name = str(p.relative_to(path))
                inventory[name] = {"sha256": sha(p), "bytes": p.stat().st_size}
                if not name.endswith(COMPILED):
                    target = destination / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(p, target)
                    if sha(target) != inventory[name]["sha256"]:
                        raise StorageError("evidence copy verification failed")
                    with target.open("rb") as f:
                        os.fsync(f.fileno())
        atomic_json(destination / "files.json", inventory)

    def _remove(self, path):
        if (self.path.stat().st_dev, self.path.stat().st_ino) != self.identity:
            raise StorageError("run directory identity changed")
        if path.is_symlink() or path.resolve() != path or not path.is_relative_to(self.path):
            raise StorageError("cleanup target is outside owned run")
        # Only directories created by this invocation, after evidence commit.
        shutil.rmtree(path)

    def __exit__(self, typ, exc, tb):
        signal.signal(signal.SIGTERM, self.old_term)
        try:
            # A failed preservation/cleanup must not be retried as success.
            if self.fixture_open:
                raise StorageError("fixture preservation/cleanup incomplete; reservation retained")
            for name, expected in self.input_hashes.items():
                if sha(self.root / name) != expected:
                    raise StorageError(f"source input changed during audit: {name}")
            for name, expected in self.copied.items():
                if sha(Path(name)) != expected:
                    raise StorageError(f"live build input changed during audit: {name}")
            self._preserve(self.path, self.evidence / "run-files")
            self.record.update(state="passed" if typ is None else "failed-or-interrupted",
                               exception=repr(exc) if exc else None, peak_scratch_bytes=self.peak)
            atomic_json(self.evidence / "run.json", self.record)
            self._check()
            hashes = {str(p.relative_to(self.evidence)): sha(p) for p in self.evidence.rglob("*") if p.is_file()}
            for p in self.evidence.rglob("*"):
                if p.is_file():
                    with p.open("rb") as f:
                        os.fsync(f.fileno())
            atomic_json(self.evidence / "SHA256SUMS.json", hashes)
            self._remove(self.path)
            self.budget.release(self.claim)
            print(f"Audit storage released; peak {self.peak} bytes; sealed evidence {self.evidence}", flush=True)
        except BaseException as cleanup_error:
            print(f"STORAGE INFRASTRUCTURE FAILURE: {cleanup_error}; retained {self.path}", flush=True)
            raise
        return False
