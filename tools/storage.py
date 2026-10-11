"""Shared, cooperative storage admission. Never evicts existing data.

Limits cover registered producers; they are not a filesystem quota. Unknown
and interrupted reservations continue to count until explicitly reconciled.
"""
from __future__ import annotations

from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import uuid

GIB = 1024 ** 3
SCRATCH_LIMIT = 20 * GIB
EVIDENCE_LIMIT = 10 * GIB
OUTPUT_LIMIT = 50 * GIB
FREE_RESERVE = 100 * GIB
CACHE_WARN = 50 * GIB
CACHE_STOP = 75 * GIB


class StorageError(RuntimeError):
    """Infrastructure failure; cannot count as a semantic/audit rejection."""


def project_root(worktree):
    common = subprocess.check_output(
        ["git", "-C", str(worktree), "rev-parse", "--path-format=absolute",
         "--git-common-dir"], text=True).strip()
    # Linked worktrees use the primary checkout's common Git directory.
    return Path(common).resolve().parent


def allocated(path, *, exclude=()):
    """Allocated regular-file bytes, no symlink traversal; hard links once."""
    total, seen = 0, set()
    for directory, dirs, files in os.walk(path, followlinks=False):
        dirs[:] = [d for d in dirs if not (Path(directory) / d).is_symlink()
                   and Path(directory) / d not in exclude]
        for name in files:
            p = Path(directory) / name
            try:
                st = p.lstat()
            except FileNotFoundError:
                # Compilers atomically rename temporary outputs during scans.
                # Reservations cover the producer's remaining allocation.
                continue
            key = st.st_dev, st.st_ino
            if not p.is_symlink() and key not in seen:
                seen.add(key)
                total += st.st_blocks * 512
    return total


def atomic_json(path, data):
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".new")
    with temporary.open("x") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


class Budget:
    def __init__(self, worktree, *, base=None, scratch_limit=SCRATCH_LIMIT,
                 evidence_limit=EVIDENCE_LIMIT, free_reserve=FREE_RESERVE,
                 output_limit=OUTPUT_LIMIT):
        # Explicit base/limits are for isolated tests, never env opt-outs.
        self.base = Path(base) if base else project_root(worktree) / "artifacts/storage"
        self.base.mkdir(parents=True, exist_ok=True)
        self.scratch = self.base / "scratch"
        self.evidence = self.base / "evidence"
        self.claims = self.base / "reservations"
        for p in (self.scratch, self.evidence, self.claims):
            p.mkdir(exist_ok=True)
            if p.is_symlink():
                raise StorageError(f"storage directory cannot be a symlink: {p}")
        self.scratch_limit = scratch_limit
        self.evidence_limit = evidence_limit
        self.free_reserve = free_reserve
        self.output_limit = output_limit

    def register_outputs(self, paths, cache):
        """Persist roots across runs so successive campaigns cannot reset usage."""
        with self.locked():
            file = self.base / 'output-roots.json'
            value = json.loads(file.read_text()) if file.exists() else {'paths': [], 'exclude': []}
            value['paths'] = sorted(set(value['paths']) | {str(Path(p).resolve()) for p in paths})
            value['exclude'] = sorted(set(value['exclude']) | {str(self.base.resolve()), str(Path(cache).resolve())})
            atomic_json(file, value)

    def output_bytes(self):
        file = self.base / 'output-roots.json'
        if not file.exists():
            return 0
        value = json.loads(file.read_text())
        paths = [Path(p) for p in value['paths']]
        paths = [p for p in paths if not any(p != q and p.is_relative_to(q) for q in paths)]
        exclude = {Path(p) for p in value['exclude']}
        return sum(allocated(p, exclude=exclude) for p in paths if p not in exclude)

    @contextmanager
    def locked(self):
        with (self.base / "lock").open("a") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            yield

    def reserve(self, owner, scratch_bytes, evidence_bytes):
        with self.locked():
            claims = [json.loads(p.read_text()) for p in self.claims.glob("*.json")]
            # Count all existing scratch, including unowned leftovers. Subtract
            # each reserved run's measured bytes once to avoid double counting.
            used = allocated(self.scratch)
            promised = sum(max(0, c["scratch_bytes"] - allocated(self.scratch / c["id"]))
                           for c in claims)
            evidence = allocated(self.evidence)
            evidence_promised = sum(max(0, c["evidence_bytes"] - allocated(self.evidence / c["id"]))
                                    for c in claims)
            if used + promised + scratch_bytes > self.scratch_limit:
                raise StorageError("managed scratch budget exhausted; inspect reservations")
            if evidence + evidence_promised + evidence_bytes > self.evidence_limit:
                raise StorageError("retained evidence budget exhausted; explicit disposition required")
            output_promised = sum(c.get('output_bytes', 0) for c in claims)
            if self.output_bytes() + output_promised + owner.get('output_bytes', 0) > self.output_limit:
                raise StorageError("retained generated-output budget exhausted; explicit disposition required")
            if shutil.disk_usage(self.base).free < self.free_reserve + promised + evidence_promised + scratch_bytes + evidence_bytes:
                raise StorageError("filesystem free reserve would be breached")
            token = uuid.uuid4().hex
            record = dict(owner, id=token, scratch_bytes=scratch_bytes,
                          evidence_bytes=evidence_bytes, created=time.time())
            atomic_json(self.claims / (token + ".json"), record)
            return record

    def release(self, claim):
        with self.locked():
            path = self.claims / (claim["id"] + ".json")
            if json.loads(path.read_text()) != claim:
                raise StorageError("reservation ownership changed")
            path.unlink()

    def check(self, claim, *, check_outputs=False):
        if allocated(self.scratch / claim["id"]) > claim["scratch_bytes"]:
            raise StorageError("run exceeded scratch reservation")
        if allocated(self.evidence / claim["id"]) > claim["evidence_bytes"]:
            raise StorageError("run exceeded evidence reservation")
        if shutil.disk_usage(self.base).free < self.free_reserve:
            raise StorageError("filesystem free reserve breached")
        if check_outputs and self.output_bytes() > self.output_limit:
            raise StorageError("aggregate retained generated outputs exceed budget")


def go_cache(worktree):
    configured = os.environ.get("GOLEAN_SHARED_GOCACHE") or os.environ.get("GOCACHE")
    path = Path(configured) if configured else project_root(worktree) / "artifacts/go-build-cache"
    if not path.is_absolute():
        raise StorageError("Go cache must be an absolute path (GOCACHE=off is not a cache)")
    path.mkdir(parents=True, exist_ok=True)
    # No hidden eviction. Periodic/cache maintenance reports provide the full
    # scan; admission runs it at producer startup, not on each Go invocation.
    return str(path.resolve())


def cache_admission(worktree):
    path = go_cache(worktree)
    size = allocated(path)
    if size >= CACHE_STOP:
        raise StorageError(f"Go cache maintenance threshold exceeded: {path}, {size} bytes")
    if size >= CACHE_WARN:
        print(f"storage warning: Go cache {path}: {size} bytes", file=__import__('sys').stderr)
    if shutil.disk_usage(path).free < FREE_RESERVE:
        raise StorageError("filesystem free reserve breached before Go build")
    return path


if __name__ == "__main__":
    import sys
    try:
        root = Path(__file__).resolve().parents[1]
        if sys.argv[1:] == ["go-cache"]:
            print(go_cache(root))
        elif sys.argv[1:] == ["check-cache"]:
            print(cache_admission(root))
        elif sys.argv[1:] == ["report"]:
            budget = Budget(root)
            print(json.dumps({"base": str(budget.base), "scratch_bytes": allocated(budget.scratch),
                              "evidence_bytes": allocated(budget.evidence),
                              "retained_output_bytes": budget.output_bytes(),
                              "reservations": [json.loads(p.read_text()) for p in budget.claims.glob('*.json')],
                              "go_cache": go_cache(root), "go_cache_bytes": allocated(go_cache(root)),
                              "free_bytes": shutil.disk_usage(budget.base).free}, indent=2))
        else:
            raise StorageError("usage: storage.py go-cache|check-cache|report")
    except (StorageError, OSError) as e:
        print(f"storage infrastructure failure: {e}", file=sys.stderr)
        sys.exit(2)
