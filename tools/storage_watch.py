#!/usr/bin/env python3
"""Admission and periodic disk guard for complete gates/campaigns.

This is cooperative accounting, not an OS quota: a writer can overshoot
between samples. It refuses at the free-space/cache thresholds and kills its
own process group on excess growth. It never deletes result directories.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from storage import Budget, GIB, CACHE_STOP, StorageError, allocated, atomic_json, cache_admission
from storage_processes import stop_tree


def inherited(root):
    token = os.environ.get('GOLEAN_STORAGE_LEASE', '')
    if len(token) != 32 or any(c not in '0123456789abcdef' for c in token):
        return False
    budget = Budget(root)
    claim = budget.claims / (token + '.json')
    if not claim.is_file():
        return False
    record = json.loads(claim.read_text())
    if record.get('label') != 'gate-disk-watch':
        return False
    pid = os.getppid()
    while pid > 1:
        if pid == record['pid']:
            return True
        try:
            # /proc/<pid>/stat's comm may contain spaces and parentheses.
            pid = int(Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()[1])
        except (OSError, ValueError, IndexError):
            return False
    return False


def watch(root, command, *, budget=None, limit=8 * GIB):
    if inherited(root):
        os.execvp(command[0], command)
    cache = cache_admission(root)
    budget = budget or Budget(root)
    (root / '.tmp').mkdir(exist_ok=True)
    paths = [root / '.tmp', root / 'artifacts', root / '.lake']
    if (root / 'spikes').is_dir():
        paths += [p / '.lake' for p in (root / 'spikes').iterdir() if p.is_dir()]
    paths += [Path(p).resolve() for p in json.loads(os.environ.get('GOLEAN_STORAGE_EXTRA_PATHS', '[]'))]
    paths = sorted(set(paths))
    paths = [p for p in paths if not any(p != q and p.is_relative_to(q) for q in paths)]
    excluded = {budget.base, Path(cache)}
    budget.register_outputs(paths, cache)
    claim = budget.reserve({'label': 'gate-disk-watch', 'worktree': str(root), 'pid': os.getpid(), 'output_bytes': limit},
                           limit, 1024**2)
    tmp = budget.scratch / claim['id']
    evidence = budget.evidence / claim['id']
    tmp.mkdir()
    evidence.mkdir()
    record = dict(claim, command=command, state='running', go_cache=cache)
    before = {str(p): allocated(p, exclude=excluded) for p in paths}
    record['before_bytes'] = before
    atomic_json(evidence / 'run.json', record)
    env = {**os.environ, 'GOLEAN_STORAGE_LEASE': claim['id'], 'TMPDIR': str(tmp), 'GOCACHE': cache}
    child = subprocess.Popen(command, env=env, start_new_session=True)
    old = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame):
        raise KeyboardInterrupt(f'signal {signum}')
    signal.signal(signal.SIGTERM, interrupted)
    cause, peak = None, 0
    last = before
    try:
        while child.poll() is None:
            last = {str(p): allocated(p, exclude=excluded) for p in paths}
            growth = sum(max(0, last[name] - size) for name, size in before.items()) + allocated(tmp)
            peak = max(peak, growth)
            budget.check(claim, check_outputs=True)
            if growth > limit:
                raise StorageError(f'gate generated growth {growth} exceeds reservation {limit}')
            if allocated(cache) >= CACHE_STOP:
                raise StorageError('shared Go cache reached maintenance threshold')
            for _ in range(10):
                if child.poll() is not None:
                    break
                time.sleep(.5)
    except BaseException as exc:
        cause = repr(exc)
        if child.poll() is None:
            stop_tree(child.pid)
            child.wait()
    finally:
        signal.signal(signal.SIGTERM, old)
    # Fast writers may finish between samples; they must still fail the guard.
    last = {str(p): allocated(p, exclude=excluded) for p in paths}
    growth = sum(max(0, last[name] - size) for name, size in before.items()) + allocated(tmp)
    peak = max(peak, growth)
    try:
        budget.check(claim, check_outputs=True)
        if growth > limit or allocated(cache) >= CACHE_STOP:
            raise StorageError('final disk accounting exceeds gate/cache budget')
    except StorageError as exc:
        cause = cause or repr(exc)
    record.update(state='infrastructure-failure' if cause else 'finished', cause=cause,
                  child_returncode=child.returncode, peak_growth_bytes=peak, after_bytes=last,
                  retained_tmp_bytes=allocated(tmp))
    atomic_json(evidence / 'run.json', record)
    # Unknown shell-generated evidence is retained. The next reservation counts
    # it, preventing unbounded accumulation; expiry needs explicit disposition.
    budget.release(claim)
    print(f"Storage gate: child exit {child.returncode}, peak growth {peak} bytes; {evidence}", file=sys.stderr)
    if cause:
        print(f'STORAGE INFRASTRUCTURE FAILURE: {cause}', file=sys.stderr)
        return 2
    return child.returncode if child.returncode >= 0 else 128 - child.returncode


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    try:
        if sys.argv[1:] == ['inside']:
            sys.exit(0 if inherited(root) else 1)
        if len(sys.argv) < 3 or sys.argv[1] != '--':
            raise StorageError('usage: storage_watch.py inside | -- command arguments...')
        sys.exit(watch(root, sys.argv[2:]))
    except (OSError, ValueError, StorageError) as exc:
        print(f'STORAGE INFRASTRUCTURE FAILURE: {exc}', file=sys.stderr)
        sys.exit(2)
