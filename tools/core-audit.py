#!/usr/bin/env python3
"""Core totality audit: a harness over EVERY GoLean/ module.

[AGENT] 2026-09-16, lane park-lane/typed-profiles-0916 (docs/2026-09-16_typed-profiles-parked.md
§3). The import list is taken from the DISK, not a fixed table, and handed to
Tests.GoCoreAudit.run, which refuses any module on disk that is not in the closure and any
GoLean.* module in the closure that is not on disk. The compiled poison controls (typed_audit.py)
were removed in the 2026-10-12 gate cull (docs/2026-10-12_gate-cull-plan.md §3.3, [USER] D3).
Run under `lake env` (scripts/check-core-audit) so the harness sees the built oleans. The
`lean` run goes through the box tool `capped` when it is on PATH, bare otherwise (box-independence,
release-readiness row 46: the cap is detected, never shipped; the limit is CAPPED_MEM_MAX).
"""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def on_disk_modules():
    top = sorted(p for p in (ROOT / "GoLean").glob("*.lean") if p.is_file())
    core = sorted(p for p in (ROOT / "GoLean/GoCore").glob("*.lean") if p.is_file())
    if not core:
        raise RuntimeError("core audit: GoLean/GoCore/ has no modules — a vacuous audit is refused")
    modules = ["GoLean." + p.stem for p in top] + ["GoLean.GoCore." + p.stem for p in core]
    if len(set(modules)) != len(modules):
        raise RuntimeError("core audit: duplicate module names on disk")
    # The root GoLean.lean is imports only and is scanned by scripts/ci's text scan; the
    # harness imports every module under GoLean/ explicitly rather than the root.
    return modules


def harness(modules):
    quoted = ", ".join('"' + m + '"' for m in modules)
    lines = [f"import {m}" for m in modules]
    lines += ["import Tests.GoCoreAudit", f"#eval Tests.GoCoreAudit.run [{quoted}]", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    modules = on_disk_modules()
    print(f"Core audit harness: {len(modules)} GoLean modules on disk "
          f"({sum(m.startswith('GoLean.GoCore.') for m in modules)} under GoLean/GoCore/)", flush=True)
    (ROOT / ".tmp").mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="core-audit-", dir=ROOT / ".tmp"))
    source = scratch / "AuditAll.lean"
    source.write_text(harness(modules))
    try:
        cap = ["capped"] if shutil.which("capped") else []
        result = subprocess.run(cap + ["lean", str(source)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
    except subprocess.TimeoutExpired:
        sys.exit(f"core audit: the harness exceeded 900 s — did not decide; scratch retained: {scratch}")
    print(result.stdout, end="", flush=True)
    if result.returncode != 0:
        sys.exit(f"core audit: harness exited {result.returncode}; scratch retained: {scratch}")
    if "Core totality audit:" not in result.stdout:
        sys.exit(f"core audit: the harness ran but printed no audit line; scratch retained: {scratch}")
    shutil.rmtree(scratch)
    print("Core totality audit harness: PASS (scratch removed)", flush=True)
