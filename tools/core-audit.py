#!/usr/bin/env python3
"""Core totality audit: a harness over EVERY GoLean/ module, then compiled poison controls.

[AGENT] 2026-09-16, lane park-lane/typed-profiles-0916 (docs/2026-09-16_typed-profiles-parked.md
§3). Replaces scripts/check-interface.py's audit for the core after the typed-profile
family and its facade were parked. The import list is taken from the DISK, not a fixed
table, and handed to Tests.GoCoreAudit.run, which refuses any module on disk that is not
in the closure and any GoLean.* module in the closure that is not on disk.
"""
from pathlib import Path

from typed_audit import ROOT, audit_main


def on_disk_modules():
    top = sorted(p for p in (ROOT / "GoLean").glob("*.lean") if p.is_file())
    core = sorted(p for p in (ROOT / "GoLean/GoCore").glob("*.lean") if p.is_file())
    if not core:
        raise RuntimeError("core audit: GoLean/GoCore/ has no modules — a vacuous audit is refused")
    modules = ["GoLean." + p.stem for p in top] + ["GoLean.GoCore." + p.stem for p in core]
    if len(set(modules)) != len(modules):
        raise RuntimeError("core audit: duplicate module names on disk")
    # The root GoLean.lean is imports only and is scanned by scripts/ci's text scans; the
    # poison overlay (typed_audit.link_package) covers the GoLean/ package DIRECTORY, so the
    # harness imports every module under it explicitly rather than the root.
    return modules


def harness(modules):
    quoted = ", ".join('"' + m + '"' for m in modules)
    lines = [f"import {m}" for m in modules]
    lines += ["import Tests.GoCoreAudit", f"#eval Tests.GoCoreAudit.run [{quoted}]", ""]
    return "\n".join(lines)


mutations = [
    ('trace_private', 'GoLean.GoCore.Trace', 'coreAuditTraceHole',
     '\nprivate axiom coreAuditTraceHole : False\n'),
    ('observer_private', 'GoLean.GoCore.AbortObservation', 'coreAuditObserverHole',
     '\nprivate axiom coreAuditObserverHole : False\n'),
    ('string_panic_private', 'GoLean.GoCore.StringPanic', 'coreAuditStringPanicHole',
     '\nprivate axiom coreAuditStringPanicHole : False\n'),
    ('audit_private', 'Tests.GoCoreAudit', 'coreAuditSelfHole',
     '\nprivate axiom coreAuditSelfHole : False\n'),
    ('contract_trailing', 'Tests.GoCoreContract', 'sorryAx',
     '\nprivate theorem coreAuditContractHole : False := by sorry\n'),
]

if __name__ == "__main__":
    modules = on_disk_modules()
    print(f"Core audit harness: {len(modules)} GoLean modules on disk "
          f"({sum(m.startswith('GoLean.GoCore.') for m in modules)} under GoLean/GoCore/)", flush=True)
    audit_main('core-audit', harness(modules), mutations)
