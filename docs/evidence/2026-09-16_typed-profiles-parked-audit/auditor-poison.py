"""[AGENT auditor] Independent poison controls against the re-homed core totality audit.
Mirrors tools/typed_audit.audit_main's mechanics but REPORTS per-poison instead of raising,
so a poison the audit does NOT catch is visible rather than fatal. Writes only into
.tmp/auditor-poison-*/ (fixtures are symlink overlays; the repo is never modified)."""
import os, re, subprocess, sys, tempfile
sys.path.insert(0, "tools")
from typed_audit import ROOT, link_package
sys.path.insert(0, ".")
import importlib.util
spec = importlib.util.spec_from_file_location("core_audit", "tools/core-audit.py")
ca = importlib.util.module_from_spec(spec); spec.loader.exec_module(ca)
HARNESS = ca.harness(ca.on_disk_modules())

POISONS = [
    ("native_decide_in_unlisted_core", "GoLean.GoCore.StateWf",
     "\nprivate theorem auditorNativeHole : (0 : Nat) < 1 := by native_decide\n"),
    ("foreign_axiom_in_unlisted_top_module", "GoLean.ChoiceTrace",
     "\nprivate axiom auditorForeignHole : False\n"),
    ("implemented_by_unsafe", "GoLean.GoCore.PanicText",
     "\nunsafe def auditorUnsafeImpl : Nat := 0\n"
     "@[implemented_by auditorUnsafeImpl] def auditorUnsafeDecl : Nat := 1\n"),
]

root = ROOT / ".tmp"
scratch = tempfile.mkdtemp(prefix="auditor-poison-", dir=root)
from pathlib import Path
scratch = Path(scratch)
harness = scratch / "AuditAll.lean"
harness.write_text(HARNESS)
capped = str(ROOT / "scripts/capped")

def run(args, env=None, cwd=ROOT):
    r = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=900)
    return r.returncode, r.stdout

rc, out = run([capped, "lean", str(harness)])
print(f"[baseline clean harness] exit={rc}")
print(out[-400:])
for label, module, poison in POISONS:
    fixture = scratch / label
    link_package(ROOT, fixture, module)
    src = fixture / (module.replace(".", "/") + ".lean")
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_text((ROOT / (module.replace(".", "/") + ".lean")).read_text() + poison)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
    crc, cout = run([capped, "lean", "-o", str(src.with_suffix(".olean")), str(src)],
                    env=env, cwd=fixture)
    print(f"\n=== {label}: compile exit={crc}")
    if crc != 0:
        print(cout[-1200:]); print(f"{label}: POISON DID NOT COMPILE (control inconclusive)"); continue
    arc, aout = run([capped, "lean", str(harness)], env=env)
    print(f"=== {label}: audit exit={arc}")
    print(aout[-1200:])
    named = [l for l in aout.splitlines() if "forbidden axiom" in l]
    print(f"{label}: VERDICT = {'REFUSED BY NAME' if arc == 1 and named else 'NOT REFUSED'}")
print(f"\nscratch: {scratch}")
