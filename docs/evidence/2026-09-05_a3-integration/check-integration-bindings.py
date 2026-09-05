from pathlib import Path
import hashlib, json, subprocess
ROOT = Path(__file__).resolve().parents[2]
MAIN = "4919b05a"
binding = json.loads((ROOT / "docs/evidence/2026-09-05_a3-admission-review/source-bindings.json").read_text())
changed = []
for path, expected in binding["sha256_by_path"].items():
    if hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected:
        changed.append(path)
assert changed == ["GoLean/GoCore/Ops.lean", "GoLean/GoCore/StateWf.lean", "GoLean.lean", "lakefile.toml", "scripts/ci"], changed
print(f"A3 original review bindings: {len(binding['sha256_by_path'])-len(changed)}/{len(binding['sha256_by_path'])} unchanged; all A3 implementation/tests/fixtures/tools identical")
for path in changed[:3]:
    assert subprocess.check_output(["git", "show", f"{MAIN}:{path}"], cwd=ROOT) == (ROOT/path).read_bytes()
    print(path + ": exact landed-main bytes")
for path, insertion in [
    ("lakefile.toml", '\n[[lean_lib]]\nname = "AdmissionTests"\nglobs = ["Tests.GoCoreAdmissionFixture", "Tests.GoCoreAdmission", "Tests.GoCoreAdmissionAudit"]\n'),
    ("scripts/ci", 'step "admission checker proofs and post-import audit"\nif bash scripts/check-admission --lean-only; then\n  ok "admission checker proofs and post-import audit"\nelse\n  bad "admission checker proofs and post-import audit"\nfi\n\n')]:
    original = subprocess.check_output(["git", "show", f"{MAIN}:{path}"], cwd=ROOT, text=True)
    current = (ROOT/path).read_text()
    assert current.count(insertion) == 1 and current.replace(insertion, "") == original
    print(path + ": all landed-main content preserved plus the exact A3 addition")
print("Integration binding and rebase checks PASS")
