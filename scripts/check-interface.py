"""Post-import audit and compiled mutation checks; run via check-interface."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MODULES = ["GoLean/GoCore/Machine", "GoLean/GoCore/Trace", "GoLean/GoCore/PoolTrace",
           "GoLean/GoCore/PanicText", "GoLean/GoCore/StringPanic", "Tests/StringPanicMembers",
           "GoLean/GoCore/ProgramTrace", "GoLean/Interface",
           "GoLean/GoCore/AdmissionIndices", "GoLean/GoCore/AdmissionPolicy",
           "GoLean/GoCore/Admission",
           "GoLean/GoCore/BooleanTyping", "GoLean/GoCore/BooleanStore",
           "GoLean/GoCore/BooleanSetup",
           "GoLean/GoCore/BooleanInitialization",
           "GoLean/GoCore/BooleanControlTyping", "GoLean/GoCore/BooleanControl",
           "GoLean/GoCore/BooleanInvariant", "GoLean/GoCore/BooleanPreservation",
           "GoLean/GoCore/BooleanProgress", "GoLean/GoCore/BooleanSafety",
           "GoLean/GoCore/BooleanProgram", "GoLean/GoCore/BooleanPool",
           "GoLean/GoCore/RecoveryTypingCore", "GoLean/GoCore/RecoveryExpressions",
           "GoLean/GoCore/RecoveryCalls", "GoLean/GoCore/RecoveryStatements",
           "GoLean/GoCore/RecoveryGraph", "GoLean/GoCore/RecoveryDiagnostics",
           "GoLean/GoCore/RecoveryAdmission",
           "Tests/RecoveryTyping", "Tests/RecoveryDiagnosticControls",
           "Tests/RecoveryTypingFixture", "Tests/RecoveryA2Artifact", "Tests/RecoveryTypingAudit",
           "GoLean/GoCore/RecoveryStore", "GoLean/GoCore/RecoveryEnvironment",
           "GoLean/GoCore/RecoveryAllocation", "GoLean/GoCore/RecoveryOperators",
           "GoLean/GoCore/RecoveryContext", "GoLean/GoCore/RecoveryControlTyping",
           "GoLean/GoCore/RecoverySetupShape", "GoLean/GoCore/RecoveryInitialization",
           "GoLean/GoCore/RecoveryResultRoots", "GoLean/GoCore/RecoverySetup",
           "GoLean/GoCore/RecoverySetupWf", "GoLean/GoCore/RecoverySetupReadout",
           "GoLean/GoCore/RecoveryCallEntry",
           "Tests/RecoveryStorage", "Tests/RecoveryStorageAudit",
           "Tests/RecoverySetup", "Tests/RecoverySetupAudit",
           "GoLean/GoCore/RecoveryDelivery", "GoLean/GoCore/RecoveryControlData",
           "GoLean/GoCore/RecoveryControl", "GoLean/GoCore/RecoveryControlMono",
           "GoLean/GoCore/RecoveryWalk", "GoLean/GoCore/RecoveryExpressionProgress",
           "GoLean/GoCore/RecoveryControlHelpers", "GoLean/GoCore/RecoveryCallControl",
           "GoLean/GoCore/RecoveryValueBasic", "GoLean/GoCore/RecoveryValueCalls",
           "GoLean/GoCore/RecoveryStatementProgress", "GoLean/GoCore/RecoveryFrameProgress",
           "GoLean/GoCore/RecoveryPanicProgress", "GoLean/GoCore/RecoveryInvariant",
           "GoLean/GoCore/RecoverySuccessfulRuns",
           "GoLean/GoCore/RecoveryCallLayout", "GoLean/GoCore/RecoverySingleton",
           "GoLean/GoCore/RecoveryPool", "GoLean/GoCore/RecoveryChoices",
           "GoLean/GoCore/RecoveryTerminal", "GoLean/GoCore/RecoveryPoolObservationTyped",
           "Tests/RecoveryTerminal", "Tests/RecoveryTerminalAudit",
           "Tests/RecoveryInvariant", "Tests/RecoveryControlAudit",
           "Tests/PanicRendering", "Tests/InterfaceContract", "Tests/BooleanRuntime",
           "Tests/BooleanProgram", "Tests/InterfaceAudit"]
HARNESS = "\n".join(f"import {m.replace('/', '.')}" for m in MODULES)
HARNESS += "\n#eval InterfaceAudit.run\n"


def main():
    paths = sorted([*ROOT.glob("GoLean/**/*.lean"), ROOT / "GoLean.lean",
                    ROOT / "Tests/PanicRendering.lean",
                    ROOT / "Tests/StringPanicMembers.lean",
                    ROOT / "Tests/InterfaceContract.lean", ROOT / "Tests/InterfaceAudit.lean",
                    ROOT / "Tests/BooleanRuntime.lean", ROOT / "Tests/BooleanTypingFixture.lean",
                    ROOT / "Tests/BooleanProgram.lean",
                    ROOT / "Tests/RecoveryTyping.lean", ROOT / "Tests/RecoveryDiagnosticControls.lean",
                    ROOT / "Tests/RecoveryTypingFixture.lean", ROOT / "Tests/RecoveryA2Artifact.lean",
                    ROOT / "Tests/RecoveryTypingAudit.lean",
                    ROOT / "Tests/RecoveryStorage.lean", ROOT / "Tests/RecoveryStorageAudit.lean",
                    ROOT / "Tests/RecoverySetup.lean", ROOT / "Tests/RecoverySetupAudit.lean",
                    ROOT / "Tests/RecoveryInvariant.lean", ROOT / "Tests/RecoveryControlAudit.lean",
                    ROOT / "Tests/RecoveryTerminal.lean", ROOT / "Tests/RecoveryTerminalAudit.lean",
                    ROOT / "lakefile.toml", ROOT / "lean-toolchain",
                    ROOT / "scripts/ci", ROOT / "scripts/capped",
                    ROOT / "scripts/check-interface", Path(__file__).resolve()])
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    print("Semantic interface source fingerprint:", digest.hexdigest(), flush=True)
    scratch_root = ROOT / ".tmp"
    scratch_root.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="interface-audit-", dir=scratch_root))

    def lean(path, fixture=None, output=None):
        env = os.environ.copy()
        if fixture is not None:
            env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
        args = [str(ROOT / "scripts/capped"), "lean", f"--root={fixture or scratch}"]
        if output is not None:
            args += ["-o", str(output)]
        result = subprocess.run(args + [str(path)], cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        print(result.stdout, end="", flush=True)
        return result

    harness = scratch / "AuditAll.lean"
    harness.write_text(HARNESS)
    result = lean(harness)
    if result.returncode:
        raise SystemExit(result.returncode)
    for label, target, declaration, marker in [
        ("abort_observation_private", "GoLean/GoCore/AbortObservation.lean",
         "private axiom abortObservationHole : False", "abortObservationHole"),
        ("pool_observation_private", "GoLean/GoCore/RecoveryPoolObservation.lean",
         "private axiom poolObservationHole : False", "poolObservationHole"),
        ("program_observation_private", "GoLean/GoCore/RecoveryProgramObservation.lean",
         "private axiom programObservationHole : False", "programObservationHole"),
        ("panic_text_private", "GoLean/GoCore/PanicText.lean",
         "private axiom panicTextHole : False", "panicTextHole"),
        ("string_panic_private", "GoLean/GoCore/StringPanic.lean",
         "private axiom stringPanicHole : False", "stringPanicHole"),
        ("string_panic_trailing", "Tests/StringPanicMembers.lean",
         "private theorem stringPanicTestHole : False := by sorry", "sorryAx"),
        ("machine_private", "GoLean/GoCore/Machine.lean",
         "private axiom machineRendererHole : False", "machineRendererHole"),
        ("rendering_trailing", "Tests/PanicRendering.lean",
         "private theorem rendererHole : False := by sorry", "sorryAx"),
        ("promoted_private", "GoLean/GoCore/Trace.lean",
         "private axiom promotedTraceHole : False", "promotedTraceHole"),
        ("boolean_store_private", "GoLean/GoCore/BooleanStore.lean",
         "private axiom booleanStoreHole : False", "booleanStoreHole"),
        ("boolean_setup_private", "GoLean/GoCore/BooleanSetup.lean",
         "private axiom booleanSetupHole : False", "booleanSetupHole"),
        ("boolean_initialization_private", "GoLean/GoCore/BooleanInitialization.lean",
         "private axiom booleanInitializationHole : False", "booleanInitializationHole"),
        ("boolean_program_private", "GoLean/GoCore/BooleanProgram.lean",
         "private axiom booleanProgramHole : False", "booleanProgramHole"),
        ("boolean_pool_private", "GoLean/GoCore/BooleanPool.lean",
         "private axiom booleanPoolHole : False", "booleanPoolHole"),
        ("boolean_program_test_trailing", "Tests/BooleanProgram.lean",
         "private theorem booleanProgramTestHole : False := by sorry", "sorryAx"),
        ("recovery_diagnostics_private", "GoLean/GoCore/RecoveryDiagnostics.lean",
         "private axiom recoveryDiagnosticsHole : False", "recoveryDiagnosticsHole"),
        ("recovery_admission_private", "GoLean/GoCore/RecoveryAdmission.lean",
         "private axiom recoveryAdmissionHole : False", "recoveryAdmissionHole"),
        ("recovery_test_trailing", "Tests/RecoveryTyping.lean",
         "private theorem recoveryTestHole : False := by sorry", "sorryAx"),
        ("recovery_store_private", "GoLean/GoCore/RecoveryStore.lean",
         "private axiom recoveryStoreHole : False", "recoveryStoreHole"),
        ("recovery_setup_private", "GoLean/GoCore/RecoverySetupWf.lean",
         "private axiom recoverySetupHole : False", "recoverySetupHole"),
        ("recovery_call_private", "GoLean/GoCore/RecoveryCallEntry.lean",
         "private axiom recoveryCallHole : False", "recoveryCallHole"),
        ("recovery_setup_test_trailing", "Tests/RecoverySetup.lean",
         "private theorem recoverySetupTestHole : False := by sorry", "sorryAx"),
        ("recovery_control_private", "GoLean/GoCore/RecoveryControl.lean",
         "private axiom recoveryControlInterfaceHole : False", "recoveryControlInterfaceHole"),
        ("recovery_invariant_private", "GoLean/GoCore/RecoveryInvariant.lean",
         "private axiom recoveryInvariantInterfaceHole : False", "recoveryInvariantInterfaceHole"),
        ("recovery_control_test_trailing", "Tests/RecoveryInvariant.lean",
         "private theorem recoveryControlTestHole : False := by sorry", "sorryAx"),
        ("recovery_layout_private", "GoLean/GoCore/RecoveryCallLayout.lean",
         "private axiom recoveryLayoutInterfaceHole : False", "recoveryLayoutInterfaceHole"),
        ("recovery_singleton_private", "GoLean/GoCore/RecoverySingleton.lean",
         "private axiom recoverySingletonInterfaceHole : False", "recoverySingletonInterfaceHole"),
        ("recovery_pool_private", "GoLean/GoCore/RecoveryPool.lean",
         "private axiom recoveryPoolInterfaceHole : False", "recoveryPoolInterfaceHole"),
        ("recovery_choices_private", "GoLean/GoCore/RecoveryChoices.lean",
         "private axiom recoveryChoicesInterfaceHole : False", "recoveryChoicesInterfaceHole"),
        ("recovery_terminal_private", "GoLean/GoCore/RecoveryTerminal.lean",
         "private axiom recoveryTerminalInterfaceHole : False", "recoveryTerminalInterfaceHole"),
        ("recovery_observer_typed_private", "GoLean/GoCore/RecoveryPoolObservationTyped.lean",
         "private axiom recoveryObserverTypedInterfaceHole : False", "recoveryObserverTypedInterfaceHole"),
        ("recovery_terminal_test_trailing", "Tests/RecoveryTerminal.lean",
         "private theorem recoveryTerminalTestHole : False := by sorry", "sorryAx"),
        ("facade_private", "GoLean/Interface.lean",
         "private axiom facadeHole : False", "facadeHole"),
        ("audit_trailing", "Tests/InterfaceAudit.lean",
         "private theorem auditHole : False := by sorry", "sorryAx"),
        ("runtime_test_trailing", "Tests/BooleanRuntime.lean",
         "private theorem booleanRuntimeTestHole : False := by sorry", "sorryAx"),
    ]:
        fixture = scratch / label
        for tree in ["GoLean", "Tests"]:
            shutil.copytree(ROOT / ".lake/build/lib/lean" / tree, fixture / tree)
        source = fixture / target
        source.write_text((ROOT / target).read_text() + "\n" + declaration + "\n")
        if lean(source, fixture, source.with_suffix(".olean")).returncode:
            raise SystemExit(f"Semantic interface: {label} failed to compile; not audit rejection")
        external = fixture / "AuditAll.lean"
        external.write_text(HARNESS)
        result = lean(external, fixture)
        if result.returncode != 1 or "forbidden axiom" not in result.stdout or marker not in result.stdout:
            raise SystemExit(f"Semantic interface: expected named audit rejection for {label}")
        print(f"Semantic interface negative: {label} rejected (exit 1, {marker})", flush=True)
    print(f"Semantic interface: PASS; scratch retained at {scratch}", flush=True)


if __name__ == "__main__":
    main()
