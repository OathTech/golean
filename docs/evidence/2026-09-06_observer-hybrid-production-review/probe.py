"""Independent native/capture/copy probes of the frozen production helper."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUTHOR = ROOT.parent / "typed-observer-classification"
EVIDENCE = AUTHOR / "docs/evidence/2026-09-06_observer-classification"


def main():
    manifest = json.loads((EVIDENCE / "hybrid-production-sources.json").read_text())
    for name, digest in manifest.items():
        assert hashlib.sha256((AUTHOR / name).read_bytes()).hexdigest() == digest, name
    sourcefiles = sorted((AUTHOR / "tools/coverageharness").glob("*.go"))
    sourcehashes = {str(p.relative_to(AUTHOR)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sourcefiles}
    (HERE / "candidate-sources.json").write_text(json.dumps(manifest, indent=2)+"\n")
    (HERE / "complete-helper-sources.json").write_text(json.dumps(sourcehashes, indent=2)+"\n")
    with tarfile.open(HERE / "helper-source.tar.gz", "w:gz") as archive:
        for p in sourcefiles:
            archive.add(p, arcname=str(p.relative_to(AUTHOR)))
    scratch = Path(tempfile.mkdtemp(prefix="observer-production-review-", dir=os.environ.get("TMPDIR")))
    package = scratch / "helper"
    package.mkdir()
    for p in sourcefiles:
        shutil.copyfile(p, package / p.name)
    env = dict(os.environ, GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0", GOTRACEBACK="system",
               GOCACHE=str(ROOT / "artifacts/go-build-cache"))
    helper = scratch / "coverageharness"
    build = subprocess.run(["go", "build", "-o", str(helper), "."], cwd=package, env=env, capture_output=True)
    (HERE / "build.log").write_bytes(build.stdout + build.stderr)
    assert build.returncode == 0
    old = json.loads((HERE.parent / "2026-09-06_observer-hybrid-review/results.json").read_text())
    setup_start = '\n _goleanCrash, _goleanCrashErr :='
    setup_end = '0600) != nil { _golean_os.Exit(78) }\n'
    rows = []
    def run(argv, cwd):
        p = subprocess.run([str(helper), *argv], cwd=cwd, env=env, capture_output=True, timeout=45)
        return dict(argv=argv, rc=p.returncode, stdout_hex=p.stdout.hex(), stderr_hex=p.stderr.hex())
    for item in old["rows"]:
        name = item["name"]
        source = item["source"].replace('import(_golean_os "os";_golean_debug "runtime/debug")\n', '')
        a = source.index(setup_start)
        b = source.index(setup_end, a)+len(setup_end)
        source = source[:a]+source[b:]
        inputdir = scratch / (name+"-source")
        inputdir.mkdir()
        original = source.encode()
        (inputdir / "main.go").write_bytes(original)
        oracle = scratch / (name+"-oracle")
        copied = run(["--copy-oracle", str(inputdir), "--out", str(oracle)], scratch)
        assert copied["rc"] == 0, copied
        assert (inputdir / "main.go").read_bytes() == original
        instrumented = (oracle / "main.go").read_bytes()
        assert instrumented.count(b"\n_goleanSetupCrash();") == 1
        assert instrumented.replace(b"\n_goleanSetupCrash();", b"", 1) == original
        (oracle / "oracle.crash").write_bytes(b"")
        (oracle / "oracle.registered").write_bytes(b"")
        native = subprocess.run(item["argv"], cwd=oracle, env=env, capture_output=True, timeout=45)
        (oracle / "stdout").write_bytes(native.stdout)
        (oracle / "stderr").write_bytes(native.stderr)
        assert native.returncode == 1 and native.stdout == b"" and native.stderr.endswith(b"\nexit status 2\n")
        report, ack = oracle / "oracle.crash", oracle / "oracle.registered"
        paired = ["--crash-report", str(report), "--crash-registered", str(ack)]
        kind = run(["--abort-status", str(oracle / "stderr"), *paired], oracle)
        message = run(["--abort-message", str(oracle / "stderr"), "--expected-status", "panic", *paired], oracle)
        output = run(["--split-stderr", str(oracle / "stderr"), "--expected-status", "panic", *paired], oracle)
        record = dict(name=name, source=source, native_argv=item["argv"], native_rc=native.returncode,
                      stdout_hex=native.stdout.hex(), stderr_hex=native.stderr.hex(), crash_hex=report.read_bytes().hex(),
                      ack_hex=ack.read_bytes().hex(), kind=kind, message=message, output=output,
                      original_preserved=True, oracle_edit_exact=True)
        if "observation" in item:
            expected = item["observation"]
            assert kind["rc"] == message["rc"] == output["rc"] == 0, record
            assert bytes.fromhex(kind["stdout_hex"]) == b"panic"
            assert json.loads(bytes.fromhex(message["stdout_hex"])) == expected["message"]
            assert json.loads(bytes.fromhex(output["stdout_hex"])) == expected["output"]
        elif name == "invalid-utf8":
            assert message["rc"] == 3 and b"UTF-8" in bytes.fromhex(message["stderr_hex"]), record
        else:
            assert kind["rc"] == message["rc"] == output["rc"] == 3, record
        rows.append(record)
        print(name, "PASS", flush=True)
    oracle = scratch / "minimal-print-oracle"
    stderr, report, ack = oracle / "stderr", oracle / "oracle.crash", oracle / "oracle.registered"
    valid_report, valid_ack = report.read_bytes(), ack.read_bytes()
    controls = []
    for label, reportbytes, ackbytes, args in [
        ("unpaired", valid_report, valid_ack, ["--crash-report", str(report)]),
        ("missing-file", valid_report, valid_ack, ["--crash-report", str(report)+"missing", "--crash-registered", str(ack)]),
        ("unacknowledged", valid_report, b"", None),
        ("malformed-ack", valid_report, b"registered\nextra", None),
        ("changed-suffix", valid_report+b"X", valid_ack, None),
        ("changed-content", valid_report.replace(b"actual", b"wrong", 1), valid_ack, None),
    ]:
        report.write_bytes(reportbytes)
        ack.write_bytes(ackbytes)
        argv = args if args is not None else ["--crash-report", str(report), "--crash-registered", str(ack)]
        got = run(["--abort-status", str(stderr), *argv], oracle)
        assert got["rc"] == 3 and got["stdout_hex"] == "", got
        controls.append(dict(name=label, result=got))
        print(label, "PASS", flush=True)
    # A genuine success reports exact bytes only with a registered empty channel.
    success = oracle / "success.stderr"
    success.write_bytes(b"\x00\x01\r\nprint output\n")
    paired = ["--crash-report", str(report), "--crash-registered", str(ack)]
    for label, reportbytes, ackbytes, expected_rc in [
        ("success-exact", b"", valid_ack, 0),
        ("success-missing-ack", b"", b"", 3),
        ("success-stale-report", valid_report, valid_ack, 3),
    ]:
        report.write_bytes(reportbytes)
        ack.write_bytes(ackbytes)
        got = run(["--split-stderr", str(success), "--expected-status", "ok", *paired], oracle)
        assert got["rc"] == expected_rc, got
        if expected_rc == 0:
            assert json.loads(bytes.fromhex(got["stdout_hex"])) == success.read_bytes().decode()
        controls.append(dict(name=label, result=got))
        print(label, "PASS", flush=True)
    # CLI protocol refusal rather than a stale observation on reused oracle copy.
    reused = run(["--copy-oracle", str(scratch / "minimal-print-source"), "--out", str(oracle)], scratch)
    assert reused["rc"] != 0 and b"fresh" in bytes.fromhex(reused["stderr_hex"])
    controls.append(dict(name="reused-oracle-copy", result=reused))
    for name, digest in manifest.items():
        assert hashlib.sha256((AUTHOR / name).read_bytes()).hexdigest() == digest, name
    (HERE / "results.json").write_text(json.dumps(dict(scope="bounded implementation review; no full differential claim",
        go_version=subprocess.check_output(["go", "version"], text=True).strip(), scratch=str(scratch), rows=rows, controls=controls), indent=2)+"\n")


if __name__ == "__main__":
    main()
