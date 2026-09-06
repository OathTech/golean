#!/usr/bin/env python3
"""Execute a fresh, finite, source-bound R-1 certificate; never replay a verdict."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile

from string_member import (
    ABORT_ROLES, ENVELOPE, ROLES, Refusal, byte_array, check_actual_member,
    check_source_binding, keys, observation, raw_panic, read_json, require,
    sha, validate_pin, relative,
)

ROOT = Path(__file__).resolve().parents[1]
FUEL = 10_000_000
# Keep the existing strict lane's three fixed adversarial tapes exactly.
# The typed theorem is generic in the stream; these are also concrete
# regression probes for the broader historical artifact.
STREAMS = ([], [9, 8, 7, 6, 5, 4, 3, 2, 1, 0], [1, 3, 5, 7, 9, 2, 4, 6, 8, 0], [5, 5, 5, 5, 5, 5, 5, 5])


class Run:
    def __init__(self, output, golean, harness, go_timeout, lean_timeout):
        output.mkdir(parents=True, exist_ok=True)
        self.directory = Path(tempfile.mkdtemp(prefix="fresh-", dir=output))
        self.golean, self.harness = str(golean.resolve()), str(harness.resolve())
        self.go_timeout, self.lean_timeout = go_timeout, lean_timeout
        self.commands = []
        self.records = {}
        self.env = os.environ.copy()
        self.env.update(GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0", GOTRACEBACK="system",
                        GOCACHE=str(ROOT / "artifacts/go-build-cache"))
        self.binary_hashes = {"golean": sha(self.golean), "harness": sha(self.harness)}

    def execute(self, label, command, timeout, cwd=ROOT, env=None):
        directory = self.directory / label
        directory.mkdir(parents=True, exist_ok=False)
        stdout, stderr = directory / "stdout", directory / "stderr"
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(command, cwd=cwd, env=env or self.env, stdout=out,
                                    stderr=err, start_new_session=True)
            try:
                code = proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                code = 124
        record = {"label": label, "command": list(map(str, command)), "cwd": str(cwd),
                  "exit": code, "stdout": str(stdout.relative_to(self.directory)),
                  "stderr": str(stderr.relative_to(self.directory)),
                  "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr)}
        self.commands.append(record)
        self.save()
        return code, stdout, stderr

    def save(self):
        (self.directory / "commands.json").write_text(json.dumps(self.commands, indent=2) + "\n")

    def require_exit(self, code, expected, label, stderr):
        require(code == expected, f"{label}: exit {code}, expected {expected}; no verdict: {stderr.read_bytes()!r}")

    def emit(self, label, source):
        wire = self.directory / (label + "-wire.json")
        code, _, err = self.execute(label + "-frontend", ["go", "run", "./tools/nativefrontend",
                                  "--dir", source, "--out", str(wire)], self.go_timeout)
        self.require_exit(code, 0, label + " frontend", err)
        require(wire.is_file(), label + ": successful frontend did not create wire")
        return wire

    def compare(self, label, left, right):
        code, _, err = self.execute(label, [self.golean, "observation-eq", "--left",
                                  json.dumps(left, ensure_ascii=True), "--right",
                                  json.dumps(right, ensure_ascii=True)], self.lean_timeout)
        self.require_exit(code, 0, label + " exact observation comparison", err)

    def model(self, label, wire, function, args, status, choices=(), witness=False, typed=False):
        command = [self.golean, "native-json-string-run" if witness else "native-json-run",
                   "--input", str(wire), "--function", function, "--fuel", str(FUEL)]
        for arg in args:
            command += ["--arg-int", str(arg["value"])]
        if choices:
            command += ["--choices", ",".join(map(str, choices))]
        if typed:
            require(witness, "typed admission requires the actual witness API")
            command += ["--require-recovery-profile"]
        code, out, err = self.execute(label, command, self.lean_timeout)
        self.require_exit(code, 1 if status == "panic" else 0, label, err)
        record = read_json(out)
        if not witness:
            observation(record, status)
            return record, None
        keys(record, ("schema", "observation", "chain", "admitted", "fuel", "choices"), "actual driver record")
        require(record["schema"] == "golean-string-abort-witness-v1", "actual driver record: wrong schema")
        require(type(record["admitted"]) is bool and (not typed or record["admitted"]), "actual driver did not admit typed subject")
        require(type(record["fuel"]) is int and record["fuel"] == FUEL and record["choices"] == list(choices),
                "actual driver record: fuel/choices differ from execution")
        require(type(record["choices"]) is list and all(type(v) is int and v >= 0 for v in record["choices"]),
                "actual driver record: malformed choices")
        observation(record["observation"], status)
        return record["observation"], record["chain"]

    def go(self, label, source, function, args, status, race=False):
        oracle = self.directory / (label + "-oracle")
        arg_text = ",".join(str(a["value"]) for a in args) or "-"
        code, _, err = self.execute(label + "-harness", [self.harness, "--input", str(ROOT / source / "main.go"),
                                  "--out", str(oracle), "--subject", function, "--args", arg_text,
                                  "--expected-status", status], self.go_timeout)
        self.require_exit(code, 0, label + " harness", err)
        crash, ack = oracle / "oracle.crash", oracle / "oracle.registered"
        crash.write_bytes(b"")
        ack.write_bytes(b"")
        env = self.env.copy()
        if (oracle / "gopath").is_dir():
            env["GOPATH"] = str(oracle / "gopath")
        code, out, err = self.execute(label + "-go", ["go", "run"] + (["-race"] if race else []) + ["."],
                                      self.go_timeout, cwd=oracle, env=env)
        self.require_exit(code, 1 if status == "panic" else 0, label + " Go", err)
        # Valid captures cannot turn a killed draw or hook setup failure
        # into a terminal verdict. Keep stdout entirely separate from fd2.
        require(not err.read_bytes().endswith(b"exit status 78\n"), "oracle crash-hook setup failure")
        shared = ["--crash-report", str(crash), "--crash-registered", str(ack)]
        if status == "panic":
            require(out.read_bytes() == b"", "aborting wrapper produced unexpected stdout; no authenticated subject observation")
            code, observed, cause = self.execute(label + "-observe", [self.harness, "--abort-record", str(err)] + shared, self.go_timeout)
            self.require_exit(code, 0, label + " raw panic observation", cause)
            result = read_json(observed)
            raw_panic(result)
        else:
            code, observed, cause = self.execute(label + "-observe", [self.harness, "--read-observation", str(out)], self.go_timeout)
            self.require_exit(code, 0, label + " normal observation", cause)
            result = read_json(observed)
            require(type(result) is dict and "output" not in result, "Go wrapper unexpectedly supplied output field")
            code, output, cause = self.execute(label + "-output", [self.harness, "--split-stderr", str(err), "--expected-status", "ok"] + shared, self.go_timeout)
            self.require_exit(code, 0, label + " exact output observation", cause)
            result["output"] = read_json(output)
            observation(result, "ok")
        self.records[label] = {"observation": result, "crash_sha256": sha(crash), "registration_sha256": sha(ack),
                               "crash": str(crash.relative_to(self.directory)), "registration": str(ack.relative_to(self.directory))}
        return result


def run_case(cfg):
    relative(cfg.case, "case id")
    relative(cfg.go_dir, "subject source directory")
    args = [] if cfg.args == "-" else [{"tag": "int", "value": int(x)} for x in cfg.args.split(",")]
    pin_path = ROOT / "baselines/string-members" / (cfg.case + ".json")
    pin = read_json(pin_path)
    validate_pin(pin, cfg.case, cfg.function, args)
    run = Run(Path(cfg.out), Path(cfg.golean), Path(cfg.harness), cfg.go_timeout, cfg.lean_timeout)
    print(f"string-member evidence: {run.directory}", flush=True)
    try:
        wire = run.emit("subject", cfg.go_dir)
        control_source = pin["binding"]["control_package"]
        control_wire = run.emit("controls", control_source)
        code, version, err = run.execute("go-version", ["go", "env", "GOVERSION"], cfg.go_timeout)
        run.require_exit(code, 0, "Go toolchain query", err)
        go_version = version.read_text().strip()
        require(go_version == (ROOT / "baselines/go-oracle-pin").read_text().strip(), "live Go differs from pinned oracle")
        check_source_binding(ROOT, pin, cfg.go_dir, wire, control_wire, go_version, ROOT / "baselines/go-oracle-pin")
        # Finite matrix: abort controls use the same fixed member check;
        # they do not recurse into run_case or waive their exact companions.
        checked_controls = {}
        for role in ROLES:
            control = pin["controls"][role]
            expected = control["expectation"]
            status = "panic" if role in ABORT_ROLES else "ok"
            go = run.go("control-" + role, control_source, control["function"], control["arguments"], status)
            machine, chain = run.model("model-control-" + role, control_wire, control["function"], control["arguments"], status,
                                       witness=status == "panic")
            run.compare("pin-control-" + role, machine, expected["machine"])
            if status == "panic":
                check_actual_member(machine, go, chain)
                require({k: go[k] for k in ("status", "childExit", "outputBytes")} == expected["go"],
                        f"control {role}: Go forced fields changed")
            else:
                run.compare("exact-control-" + role, go, machine)
            checked_controls[role] = {"go": go, "machine": machine, "actual_chain": chain}
        require(set(checked_controls) == set(ROLES), "a mandatory control was not executed")
        subject_go = [run.go("subject-plain", cfg.go_dir, cfg.function, args, "panic"),
                      run.go("subject-race", cfg.go_dir, cfg.function, args, "panic", race=True)]
        subjects = []
        for i, choices in enumerate(STREAMS):
            machine, chain = run.model(f"subject-model-{i}", wire, cfg.function, args, "panic", choices,
                                       witness=True, typed=pin["scope"] == "typed-explicit-string")
            run.compare(f"subject-pin-{i}", machine, pin["machine"])
            for go in subject_go:
                check_actual_member(machine, go, chain)
            subjects.append({"choices": choices, "machine": machine, "actual_chain": chain})
        # Recheck all immutable inputs after execution, before issuing any
        # result. A source change during a run invalidates its certificate.
        check_source_binding(ROOT, pin, cfg.go_dir, wire, control_wire, go_version, ROOT / "baselines/go-oracle-pin")
        require(run.binary_hashes == {"golean": sha(run.golean), "harness": sha(run.harness)}, "executable changed during certificate run")
        require(read_json(pin_path) == pin, "member pin changed during run")
        certificate = {"schema": "golean-string-member-certificate-v1", "envelope": ENVELOPE,
                       "case": cfg.case, "scope": pin["scope"], "pin_sha256": sha(pin_path),
                       "bindings": pin["binding"], "binaries": run.binary_hashes, "controls": checked_controls,
                       "subject_go": subject_go, "subject_models": subjects, "go_records": run.records,
                       "commands": run.commands}
        (run.directory / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
        print(f"PASS string-member: {ENVELOPE}; exact forced fields and {pin['scope']} evidence; gc text equality is not claimed")
    except Exception as exc:
        (run.directory / "refusal.txt").write_text(str(exc) + "\n")
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("case", "go-dir", "function", "args", "out", "golean", "harness"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--go-timeout", type=int, default=60)
    parser.add_argument("--lean-timeout", type=int, default=60)
    cfg = parser.parse_args()
    try:
        require(cfg.go_timeout > 0 and cfg.lean_timeout > 0, "timeouts must be positive")
        run_case(cfg)
    except (Refusal, OSError, ValueError) as exc:
        print(f"string-member refusal: {exc}", flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
