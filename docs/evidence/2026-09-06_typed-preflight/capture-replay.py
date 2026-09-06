#!/usr/bin/env python3
"""Capture a bounded before/after oracle from an already completed full run.

This is evidence tooling, not a conformance gate or semantic definition.
It retains full stdout/stderr bytes, explicit CLI arguments/exit statuses,
choice reports and every labeled consumption. It never edits the harness,
model, corpus, baselines or previously captured per-case files.
"""
import argparse
import concurrent.futures
import csv
import hashlib
import json
import subprocess
from pathlib import Path

FIXED = ["default", "9,8,7,6,5,4,3,2,1,0", "1,3,5,7,9,2,4,6,8,0", "5,5,5,5,5,5,5,5"]


def seeded(seed, length):
    out = []
    for _ in range(length):
        seed = (seed * 1103515245 + 12345) & 0x7fffffff
        out.append(str((seed >> 16) & 0xffff))
    return ",".join(out)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=240)
    args = parser.parse_args()
    root = args.root.resolve()
    coverage = args.coverage.resolve()
    output = args.out.resolve()
    if args.jobs < 1 or args.timeout < 1:
        parser.error("jobs and timeout must be positive")
    output.mkdir(parents=True, exist_ok=False)
    manifest = args.manifest.read_bytes()
    (output / "manifest.tsv").write_bytes(manifest)
    rows = list(csv.reader(manifest.decode().splitlines(), delimiter="\t"))
    rows = [r for r in rows if r and not r[0].startswith("#")]
    if any(len(r) != 10 for r in rows):
        raise SystemExit("manifest must have ten columns on every non-comment row")
    if len({r[0] for r in rows}) != len(rows):
        raise SystemExit("manifest contains duplicate case ids")
    with (coverage / "latest.tsv").open() as file:
        results = {r["id"]: r for r in csv.DictReader(file, delimiter="\t")}
    if set(results) != {r[0] for r in rows}:
        raise SystemExit("manifest and completed coverage result ids disagree")
    binary = root / ".lake/build/bin/golean"
    provenance = {
        "root": str(root), "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "binary_sha256": sha(binary), "manifest_sha256": sha(args.manifest),
        "capture_script_sha256": sha(Path(__file__)),
        "coverage_results_sha256": sha(coverage / "latest.tsv"),
        "coverage_meta_sha256": sha(coverage / "latest.meta.tsv"),
        "jobs": args.jobs, "timeout_seconds_per_invocation": args.timeout,
        "fuel_policy": "10,000,000 except explicit membership nonterm=N rows use N",
        "stream_policy": "default and three fixed CI streams; strict depth=N adds the same three seeded CI streams",
        "scope": "bounded captured paths only; full conformance result preserved separately; no all-choices proof",
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")

    def capture(item):
        index, row = item
        cid, go_dir, fn, ints, expected, features, reason, lane, why, params = row
        directory = output / f"{index:06d}"
        directory.mkdir()
        base = {"id": cid, "manifest_row": row, "coverage_result": results[cid], "commands": []}
        wire = coverage / "native" / cid / "wire.json"
        if not wire.is_file():
            unexpected = results[cid]["result"] == "PASS"
            base["capture_status"] = "INCOMPLETE" if unexpected else "NO_WIRE"
            base["incomplete_commands"] = int(unexpected)
            (directory / "case.json").write_text(json.dumps(base, indent=2) + "\n")
            return index, cid, base["capture_status"], int(unexpected)
        base["wire_sha256"] = sha(wire)
        (directory / "wire.json").write_bytes(wire.read_bytes())
        # The manifest grammar separates lane parameters by comma.
        parameters = dict(piece.split("=", 1) for piece in params.split(",") if "=" in piece)
        fuel = int(parameters.get("nonterm", "10000000"))
        streams = list(FIXED)
        if lane == "strict" and "depth" in parameters:
            streams += [seeded(s, int(parameters["depth"])) for s in (1, 2, 3)]
        base["fuel"] = fuel
        base["fuel_exception"] = "nonterm" in parameters
        base["streams"] = streams
        integer_args = [] if ints == "-" else [arg for n in ints.split(",") for arg in ("--arg-int", n)]
        incomplete = 0

        def run(command, name):
            nonlocal incomplete
            timed_out = False
            with (directory / f"{name}.stdout").open("wb") as out, (directory / f"{name}.stderr").open("wb") as err:
                try:
                    completed = subprocess.run(command, cwd=root, stdout=out, stderr=err, timeout=args.timeout)
                    rc = completed.returncode
                except subprocess.TimeoutExpired:
                    rc = None
                    timed_out = True
            # Exit 1 is a model error observation for native-json-run; trace
            # batch itself may return 0 while explicitly recording ERROR rows.
            base["commands"].append({"name": name, "argv": command, "exit": rc, "timeout": timed_out})
            if timed_out or rc not in (0, 1):
                incomplete += 1

        for n, stream in enumerate(streams):
            command = [str(binary), "native-json-run", "--input", str(wire), "--function", fn,
                       "--fuel", str(fuel), *integer_args]
            if stream != "default":
                command += ["--choices", stream]
            run(command, f"observation-{n}")
        batch = directory / "trace-batch.tsv"
        batch.write_text("\t".join([cid, str(wire), fn, ints, ";".join(streams)]) + "\n")
        run([str(binary), "choice-trace", "--batch", str(batch), "--out", str(directory / "trace.tsv"),
             "--dump", str(directory / "consumptions.tsv"), "--fuel", str(fuel)], "trace")
        trace_errors = []
        if (directory / "trace.tsv").is_file():
            with (directory / "trace.tsv").open() as file:
                trace_rows = list(csv.DictReader(file, delimiter="\t"))
            for trace in trace_rows:
                if trace["status"] == "ERROR" or trace["violations"] != "0" or trace["alarms"] != "0" or trace["driverAgreement"] != "ok":
                    trace_errors.append(trace)
            if len(trace_rows) != len(streams) and not trace_errors:
                incomplete += 1
        else:
            incomplete += 1
        base["trace_findings"] = trace_errors
        base["capture_status"] = "INCOMPLETE" if incomplete else "RECORDED_WITH_FINDINGS" if trace_errors else "RECORDED"
        base["incomplete_commands"] = incomplete
        base["files_sha256"] = {p.name: sha(p) for p in directory.iterdir() if p.is_file()}
        (directory / "case.json").write_text(json.dumps(base, indent=2) + "\n")
        return index, cid, base["capture_status"], incomplete

    with (output / "index.tsv").open("w") as index_file:
        writer = csv.writer(index_file, delimiter="\t", lineterminator="\n")
        writer.writerow(["directory", "id", "capture_status", "incomplete_commands"])
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(capture, item): item[1][0] for item in enumerate(rows)}
            for count, future in enumerate(concurrent.futures.as_completed(futures), 1):
                index, cid, status, incomplete = future.result()
                writer.writerow([f"{index:06d}", cid, status, incomplete])
                index_file.flush()
                if count % 100 == 0 or status == "INCOMPLETE":
                    print(f"captured {count}/{len(rows)}: {cid} {status}", flush=True)
    print(f"Capture finished; review per-case statuses in {output / 'index.tsv'}", flush=True)


if __name__ == "__main__":
    main()
