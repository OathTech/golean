# Project review probes — whole-project audit (2026-09-11)

[AGENT] Compact evidence for the [whole-project review](../../2026-09-11_project-review.md).
These inputs and observations were collected during the read-only investigation,
before the documentation landing. Publication adds no runtime changes, baseline
updates, permanent regression cases, or fixes.

The source snapshot was clean main at
`bf721a4c28864a9c23c33dba5b9c1cc934bd24e7`.
The tools were `go version go1.26.5 linux/amd64` and
`leanprover/lean4:v4.32.2`. The frontend was built fresh. Machine probes used
the existing `.lake/build/bin/golean`; its current source/build provenance
passed `python3 tools/certification.py check-records`, with certification
inputs SHA-256
`2fd17f08bbb8b9438a0e99ae1a1a8ea85118cf057fb4c46de5f98bd6cd54e9d7`.
This was not a fresh complete differential campaign or slow enumeration.

The host was the audit's Linux/amd64 development environment. Box class and
concurrent load were not recorded for the timing probe; no controlled-machine
performance claim is made. Times are single-run wall times including process
startup and JSON decoding, with the wire already generated.

**Records and conclusions.**

- [probe-inputs.json](probe-inputs.json) preserves the small source files in
  eleven probe directories, including hidden and platform-specific filenames.
  It is a path-to-text record, not a copy of a source tree or generated wire.
- [probe-results.json](probe-results.json) is the captured eight-case initial
  result array: Go return code and combined text output, frontend return code
  and combined text output, and interpreter return code and JSON observation.
- The filename cases all returned 1 under Go and 2 under GoLean, with successful
  frontend export and no warning. This is an accepted-program mismatch.
- `new_expression` and `discard_call` returned 42 on both sides.
  `anonymous_struct`, `complex`, and `range_func` ran under Go but reached
  explicit frontend-quarantined refusals under GoLean.
- Later module probes returned Go/GoLean 9/3 for `module1.21`, and 3/3 for
  `module1.26`, using the same compiler and identical Go source. Only the
  go.mod directive differs.
- Two mutations of the generated discarded-call wire were accepted and returned
  42: removing its one `resultTypes` vector and prefixing a conflicting duplicate
  `schema` property. The missing-vector example demonstrates unvalidated
  reconstruction of type metadata, not a wrong computed value in that example.
- The append loop returned correct lengths at 100, 500, 1,000 and 2,000 appends
  in 0.0262, 0.1500, 0.7625 and 4.4939 seconds. The 4,000-append subprocess
  exceeded 30 seconds. The timeout is a lower bound, not a completed runtime.

The module, mutation and timing results above are transcribed from the audit's
tool outputs; they are not fields in the eight-case captured JSON. Generated
wires, compiled binaries and Go caches remain scratch artifacts. The reproduction
below regenerates those inputs, without relying on the original scratch path.

**Reproduction.** From a checkout with the audited source and its built GoLean
executable, run the block below from the repository root. It builds a frontend,
recreates the input directories from the record, and captures fresh results in a
unique permitted scratch directory. Use the pinned toolchains. A run on a newer
source revision may differ because the findings have been fixed; it is new
evidence, not a reproduction at the original snapshot. The commands below are
the portable equivalent of the audit invocations; this README was prepared at
publication and is not a literal shell transcript.

```sh
review_run=$(mktemp -d "${TMPDIR:-$PWD/.tmp}/golean-review.XXXXXX")
scripts/capped python3 - "$review_run" <<'PY'
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path.cwd()
scratch = Path(sys.argv[1]).resolve()
evidence = root / "docs/evidence/2026-09-11_project-review"
inputs = json.loads((evidence / "probe-inputs.json").read_text())
for name, files in inputs.items():
    case = scratch / name
    case.mkdir()
    for filename, text in files.items():
        (case / filename).write_text(text)

env = os.environ.copy()
env.update(GO111MODULE="off", GOCACHE=str(scratch / "go-cache"),
           TMPDIR=str(scratch))

def call(args, cwd=root, module=False, timeout=120):
    current = dict(env, GO111MODULE="on" if module else "off")
    result = subprocess.run([str(a) for a in args], cwd=cwd, env=current,
                            capture_output=True, text=True, timeout=timeout)
    return result.returncode, (result.stdout + result.stderr).strip()

frontend = scratch / "nativefrontend"
code, detail = call(["go", "build", "-o", frontend, "./tools/nativefrontend"])
assert code == 0, detail
interpreter = root / ".lake/build/bin/golean"

def lower(name):
    case = scratch / name
    return call([frontend, "--dir", case, "--out", case / "program.json"])

def machine(wire, *extra):
    return call([interpreter, "native-json-run", "--input", wire,
                 "--function", "probe", "--fuel", "100000", *extra])

initial_names = [
    "filename_windows", "filename_ignored", "filename_hidden",
    "new_expression", "anonymous_struct", "complex", "range_func",
    "discard_call",
]
initial_results = []
for name in initial_names:
    go_code, go_text = call(["go", "run", "."], cwd=scratch / name)
    fe_code, fe_text = lower(name)
    assert fe_code == 0, (name, fe_text)
    lean_code, lean_text = machine(scratch / name / "program.json")
    initial_results.append(dict(
        probe=name, go_exit=go_code, go=go_text,
        frontend_exit=fe_code, frontend=fe_text,
        lean_exit=lean_code, lean=lean_text))
(scratch / "probe-results.json").write_text(
    json.dumps(initial_results, indent=2) + "\n")

later = {}
for name in ["module1.21", "module1.26"]:
    go_result = call(["go", "run", "."], cwd=scratch / name, module=True)
    fe_result = lower(name)
    assert fe_result[0] == 0, (name, fe_result)
    later[name] = dict(go=go_result, frontend=fe_result,
                      lean=machine(scratch / name / "program.json"))

base = json.loads((scratch / "discard_call/program.json").read_text())
missing = json.loads(json.dumps(base))
removed = []
def remove_result_types(value):
    if isinstance(value, dict):
        if "resultTypes" in value:
            removed.append(value.pop("resultTypes"))
        for child in value.values():
            remove_result_types(child)
    elif isinstance(value, list):
        for child in value:
            remove_result_types(child)
remove_result_types(missing)
assert len(removed) == 1, ("wire changed", removed)
absent = scratch / "absent_result_types.json"
absent.write_text(json.dumps(missing))
duplicate = scratch / "duplicate_schema.json"
duplicate.write_text('{"schema":"forged-schema",' + json.dumps(base)[1:])
later["absent_result_types"] = machine(absent)
later["duplicate_schema"] = machine(duplicate)
later["removed_result_types"] = removed

code, detail = lower("append_benchmark")
assert code == 0, detail
times = []
for n in [100, 500, 1000, 2000, 4000]:
    started = time.monotonic()
    try:
        result = call([
            interpreter, "native-json-run", "--input",
            scratch / "append_benchmark/program.json", "--function",
            "probe", "--arg-int", str(n)], timeout=30)
        times.append(dict(n=n, seconds=time.monotonic()-started,
                          exit=result[0], observation=result[1]))
    except subprocess.TimeoutExpired:
        times.append(dict(n=n, timeout_seconds=30))
later["append_benchmark"] = times
(scratch / "later-probe-results.json").write_text(
    json.dumps(later, indent=2) + "\n")
print(scratch)
print(json.dumps(later, indent=2))
PY
```

The enclosing `scripts/capped` contains the build and all child executions.
The filename Go invocations use module mode off; the module-version Go
invocations turn it on. The frontend itself selects its fixed language version.
The mutation probes exercise the production byte parser, before the duplicate
key can be lost in a parsed object. The benchmark deliberately uses the CLI's
default fuel, as in the original measurement.

For an initial result comparison, compare the freshly produced
`probe-results.json` with the tracked record. Compare parsed observations as
well as status codes; formatting-only differences are not semantic changes.
Do not install freshly generated results as baselines merely because they
differ. The consuming review states the interpretation and limitations of
each finding.
