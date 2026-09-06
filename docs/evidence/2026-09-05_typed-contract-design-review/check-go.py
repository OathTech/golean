"""Capture raw first panic lines; this is a direct Go probe, not a diff gate."""
import json
import os
from pathlib import Path
import subprocess

directory = Path(__file__).resolve().parent
env = os.environ.copy()
env.update(GOCACHE=str(Path.cwd() / "artifacts/go-build-cache"), GO111MODULE="off")
rows = []
for name in ("unicode", "newline", "invalid-utf8", "repanic", "newline-repanic"):
    result = subprocess.run(
        ["go", "run", str(directory / f"{name}.go")],
        env=env, capture_output=True, timeout=60,
    )
    first = result.stderr.split(b"\n", 1)[0]
    assert result.returncode != 0 and first.startswith(b"panic: "), (name, result)
    rows.append({"name": name, "exit": result.returncode,
                 "first_line_hex": first.hex(),
                 "first_line_utf8": first.decode("utf-8", errors="backslashreplace")})
print(json.dumps(rows, ensure_ascii=True, indent=2))
