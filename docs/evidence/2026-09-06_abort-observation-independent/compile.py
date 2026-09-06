import json
from pathlib import Path
import subprocess

here = Path(__file__).resolve().parent
root = here.parents[2]
for path in json.loads((here / "modules.json").read_text()):
    source = root / path
    target = root / ".lake/build/lib/lean" / Path(path).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run(["lean", "-o", str(target), str(source)], cwd=root,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       timeout=180)
    (here / (source.stem + ".log")).write_text(p.stdout)
    print(path, "exit", p.returncode, flush=True)
    if p.returncode:
        print(p.stdout, flush=True)
        raise SystemExit(p.returncode)
