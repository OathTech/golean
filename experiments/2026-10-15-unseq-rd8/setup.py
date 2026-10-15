#!/usr/bin/env python3
"""Materialize immutable RD8 inputs and independent dependencies in this lane."""
import argparse
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

PIN = "eba7d3bdaa7786cfc6daad949cd3217185e2c867"
PACKAGE = "experiments/2026-10-14_relational-codex"


def git(source, *args):
    return subprocess.check_output(["git", "-C", str(source), *args],
        env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logic-source", type=Path, required=True)
    parser.add_argument("--seeds", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    lane = here.parent.parent
    dest = lane / ".tmp/rd8"
    if not dest.exists():
        dest.mkdir(parents=True)
        data = git(args.logic_source, "archive", PIN, PACKAGE)
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for entry in archive.getmembers():
                if entry.isdir():
                    continue
                relative = Path(entry.name).relative_to(PACKAGE)
                if entry.issym() or entry.islnk() or ".." in relative.parts:
                    raise SystemExit(f"Unsupported archive entry: {entry.name}")
                target = dest / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.extractfile(entry).read())
        (dest / "lake-manifest.json").unlink(missing_ok=True)
    pins = json.loads((dest / "pins.json").read_text())
    for name, rev in pins.items():
        if name == "GoLean":
            continue  # This lane supplies the candidate; never build a peer.
        source = args.seeds / name
        target = dest / ".lake/packages" / name
        if not target.exists():
            if git(source, "status", "--porcelain").strip():
                raise SystemExit(f"Dirty seed: {source}")
            changes = git(source, "diff", "--name-only", rev, "HEAD").decode().splitlines()
            if any(not p.startswith("docs/") or not p.endswith(".md") for p in changes):
                raise SystemExit(f"Seed code/configuration differs: {source}")
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "clone", "--no-hardlinks", "--no-checkout",
                str(source), str(target)], check=True)
            subprocess.run(["git", "-C", str(target), "checkout", "--detach", rev], check=True)
            cache = Path("Iris/.lake/build" if name == "iris" else ".lake/build")
            if not (source / cache).is_dir():
                raise SystemExit(f"Missing explicit seed cache: {source / cache}")
            shutil.copytree(source / cache, target / cache, symlinks=False)
        if target.is_symlink() or git(target, "rev-parse", "HEAD").decode().strip() != rev:
            raise SystemExit(f"Wrong dependency: {target}")
        if (target / ".git/objects/info/alternates").exists():
            raise SystemExit(f"Shared object database: {target}")
    # Preserve every frozen Lean source; only generated package wiring differs.
    config = (dest / "lakefile.toml").read_text().replace('path = ".golean-ws"', 'path = "../.."')
    if 'name = "U1RD8"' not in config:
        config += '\n[[lean_lib]]\nname = "U1RD8"\nglobs = ["U1RD8.+"]\n'
    (dest / "lakefile.toml").write_text(config)
    shutil.copytree(here / "U1RD8", dest / "U1RD8", dirs_exist_ok=True)
    for name in ["UnseqFrozen", "UnseqRequests", "UnseqOperations", "UnseqLifting"]:
        path = f"RelationalCodeX/{name}.lean"
        if (dest / path).read_bytes() != git(args.logic_source, "show", f"{PIN}:{PACKAGE}/{path}"):
            raise SystemExit(f"Frozen input changed: {path}")
    print(f"RD8 {PIN}: frozen inputs verified; private build root {dest}")


if __name__ == "__main__":
    main()
