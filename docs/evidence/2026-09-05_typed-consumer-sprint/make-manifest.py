#!/usr/bin/env python3
"""Generate the MANIFEST for the typed-consumer sprint's evidence payload
(the files that did NOT land on main; the bytes stay on the archive branch).

[USER] ruling (Mike, 2026-09-07, relayed by the [AGENT] coordinator — cite as
relayed): «The evidence blob should not land, and generally we should not dump
big evidence bundles on main (they can't be easily hosted on GH for one)».
AGENTS.md "Evidence on main": main keeps the directory's README plus a
MANIFEST (sha256, bytes, origin commit, path — one row per file left on the
branch). This script reads git OBJECTS only (`git ls-tree`, `git cat-file`,
`git log`); it never checks the payload out into the working tree.

Usage (from the repo root):
  python3 docs/evidence/2026-09-05_typed-consumer-sprint/make-manifest.py \
      --tip 7edc298f257519652646b7a59bca959671d33063 \
      --base 471956831251e428df3a64c5b8fc7fb79cbebbfc \
      --main <main SHA used for source-copy detection> \
      --out docs/evidence/2026-09-05_typed-consumer-sprint

Outputs (all TSV, `#`-prefixed header comments, tab-separated rows):
  MANIFEST.tsv              one row per top-level evidence dir on the archive
                            branch: files, bytes, per-class counts, the
                            per-dir manifest file
  manifest/<dir>.tsv        one row per file: path, sha256, bytes,
                            origin_commit (the archive-branch commit that
                            introduced the path: `git log --diff-filter=A
                            --no-renames --topo-order --reverse
                            --diff-merges=first-parent`, oldest first), class
  source-copies.tsv         path, copy_of, tree — every evidence blob that is
                            byte-identical (git blob id) to a NON-evidence
                            tracked blob in the tip tree or in main's tree

Classes (assigned in this precedence order; the README states the rules):
  archive      archive extension (.tar .tgz .gz .zip .xz .zst .7z)
  source-copy  blob-identical to a tracked non-evidence file (tip or main)
  gate-tail    .log .exit .stderr .stdout
  review       .md (incl. .md.before): prose reviews, FINAL/README records,
               whole-file copies of docs/BUGS.md / the ledgers
  capture      .json .jsonl .tsv (incl. .tsv.before) .sha256 .sha256sums,
               SHA256SUMS: result tables, manifests, hash inventories
  probe        .go .lean .py .toml .patch .diff .body .replacement,
               `.go.txt`/`.lean.txt` drafts, extension-less scripts
               (ci, capped, check-*, coverage-*, diff-coverage,
               lean-toolchain, test-lane-validation): new probe/fixture/
               candidate sources that are NOT byte-identical copies
  witness      .txt transcripts/readbacks (version lines, commands, probes)
  other        anything else
"""
import argparse
import collections
import hashlib
import os
import subprocess
import sys

EVIDENCE = "docs/evidence/"
ARCHIVE_EXTS = (".tar", ".tgz", ".gz", ".zip", ".xz", ".zst", ".7z")
EMPTY_BLOB = "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
CLASSES = ("gate-tail", "witness", "probe", "source-copy", "archive", "capture", "review", "other")
GATE_EXTS = (".log", ".exit", ".stderr", ".stdout")
CAPTURE_EXTS = (".json", ".jsonl", ".tsv", ".sha256", ".sha256sums")
PROBE_EXTS = (".go", ".lean", ".py", ".toml", ".patch", ".diff", ".body", ".replacement")
PROBE_NOEXT = {"ci", "capped", "diff-coverage", "lean-toolchain", "test-lane-validation",
               "coverage-manifest", "coverage-baseline-diff", "check-declarations", "check-interface"}


def git(*args, binary=False, check=True):
    out = subprocess.run(["git", *args], capture_output=True, check=check)
    return out.stdout if binary else out.stdout.decode()


def ls_tree(ref, path=None):
    """{path: (mode, blob, size)} for every blob under path (or the whole tree)."""
    args = ["ls-tree", "-r", "-l", "-z", ref]
    if path:
        args += ["--", path]
    raw = git(*args, binary=True)
    out = {}
    for rec in raw.split(b"\0"):
        if not rec:
            continue
        meta, p = rec.split(b"\t", 1)
        mode, typ, blob, size = meta.decode().split()
        if typ != "blob":
            continue
        out[p.decode("utf-8", errors="surrogateescape")] = (mode, blob, int(size))
    return out


def classify(path, is_copy):
    base = os.path.basename(path)
    lower = base.lower()
    if any(lower.endswith(e) for e in ARCHIVE_EXTS):
        return "archive"
    if is_copy:
        return "source-copy"
    stem = lower
    inner = None
    for wrap in (".before", ".txt"):
        if stem.endswith(wrap) and "." in stem[: -len(wrap)]:
            inner = os.path.splitext(stem[: -len(wrap)])[1]
            break
    ext = os.path.splitext(stem)[1]
    if ext in GATE_EXTS:
        return "gate-tail"
    if ext == ".md" or inner == ".md":
        return "review"
    if ext in CAPTURE_EXTS or inner in CAPTURE_EXTS or base == "SHA256SUMS":
        return "capture"
    if ext in PROBE_EXTS or inner in PROBE_EXTS or (ext == "" and base in PROBE_NOEXT):
        return "probe"
    if ext == ".txt":
        return "witness"
    return "other"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--tip", required=True, help="archive-branch tip (full SHA)")
    ap.add_argument("--base", required=True, help="merge-base with main at the time of the sprint (full SHA)")
    ap.add_argument("--main", required=True, help="main SHA whose non-evidence tree is used for source-copy detection")
    ap.add_argument("--out", required=True, help="output directory (this evidence dir)")
    a = ap.parse_args()
    tip_full = git("rev-parse", a.tip).strip()
    base_full = git("rev-parse", a.base).strip()
    main_full = git("rev-parse", a.main).strip()

    # 1. the payload: every docs/evidence path that differs between base and tip
    changed = [p for p in git("diff", "--name-only", "-z", base_full, tip_full, "--", "docs/evidence",
                              binary=True).decode("utf-8", errors="surrogateescape").split("\0") if p]
    tip_tree = ls_tree(tip_full)
    payload = sorted(p for p in changed if p in tip_tree)  # deleted-at-tip paths would not be "left on the branch"
    if len(payload) != len(changed):
        print(f"note: {len(changed) - len(payload)} changed path(s) absent at the tip (deleted on the branch)",
              file=sys.stderr)

    # 2. non-evidence blobs at the tip and on main (source-copy detection)
    outside = {}
    for label, tree in (("tip", tip_tree), ("main", ls_tree(main_full))):
        for p, (mode, blob, size) in tree.items():
            if not p.startswith(EVIDENCE) and mode in ("100644", "100755") and blob != EMPTY_BLOB:
                outside.setdefault(blob, (p, label))

    # 3. origin commits: oldest add per path on base..tip, renames not followed
    # --topo-order + --reverse: parents before children, so a file added on a
    # side branch is attributed to that commit, not to the merge that brought it
    # in; --diff-merges=first-parent also attributes files that the integrator
    # ADDED IN the merge commit itself (evidence written at integration time)
    log = git("log", "--topo-order", "--reverse", "--no-renames", "--diff-filter=A", "--name-only", "-z",
              "--diff-merges=first-parent", "--format=%x01%H", f"{base_full}..{tip_full}", "--", "docs/evidence",
              binary=True)
    origin = {}
    cur = None
    for rec in log.decode("utf-8", errors="surrogateescape").split("\0"):
        for piece in rec.split("\n"):
            if not piece:
                continue
            if piece.startswith("\x01"):
                cur = piece[1:]
            elif cur and piece not in origin:
                origin[piece] = cur
    missing = [p for p in payload if p not in origin]
    if missing:
        print(f"error: {len(missing)} payload path(s) have no add commit on {base_full[:8]}..{tip_full[:8]}, "
              f"e.g. {missing[0]}", file=sys.stderr)
        sys.exit(1)

    # 4. sha256 of every payload blob, streamed from the object store
    blobs = sorted({tip_tree[p][1] for p in payload})
    proc = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    proc.stdin.write(("\n".join(blobs) + "\n").encode())
    proc.stdin.close()
    sha256 = {}
    for blob in blobs:
        header = proc.stdout.readline().decode().split()
        if len(header) != 3 or header[0] != blob or header[1] != "blob":
            print(f"error: unexpected cat-file header {header!r} for {blob}", file=sys.stderr)
            sys.exit(1)
        size = int(header[2])
        data = proc.stdout.read(size)
        proc.stdout.read(1)  # trailing LF
        if len(data) != size:
            print(f"error: short read for blob {blob}", file=sys.stderr)
            sys.exit(1)
        sha256[blob] = hashlib.sha256(data).hexdigest()
    proc.wait()

    # 5. rows, per top-level dir
    rows_by_dir = collections.defaultdict(list)
    copies = []
    for p in payload:
        mode, blob, size = tip_tree[p]
        is_copy = blob != EMPTY_BLOB and blob in outside
        cls = classify(p, is_copy)
        if cls == "source-copy":
            copies.append((p, outside[blob][0], outside[blob][1]))
        rel = p[len(EVIDENCE):]
        top = rel.split("/", 1)[0] if "/" in rel else "(root)"
        rows_by_dir[top].append((p, sha256[blob], size, origin[p], cls))

    os.makedirs(os.path.join(a.out, "manifest"), exist_ok=True)
    cmd = (f"python3 {os.path.relpath(__file__)} --tip {tip_full} --base {base_full} --main {main_full} "
           f"--out {a.out}")
    hdr = [f"# generated by: {cmd}",
           f"# archive branch tip {tip_full}; base (merge-base with main) {base_full}; "
           f"source-copy detection against the non-evidence trees of the tip and of main {main_full}",
           "# the bytes are NOT on main; `git show <tip>:<path>` (or `git cat-file -p`) on the archive branch yields them"]
    totals = collections.Counter()
    total_bytes = collections.Counter()
    index_rows = []
    for top in sorted(rows_by_dir):
        rows = rows_by_dir[top]
        fn = os.path.join("manifest", f"{top}.tsv")
        with open(os.path.join(a.out, fn), "w", encoding="utf-8") as f:
            f.write("\n".join(hdr) + "\n")
            f.write("# columns: path\tsha256\tbytes\torigin_commit\tclass\n")
            for p, h, size, oc, cls in rows:
                f.write(f"{p}\t{h}\t{size}\t{oc}\t{cls}\n")
        counts = collections.Counter(cls for *_r, cls in rows)
        nbytes = sum(size for _p, _h, size, _oc, _cls in rows)
        for cls in CLASSES:
            totals[cls] += counts[cls]
        for _p, _h, size, _oc, cls in rows:
            total_bytes[cls] += size
        index_rows.append((top, len(rows), nbytes, [counts[c] for c in CLASSES], fn))
    with open(os.path.join(a.out, "MANIFEST.tsv"), "w", encoding="utf-8") as f:
        f.write("\n".join(hdr) + "\n")
        f.write("# one row per top-level docs/evidence/<dir>/ left on the archive branch; the per-file rows are in manifest/<dir>.tsv\n")
        f.write("# columns: dir\tfiles\tbytes\t" + "\t".join(CLASSES) + "\tmanifest_file\n")
        for top, n, nbytes, counts, fn in index_rows:
            f.write(f"{EVIDENCE}{top}/\t{n}\t{nbytes}\t" + "\t".join(str(c) for c in counts) + f"\t{fn}\n")
        f.write(f"# TOTAL\t{sum(r[1] for r in index_rows)}\t{sum(r[2] for r in index_rows)}\t"
                + "\t".join(str(totals[c]) for c in CLASSES) + "\t-\n")
    with open(os.path.join(a.out, "source-copies.tsv"), "w", encoding="utf-8") as f:
        f.write("\n".join(hdr) + "\n")
        f.write("# every payload file whose git blob is byte-identical to a tracked NON-evidence blob; "
                "tree = which tree holds the original (tip = the archive tip, main = the main SHA above)\n")
        f.write("# columns: path\tcopy_of\ttree\n")
        for p, of, tree in copies:
            f.write(f"{p}\t{of}\t{tree}\n")
    # summary to stdout (the README quotes it)
    print(f"payload: {len(payload)} files / {sum(r[2] for r in index_rows)} bytes in {len(index_rows)} dirs; "
          f"tip {tip_full[:8]} base {base_full[:8]} main {main_full[:8]}")
    print("class\tfiles\tbytes")
    for c in CLASSES:
        print(f"{c}\t{totals[c]}\t{total_bytes[c]}")
    print(f"source copies: {len(copies)} (tip-tree originals {sum(1 for c in copies if c[2]=='tip')}, "
          f"main-only originals {sum(1 for c in copies if c[2]=='main')})")
    largest = max(((os.path.getsize(os.path.join(a.out, fn)), fn) for *_r, fn in index_rows))
    print(f"largest per-dir manifest: {largest[1]} {largest[0]} bytes; index {os.path.getsize(os.path.join(a.out, 'MANIFEST.tsv'))} bytes")


if __name__ == "__main__":
    main()
