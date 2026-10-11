# Train records-1011 — the records landing after the 2026-10-08 crash (2026-10-11)

[AGENT] recovery worker. Authority: [USER] Mike 2026-10-11, «(1) approved» on the
merge ask for `land/records-1011` (the audit ask posed in-session; the [USER]'s
approval covered it — records only, 13 commits, 18 files, 0 outside `docs/`).

- Pre-merge `main`: `4e3aeb3d` = `refs/snapshots/records-1011/main`; merged tip `a34a52c6`
  (`git merge --ff-only land/records-1011`).
- Step 5a at the merged tip: `scripts/build-certified` — «Certified build: compiled inputs
  match; sha256=5f093779…»; `tools/certification.py release-check --base
  refs/snapshots/records-1011/main` — «No certification inputs/claims changed since
  pre-merge tip 4e3aeb3d», EXIT=0.
- Fast gate at the merged tip: `GOLEAN_MEM_MAX=32G CAPPED_MEM_MAX=32G capped scripts/ci`
  (the box-wide `capped`, the box default 32 G forced through the then-unaligned project
  wrapper too — [USER] D2 the same day; warm primary build, LEAN_NUM_THREADS=4):
  **RESULT: PASS**, 520 s wall, EXIT=0; tail in `ci.tail.txt`.
- Records checks on the landing branch before the merge: check-evidence-size, check-agents-alias,
  check-bugs all EXIT=0.
