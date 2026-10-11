# Train capped-1011 — the capped-alignment lane landed (2026-10-11)

[AGENT] recovery worker as train worker. Authority: [USER] Mike 2026-10-11 «(2) approved»
(the lane) and «go ahead as proposed» (the merge, with the audit as posed: the open
points named in the ask — fallback body tested only by patching the box tool's path away,
the cold-build note is a note not a refusal, two leaked empty `capped-*` cgroups left).

- Pre-merge `main` `6a5a4083` = `refs/snapshots/capped-1011/main`; `fix/capped-alignment-1011`
  @ `890d1933` fast-forwarded (2 commits: the alignment + its lane records).
- 5a at the merged tip: `capped scripts/build-certified` (box default, through the shim) —
  «Certified build: compiled inputs match; sha256=5f093779…» (the binary is unchanged: no
  Lean source moved); `release-check --base refs/snapshots/capped-1011/main` EXIT=2 «STALE
  certification: changed dependency files/scripts/capped» (expected).
- `capped scripts/ci --slow` (box default 32 G, LEAN_NUM_THREADS=4): EXIT=1, 1035 s,
  **RESULT: FAIL on exactly the 5a pair** — `certificate provenance` STALE and its echo
  `imported-goose/channel/google-search` PASS/membership → FAIL/membership; 3936 cases run,
  no other drift; negative 394, no regression; every other step ok (tail `ci-slow.tail.txt`).
- Candidate (`artifacts/coverage/membership/imported-goose/channel/google-search/certification-candidate.json`)
  vs the tracked record: `schema`, `claim`, `observations_sha256` IDENTICAL; `inputs` differ
  ONLY in `files` `scripts/capped`, `scripts/ci`, `scripts/grossmith-run`,
  `tools/admission-check.py` (the lane's four edits); the receipt moved (`8b53af43` →
  `890d1933`, 148.7 s). INSTALLED as `baselines/certified/imported-goose__channel__google-search.certified.json`
  — a provenance refresh, not a re-pin; the certified set is unchanged. `check-records` PASS;
  with it installed `release-check` EXIT=1 «Recertification required since pre-merge tip:
  inputs: changed dependency files/scripts/capped» — the protocol's trigger for this very
  run, recorded (as at r75).
- The re-gate (`capped scripts/ci --diff`) at the 5a tip is recorded by the close commit.
