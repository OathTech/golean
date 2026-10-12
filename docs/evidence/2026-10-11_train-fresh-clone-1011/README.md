# Train fresh-clone-1011 — the three fresh-clone fixes landed (2026-10-11/12)

[AGENT] recovery worker as train worker. Authority: [USER] Mike 2026-10-11 «Fix the issue,
land fixes on main. Then let me know when you're ready for me to push», «Can you fix this so
that anyone who downloads the repo gets a reasonable experience?», «We're actually trying
to build software people will use».

- Lane `fix/setup-deps-urls-1011` @ `7b70a597` (5 commits): the dependency table's public
  URLs for covmap and grossmith; the gate never pages or opens an editor; the certificate no
  longer binds the Python version (inputs schema v2, the version in the receipt, a 3.11
  floor by name); README «Getting started on a fresh clone». Lane records:
  `docs/evidence/2026-10-11_setup-deps-urls/`.
- Pre-merge `main` `27559ce5` = `refs/snapshots/fresh-clone-1011/main`; fast-forwarded to `7b70a597`.
- 5a at the merged tip: `capped scripts/build-certified` — «compiled inputs match;
  sha256=e74942a5…» (the binary moved: `tools/certification.py` is a compiled build input,
  embedded by `compiledBuildInputs%`); `release-check` EXIT=2 with the new named cause
  «certification inputs schema 'golean-certification-inputs-v1' is not the current
  'golean-certification-inputs-v2': the input inventory changed; re-certify».
- `capped scripts/ci --slow` (box default 32 G, threads 4): EXIT=1, 1034 s, **RESULT: FAIL on
  exactly the 5a pair** (provenance as above; `imported-goose/channel/google-search`
  PASS/membership → FAIL/membership); 3936 cases run, no other drift; negative 394, no
  regression; every other step ok (tail `ci-slow.tail.txt`).
- Candidate vs tracked record: `schema`, `claim`, `observations_sha256` IDENTICAL; `inputs`:
  schema v1 → v2, the `python` key gone, `files` differ in exactly the lane's five edits
  (`scripts/check-equations`, `scripts/ci`, `scripts/setup-deps`, `tools/certification.py`,
  `tools/test_certification.py`), `build/files` in `tools/certification.py`; receipt: `python`
  3.12.3 recorded (provenance), binary `5f093779…` → `e74942a5…`, source `890d1933` →
  `7b70a597`, 146.9 s. INSTALLED — the first v2 record; a provenance refresh, the certified
  set unchanged. `check-records` PASS; `release-check` EXIT=1 «Recertification required since
  pre-merge tip» — the trigger for this run, recorded.
- On milner-oath (Python 3.14.4) this record is FRESH after `git pull`: nothing machine-
  specific is bound any more; `python3 tools/certification.py check-records` there is the test.

## Close — the re-gate STOPPED by the [USER] (2026-10-12), corrected record

`capped scripts/ci --diff` at the 5a tip `6ee2c0a6` was stopped by the [USER] (Mike,
2026-10-12, verbatim: «is this still running? This is insane» … «no you can kill it and then
land whatever commit you have pending, I'll fix this on the new machine»). The first version
of this section, written from the step counter at the moment of the kill, said the negative
corpus and the baseline diffs had not run; the log says otherwise, and this is the corrected
record (tail `ci-diff.STOPPED.tail.txt`): at the stop, 861 s in, every deciding step had
reported — `certificate provenance` ok (the installed v2 record FRESH at this tip), the full
native differential corpus 3936 run, negative corpus 394 run, **negative baseline diff: no
regression; differential baseline diff: no regression (3936/3936)** — and the kill landed in
the REPORT-ONLY cross-ledger reconciliation, before the summary block. So no `RESULT: PASS`
line was printed, and `main` @ `6ee2c0a6` carries that: every deciding check green, the
stamp absent. The [USER]'s ruling is that the gate's cost is the defect (plan §7, the restart
priority: the gate cull).
