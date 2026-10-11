# Lane fix/setup-deps-urls-1011 — gate records (2026-10-11)

[AGENT] recovery worker. Trigger: on milner-oath's fresh clone, `scripts/setup-deps --only
covmap,grossmith` failed closed («has no public URL and --from did not provide it»); [USER]
Mike 2026-10-11, verbatim: «wrong, both of these are publicly available». The table rows now
carry `https://github.com/OathTech/{covmap,grossmith}.git`; pins unchanged.

- The changed table exercised in the lane worktree (no network from the sandbox, so via
  `--from /home/dev/projects/golean`): default set EXIT=0; `--only covmap,grossmith` EXIT=0
  (both rows parse; the local source takes precedence). The URL path itself can only be
  exercised on a box with GitHub access: milner-oath, after this lands.
- `capped -m 64G -- scripts/ci --diff`, cold worktree (the named raise), threads 8, 1667 s:
  **RESULT: FAIL on exactly the 5a pair** — `certificate provenance` STALE («changed dependency
  files/scripts/setup-deps»: the script is a certified input) and its echo
  `imported-goose/channel/google-search` PASS/membership → FAIL/membership; 3936 cases run, no
  other drift; negative 394, no regression; every other step ok; reconciler 1 HIGH = that
  stale certificate + the 3 standing MEDIUM. Tail: `ci-diff-cold-64G.tail.txt`.

Merge expectation (protocol 5a): release-check STALE on `scripts/setup-deps`; `ci --slow`; the
candidate's `schema`/`claim`/`observations_sha256` identical with only that input hash and the
receipt moved; install; re-gate green.

## Second gate — the lane with all three fixes (2026-10-11, later)

The lane grew two more fixes from the milner-oath trial ([USER] «Fix the issue, land fixes
on main»): the gate never pages or opens an editor (`scripts/ci` exports `GIT_PAGER=cat
PAGER=cat GIT_EDITOR=:`; `check-equations` uses `git --no-pager grep`), and the certificate
no longer binds the Python version (inputs schema v2; the version in the receipt; a 3.11
floor by name; [USER] «Why do we need to couple on this exact python version? The repo is
supposed to be rebuildable by people with a reasonable setup»). The certifier's unit tests:
69 controls PASS after `scripts/build-certified` (a first run before the rebuild refused by
name: STALE executable build). The lane's first gate run (above) was stopped mid-way when
the list of issues was still open ([USER] «You probably shouldn't rerun the gate if we
haven't pinned down all the issues?»); this is the run that counts.

`capped scripts/ci --diff`, warm, box default (32 G, threads 4), 891 s
(`ci-diff-warm-32G-all-fixes.tail.txt`): **RESULT: FAIL on exactly the 5a pair** —
`certificate provenance` with the NEW named cause «certification inputs schema
'golean-certification-inputs-v1' is not the current 'golean-certification-inputs-v2': the
input inventory changed; re-certify», and its echo `imported-goose/channel/google-search`
PASS/membership → FAIL/membership; 3936 cases run, no other drift; negative 394, no
regression; every other step ok, incl. semantic equations (the pager site) and the
certification controls (69). The merge's 5a run mints the v2 record.
