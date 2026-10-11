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
