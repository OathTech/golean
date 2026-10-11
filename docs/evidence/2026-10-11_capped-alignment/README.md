# Lane fix/capped-alignment-1011 — gate records (2026-10-11)

[AGENT] capped-alignment worker. Authority: [USER] Mike 2026-10-11 «(2) approved»
(the alignment lane), on the rulings «the global capped script is the correct one
to use, here and on the new box», «D2: conform to the box default, of course raising
it is allowed during execution when needed», «D5: keep the last run only».

Two gate runs in the lane worktree (`.claude/worktrees/capped-alignment-1011`,
`deps/` populated with `scripts/setup-deps --from` the primary), both under the
box-wide `capped` through the new shim, the box-wide build lock held:

1. **Fast gate, COLD tree, the named raise** — `capped -m 64G -- scripts/ci`
   (`ci-fast-cold-64G.tail.txt`): LEAN_NUM_THREADS=8 from the effective cap; 1168 s;
   **RESULT: FAIL** on (a) `certificate provenance` — STALE, «changed dependency
   files/scripts/capped» (the shim is a certified build input: the expected 5a pair,
   fixed only by the train's step 5a) and (b) the negative/differential baseline
   diffs — «NO recorded run» (a fresh worktree has none). Every other step ok. D5
   observed: `Admission scratch kept as the last passing run: …/.tmp/admission-audit-last`
   and the lane's `.tmp/` holds exactly one `admission-audit-last`.
2. **`scripts/ci --diff`, WARM tree, the box default** — `capped scripts/ci --diff`
   (`ci-diff-warm-32G.tail.txt`): cap 32G → LEAN_NUM_THREADS=4; 915 s;
   **RESULT: FAIL on exactly the 5a pair**: `certificate provenance` STALE as above, and
   the differential baseline diff's one DRIFT row `imported-goose/channel/google-search`
   `baseline[PASS/membership] -> now[FAIL/membership]` (the certified row reads its own
   stale certificate). 3936 cases run, no other drift; negative corpus 394 run, no
   regression; reconciler: the one HIGH = that stale certificate, the 3 standing MEDIUM.

The hand exercise of the shim (default 32 G verified; a legacy `GOLEAN_MEM_MAX=256M`
honoured and OOM-killed with the banner, exit 137; exit 42 propagates; the opt-out warns;
`-m 1G` passes through; a nested call does not re-wrap; the fallback body with the box
tool's path patched away verifies at 32 G and exports both token names) is in the lane's
first commit message. Rebased onto `main` @ 6a5a4083 (the records-train close, docs only)
after the runs; the gate inputs are unchanged by that rebase.

Merge expectation (protocol 5a): release-check at the merged tip will report STALE on
`scripts/capped`; the train runs `scripts/ci --slow`, installs the reviewed candidate for
`imported-goose/channel/google-search`, commits it as the 5a records commit, re-runs the
gate green. A changed certified SET would be a finding; an unchanged set with only the
input hash and receipt moved is the expected provenance refresh.
