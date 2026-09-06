# Renderer and Boolean foundation integration evidence

[AGENT], 2026-09-06. Fresh validation of the staged merge of reviewed renderer
`ff7173dd` into integration parent `c7eeaf57`. That parent contains exact
Boolean initialization (`354ef7f2`) and the reviewed structural runtime
contracts (`8717b974`, integrated by `29092c26`).

Four test/audit integration conflicts were resolved by retaining both sets
of tests, required exports, all-imported-local-origin audit selection,
constructive renderer-helper checks and every compiled poison control.
There was no additional interpreter, frontend or observation-policy change
in resolving those conflicts. The independently reviewed renderer repair
and its earlier red/full evidence remain in the neighboring evidence sets.

- Fresh capped `bash scripts/check-interface`: PASS, 44 required exports,
  11,909 imported local declarations and all nine compiled poison controls.
- Fresh capped `scripts/ci --diff`: PASS. Warning-free default build,
  interface/admission/Boolean gates, native pins and tests, all 202 eval
  checks, complete 3607-case executable and 394-case negative runs, the
  Go-dependent harness controls and regenerated float/init-order fixtures.
- Executable cases: 3363 PASS / 244 known FAIL. Comparing every case's
  result and stage against the reviewed renderer's complete run found zero
  drift, including no added or missing case. This is also exactly the
  reconciled 3607-case baseline. Known failures remain failures.

Commands used `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3`, with
`GOLEAN_COVERAGE_JOBS=2` for full CI, under `scripts/capped` at the unchanged
Lean4.32.2/Go1.26.5 pins. Logs and metadata retain their original source and
dirty-worktree labels; the source manifest binds the actual tested files.
CI's slow membership certificate remains explicitly cached under its
standing `--diff` policy; this is not a fresh `--slow` certification.

The independent whole-program Boolean bridge was developed in ignored
scratch during this frozen run. Its public modules/tests are absent from
this tested source, and are not accepted by this gate. They require separate
promotion and fresh audits. Likewise the observer byte-transport/classifier
repairs, recovery profile/customers, B7/I1 and final sprint decision packet
are not discharged here. This checkpoint makes no main-merge or stable-pin
claim. `SHA256SUMS` seals the evidence files; `sources.sha256` is relative
to the integration worktree root before the next source increment.
