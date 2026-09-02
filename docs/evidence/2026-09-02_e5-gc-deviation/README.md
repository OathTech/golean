# E5 gc deviation — early store across the assignment phase boundary, the reproducer matrix (2026-09-02)

Consuming docs: `docs/spec-divergence-ledger.md` **L-016** (the gc-bug
backlog entry this dir is the reproducer for);
`docs/2026-08-11_latitude-inventory.md` §E5 (re-labelled from latitude
to gc DEVIATION 2026-09-02); `docs/2026-09-01_grossmith-campaign-3.md`
§5.0/§5.2 (the campaign-3 witnesses `case_03110`, `case_03079` whose
reduction this is); `docs/BUGS.md` BUG-032 (correction note) and
BUG-075 (the return-side twin).

Provenance. The probe matrix was built and run by the grossmith
campaign-3 verifier on 2026-09-02 [AGENT] in the gitignored
`artifacts/grossmith/2026-09-01/probe-e5/` (its outputs are copied
here verbatim); the re-classification of what it shows — gc
DEVIATION, not latitude — is the [USER] ruling of 2026-09-02 (Mike,
verbatim: "agree we should mark as a gc deviation, and record in our
gc bug backlog"), recorded at L-016. Nothing in this dir was
re-decided by the recording agent.

## The question

`spec#Assignment_statements`: "The assignment proceeds in two phases.
First, the operands of index expressions and pointer indirections
(including implicit pointer indirections in selectors) on the left and
the expressions on the right are all evaluated in the usual order.
Second, the assignments are carried out in left-to-right order." A
phase-1 panic therefore precedes every phase-2 store. Does gc ever
make an earlier target's store visible (under `recover`) when a LATER
right-hand operand panics?

## What is here

- `probe/main.go` — the six-probe subject (p1–p6), one function per
  probe, each returning the recovered value of `v`; `main()` prints
  all six for the gc-side run. VERBATIM copy of the campaign's
  `probe-e5/case/main.go` except ONE comment token: the original wrote
  `spec#Assignments`, an anchor that does not exist in the pinned spec
  (the section id is `Assignment_statements`); the token is corrected
  so `scripts/check-spec-anchors` resolves it. No code changed.
- `gc-output-default.txt`, `gc-output-noopt.txt` — gc at default
  flags and at `-gcflags=all='-N -l'`, re-run fresh for this dir at
  the pin (identical to each other and to the campaign's recorded gc
  column).
- `manifest.tsv` — the six-row hand manifest for `scripts/diff-coverage`,
  with `go_dir` rewritten REPO-RELATIVE to `probe/` here (the original
  pointed at the gitignored artifacts dir under an absolute worktree
  path).
- `machine-run/{results.tsv,results.meta.tsv,run.log}` — the
  campaign's differential run of that manifest, copied VERBATIM: they
  carry the ORIGINAL run's absolute worktree paths
  (`/home/dev/projects/golean/.claude/worktrees/t4-grossmith/artifacts/...`,
  a dead path by design once the artifacts dir is cleaned) and its
  provenance row `git_commit 864d1bdc`, `git_dirty true`. Disclosed
  rather than rewritten: these are the bytes the report's §5.2 table
  was read from. The machine-side observation on every row is in
  `results.tsv`'s `Lean=` JSON (values 58 = spec point on p1/p2/p5,
  where `Go=` is 29).
- `harness/p1-probeConstStoreBeforePanic/`,
  `harness/p5-probeTwoTargets/` — the exact gc-side subjects the
  differential compiled for the two minimal reproducers (the probe
  file minus `main`, plus the harness's generated
  `zz_golean_harness.go` observation shim), so the `Go=` JSON in
  `results.tsv` can be re-derived byte-for-byte. Same one-token
  comment fix as `probe/main.go`.

## The matrix (gc = default flags = `-N -l`; machine = `results.tsv`)

| probe | statement (v = 58 before; z = 0; s = []int{1}, i = 5) | gc | machine | spec |
|---|---|---|---|---|
| p1 | `a, v, b = -a+a, 29, z/z` | **29** (early store) | 58 | 58 |
| p2 | `a, v, b = -a+a, w, z/z` (w a variable, = 29) | **29** (early store) | 58 | 58 |
| p3 | `b, v = z/z, 29` (panic FIRST) | 58 | 58 | 58 |
| p4 | `v, b = 29, s[i]` (INDEX panic, not division) | 58 (store held back) | 58 | 58 |
| p5 | `v, b = 29, z/z` (two targets, as generated) | **29** (early store) | 58 | 58 |
| p6 | control: `v = 29; b = z/z` (two statements) | 29 | 29 | 29 |

## Conclusion (the one paragraph the citing docs rely on)

gc stores an earlier target before a LATER right-hand operand's
division panic, observably under `recover` (p1/p2/p5), on a shape
where the spec's two-phase sentence puts every store after every
operand evaluation; the machine realizes the spec point on all six
rows. gc's behaviour is not an optimizer artifact (`-N -l` identical),
not about constants (p2), and OPERATION-SPECIFIC: an index panic holds
the store back (p4) while a division panic does not. That operation
dependence is the signature of gc's `ascompatee` early-copy heuristic
(`deps/go/src/cmd/compile/internal/walk/assign.go`: a later
right-hand expression is evaluated BEFORE earlier stores only when
`readsMemory` says an earlier store could ALIAS it — index/deref yes
(p4, probed), division no (p1/p2/p5, probed); the list's other
no-entries (arithmetic, shift, conversion, type assertion) predict the
same early store but are NOT probed in this matrix — and the panic-before-store guarantee
of gc's own regression test `deps/go/test/fixedbugs/issue43835.go` is
enforced only for RESULT PARAMETERS in functions with defers,
`deferResultWrite`; a captured local like `v` here is the same
observation channel and is not covered). [AGENT] mechanism reading —
from the source, not a debugger trace. The [USER] ruling classifies
this as a gc deviation (L-016), not latitude.

## Reproduction (from the repo root)

    # gc side (pin go1.26.5)
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-09-02_e5-gc-deviation/probe/main.go 2>&1                        # -> gc-output-default.txt
    go run -gcflags=all='-N -l' docs/evidence/2026-09-02_e5-gc-deviation/probe/main.go 2>&1   # -> gc-output-noopt.txt
    # (the builtin println writes to STDERR — hence the 2>&1)

    # machine side (the campaign's run; a capped differential over the hand manifest)
    GOLEAN_COVERAGE_ARTIFACTS=artifacts/e5-gc-deviation \
      scripts/capped scripts/diff-coverage docs/evidence/2026-09-02_e5-gc-deviation/manifest.tsv
    # results land in artifacts/e5-gc-deviation/results.tsv; expect FAIL/differential on
    # e5/probeConstStoreBeforePanic, e5/probeVarStoreBeforePanic, e5/probeTwoTargets
    # (Lean=58 vs Go=29) and PASS on the other three — the FAILs are gc's deviation, not ours.

## Toolchain / provenance

- Go: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`;
  `deps/go` at `c19862e5f8` = the go1.26.5 tag), both for the campaign
  run and for the fresh gc outputs here.
- Machine run: `results.meta.tsv` — commit `864d1bdc` of the
  `t4-grossmith` lane, dirty tree (the campaign worktree mid-lane),
  native frontend, `go_drift_actual false`. NOT re-run for this dir
  (docs-only slice; the fresh part is the gc side only, which needs
  no machine build).
- Host: linux/amd64 dev box; not timing-sensitive (deterministic
  sequential probes; no load caveat applies).
- Dates: probe matrix built and run 2026-09-02 (campaign-3 §5.2);
  gc outputs re-captured 2026-09-02 at repo commit `fa01caec`.
