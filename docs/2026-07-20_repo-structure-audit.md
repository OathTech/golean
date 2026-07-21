# Repo structure audit — 2026-07-20

Read-only audit of the working tree (branch `slice-call-frame`, another agent
active in `proofs/` — nothing was edited or built except this report). Method:
`tree`, `git ls-files` vs a raw `find` sweep (to catch things invisible to git:
empty directories, ignored paths, untracked files), import-graph trace of every
`.lean` file, cross-reference of every script against `scripts/ci` and each
other, and spot-reads of docs/READMEs for staleness.

Scope note: `proofs/Audit.lean` and `proofs/GoLeanProofs.lean` were dirty
(in-flight work by the other agent) and were not judged here.

## 1. Review of current state

### What is well-wired (no action needed)

- **Build**: `lakefile.toml` builds lib `GoLean`, exes `golean` (root `Main`)
  and `gocore-eval-tests` (root `Tests.GoCoreEval`). `proofs/` is a deliberate
  separate Lake package (documented in its lakefile) with its own toolchain
  pin; `Audit` is a default target so the axiom/non-vacuity gate runs on every
  proofs build.
- **The gate**: `scripts/ci` runs preflight, proofs-file coverage check,
  `check-bugs.sh`, `check-coverage`, both builds, eval tests, baseline diff,
  re-pin guard. `.github/workflows/lean_action_ci.yml` runs the same gate on
  push/PR and the full differential nightly. Local and CI agree by design.
- **Executable differential corpus**: 560 cases under `Corpus/coverage/exec/`
  discovered via `cases.tsv`, tags cross-checked against
  `Corpus/coverage/tags.tsv`, results ratcheted by the tracked
  `baselines/native-full.tsv` (717 cases + header; the recorded `latest.tsv`
  run is at `3d365b8`, an ancestor of HEAD). `baselines/untriaged-count` is
  read by `check-bugs.sh`. `tools/nativefrontend` and `tools/coverageharness`
  are both invoked by `scripts/diff-coverage`. All wired.
- **Script graph**: 11 of 12 scripts are reachable from `scripts/ci` directly
  or transitively. The exception is noted below.
- **Filesystem vs git**: the only untracked files on disk are two `.DS_Store`
  (ignored-in-effect). No symlinks, sockets, or stray tracked/untracked
  divergence. The anomalies are all *empty directories*, which git cannot see.

### Anomalies found

**A. The compile-negative corpus is not regression-gated.**
`Corpus/coverage/negative/` holds 310 cases. `scripts/check-coverage` reads
their `case.tsv` tags (so the dead-tag check covers them), but:
- `scripts/coverage-negative` is not invoked by `scripts/ci` (with or without
  `--diff`), only reachable manually or via `scripts/coverage negative`.
- Its output (`artifacts/coverage/negative-latest.tsv`, last run 2026-07-17,
  now 3 days / many commits stale) has **no tracked baseline** in `baselines/`
  and no diff step. A regression in negative-case classification would be
  invisible to the gate. This is the largest "not wired in" gap.

**B. Empty case directories — invisible to git, silently skipped.**
Case discovery enumerates `cases.tsv`/`case.tsv` files, so a case directory
with no metadata file simply doesn't exist to the tooling — no error, contra
the fail-closed principle. Present on this machine (none are in the baseline
or `negative-latest.tsv`; they are husks, likely from moves/renames):
- `Corpus/coverage/exec/variadic/multi-result-append/`
- `Corpus/coverage/negative/compile/defer/defer-function-result/`
- `Corpus/coverage/negative/compile/defer/defer-recover-result/`
- `Corpus/coverage/negative/compile/builtins/new-non-type/`
- `Corpus/coverage/negative/compile/control-flow/switch-uncomparable-tag/`
- `Corpus/coverage/negative/compile/interfaces/type-switch-nil-multi-case/`
- `Corpus/coverage/negative/compile/interfaces/ambiguous-promoted-method-call/`
- `Corpus/coverage/negative/compile/channels/make-receive-only/`
(Note several of these names *do* exist as exec cases, e.g.
`interfaces/type-switch-nil-multi-case` is a FAIL/frontend-export row in the
exec baseline — consistent with a negative→exec promotion that left husks.)

**C. Stale escape-hatch allowlist entry in `scripts/ci`.**
`STANDALONE_PROOFS="SliceSpike Probe"` — but `proofs/Probe.lean` does not
exist. A future file by that name would be silently exempt from the
proofs-file audit-coverage check (an open hole in a tamper-hardened gate).
`SliceSpike` is fine: it exists and its exemption is documented.

**D. Dead Lean modules (Gobra-era vestiges), all still imported by
`GoLean.lean`:**
- `GoLean/IR.lean` — 1 line, pure re-import shim of `GoLean.GoCore`.
- `GoLean/Runtime.lean` — 1 line, pure re-import shim of `GoLean.GoCore.Value`.
- `GoLean/DiffTest.lean` — defines `Observable`, referenced nowhere else in
  the repo.
- `GoLean/Basic.lean` — defines `projectName`, referenced nowhere else.
They cost little but misrepresent the architecture (five of the eight
top-level modules under `GoLean/` are real; these four are noise) and they
pass the escape-hatch preflight scan every run for nothing.

**E. Dead scaffolding directories (empty, invisible to git):**
- `Differential/` — empty since Jun 29, referenced by nothing.
- `third_party/gobra/viperserver/{carbon,silicon}/` — Gobra was removed; no
  `.gitmodules` exists. Only stale doc references remain (`docs/phase1.md`,
  `docs/roadmap.md:160`, `docs/native-frontend-goal.md:81`).
- `Corpus/challenges/go-bestiary/full/` — zero files, zero references
  anywhere; `bestiary.go` lives in `Corpus/challenges/semantic-edges/full/`.
- Assorted empty `.claude/.cc-writes/` husks (root, `proofs/`, `scripts/`,
  `Corpus/coverage/exec/`) — Claude Code sandbox droppings. Harmless but the
  one inside the corpus is ugly; note `.gitignore` only ignores the root
  `/.claude`, so a *non-empty* nested one would show up as untracked.

**F. `scripts/semantic-edges-challenge-smoke` is unwired.**
The only script not reachable from `scripts/ci`; referenced only from
`TODO.md:232` (which still calls the suite "the active Gobra/Lean differential
suite"). Unclear whether it still runs; it is a manual-only tool with no
freshness signal.

**G. Stale merged branches.**
Local `gocore-semantics-upgrade`, `native-frontend`, `phase-2-gocore-memory`,
`slice-l5-pure`, `vertical-slice-1-pointer-call` are all 0 commits ahead of
`main` (fully merged). Remote also carries merged `gocore-semantics-upgrade`
and `phase-2-gocore-memory`. Only `slice-call-frame` (current, 6 ahead) is
live. Cheap confusion risk for any agent enumerating branches.

**H. Doc staleness / layering.**
19 of 42 docs mention Gobra; several *describe the removed frontend as
current*:
- `Corpus/coverage/README.md` — "the current Gobra frontend only supports…"
- `Corpus/challenges/semantic-edges/README.md` — "active Gobra/Lean
  differential manifest".
- `docs/phase1.md`, `docs/gobra-json-schema.md`, `docs/differential-testing.md`
  — describe the Gobra pipeline as the plan of record.
- `docs/roadmap.md:160` still says "Maintain `third_party/gobra`…".
The historical/dated notes (`2026-07-*`) are fine as records. The problem is
the *undated* docs, where living references (`architecture.md`,
`semantics.md`, `coverage-ledger.md`, `roadmap.md`) sit indistinguishable
next to completed/superseded plans (`phase1.md`, `coverage-buildout-plan.md`,
`coverage-core-spike-plan.md`, `semantics-cleanup-plan.md`,
`gobra-json-schema.md`, `architecture-audit.md`). A reader (or agent) cannot
tell record from contract without reading each one.

**I. Minor.**
- `artifacts/` (gitignored, correctly) carries ~25 old probe/debug dirs
  (`probe-*`, `debug-*`, `gobra-smoke*`, `manual-smoke`, migration TSVs).
  Cleanup needs owner approval per CLAUDE.md's no-`rm -rf` rule.
- `scripts/check-bugs.sh` is the only script with a `.sh` suffix — trivial
  naming inconsistency.
- `.DS_Store` at root and `GoLean/` (ignored; harmless).

## 2. Actionable proposals

1. **Gate the negative corpus.** Add `baselines/negative-full.tsv` (same
   result+id+stage discipline), teach `scripts/coverage-baseline-diff` (or a
   sibling) to diff it, run the static diff in `scripts/ci` and the full
   negative run under `--diff`/nightly. Until then the 310 negative cases are
   guardrails not attached to anything.
2. **Fail closed on husk case dirs.** In `coverage-manifest` /
   `coverage-negative-manifest` (or `check-coverage`), error on any directory
   under the corpus roots that contains neither a metadata file nor
   subdirectories with one. Delete the 8 husk dirs listed in (B) — they are
   local-only (git never sees empty dirs), so this costs nothing and a fresh
   clone already agrees.
3. **Remove `Probe` from `STANDALONE_PROOFS`** in `scripts/ci` (or create the
   file with a documented purpose). An allowlist entry for a nonexistent file
   is a pre-authorized hole in the audit-coverage check.
4. **Delete the four dead modules** `GoLean/IR.lean`, `GoLean/Runtime.lean`,
   `GoLean/DiffTest.lean`, `GoLean/Basic.lean` and their imports in
   `GoLean.lean`. Pure deletion; gate should show no drift (baseline-diff
   confirms).
5. **Delete dead scaffolding dirs**: `Differential/`, `third_party/`,
   `Corpus/challenges/go-bestiary/`; fix the three doc references to
   `third_party/gobra`. (Also rm the stray `.cc-writes` husks, incl. the one
   inside `Corpus/coverage/exec/`.)
6. **Prune merged branches** (5 local, 2 remote) once confirmed with the
   owner — one command, removes real agent-confusion surface.
7. **Decide the challenge corpus's status.** Either wire
   `semantic-edges-challenge-smoke` into `scripts/ci` as a cheap smoke (it is
   `go run` only), or mark it manual-only in its README and TODO — and fix
   both files' claim that Gobra is the active pipeline.
8. **Split living docs from records.** Move superseded/completed plans
   (`phase1.md`, `gobra-json-schema.md`, `differential-testing.md`,
   `coverage-buildout-plan.md`, `coverage-core-spike-plan.md`,
   `semantics-cleanup-plan.md`, `architecture-audit.md`) into
   `docs/archive/` (or add a one-line `> Superseded by …` header), and fix the
   actively-wrong lines in `Corpus/coverage/README.md`,
   `Corpus/challenges/semantic-edges/README.md`, `docs/roadmap.md:160`,
   `TODO.md:232`. Keep dated `2026-07-*` notes where they are — they are the
   record and are self-dating.
9. **Housekeeping (low, needs approval where destructive):** clear old
   `artifacts/` probe/debug dirs; optionally rename `check-bugs.sh` →
   `check-bugs`; add nested `.claude/` and `.DS_Store` patterns to
   `.gitignore` (currently only root `/.claude` and bare `.DS_Store` are
   covered — `.DS_Store` actually is covered; nested `.claude` is not).

## 3. Prioritization

| Pri | Item | Why this rank | Cost |
|-----|------|---------------|------|
| P1 | (1) negative-corpus baseline + gate wiring | Only unguarded test asset in the repo; violates "guardrails first" silently | ~half-day |
| P1 | (3) stale `Probe` allowlist entry | One-line fix to a tamper-hardened gate; open hole until fixed | 1 min |
| P1 | (2) fail-closed husk-dir check + delete husks | Direct fail-closed violation; husks are already invisible to clones | ~1 h |
| P2 | (4) delete dead Lean modules | Dead code in the always-built lib; misleads architecture readers | ~30 min + gate run |
| P2 | (5) dead dirs + third_party doc refs | Zero-risk deletions; removes "is Gobra still here?" confusion | 15 min |
| P2 | (7) challenge-corpus decision | Small, but an unwired script rots; decide wire-or-document | ~30 min |
| P3 | (6) prune merged branches | Cosmetic but cheap; needs owner nod | 5 min |
| P3 | (8) docs archive split + stale-line fixes | Improves agent/human onboarding accuracy; no correctness impact | ~1 h |
| P3 | (9) artifacts cleanup, naming, gitignore | Cosmetic; artifacts cleanup needs explicit approval | 15 min |

Sequencing note: items 2, 4, 5 are working-tree deletions/edits — hold them
until the current `slice-call-frame` work lands to avoid disturbing the active
agent; item 3 is a one-line `scripts/ci` change with the same caveat. Item 1
is best done as its own small slice with the usual gate.
