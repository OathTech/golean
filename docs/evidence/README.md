# docs/evidence/ — the probe-evidence convention

[AGENT] Written 2026-08-31 (fidelity work program, Tier-3 item D-9):
the convention below is what the existing 26 dirs already follow
de facto (assessment: lane-d-apparatus.md §3 — "a strong, uniform
de-facto convention — entirely unwritten and unenforced"). This
file makes it explicit. FORWARD-LOOKING RULE ONLY: it binds every
NEW evidence directory; no backfill of existing dirs is required
(gaps in the old dirs are recorded in the assessment, not silently
rewritten).

## What lives here

First-hand probe records that a doc cites as evidence: oracle
transcripts, wire dumps, sweep outputs, measurement runs. These are
NOT corpus cases (`scripts/coverage-manifest` does not scan this
tree) and NOT proof artifacts — they are the reproducibility trail
behind a written claim. The standard is the outsider's question:
*could a hostile reader re-run this and get these bytes?*

## The rules (each new `docs/evidence/<date>_<slug>/`)

1. **A README.md**, titled `# <what this is> — <context> (<date>)`.
2. **The exact command lines** that produced every artifact in the
   dir (a Reproduction block; copy-pasteable from the repo root).
   Generated files should name their producer in a header where the
   format permits — and use repo-relative paths, never absolute
   worktree paths (the recorded dead-path gap).
3. **Toolchain line**: the Go version used (`go version` output) —
   which must be the pin in `baselines/go-oracle-pin` unless the
   README says loudly why not — and, for machine-tier records, the
   Lean toolchain/binary provenance.
4. **Commit SHA**: for any record where repo state matters (machine
   runs, frontend emits, sweeps), the exact commit the tree was at,
   plus a dirty-tree note if it was not clean. Pure-gc dossier
   records (oracle-only) may omit it, saying so.
5. **Host note**: `linux/amd64` at minimum; for load- or
   timing-sensitive numbers (scheduler probes, timeout studies),
   name the box class and note concurrent load, since such numbers
   have measurably varied with it.
6. **Date and conclusion**: when it was run, and the one-paragraph
   conclusion the citing doc relies on — so the dir is legible
   without the doc, and drift between them is detectable.
7. **Provenance tags**: [AGENT]/[USER] on any decision the README
   records (house rule, CLAUDE.md).
8. **Bidirectional citation**: the README names the consuming doc;
   the doc cites the dir.

Nothing here is gate-enforced (this is a working convention, not a
fortress); the reconciler and future audits read against it.
