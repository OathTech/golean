# docs/evidence/ — what a committed record is, and is not

[AGENT] convention of 2026-08-31, rewritten 2026-10-12 under the [USER]
ruling that a committed record must be «useful with a high bar for
evidence» (`docs/architecture-rules.md`, «Evidence on main»; the triage and
its reasoning: `docs/2026-10-12_gate-cull-plan.md` §9, D10).

## The bar

A directory exists here only if the commit message's conclusion cannot
stand without it: the capture of a non-reproducible event, or a probe
source whose oracle output pins a claim a reader must be able to re-run.
Gate tails, train stamps, audit transcripts, run dumps and wire dumps are
reproducible from the tree at a commit and are not committed. A probe that
pins semantics is a `Corpus/` case; a test fixture lives beside its test.

## The rules for a record that clears the bar

1. **A README.md**, titled `# <what this is> — <context> (<date>)`, with
   the one-paragraph conclusion the citing doc relies on.
2. **The exact command lines** that produced every artifact (repo-relative
   paths, copy-pasteable from the repo root).
3. **Toolchain line**: the Go version (the pin in `baselines/go-oracle-pin`
   unless the README says loudly why not); for machine-tier records the
   Lean toolchain.
4. **Commit SHA** where repo state matters, with a dirty-tree note if it
   was not clean.
5. **Host note** for load- or timing-sensitive numbers.
6. **Provenance tags** ([AGENT]/[USER]) on any decision recorded.
7. **Bidirectional citation**: the README names the consuming doc; the doc
   cites the dir.

## The 2026-10-12 triage

Before: 179 directories, 2504 files, 32.6 MB tracked. Deleted whole: 106
directories (train stamps, audit and review transcripts whose findings are
in their dated docs, and records cited by no living doc, code or commit
message); 2 directories reduced to their README; inside the kept
records, 165 gate tails and 11 dumps over 256 KiB; two test fixtures
moved to `tools/nativefrontend/testdata/fr25/`. After: 73 directories,
1205 files, 6.2 MB. Every deleted record is in history at
`git show 63c9ea65:docs/evidence/<dir>/`.
