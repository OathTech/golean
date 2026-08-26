# The AuditCorpus landmark record

Created at the arc-4 landing fix round (2026-08-26, F7). The
validation-corpus split (A4-U25) created a second landmark obligation —
"the corpus builds AT LANDMARKS via `scripts/capped lake build
AuditCorpus`" — but, unlike the comparator judge (whose runs append
`LANDMARK-RUN:` lines to `docs/2026-08-02_comparator-judge-sprint.md`),
it had NO tracked record: the first landmark build's evidence lived
only in gitignored `artifacts/corpus-landing.log`, the exact failure
mode CLAUDE.md pins for differential runs ("`artifacts/` is
gitignored, so a run's `latest.tsv` is *not* the record").

## Format (mirrors the judge's marker)

```
CORPUS-LANDMARK-RUN: <sha> <YYYY-MM-DD> <jobs> <declarations> <cold|warm>
```

`<jobs>` = Lake's completion count for that invocation;
`<declarations>` = the sweep line's declaration count ("corpus audit
sweep: N declarations across the corpus closure, all axiom-clean") —
the sweep line printing at all IS the pass signal (the sweep throws on
any disallowed axiom). `<cold|warm>` records cache state honestly: a
warm entry certifies content (the sweep re-runs regardless), not a
cold-build wall. Rules as for the judge: append a marker with every
landmark corpus build; never edit an old marker.

## Reconciling the two pre-record counts (the audit's discrepancy)

The A4-U26 exit recorded "corpus **204 jobs exit 0**, sweep 23,278
declarations" and the landing log recorded "Build completed
successfully (203 jobs)" with the same 23,278-declaration sweep line.
Both are real: they are counts at DIFFERENT TREES — 204 at the
pre-merge U26 tip (772a295b), 203 at the post-main-merge landing tip
(f40f67f9; the merge brought Arc 2's lakefile/aggregator changes,
which shift the corpus invocation's job graph by one). Neither log
pinned sha↔count together, which is why the discrepancy looked like a
contradiction; the marker format above pins them. The declaration
count — the number that certifies content — agreed exactly (23,278).
Retroactive markers for the two pre-record runs (evidence:
`artifacts/corpus-landing.log` at the landing; the U26 exit record in
`docs/campaign-arc4-log.md`):

```
CORPUS-LANDMARK-RUN: 772a295b 2026-08-26 204 23278 warm
CORPUS-LANDMARK-RUN: f40f67f9 2026-08-26 203 23278 warm
```

(Both retroactive markers are transcribed from prose records, marked
here once; every subsequent entry is appended by the run that earns
it. Note the fix round REDREW the corpus boundary — the Ring/Round*
witness chains returned to the live target, so job/declaration counts
drop sharply from these two entries onward; see
`proofs/GoLeanProofsCorpus.lean`'s amended criterion.)

CORPUS-LANDMARK-RUN: 7cfffdca 2026-08-26 112 21124 cold
(fix-round landmark: the corpus boundary redrawn — 24 handler-equation
chain modules + live deps; the handler chains rebuilt COLD after the
SpillTransport re-head, 381 s wall at LEAN_NUM_THREADS=4/96G; sweep
line verbatim: "corpus audit sweep: 21124 declarations across the
corpus closure, all axiom-clean"; log artifacts/fixround-corpus.log)
