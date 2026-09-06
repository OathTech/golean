# BUG-107 isolated repair accepted

[AGENT] Root, 2026-09-06. The design note records the original red-first
proposal; this checkpoint records its completed isolated validation.
The twelve frozen candidate inputs are unchanged. Independent implementation
review is preserved in `independent-review/`, and independent baseline and
dependency disposition is attached at `169ec3c3` (review source `7a684765`).

Final `scripts/ci --slow` returned numerical exit 0 (job 57432), under
16 GiB, three Lean threads and two corpus workers. All 3,851 final input
hashes were revalidated. The full run has exactly 3,635 rows: 3,390 PASS
and 245 FAIL, with 394 negative PASS. The executable failing set and stages
equal the accepted first full run; only the eight new identity/observer
rows distinguish this baseline from the original 3,627-row basis.
The full differential subprocess returns 1 for those known failures; they
remain failures. CI passes because the exact reviewed baseline matches.

The only slow-tier row, `imported-goose/channel/google-search`, was freshly
re-certified. Its set, wire and parameter pin are unchanged. The fresh
hardware float vectors and gc initialization table also match their pins.
The original metadata's `full_run=unknown` is preserved; the unfiltered
manifest hash and exact row inventory establish the full scope separately.
See `slow-completion.json` and the raw logs, records and slow artifacts.

Earlier evidence includes the actual Go 8/model 15 counterexample, five
differential failures, two explicit observer refusals, the wrapping positive,
48 fresh identity/atomic cases and 204 evaluator checks after the repair.
The first full CI's missing Goose dependency failure is retained; the exact
pinned clean dependency was restored and independently checked before the
successful final sequence. No failure was converted into a conformance PASS.

Integration with R1/B7/I1 is still separate work. This is a fidelity repair,
not a representation equivalence across the old wrong answer. The combined
runtime still needs its full/slow train and exact baseline disposition.
No main merge, push or additional platform support is claimed.
