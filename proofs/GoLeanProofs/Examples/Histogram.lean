import GoLeanProofs.Examples.Histogram.Pure
import GoLeanProofs.Examples.Histogram.Machine

/-!
# Histogram — the map-histogram example (Gallery Campaign G1, flagship)

Go source: `Corpus/coverage/exec/examples/histogram/main.go`
(differentially green against `go run`, 13 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/histogram-lowered.repr`
and carried in `GoLeanProofs.Examples.HistogramProgram`.

The subject builds a `map[uint64]uint64` of counts over a slice, reads
the count of a queried key, and then counts the map's entries with a
VARIABLE-FREE `for range counts {}`. The harness is the S3 RELATIONAL
style: it returns the values it counted (as a fixed-cap `[8]uint64`)
alongside both summaries, so the postcondition is a relation over the
RETURNED DATA — `hits = occurrences q vals` and
`distinct = distinctCount vals` — with no family function
re-describing the setup inside the claim.

**Why the `∀ ch` quantifier is load-bearing here.** `for range counts`
consumes one `Choices` pick per iteration, so the headline quantifies
over EVERY map-iteration order. `distinctCount` is a function of the
returned values alone, so it cannot see the order the machine chose —
and the claim holds at all of them precisely for that reason. A spec
naming "the first key visited" would be unprovable here, and that
unprovability would be the envelope working.

The per-phase shards:

* `Histogram.Pure` — the two statement functions (`occurrences`,
  `distinctCount`), the counting fold, and the bridges.
* `Histogram.Machine` — the two pinned `Func`s, the address layout, and
  the variable-free choice-pick step.
* `Histogram.HarnessR` — the run, end to end, and THE HEADLINE.
-/
