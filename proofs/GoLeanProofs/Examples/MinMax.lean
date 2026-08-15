import GoLeanProofs.Examples.MinMax.Core
import GoLeanProofs.Examples.MinMax.HarnessR

/-!
# Verified example: min/max of a slice — THE ENTRY POINT

A thin AGGREGATOR. It declares nothing; `import
GoLeanProofs.Examples.MinMax` gives you the whole `minmax` example,
the DESIGNATED gallery headline `minmax_ok` included.

* `GoLeanProofs.Examples.MinMax.Core` — the development: the pinned
  lowering's proofs, the demoted `minmax_ok_v1` / `minmax_readout_v1`
  (kept unweakened), and the memory-quantified `minmax_framed` /
  `minmax_framed_readout`.
* `GoLeanProofs.Examples.MinMax.HarnessR` — the swap shard declaring
  the designated headline `minmax_ok` (the S3 RELATIONAL form over
  `minmax_harness_r`) and `minmax_readout`.

**Why this file is a stub** (G4.2 DAG repair, 2026-08-15). It used to
BE the development, and `HarnessR` imported it — so `import
…Examples.MinMax` could not reach `minmax_ok`, and the re-export that
would have fixed it was inexpressible: it closes a cycle, and Lean's
import graph is acyclic. That is finding C-H5 of
`docs/2026-08-15_phase2-premerge-audit.md`, whose structural half was
deferred to C-H4. Splitting the development out to `Core` and demoting
this file to an aggregator DISCHARGES both.

**Nothing moved but the file boundary.** Every declaration in
`Core.lean` is byte-identical to what this file held at `6e3e512c`,
its import header included; only the module docstring changed, and
only in the paragraph that described the old limitation.
-/
