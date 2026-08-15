import GoLeanProofs.Examples.Reverse.Core
import GoLeanProofs.Examples.Reverse.HarnessV

/-!
# Verified example: in-place slice reversal — THE ENTRY POINT

A thin AGGREGATOR. It declares nothing; `import
GoLeanProofs.Examples.Reverse` gives you the whole `reverse` example,
the DESIGNATED gallery headline `reverse_ok` included.

* `GoLeanProofs.Examples.Reverse.Core` — the development: the pinned
  lowering's proofs, the input family `revFamily`, the demoted
  `reverse_ok_v1` / `reverse_readout_v1` (kept unweakened), and the
  memory-quantified `reverse_framed`.
* `GoLeanProofs.Examples.Reverse.HarnessV` — the swap shard declaring
  the designated headline `reverse_ok` (the S1 COPY-RELATIONAL form
  over `reverse_harness_v`) and `reverse_readout`.

**Why this file is a stub** (G4.2 DAG repair, 2026-08-15). It used to
BE the development, and `HarnessV` imported it — so `import
…Examples.Reverse` could not reach `reverse_ok`, and the re-export
that would have fixed it was inexpressible: it closes a cycle, and
Lean's import graph is acyclic. That is finding C-H5 of
`docs/2026-08-15_phase2-premerge-audit.md`, whose structural half was
deferred to C-H4. Splitting the development out to `Core` and demoting
this file to an aggregator DISCHARGES both.

**Nothing moved but the file boundary.** Every declaration in
`Core.lean` is byte-identical to what this file held at `6e3e512c`,
its import header included; only the module docstring changed, and
only in the paragraph that described the old limitation.
-/
