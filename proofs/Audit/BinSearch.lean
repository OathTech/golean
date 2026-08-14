import Lean
import GoLeanProofs.Examples.BinSearch

/-!
# In-build axiom gate — the BinSearch example

Per-example shard of `proofs/Audit.lean` (examples phase-2 slice 0,
lever 3, 2026-08-14; the per-file dependency shape of `deps/brick-wp`'s
2026-08-14 sharded audit). The `example :=` witness references and the
`#guard_msgs #print axioms` pins below are VERBATIM from the
pre-shard `Audit.lean`.

The shard imports ONLY this example's module, so a change to another
example does not re-elaborate it. It is built because the root
`Audit.lean` imports it — and `scripts/ci`'s proofs-file audit-coverage
step FAILS if any `proofs/**/*.lean` leaves the audited import closure,
so dropping that import cannot silently retire these pins.
-/

namespace GoLean.Iris.Audit

/-! ## The binsearch example (scale-out slice 2c, 2026-08-13)

`✓` **`search_ok` — framed TOTAL first-occurrence binary search**
(`Examples/BinSearch.lean` over the pinned `searchLowered`): for any
SORTED `[]uint64` input below length `2^62`, any in-range target, at
ANY placement (`base`), beside ANY disjoint frame: execution completes
normally past one fuel bound at every choice stream, the result cell
holds `findSpec xs t` (FIRST occurrence or -1 — the duplicates
lower-bound behavior, oracle-pinned), the backing array is unchanged,
and every frame cell is preserved verbatim. Statement deltas vs the
design block: none. The `2^62` bound is the midpoint-overflow teaching
point (`lo + hi` computed in Go `int` — the Bloch bug; the proof
carries `lo + hi < 2^63` through every iteration; the exact unsafe
boundary starts at `2^62 + 1`, recorded in the module). The post-loop
`&&` is walked LAZILY: the `lo = len` exit segment provably never
reads `s[lo]`. Route notes (recorded): per-iteration `mid :=`
declarations allocate at symbolic addresses — loop states carry a
garbage suffix with a freshness invariant; `seqCont`'s environment
DecidableEq blocks `rfl` under `mid`-carrying scopes, discharged by
the module's `stepFn_seqn_splice`. The element-range hypothesis `hxs`
is deliberately unconsumed (the machine's comparisons are
kind-agnostic; it stays as the honest uint64-domain restriction).
`search_framed_readout` is the framed D1 twin. -/
-- HARNESS RESTATEMENT (form note §11): `search_ok` is now the harness
-- headline (search_harness: sorted family s[i] = seed + 2i under
-- hnowrap; raw target parameter; returned index = findSpec of the
-- family; the 2^62 Bloch bound carries over as the subject's own
-- domain; the past-the-end miss walks the short-circuit && lazily).
-- Memory-quantified forms kept proof-side as `search_framed`/
-- `search_framed_readout` (renamed).
example := @GoLean.Examples.BinSearch.search_ok
example := @GoLean.Examples.BinSearch.search_framed
example := @GoLean.Examples.BinSearch.search_framed_readout
example := @GoLean.Examples.BinSearch.bsFamily_sorted
/-- info: 'GoLean.Examples.BinSearch.search_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BinSearch.search_ok
/-- info: 'GoLean.Examples.BinSearch.search_framed_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BinSearch.search_framed_readout

end GoLean.Iris.Audit
