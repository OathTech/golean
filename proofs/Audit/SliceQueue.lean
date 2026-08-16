import Lean
import GoLeanProofs.Examples.SliceQueue

/-!
# In-build axiom gate — the SliceQueue (queue) example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A2, unit G1.8, 2026-08-15), in the shape the phase-2 shards use.
The shard imports ONLY this example's root.

`✓` **`queue_ok` — the S3 RELATIONAL headline over
`queue_harness_r(n, seed, k)`** (`Examples/SliceQueue.lean` over the
pinned `queueLowered`): for every `n ≤ 8`, EVERY `seed < 2^64` and
EVERY `k < 2^64`, past the fuel bound `247·n + 254`, at EVERY
nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns three values — the `n` enqueued
values as a zero-padded `[8]uint64` array, `enqueued.take k` (FIFO
order, truncated at what the queue holds), and the REMAINING queue
size `n − k` (Nat subtraction, truncating at zero). The postcondition
is a relation over the RETURNED data, and it is **the stack mirror's
sentence with `.reverse` deleted** — that one word is the whole
difference between the two examples.

The statement was fixed and EXECUTED against the machine BEFORE it was
delegated (lane practice): MATCH at eleven argument points at the
default stream — including the uint64 wrap region (`seed = 2^64−1`,
`2^64−2`, `2^63−1`) — and again at `n = 8, k = 4` under four different
choice streams. `queue_readout` is the D1 run-conditioned twin,
derived through `harness_readout_of_total`.

`✓` **The corpus half**: `queueHarnessRFunc_pin`, `enqueue_pin`,
`dequeue_pin`, `qsize_pin` — the harness and all three subject `Func`s
are `rfl`-tied to the pinned lowering (`queueLowered`, itself pinned by
`scripts/check-golden`). All four are axiom-FREE.

`✓` **The enqueue phase, capacity- and address-generic at EVERY choice
stream** — the campaign's first proof THROUGH Go's `append` and its
NONDETERMINISM ENVELOPE:

* `qe_iter` — ONE enqueue is EXACTLY 130 interpreter steps on BOTH
  paths: in-place (`newLen ≤ cap`, no choice consumed) and spill
  (`len = cap`, ONE capacity choice consumed; the realized capacity is
  `qSpillCap C extra`, ranging over the machine's admitted envelope
  `[newLen, appendSpillUpper]`). The backing address, capacity, dead
  tail and remaining stream are existentially packaged (`qEnqInv`).
* `qe_loop` — `130·(n−j)` steps end-to-end for the whole loop, by
  induction over the existential package.
* The executable `append` facts underneath: `qappend_inplace`,
  `qappend_spill`, `buildAppendBacking_u64`, `sliceVisibleValues_u64`
  (GAP-WITNESS: no kit form existed for any growing-slice fact); plus
  the moving-offset re-slice fact `applyStrictOp_sliceExpr_slice`
  (`q[1:len(q)]` on a slice base: same backing, offset+1) landed for
  the dequeue phase.

**`∀ ch` DOES REAL WORK — the headline honesty clause.** One choice
per spilling `append`; the CLAIM is capacity-independent (capacity is
not observable through this harness) while the PROOF is
capacity-generic (`qEnqInv` carries the backing address, capacity and
dead tail as existentials and never names them), so the theorem holds
at every stream and survives a re-envelope of the append growth rule
that keeps the choice arity. The step COUNT is choice-invariant —
1750 steps at `n = 8, k = 4` under four streams — while `nextAddr`
(97 vs 96) and the number of choices consumed (2 vs 1) are not. The
DEQUEUE half is choice-free: `q[1:]` only advances a header offset.

**`∃ enqueued` is family-determined**: the witness is
`qFam n seed = [seed, seed+1, …]` reduced mod 2^64; the statement
avoids saying so, exactly as `stack`, `histogram` and `dotprod` do.
Making the input genuine ∀-data needs the ghost rung-1 annotation,
which is designed and not built.

**The arithmetic wraps and the claim covers the wrap region, but the
corpus's differential ceiling is BELOW the theorem's.** The theorem's
domain is the full `seed < 2^64`; no corpus row pins a seed above
`2^63 − 1` (the differential driver's arguments are int64-limited), so
`[2^63, 2^64)` is theorem-claimed and oracle-unpinned — probe-matched
against the machine at `2^64 − 1` and `2^64 − 2`, which is a weaker
check and is labelled as one.

**The cap `n ≤ 8` is the program's own arithmetic** (`queueCapN = 8`);
`seed`/`k < 2^64` are Go's uint64 domain, not ours. **`n − k` is Nat
subtraction**, truncating at zero: the Go dequeues `min(k, n)` values
and returns `qsize(q)`, so an over-large `k` drains the queue rather
than driving the count below zero.

**The fuel bound `247·n + 254` is a BOUND, not the exact count.** The
measured count is `242 + 130·n + 117·min(k,n) + 12·[n < k]`
(probe-confirmed at thirteen `(n,k)` points and proved as `q_run`'s
exact count); the shipped `N` equals it exactly when `k > n` — 2230 at
`n = 8, k = 9`, measured and bound alike — and is loose by
`117·(n − k) + 12` when `k ≤ n`. Bound and measurement are labelled
separately; neither is presented as the other.

Deletion test — **RUN by the lane owner as a MACHINE PROBE**, each
named hypothesis dropped in turn and the postcondition re-evaluated
against the real run, because "the proof consumes it" and "the claim
is false without it" are different statements:

* `hcap` is a **totality** boundary — at `n = 9` the subject panics
  (`index out of range [8] with length 8`), so the `= .ok …` conjunct
  fails outright.
* `hk` is a **truth** boundary — at `n = 3, seed = 5, k = 2^64` the
  machine normalizes `k` to `0`, dequeues nothing and returns size
  `3`, against a postcondition that reads `k` as the Nat `2^64`.
* `hseed` is a **proof-structure** boundary only — at `seed = 2^64`
  the machine still MATCHES, because the entry normalization and
  `qFam` both reduce mod 2^64 and move together. The proof needs it
  (`unorm_nat_of_lt`); the claim does not break there.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`queueHarnessRFunc` (`rfl`-linked to the lowering by
`queueHarnessRFunc_pin`) + `qArr8` + `List`/`Int` arithmetic — no heap
vocabulary, no Iris, no frame names, no family function.

NOT DESIGNATED: this example is absent from `Examples/Targets.lean`,
from `scripts/ci`'s Targets allowlist, from `Audit.lean`'s
designated-name list and from the Comparator Challenge's trusted
closure (gallery-campaign charter §HARD BOUNDARIES).
-/

namespace GoLean.Iris.Audit

/-! ## The queue example (Gallery Campaign G1, proof lane A2) -/

-- Statement vocabulary
example := @GoLean.Examples.SliceQueue.qArr8
example := @GoLean.Examples.SliceQueue.queueHarnessRFunc
example := @GoLean.Examples.SliceQueue.enqueueFunc
example := @GoLean.Examples.SliceQueue.dequeueFunc
example := @GoLean.Examples.SliceQueue.qsizeFunc
-- The lowering pins (the third link of the golden chain)
example := @GoLean.Examples.SliceQueue.queueHarnessRFunc_pin
example := @GoLean.Examples.SliceQueue.enqueue_pin
example := @GoLean.Examples.SliceQueue.dequeue_pin
example := @GoLean.Examples.SliceQueue.qsize_pin
-- Proof vocabulary the prose names
example := @GoLean.Examples.SliceQueue.qFam
example := @GoLean.Examples.SliceQueue.qPre
example := @GoLean.Examples.SliceQueue.qBack
example := @GoLean.Examples.SliceQueue.qFam_take
example := @GoLean.Examples.SliceQueue.qSpillCap
example := @GoLean.Examples.SliceQueue.qEnqInv
-- The landed enqueue-phase results and the append gap-witnesses
example := @GoLean.Examples.SliceQueue.qe_iter
example := @GoLean.Examples.SliceQueue.qe_loop
example := @GoLean.Examples.SliceQueue.qappend_inplace
example := @GoLean.Examples.SliceQueue.qappend_spill
example := @GoLean.Examples.SliceQueue.applyStrictOp_sliceExpr_slice

/-- info: 'GoLean.Examples.SliceQueue.qe_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qe_loop
/-- info: 'GoLean.Examples.SliceQueue.qe_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qe_iter
/-- info: 'GoLean.Examples.SliceQueue.qappend_spill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qappend_spill
/-- info: 'GoLean.Examples.SliceQueue.qappend_inplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qappend_inplace
/-- info: 'GoLean.Examples.SliceQueue.applyStrictOp_sliceExpr_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.applyStrictOp_sliceExpr_slice
/-- info: 'GoLean.Examples.SliceQueue.qFam_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qFam_take
/-- info: 'GoLean.Examples.SliceQueue.queueHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.queueHarnessRFunc_pin
/-- info: 'GoLean.Examples.SliceQueue.enqueue_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.enqueue_pin
/-- info: 'GoLean.Examples.SliceQueue.dequeue_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.dequeue_pin
/-- info: 'GoLean.Examples.SliceQueue.qsize_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qsize_pin

end GoLean.Iris.Audit

/-! ## Session-2 additions (headline still owed; see the root's status
block): the min-branch, the dequeue head, and the whole `dequeue`
callee — all axiom-clean. -/

example := @GoLean.Examples.SliceQueue.qx_toHead
example := @GoLean.Examples.SliceQueue.qd_head
example := @GoLean.Examples.SliceQueue.qd_callee

/-- info: 'GoLean.Examples.SliceQueue.qx_toHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qx_toHead
/-- info: 'GoLean.Examples.SliceQueue.qd_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qd_head
/-- info: 'GoLean.Examples.SliceQueue.qd_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.qd_callee

/-! ## The headline landing (G1.8 completion): the dequeue iteration
and loop, the exit epilogue, the exact-count run, and the two
user-facing statements — `queue_ok` (the fixed S3 relational FIFO
headline) and its run-conditioned twin `queue_readout`. All zero
`sorry`, standard axiom trio. The shard prose above is the lane
owner's to update. -/

example := @GoLean.Examples.SliceQueue.qd_iter
example := @GoLean.Examples.SliceQueue.qd_loop
example := @GoLean.Examples.SliceQueue.q_exit
example := @GoLean.Examples.SliceQueue.q_run
example := @GoLean.Examples.SliceQueue.queue_ok
example := @GoLean.Examples.SliceQueue.queue_readout

/-- info: 'GoLean.Examples.SliceQueue.queue_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.queue_ok
/-- info: 'GoLean.Examples.SliceQueue.queue_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceQueue.queue_readout
