# Stdlib extern policy for the quorum pilot (phase 2 decision note, 2026-07-30)

Decided against the REAL dependency surface of
`deps/raft/quorum/{majority.go,quorum.go}` (read, not assumed):

## What CommittedIndex + VoteResult actually need

- `math.MaxUint64` — **already free**: go/types folds cross-package
  constants; the frontend emits the folded literal (probed:
  `18446744073709551615` on the wire). No extern.
- `slices.Sort(srt)` with `srt : []uint64` — **the one true extern**.
  Generic stdlib call on the critical path (the hand-rolled insertion
  sort the plan remembered is gone from current etcd-io/raft).
- `cmp`, `fmt`, `strings`, `strconv` — used ONLY by
  `String()`/`Describe()` (rendering) — NOT needed; those functions
  ride the existing per-decl quarantine (fail closed if called).
- Everything else (`len`, map range, array-to-slice, `make`, uint64
  conversions/arithmetic, the interface method call) already lowers.

## The slices.Sort extern (decided)

A machine STATEMENT op `sortSlice` (the wide-op shape shared with
`appendSlice`/`copySlice`/`clearSlice`):
- Semantics: in-place ascending sort of the slice's visible elements
  (a store loop over the backing, like `clearSlice`). For INTEGER
  element kinds the observable result is fully determined (sortedness +
  permutation; equal integers are indistinguishable, so Go's
  instability is unobservable) — the extern is exact, not an
  approximation.
- Frontend: `slices.Sort(x)` call statements whose instantiated
  element type is an integer kind emit `{"stmt":"sort-slice","x":…}`.
  ANY other `slices.*`/`sort.*` use fails closed (visible refusal) —
  `slices.SortFunc`, non-integer elements, sort-as-expression.
- Proof face (phase 4): one law with the spec "the cells hold a sorted
  permutation of the previous values" — exactly the premise the
  CommittedIndex walk needs to reach `committedIndexRef`'s
  sorted-position read. Granularity: ONE step for the whole sort
  (multi-cell read+write) — recorded in the granularity ledger; like
  the frame exits, unobservable sequentially, revisit under
  concurrency (a goroutine observing a half-sorted slice is not a
  state this machine can produce; Go's real sort is also not observably
  atomic — the ledger entry records the delta).
- REJECTED alternative — monomorphizing the real `slices.Sort` (pdqsort
  over `cmp.Ordered`): drags in generics machinery for zero observable
  difference on integer elements; the pilot's claim is about
  `CommittedIndex`, not about pdqsort.

## Source scoping (decided): single-package vendoring, v1

Phase 3 vendors the quorum source into corpus case dirs as
`package main` (verbatim function bodies; only the package clause and
import block adjusted — imports the machine does not model are dropped
along with the render-only functions that used them, which the
per-decl quarantine keeps honest). TRUE multi-package lowering (import
resolution, qualified identity across packages — the TypeId keys are
already package-qualified in anticipation) is deferred until after the
pilot; the pilot's claim names the FUNCTIONS (`CommittedIndex`,
`AckedIndex`, `VoteResult`) whose bodies are byte-identical to
etcd-io/raft, and the diff against upstream is recorded in the case
README.
