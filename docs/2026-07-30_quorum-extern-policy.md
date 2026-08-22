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
  (a read loop then a store loop over the slice's SINGLE backing cell)
  — recorded in the granularity ledger, `docs/2026-07-23_reshape-r1r2-
  machine-design.md` §1. (Correction 2026-07-31, pre-merge audit finding
  3: this bullet asserted the ledger entry existed when no row had been
  added, and called the step "multi-cell read+write" when a slice's
  elements share one backing cell. The row now exists and says
  single-cell/multi-write.) Like
  concurrency (a goroutine observing a half-sorted slice is not a
  state this machine can produce; Go's real sort is also not observably
  atomic — the ledger entry records the delta).
- REJECTED alternative — monomorphizing the real `slices.Sort` (pdqsort
  over `cmp.Ordered`): drags in generics machinery for zero observable
  difference on integer elements; the pilot's claim is about
  `CommittedIndex`, not about pdqsort.
  **SUPERSEDED PREMISE (2026-08-22, launch audit D8-F1/V2):** the
  "drags in generics machinery" ground expired — the generics
  monomorphization pipeline landed 2026-08-05 (`befe9da6`) and models
  the harder generic `slices.SortFunc` with ZERO GoCore surface via an
  injected declaration (`stdlibshim.go`/`genericshim.go`, 2026-08-21
  `17eb6d5e`). The `sortSlice` node's stated justification is
  therefore no longer live; the relocation is a parked arc (launch
  synthesis doc, deferred list) — the node stays until that arc,
  fail-closed at int kinds as before.

## Source scoping (decided): single-package vendoring, v1

Phase 3 vendors the quorum source into corpus case dirs as
`package main` (verbatim function bodies; only the package clause and
import block adjusted — imports the machine does not model are dropped
along with the render-only functions that used them, which the
per-decl quarantine keeps honest). TRUE multi-package lowering (import
resolution, qualified identity across packages) is deferred until after
the pilot.

**Correction 2026-07-31 (pre-merge audit, findings 4/7).** This sentence
used to claim "the TypeId keys are already package-qualified in
anticipation" of that work. They are qualified by package NAME, and Go
keys type identity on the import PATH — so the keys do NOT give
cross-package identity, and a single `package main` importing
`html/template` and `text/template` produced ONE key
`template.Template` for two distinct types, on which a type assert
answered `true` where Go answers `false` (and the panicking form ran
where Go panics with "types from different packages"). No future
multi-package work was needed to reach it.

v1 scope, decided: the frontend now COLLISION-CHECKS at the single
boundary constructor that builds the key
(`emitter.checkPackageNameCollisions`) and fails the export closed when
two distinct import paths would share a package-name qualifier —
`Corpus/coverage/exec/interfaces/imported-package-name-collision` is the
red pin. Widening the key itself to `obj.Pkg().Path()` is the real fix
and belongs with the multi-package slice (it re-keys every TypeId, hence
every pinned lowering and every panic-message rendering, so it is not an
audit-response-sized change). Tracked as BUG-010.

The rest of the v1 scoping is unchanged: the pilot's claim names the
FUNCTIONS (`CommittedIndex`, `AckedIndex`, `VoteResult`) whose bodies are
byte-identical to etcd-io/raft, and the diff against upstream is recorded
in the case README.
