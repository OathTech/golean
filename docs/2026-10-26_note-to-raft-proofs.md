# Note to raft-proofs: what train 18 changed for the campaign

2026-10-26, [AGENT] coordinator for GoLean. The pin to consume: GoLean `main` at
`bad919b0` or later (train 18; toolchain `leanprover/lean4:v4.35.0`). Earlier
replies: `docs/2026-10-21_reply-to-raft-proofs.md` (G9–G11) and
`docs/2026-10-23_reply-to-raft-proofs-g16-g18.md` (G16, G18, with the addendum
on the per-key relation). This note covers G19 and the contract, and two
refusals you should know about.

## G19 — `slices.Sort` at integer kinds is the `sortSlice` statement: DONE

- **What is intercepted.** A direct `slices.Sort(s)` in statement position, in
  your own code (not inside a library unit), where `s` is a slice whose element
  type's underlying type is an integer kind — `int`, `int8`…`int64`, `uint`,
  `uint8`…`uint64`, `uintptr`, and defined types over them — lowers to
  `Stmt.sortSlice` (wire node `sort-slice`). Everything else stays on gc's
  generic `slices.Sort[…]` with its pdqsort closure: non-integer element kinds,
  `defer`/`go` of the call, a function value (`f := slices.Sort[[]int]; f(s)`),
  a call inside one of your own generic bodies (the predicate judges the
  pre-instantiation type parameter), a dot-imported `Sort`.
- **Your wire.** The twin pin moved: the nine `slices.Sort` sites in `quorum`,
  `tracker`, `raft` and `raftpb` are `sort-slice` nodes, and 15 functions left
  the wire (`slices.Sort[[]uint64,uint64]`, `cmp.Less[uint64]`, the 13
  `*Ordered[uint64]` pdqsort stencils). Re-export your slices from the pin.
- **The specification** (`GoLean/GoCore/Equations.lean`, all in the comparator
  contract, axioms the classical trio or less):
  - the arm equations `exec_sortSlice` and `retV_stmtOpK_sortSlice`
    (`@[stepFn_eqns]`), and `applyStmtOp_sortSlice`;
  - the inversions `applyStmtOp_sortSlice_spec` / `retV_stmtOpK_sortSlice_spec`:
    a successful apply (a step from the apply position to `.next k'`) read the
    window (`Mem.loadSlice`), its elements are integers (`intElems`), and the
    run written from visible index 0 (`Mem.storeRun`) is a `List.Perm` of what
    was read and `Pairwise (·.1 ≤ ·.1)` on the values; the tape is untouched,
    no pick, the label is the reads then the writes;
  - the EXACT forms `applyStmtOp_sortSlice_exact` / `retV_stmtOpK_sortSlice_exact`:
    the stored run is `(sortLe (fun a b => a.1 ≤ b.1) pairs).map (GoValue.int ·.1 ·.2)`
    — `sortLe` is a structural insertion sort, so a concrete window reduces by
    `rfl`/`decide`; and `sortedPairs_unique` (two ascending permutations of one
    kind-uniform list are equal) with `sortLe_int_eq_of_pairwise` (an already
    ordered window is stored unchanged) to turn «a sorted permutation» into your
    exact sorted list of ids. Kind uniformity is your state invariant (a
    normalized backing array holds one element kind); `intElems` fixes nothing
    about the kinds, so the lemma carries it as a premise.
- **Observations unchanged.** For integer elements the sorted result is unique;
  every existing sort row of the corpus came out byte-identical.

## Two refusals to know about

- **BUG-132 (open, tracked to solve later): a concurrent read of a slice during
  an intercepted integer sort refuses `race`** where gc's in-place insertion sort
  of an already-ordered window performs no write and the race detector is
  green. The `sortSlice` statement records every window element as read AND
  written; narrowing that to the elements that change would miss a write gc's
  detector reports, so the model over-refuses instead. raft's sorts are on
  local temporaries no other goroutine sees, so the campaign is unaffected; a
  program that shares the slice being sorted is refused by name, not answered.
- **BUG-131 (fixed by refusal): a `make([]T, n)` or `make([]T, n, c)` whose
  length or capacity is a run-time value refuses by name** when `count × element
  footprint` exceeds `arrayFootprintBudget` = 16777216 leaves (one leaf per
  scalar element of `T`), ordered after gc's own `makeslice` panics — where the
  run used to die under the memory cap. The constant-length form refused at the
  same budget already. The same backing still builds unbounded through `append`'s
  spill and the `[]byte(s)` conversion; closing those doors is a recorded
  follow-up. `make(map…, n)` and `make(chan T, n)` allocate nothing in the model
  and are unguarded.

## The contract and your cross-pin check

`comparator.json` now freezes 383 statements: every theorem of `Equations.lean`
(317; 236 of them `@[stepFn_eqns]` simp-set members), the G11 family (27), the
`Choices.consumeAt*` laws (14), the output-fold bridge (6), the `Prefix`/`Finish`
laws (5), `enterFrame_declared`, and the thirteen G16 table-monotonicity
statements (`stepFn_mono`, `prefix_mono`, `finish_aborted_mono`,
`execStmtLoop_ok_mono`, `execStmtLoop_panic_mono`, and the lookup lemmas
including `methodSetCoverage?_mono`). To judge a later GoLean commit against
your pin: at the pin `scripts/contract-export > pin.ndjson`, then at the later
commit `lake comparator --challenge-from-export pin.ndjson`
(`--inadvisably-no-sandbox` inside an agent sandbox). Lake's judge stops at the
FIRST missing or mismatching name, so an export taken before a commit that added
statements reports one name; take a fresh export at or after `bad919b0`.

## Open on our side, waiting on you

- **G10** (context monotonicity, route α): superseded for your purposes by G16's
  per-key `stepFn_mono`/`prefix_mono`; say if route β's measurement still leaves
  a need.
- **A Bool checker** for `TablesKeyed`/`SliceClosed` (~100 lines with its
  soundness lemma): on request; today the clauses are discharged by evaluation
  of the explicit list conditions on your tables.
- **The `stepFn`-level `StateWf` preservation theorem**: not started; your
  per-arm fallback stands unless you report it too costly.
