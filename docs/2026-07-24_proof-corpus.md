# The proof corpus: making the calculus answerable to real Go (2026-07-24)

Decision of record (user direction). Companion to
`docs/2026-07-24_sequential-coverage-scoping.md` (the coverage ladder) and
to the non-vacuity gate in `CLAUDE.md`.

## 1. The gap this closes

The differential corpus pins **behavior**: 744 cases, 228 passing, growing
fast because cases are cheap. The proof layer pins **claims**: today that
is essentially ONE program (the golden `incViaCall` walk, in four
statement shapes) plus the `while (x==0){x=x+1}` witness. So the calculus
is known to work on two toys, and every new feature widens the behavioral
surface without testing whether we can still *prove* anything over it.

That asymmetry is the north-star risk in miniature. `etcd-io/raft` will
not be reached by a calculus whose laws each have a witness but which has
never been asked to compose them over an idiomatic function.

## 2. What a proof corpus is

A tracked set of **(differential case id → proven surface theorem)**
pairs. The programs come from the DIFFERENTIAL CORPUS — already canonical
Go, already oracle-validated — so a proof-corpus entry proves something
about a program we independently know the behavior of. That pairing is
the point: the differential says *what the program does*, the proof says
*what we can establish about it*, and both are about the same file.

The theorem should be a **surface judgment** — `GoFuncSpec` where the
shape allows (the engineer-readable form: "`f(args)` needs no heap and
returns 2"), else `GoSpec`/`GoTriple`/`GoInvariant`.

## 3. Selection criteria (this is NOT a mirror of the coverage corpus)

Proofs cost orders of magnitude more than corpus cases; a proof corpus
that chased coverage would stall the project. Entries are chosen to
stress the calculus, not to tile the language:

1. **Composition over breadth** — prefer one function that combines a
   loop, a call, and a conditional over three that each isolate one.
   Per-law witnesses already cover isolation; nothing else covers
   composition.
2. **Idiom over minimality** — write the program the way Go is actually
   written (early returns, `err` checks once errors exist, accumulator
   loops). A calculus that only proves un-idiomatic code is not useful
   for real Go, which is the whole claim being tested.
3. **North-star shapes** — as features allow, prefer miniatures of raft:
   a state-machine step function, a bounds-checked log append, a quorum
   count over a slice.
4. **One entry per feature AREA, not per feature** — the unit is
   "closures", "switch", "defer", not each sub-form.

## 4. Gating

Each entry is referenced from `proofs/Audit.lean` exactly as the existing
non-vacuity witnesses are (`example := @…`), so **deleting or breaking a
proof-corpus theorem fails the build**. The manifest below is the tracked
record; `scripts/ci` needs no new step because the Audit gate already
runs in-build.

## 5. Manifest

Format: `case id — theorem — what it stresses`. Seeded with what exists,
so the record starts honest rather than aspirational.

| differential case | theorem | stresses |
|---|---|---|
| `pointers/inc-via-call` | `GoLean.Surface.goldenFuncSpec` | call/frame protocol, pointer mutation through a callee, the D2-proper result read |
| `pointers/inc-via-call` | `GoLean.Surface.goldenInvariant` | per-step invariance over a whole call (what a triple structurally cannot say) |
| `control-flow/while-eq-single-iteration` | `GoLean.Iris.wp_while_eq_once` | the Löb loop rule with a real machine-walked condition |
| `panic-recover/recover-direct` (core shape; eval-pin `GoCore recover catches panic-path defer`) | `GoLean.Iris.wp_recover_catch_seven` | **defer + panic + recover composed**: registration, unwinding, the panic-path drain, the recover continuation walk, a write through a captured pointer, the cancelled unwind — the W3/unwinding entry. Added 2026-07-26 (proof-corpus catch-up arc); the program is the hand-authored core shape sharing the case's structure (closure capturing the named result, recover guarding the write), like the `wp_while_eq_once` precedent. |
| `panic-recover/recover-direct` (**PINNED ACTUAL LOWERING** — `GoldenRecover.recoverLowered`, `scripts/check-golden`'s second program) | `GoLean.Surface.recoverFuncSpec` | the same composition at `GoFuncSpec` strength over decoded(frontend(source)): block scopes, recover's value routed through the `$c0` interface-typed temporary (init + assign, the recover continuation walk crossing the assign frames), the cell-read `!= nil` guard, and the FALL-path value frame exit (`wp_frame_fall_int` — Go's "returns normally" after recovery; no `return` anywhere in the callee). Paid 2026-07-30 (slice B); retires the owed frontend-lowering-twin row below. |
| `quorum/committed-index-real` (**PINNED ACTUAL LOWERING** — `GoldenQuorum.quorumLowered`, `scripts/check-golden`'s third program) | `GoLean.Iris.wp_call_dynamic_enter_ackedIndex` | **interface DYNAMIC DISPATCH frame entry on real etcd-io/raft code**: the callsite names the anchor `main.AckedIndexer.AckedIndex`, the receiver arrives as an interface box of dynamic type `.defined main.mapAckIndexer`, and one step redirects to `main.mapAckIndexer.AckedIndex` with the receiver unboxed, binds receiver+`id` normalized at their declared (named) types and defaults `$res0 : main.Index`/`$res1 : bool`. Every premise computed against the pin; only the three ghost pins external. Landed 2026-07-31 (phase-4 types-pin slice) together with the general law `wp_call_dynamic_enter₂`. |
| `quorum/committed-index-real` (same pin) | `GoLean.Iris.wp_map_lookup_ackedIndex` | the REAL `idx, ok := m[id]` comma-ok read of `main.mapAckIndexer.AckedIndex`, now FAITHFUL to the lowering's `.defined main.Index` target cell (the recorded `uint64` divergence is closed by the `σ.types` pin). |
| `quorum/committed-index-real` (same pin) | `GoLean.Surface.quorumAckedIndexFuncSpec2` | **W1 PAID — the first multi-result function spec.** `main.mapAckIndexer.AckedIndex` on a concrete one-entry receiver, at `GoFuncSpec2` strength over the pinned lowering: the caller's two cells receive `(12, true)`, in any admissible heap, beside any frame. Stresses the whole two-result protocol end to end — the two-target/two-argument call operand walk (`wp_call_target_next`/`targets_done_arg`/`arg_next`), the STATIC 2-param/2-result frame entry (`wp_call_enter₂` + witness `wp_call_enter_ackedIndexImpl`), `wp_init` at the DEFINED type `main.Index`, the comma-ok read, two stores at a defined type, and the TWO-result frame EXIT (`wp_frame_return₂` on the new `wp_read₂_store₂_step` core). Vacuity guard same commit: `quorumAckedIndexPre_satisfiable`. Landed 2026-07-31 (phase-4 slice 5); the phase-0 statement it replaces was FALSE (arity-stuck), which is recorded at the statement. |
| `quorum/committed-index-real` (same pin) | `GoLean.Quorum.isCommittedIndex_oneKnown` | the MATH half of the tier-1 claim on the one-voter instance: `committedIndexRef [1] ackedOneKnown = 12` (`rfl`) upgraded to the declarative `IsCommittedIndex` by the proven `committedIndexRef_meets_spec`, with the negative twin at 11. **The machine half is now PAID** — see the row below. |
| `quorum/committed-index-real` (same pin) | `GoLean.Surface.quorumOneKnownFuncSpec` / `quorumOneKnownMeetsSpec` | **THE ARC'S NAMED GOAL, PAID (2026-07-31, phase-4 summit).** `committedOneKnown()` — the pinned lowering of the real etcd-io/raft driver — returns `12` at `GoFuncSpec` strength, and the same discharge restated with the DECLARATIVE quorum spec as its postcondition (`IsCommittedIndex [1] ackedOneKnown n.toNat`). The walk (`wp_oneKnownCall → wp_oneKnown_body → wp_run_body → wp_committedIndexCall → wp_committedIndex_body`) crosses: two `make(map…)`s that ALLOCATE inside the apply step and two `m[k]=v` writes, three frame entries at two arities, `len(c)` on a named map type, `var stk [7]uint64` and its reslice `stk[:n]`, the NONDETERMINISTIC map range, interface dynamic dispatch, comma-ok, a store THROUGH a slice index into the backing array, `slices.Sort`, and the `n - (n/2+1)` readout. First-order readout `quorumOneKnownReturnsTwelve` + run-conditioned negative twin `quorumOneKnownNotEleven`. **Scope: n = 1** (degenerate range nondeterminism, reslice branch); the 3-voter widening is owed. |
| `quorum/committed-index-real/three-all` (same pin) | `GoLean.Iris.wp_map_iter_inv` (applied) / `GoLean.Iris.GoldenQuorum.wp_ci_loop` | **the n-VOTER voter loop, order-insensitively.** `wp_ci_loop` walks `var i int; i = n-1; for id := range c { … }` for an ARBITRARY voter list and an ARBITRARY acked function, discharging the whole nondeterministic range through the inductive range rule with the invariant `∃ ks filled, ⌜rem = cfgSnapshot ks ∧ ks ⊆ ks₀ ∧ (ks.map ack ++ filled) ~ ks₀.map ack⌝ ∗ …` — one `List.Perm` carrying the entire order-insensitivity. Its body obligation `wp_ci_range_body` is one iteration at an arbitrary voter, arbitrary acked snapshot and arbitrary scratch-array shape, writing at a SYMBOLIC index (the first such walk in the project). Landed 2026-08-01, proof-automation arc phase 3. |
| `quorum/committed-index-real/three-all` (same pin) | `GoLean.Surface.quorumThreeAllFuncSpec` / `quorumThreeAllMeetsSpec` | **THE 3-VOTER RUNG, PAID (2026-08-01, proof-automation arc phase 3).** etcd's own `majority_commit.txt` row — `committedThreeAll()` over `MajorityConfig{1,2,3}` with `mapAckIndexer{1:12, 2:5, 3:6}` — returns `6` at `GoFuncSpec` strength, restated with the declarative spec (`IsCommittedIndex [1,2,3] ackedThreeAll`). What n = 1 could not test and this does: the map range has `3! = 6` iteration orders and NONE is enumerated (one generic iteration + the permutation invariant); `slices.Sort` does real work over an array whose contents are known only as a MULTISET, collapsed by `mergeSort_eq_of_perm`; and `pos = n - (n/2+1)` lands at a nonzero index (1), so the readout is the middle element, not the only one. First-order readout `quorumThreeAllReturnsSix` + run-conditioned negative twin `quorumThreeAllNotTwelve` (at `12`, the largest acked index). **Owed from this rung:** the `make([]uint64, n)` fit branch (still witness-only), the general-`n` sort/readout, and the ∀-config theorem itself. |


**Owed, in ladder order** (each becomes an entry when its rung lands; a
rung is not "finished" until its entry exists, though slices need not
block on it):

- ~~W1 tuples — a multi-result function proved at `GoFuncSpec`~~ —
  **PAID 2026-07-31** (`quorumAckedIndexFuncSpec2`, manifest row above:
  two-result frame entry AND exit, at `GoFuncSpec2` strength over the
  pinned real lowering). Prediction 3 confirmed twice over: the arity
  bound where predicted, and BOTH the entry and exit laws are
  arity-specialized (2/2) — the n-ary widening (list-indexed allocation
  and store cores, `wp_alloc_step₄`'s scope note) is the residue and is
  recorded as owed there. Also owed from this rung: the FALL-path
  two-result exit (`wp_frame_fall`'s analogue for two results) — Go
  reaches it for a multi-result function that ends without `return`.
- ~~NEW (2026-07-31): the quorum DRIVER walk~~ — **PAID 2026-07-31**
  (`quorumOneKnownFuncSpec`, manifest row above). The residue it leaves,
  recorded rather than dropped:
  - ~~**the 3-VOTER walk.**~~ **PAID 2026-08-01** (`quorumThreeAllFuncSpec`,
    manifest row above). It did test what it was predicted to test: the
    range law composes when the order genuinely varies (one generic
    iteration, no order enumerated), the sort needed a NEW general fact
    (`mergeSort_eq_of_perm` — the machine's sort is order-blind) because
    the array contents are determined only as a multiset, and
    `pos = n - (n/2+1)` at a nonzero index made the readout a real
    selection. Residue: the general-`n` sort and readout (the machine's
    `sortSlice` at a symbolic length is not yet characterized), and the
    `∀`-config theorem.
  - **the `make([]uint64, n)` branch of the fit test**, exercised only by
    the law witness (`wp_make_slice_c2`), not by a composed walk.
  - **the unconditional negative twin**
    (`quorumOneKnownNotEleven_statement`): not refutable from the triple,
    since a `GoTriple` is vacuous on a non-terminating program; refuting
    it needs an EXHIBITED terminating run (kernel evaluation of the
    interpreter over the whole pinned program). The run-conditioned twin
    is proven.
  - `newValue` and `appendSlice`'s spill path — the other two allocating
    wide ops; the core (`wp_stmt_op_apply_alloc_store`) covers them, no
    walk forces them yet.
- W2 switch — `control-flow/switch-basic`'s `classify`; stresses the
  if-chain walk and whether case dispatch composes with early return.
  (The `wp_breakable_*` laws landed 2026-07-26; the composed entry
  remains owed.)
- W5 closures — `functions/closure-share`; stresses reasoning about a
  captured cell aliased between two callees (the first genuinely
  separation-logic-shaped obligation in the corpus). (The
  `wp_call_value_*` entry laws landed 2026-07-26.)
- W3 defer — PARTIALLY PAID 2026-07-26 by `wp_recover_catch_seven`
  (composition incl. the panic path); `defer/multiple-lifo`'s
  LIFO-ordering entry remains owed.
- W4 structs/arrays — a bounds-checked accumulator over an array.
- ~~NEW (2026-07-26): the frontend-LOWERING twin of
  `wp_recover_catch_seven`~~ — **PAID 2026-07-30** (`recoverFuncSpec`,
  manifest row above; the golden-pin mechanism now carries two programs).

## 6. What this will find (predictions, recorded so they can be wrong)

Stated in advance so the exercise is falsifiable rather than
self-congratulatory:

1. The first non-golden entry will need laws that do not exist yet
   (`wp_call_value_enter` for closures; a multi-result frame exit). That
   is the intended signal, not a setback.
2. Walk plumbing will be the bottleneck before any law is *wrong* — the
   `iapply … fupd_intro; inext; …` chains are already the bulk of every
   proof, and they grow linearly with program size. If proving a
   twenty-line function needs a thousand-line walk, the calculus needs a
   tactic or a bind-form combinator, and we will have learned that from a
   real program rather than from theory.
3. `GoFuncSpec`'s v1 shape (unary int result) will bind first — the
   `(T, error)` widening is likely the first forced generalization.
