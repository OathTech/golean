# Backlog: scalable structure for the proof layer (2026-07-20)

`proofs/GoLeanProofs.lean` is ~1,150 lines rolling six concerns together —
past the point where one file is defensible (raised in review during arc
`slice-call-frame`). Deliberately **backlogged rather than split ad hoc**:
the split should serve the *eventual* scalable structure, not just today's
contents.

## Starting-point proposal (from the review discussion)

```
proofs/GoLeanProofs.lean        root: doc + imports (lib target unchanged)
proofs/GoLeanProofs/Lang.lean       Config ⇒ Iris Language wiring
proofs/GoLeanProofs/HeapBridge.lean heapToMap bridges + HeapWf + pure store/alloc facts
proofs/GoLeanProofs/Ghost.lean      GoCoreGS + state interpretation
proofs/GoLeanProofs/PureSteps.lean  pure control-step laws (seqn / seq_done / frame_fall)
proofs/GoLeanProofs/Store.lean      store cores, laws, ExprR inversion helpers, witnesses
proofs/GoLeanProofs/Call.lean       call law + cross-frame witness
proofs/GoLeanProofs/Adequacy.lean   functor bundle, go_adequacy, end-to-end witnesses
```

## Things the design must handle (found while scoping — don't lose these)

- **Gate interactions.** The Audit sweep is module-scoped (root name starts
  with `GoLean`) — `GoLeanProofs.*` submodules are covered automatically ✓.
  But `scripts/ci`'s proofs-file coverage gate globs only `proofs/*.lean` —
  **a subdirectory module would dodge it** (the tamper-audit F2 class). The
  split must ship with the gate upgraded to a transitive-import-closure check
  from the build roots (`Audit`, `GoLeanProofs`), recursively over
  `proofs/**/*.lean`, module names path-derived.
- **`private` boundaries.** Several helpers are `private` but genuinely
  reusable across the split (`exprR_*_det` inversions used by both Store and
  Call witnesses; `intKind_beq_self`). Splitting forces a deliberate
  public-lemma surface — good, but decide naming/placement once.
- **Growth axes to plan for:** more WP laws per construct (a `Laws/` family?),
  more witnesses (`Witnesses/`? or law+witness co-located per the non-vacuity
  gate's ship-together rule — co-location is probably right), the
  correspondence proofs when item 6 lands (`proofs/` vs core `GoLean/`
  placement — Correspondence.lean currently lives core-side), and eventually
  per-target-program specs (slice, quorum, raft) which should NOT live in the
  law library.
- **Relation to task #20** (Lean module-system migration, backlogged): do the
  split in classic style now; don't couple the two.
- **Witness/law co-location rule:** the CLAUDE.md non-vacuity gate says law
  and witness ship together — the structure should keep them adjacent so the
  gate stays easy to check by eye.

## When

Natural slot: at the `slice-call-frame` arc boundary (post-merge, pre-arc-3) —
a pure mechanical commit on a fresh branch, gates green before/after, no
semantic changes mixed in.
