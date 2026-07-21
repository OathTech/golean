# Backlog: scalable structure for the proof layer (2026-07-20)

`proofs/GoLeanProofs.lean` is ~1,150 lines rolling six concerns together —
past the point where one file is defensible (raised in review during arc
`slice-call-frame`). Deliberately **backlogged rather than split ad hoc**:
the split should serve the *eventual* scalable structure, not just today's
contents.

## Design of record (2026-07-21 — supersedes the starting-point sketch)

Two distinct questions, answered separately:

### (1) File decomposition: four STRATA, laws by CONSTRUCT

```
proofs/GoLeanProofs.lean               root: doc + imports (lib target unchanged)
proofs/Audit.lean                      the gate (root; single file until it hurts)

# Infrastructure — stable; changes are deliberate design events
proofs/GoLeanProofs/Lang.lean          Config ⇒ Iris wiring (ToVal, PrimStep, Language)
proofs/GoLeanProofs/HeapBridge.lean    heapToMap bridges, HeapWf, alloc eqns, pure store facts
proofs/GoLeanProofs/Ghost.lean         GoCoreGS, state interpretation, IrisGS
proofs/GoLeanProofs/Lifting.lean       the store/alloc step cores (de-privatized, marked
                                       internal — the "one step + ghost update" engines)
proofs/GoLeanProofs/Inversions.lean    exprR_*_det + intKind facts (de-privatized; shared)

# Laws — grows ONE FILE PER CONSTRUCT FAMILY; law + witness CO-LOCATED
# (the non-vacuity ship-together rule becomes a per-file visual invariant)
proofs/GoLeanProofs/Laws/Control.lean  wp_seqn/seq_next/seq_done/seq_return/return/frame_fall
proofs/GoLeanProofs/Laws/Assign.lean   wp_assign, wp_deref_store, wp_store_via_ptr,
                                       wp_assign_var + witnesses
proofs/GoLeanProofs/Laws/Init.lean     wp_init + witness
proofs/GoLeanProofs/Laws/Call.lean     wp_call_unary, wp_call_nullary_ret,
                                       wp_frame_return + witnesses

# Specs — grows ONE FILE PER VERIFIED TARGET PROGRAM
proofs/GoLeanProofs/Specs/Slice.lean   incFunc/mainBody/sliceProg, wp_inc_call,
                                       wp_main_*, slice_adequate

proofs/GoLeanProofs/Adequacy.lean      GoCoreGpreS/GoCoreS/go_adequacy
                                       (+ future go_heap_adequacy)
```

Rationale: this week's growth pattern shows new work arrives as
construct-law-families and program-specs, not infrastructure (which changed
only at deliberate design events — the CEK reshape, the state-interp
upgrade). The frequent operation (add a law family / add a spec) must be a
new-file operation touching nothing else. Future arrivals slot cleanly:
`Laws/Loop.lean` (while + invariant), `Laws/Map.lean`, `Specs/Quorum.lean`.

### (2) proofs/ folder organization as the project grows

1. **`proofs/` = the Iris-dependent world; Iris-free stays core-side.** The
   separate Lake package is the trust-story boundary: everything needed to
   *believe* an end-state theorem (Rel, Eval, Correspondence — incl. item 6's
   correspondence proofs when they land, which are Iris-free) lives in
   `GoLean/`; `proofs/` is pure methodology and dissolves via adequacy.
2. **The four strata are the growth axes.** Concurrency infrastructure (post-
   F4 decision) = a deliberate infrastructure event; raft-ladder targets =
   routine `Specs/` additions; adequacy variants extend `Adequacy.lean` until
   it earns a directory; `Audit.lean` likewise splits per-stratum only when
   unwieldy (root importing all gate files).
3. **Gates make the structure self-enforcing:** the import-closure ci check
   (landed 2026-07-21) makes an unwired file a loud failure; the module-scoped
   sweep audits whatever is wired; non-vacuity is checkable per-`Laws/` file
   by eye. Structure the gates enforce doesn't rot.


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
