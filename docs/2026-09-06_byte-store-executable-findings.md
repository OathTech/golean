# Bounded byte-store executable experiment and consuming variant

[AGENT], 2026-09-06. Follow-up authorized by the sprint coordinator in a
new owned `typed-byte-store-exec` worktree. The original prototype tip
`39add7fd` is preserved; its independent review `8e50c38e` is attached here
as `880c848a`. The O2 terminal/facade's 151 inputs remain frozen.

## Measured scope

The opt-in `ByteStoreBench` executable allocates one canonical byte backing
array, stores integer 1 into every element, then checks the declared length,
actual length, and every element's value and `uint8` tag. It compares the
existing `storeLoc` loop, the certified prototype from `39add7fd`, and the
consuming certified variant described below. Only counts 1,024 and 4,096
are accepted by the executable. Each separate process used the unchanged
16 GiB capped wrapper, three Lean threads, and a 20-second timeout.

| Stores/backing length | Ordinary `storeLoc` | Certified prototype | Consuming certified variant |
|---|---|---|---|
| 1,024 | 1.267441 s, verified | 0.017808 s, verified | 0.043329 s, verified |
| 4,096 | 20.030630 s, timeout | 0.047761 s, verified | 0.017054 s, verified |

These are single direct compiled-Lean measurements on a shared host. They
include wrapper/process startup and final validation. The short runs are
dominated by startup variation and noise; the nonmonotonic consuming times
make a fitted complexity result or speed ratio unjustified. The ordinary
4,096-write run returned exit 124 and no observation. It is not a pass.
No native Go comparison, original 16 MiB case, larger sample, memory-cap
change, or capture-completion claim is part of this experiment.

The original two-mode executable hash is recorded separately. Its source
is retained as `initial-benchmark-source.lean`; the later benchmark adds
the consuming mode and keeps both original loop bodies unchanged. The
final three-mode executable is byte-identical to the executable used for
the consuming measurements, including after the proof-only additions.

## Why a consuming variant is relevant

Inspection of the original prototype's generated C shows the original
state retained while the root cell, `GoValue.array`, and backing array are
extracted and incremented before `setByte`. The old state's root therefore
still holds the backing reference. Avoiding normalization does not remove
this artificial sharing; an array write can still copy the full backing.
The measurements do not isolate this copy cost, but the emitted reference
operations identify a concrete reason it remains.

`ByteStoreConsume.lean` destructures the state, then uses standard Lean
`Array.modifyM` for its root-cell update. The logical definition of
`modifyM` is total. The standard library's existing compiled implementation
temporarily replaces the root slot before invoking its callback, allowing
the old cell and backing value to be consumed when otherwise exclusive.
The prototype introduces no new unsafe implementation or compiler override.

The generated C confirms that pattern: the exclusive state case extracts
the heap without incrementing it, then `lean_array_fset` replaces the old
root slot before its cell callback descends into the backing array. The
exclusive cell and array cases extract their contents without incrementing
them. This removes the first prototype's artificial retained reference.
Actual sharing elsewhere may still require copying; no uniqueness premise
or constant-time guarantee is added to the semantic theorem.

## Exact theorem and boundary

`consumeByteElement_eq` equates the entire `Except Stop ExecState` with the
first prototype whenever the root is a found byte-array cell. It requires
no normality premise. `consumeByteElement_eq_storeLoc` then composes that
equation with the independently stated `BackingNormal` premise from the
original spike. Every integer index and incoming `GoValue` remains
quantified. The exact state, errors, their order, new-value normalization,
and unchanged cells/elements follow through that equation.

`consumeCertifiedByteElement` preserves the local normality certificate;
`consumeCertifiedByteElement_eq_storeLoc` proves equality after erasing
the returned subtype. Its proof uses the original preservation theorem.
The certificate remains an erased Prop field. It supplies no whole-state
well-formedness, alias exclusion, or future-success hypothesis.

The raw consuming helper visibly refuses other root shapes with a
prototype-specific error, and missing roots with an explicit unbound-root
error. These branches are excluded by the certified interface and are
outside its exact refinement theorem. This helper is not a replacement
API for arbitrary raw states. All raw malformed cases allowed by the
local found-canonical-array premise remain covered, including malformed
unrelated cells and arbitrary incoming values. Production routing and
certificate establishment are still open design obligations.

Nothing here changes a runtime caller, executable semantic rule, event
footprint, choice behavior, B7 correspondence, C1 contract, timeout policy,
baseline, or admission restriction. The original per-operation batching
limitation remains: roughly 2,000 writes into a 16 MiB backing array still
revisit that full array unless normalization and artificial sharing are
both addressed. These prototypes do not establish whole-interpreter
performance or close BUG-090.

## Validation

The benchmark executable build passed (19 jobs initially; final incremental
build passed with the measured binary hash unchanged). The complete opt-in
`lake build` passed (13 jobs), including 13 required principal exports,
31 explicitly named kernel theorems, and an origin audit of 3,508
local/imported GoLean declarations. The audit includes all three prototype,
consuming, and benchmark modules; 216 declarations and 140 theorems
including generated ones originate there. It rejects axioms beyond the
standard classical trio. The original production sources are unchanged.

One initial audit attempt exposed missing Lake library ownership for the
executable module, leaving its dependency traversal stale. Declaring
`ByteStoreBench` as a library as well as the executable root repaired that
build dependency; the final audit freshly built all required modules. The
failure log is retained. No semantic proof was weakened.

Commands, raw stdout/stderr, timings, source hashes, measured source
versions, build/audit logs, and generated C evidence are retained under
`docs/evidence/2026-09-06_byte-store-exec`. Independent review of this
consuming extension remains pending; the earlier prototype's acceptance
does not automatically cover it.
