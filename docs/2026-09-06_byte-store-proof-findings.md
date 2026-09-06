# BUG-090: local normality can eliminate repeated backing normalization

[AGENT], 2026-09-06. Independent bounded design subtask from the active
typed-consumer sprint coordinator. Base `b34cee67`; implementation lives
only in the opt-in `spikes/byte-store` package. The terminal/facade lane's
151 frozen source inputs are unchanged.

The proof establishes that one byte-element store can avoid normalizing the
entire backing array **when a local canonical-byte certificate is already
available**. It does not establish that current interpreter callers have
that certificate, change a runtime caller, measure a speedup, close BUG-090,
or complete the original large case's observation capture.

## Independent review of the scaled packet

Reviewed commit `380753b9`, packet
`docs/evidence/2026-09-06_bug090-scaled-profile` in the I1 lane, whose source
base is `798e9c76`. The read-only checker in this evidence directory checks
all eight recorded source hashes against their historical git blobs, checks
the pinned probe against the archived source, checks archived commands,
parses the actual Go results independently, and compares all completed
model JSON objects including empty output, status, schema, and typed values.

All twelve completed scaled calls agree with actual Go. The two timeouts
(`StoreAll-4096`, `RepeatLen-256`) have no observations and remain failures
to complete. The recorded timings distinguish cheap allocation, growing
cost for one store, and strongly growing cost for repeated stores. These
single shared-host samples are consistent with the source mechanism; they
are not an isolated CPU profile, fitted complexity result, new run, or
full compiler/dependency certificate. The archived executable hash is
recorded but was not independently rebuilt or rerun for this review.

The current heap is `Array HeapCell`. The historical BUG-090 association
list explanation is stale for this source. `storeLoc` updates one array
element and recursively writes its root; root storage calls
`normalizeValueForTy`, whose array arm traverses the whole array.
`Machine.applyStmtOpCore`'s copy arm and `Machine.applyStmtOp`'s in-place
append arm repeatedly call `storeLoc` for individual elements. These are
concrete remaining costs after the dense-heap change.

## Exact prototype contract

`ByteNormal v` means that `v` is exactly `.int z .uint8`, with
`0 ≤ z < 256`. `BackingNormal n values` means `values.size = n` and each
member satisfies `ByteNormal`. The main theorem assumes only a root lookup
of `.value (.array n (.int .uint8)) (.array values)` and this local premise.
Neither definition mentions the desired store result, future execution,
the normalizer, or a whole-state well-formedness judgment.

`storeByteElement` first performs the existing `arrayIndexNat` and option
bounds checks. It then normalizes the new value alone and installs the
single array update through the existing `updateCell`. Other cell shapes
fall back to the existing indexed `storeLoc`. The matching byte-array
branch performs no normality scan; use without a certificate is outside
its refinement theorem.

`storeByteElement_eq_storeLoc` equates the entire `Except Stop ExecState`
for every integer index and incoming `GoValue`. Thus it preserves:

- negative and high-index panic text, and bounds failure before incoming
  value normalization;
- normalization of negative or oversized integers and mismatched integer
  tags, plus the exact type error for nonintegers;
- all successful state fields, the root's declared type, untouched backing
  elements and heap cells, and heap bounds;
- raw unrelated malformed heap cells or type environments allowed by the
  local premise. Aliases are not excluded by that premise.

`normalizeList_set` and `normalizeArray_set` prove the key equation: all
old elements are fixed points, so normalization after one replacement
equals normalizing just the replacement and setting it. These proofs also
retain the incoming error; they do not assume successful normalization.

`setByte_preserves` and `storeByteElement_preserves` preserve the local
certificate on success. The subtype in `storeCertifiedByteElement`
contains the state and an erased Prop certificate, with no second array
field. Its erased result is also proved equal to the existing `storeLoc`.
This demonstrates a possible proof-carrying interface without an executable
scan on every operation.

The kernel challenges include a raw unrelated ill-typed cell, arbitrary
incoming values, negative and oversized integer wrapping, mismatched tags,
noninteger type errors, both index failures, and empty backing arrays.
Wrong length and a noncanonical byte are excluded by the premise. A
separate kernel counterexample proves that unrestricted refinement is
false: storing index 1 of `[256:uint8, 0:uint8]` leaves the first element
256 in the candidate but normalizes it to 0 in ordinary root storage.
Even an overwritten malformed old member is outside this sufficient
premise; no claim of maximal permissiveness is made.

## What remains before an executable repair

A future integration must establish normality at creation or an audited
boundary and preserve it across every operation that may change that
backing array. The local preservation theorem covers this one indexed
store. It is not a whole-machine invariant, certificate for all allocations,
bulk append/copy theorem, or routing rule for raw uncertified states.
Nested locations, named array aliases, other element kinds, and representation
migration are outside this prototype's specialized theorem.

Per-operation batching alone is insufficient to remove repeated whole-array
work. The pinned `strings.Repeat` grows a Builder, doubles its written
prefix up to an 8 KiB chunk, then appends chunks until completion.
For the corpus input of a 16-byte string repeated `(1 << 20) + 1` times,
the source-level loop performs 2,058 Builder writes for 16,777,232 bytes.
Normalizing that full backing once per write would still visit
34,527,543,456 elements (about 32.16 Gi elements). This is arithmetic over
the source algorithm, not a new model execution or measured memory traffic.

Threading normality removes those normalizer passes in the proved branch.
It does not prove constant-time array storage: Lean's persistent arrays may
copy when shared, the array contains `GoValue` objects, and bounds lookup,
allocation, source copying, decoding, and other interpreter costs remain.
No C1 access footprint, semantic step granularity, choice consumption,
driver observation, budget, timeout, or cap is changed here.

## Validation and evidence

The original default `lake build` passed (170 jobs). The opt-in package
build passed (11 jobs), including 28 explicitly named kernel theorems and
its audit of 172 local declarations, 129 local theorems including generated
ones, and 3,464 local/imported GoLean declarations. Ten principal theorem
exports are required explicitly. Axioms beyond the standard classical trio
are rejected across those declarations, including private/generated ones.
All Lean/Lake commands used the unchanged 16 GiB capped wrapper and three
Lean threads. The spike uses the repository's Lean `v4.32.2` pin.

No fresh Go differential timing or giant-case run was performed: runtime
source and callers are byte-identical to the base. The independent archived
Go/model comparison and the exact kernel store refinement serve different
purposes and are reported separately. Proof-development failures, build
logs, source hashes, named theorem output, and the read-only scaled packet
checker are retained under
`docs/evidence/2026-09-06_byte-store-proof`. The coordinator's independent
review remains pending.
