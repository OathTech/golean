# Exact in-place byte append optimization

[AGENT], 2026-09-06. Candidate based on `c969079a`; independently reviewed
byte-store prototypes are the source of the local store lemmas. This lane
addresses the actual `strings.Repeat` → `Builder.WriteString` → in-place
`appendSlice` path. It does not close BUG-090 or the original B7 capture.

`storeLoc` normalizes a declared array's entire contents on each element
write. Its `normalizeListWith` additionally builds each result by prepending
a singleton array to the recursive tail. The candidate avoids both costs
within one append: a structurally recursive accumulator is proved equal to
the entire old normalizer, and the first ordinary successful normalization
establishes a local byte-backing certificate. Remaining element stores use
the reviewed consuming update and preserve that erased certificate.

The initial array may be malformed or noncanonical. The first store still
performs its bounds check before normalization; overwritten malformed data
may be repaired and untouched malformed data still refuses in left-to-right
order. Missing roots, payload cells, other declared types, nested location
paths, empty arrays and nil bases retain the original behavior. Incoming
values and indices are unrestricted. The final helper theorem has no state
invariant premise:

```
appendValuesFast state slice values = appendValuesOriginal state slice values
```

`GoLean.GoCore.Machine.applyStmtOp_byteAppend_exact` strengthens this to
the whole `Except Stop (ExecState × Choices)` of the actual operation for
every raw state, operation, operands, target count and choice tape. Its
reference body is copied from `c969079a` with only the definition name
changed. The single production caller change replaces the in-place append
loop; the relation shares that same operation. The existing state-domain
preservation proof explicitly rewrites through the exact helper equation.
No choice consumption, state output, error, memory access granularity,
event footprint, allocation policy or support boundary changes.

The production lemmas in `GoLean/GoCore/ByteArrayStore.lean` derive from
`typed-byte-store-proof` at `39add7fd` and `typed-byte-store-exec` at
`68590160` (consuming extension independently accepted at `631b883f`).
The prototype's `ByteNormal` and `BackingNormal` state byte tags, ranges
and length independently of the executable normalizer. The new loop's
public equality needs neither those premises nor whole-state well-formedness.
The former prototype-specific missing-root refusal is reachable only inside
the locally certified consuming interface, whose theorem excludes it; the
unrestricted caller keeps the ordinary fallback.

Initial fresh real-caller results on the same emitted native artifact:
the previous executable took 1.593 seconds at 64 repetitions of a sixteen-byte
string and timed out after 20 seconds at 256. The candidate took 0.128,
0.132, 0.146, 0.194 and 0.762 seconds at counts 64, 256, 1024, 4096 and
16384. Count 65536 (1 MiB output) took 9.857 seconds; count 131072
(2 MiB output) timed out after 20 seconds. These are single shared-machine
measurements including startup and wire decoding. Completed observations
are normal integer lengths; timeouts have no observation and are not passes.

The remaining cost is material: each Builder call establishes its local
certificate anew, and Builder's `String` conversion also materializes the
growing visible slice. The original 16,777,232-byte output uses roughly
2058 writes and remains unrun on this candidate. Microbenchmarks and the
1 MiB completion do not establish its capture. Reusing certificates across
machine steps would need an explicit validity-preserving cache/representation
with exact erasure for arbitrary raw states and every heap mutation, rather
than asserting that existing `StateWf` guarantees canonical bytes. That is
a distinct design obligation, not implicit authorization to strengthen the
semantic domain.

Validation so far: default `lake build` passed (182 jobs), the exact
operation theorem and six malformed-state/order challenges passed, and a
post-import audit checked 5491 local/GoLean/test declarations against the
standard classical trio. Warning cleanup subsequently rebuilt the proof
module and test suite without warnings. Full CI/differential validation,
compiling poison controls, final evidence sealing and independent candidate
review are still pending. All runs used 16 GiB, three Lean threads and
two differential workers where applicable. Initial proof/build failures
and the missing dependency setup failure are retained in lane artifacts.
