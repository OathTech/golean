/-!
# `Platform` — the gc layout pins as ONE named parameter (design-hygiene A5)

Every implementation-specific number the machine realizes lives here, as
a field of one record, instantiated ONCE (`platform := gcAmd64`). Before
A5 (2026-09-04) the same numbers were four constants and one function
spread over `Value.lean` and `Ops.lean`, each with its own envelope prose;
now the envelope statements sit on the instance and the machine reads the
fields. The re-envelope obligations the latitude inventory records (R1,
R16) become INSTANTIATION — a second `Platform` value — not surgery.

What is parametric TODAY: `tySizeAlign` (Ops.lean) takes a
`Platform` — except its four `.sync` arms (Ops.lean), which are the
amd64 `unsafe.Sizeof` constants and ignore `p` (owed for B7); `maxAllocBytes`/`chanHeaderBytes`/`intExclusiveUpperBound`
and `IntKind.bits?` read `platform`. What is NOT yet threaded: the
`ExecState` carries no platform field and `IntKind.normalize` reads the
constant, so theorems are stated at `platform` (= `gcAmd64`), not
`∀ p : Platform` — threading a field through `ExecState` touches every
state-shape lemma and is deferred to the `ProgramCtx`/`Store` split
(review B7), where the state gains its context record anyway. [AGENT]
-/

namespace GoLean.GoCore

/-- The implementation-specific layout parameters of a Go target. -/
structure Platform where
  /-- Width of `int`/`uint` (and `uintptr`) in bits — spec#Numeric_types
  makes it "either 32 or 64 bits" (latitude inventory R1). -/
  intBits : Nat
  /-- The machine word / pointer size in bytes (go/types `Sizes.WordSize`). -/
  wordBytes : Nat
  /-- The maximum alignment (go/types `Sizes.MaxAlign`). -/
  maxAlign : Nat
  /-- The maximum allocatable size in BYTES (`runtime.maxAlloc`; inventory
  R16). -/
  maxAllocBytes : Nat
  /-- The channel header size (`runtime.hchanSize`; R16's channel half). -/
  chanHeaderBytes : Nat
  deriving Repr, BEq

/-- The exclusive upper bound of `int`: `2^(intBits-1)`. gc's `growslice`
panics `len out of range` when the new length overflows `int`
(slice.go:191) — the same message as the byte-size check. -/
def Platform.intExclusiveUpperBound (p : Platform) : Nat := 2 ^ (p.intBits - 1)

/-- **THE PINNED PLATFORM — gc on linux/amd64**, the oracle host's
realization (go1.26.5), shared by the frontend's go/types `Sizes` and the
negative lane's acceptance.

* `intBits = 64` — PINNED LATITUDE (inventory R1; register extension #6):
  the spec's envelope is {32, 64}; the 64-bit member is pinned here.
  TRANSFER CAVEAT: any claim about wrap/overflow at `int`/`uint`
  boundaries transfers only to 64-bit targets; a 32-bit conforming
  implementation is outside this singleton. Re-envelope = a second
  `Platform` (width across normalize/conversions/frontend Sizes/
  negative-lane acceptance), XIMPL-gated — blocked in practice on any
  32-bit oracle lane.
* `wordBytes = 8`, `maxAlign = 8` — go/types `gcSizes` for amd64
  (`deps/go/src/go/types/gcsizes.go`), the R16 pin's LAYOUT half:
  `make([]T, n)`'s byte size is `sizeof(T) × n`, so element layout places
  the panic boundary (`[]byte` from 2^48+1, `[]int64` from 2^45+1,
  `[]struct{int64; byte}` — 16 bytes with padding — from 2^44+1).
* `maxAllocBytes = 2^48` — PINNED LATITUDE (inventory R16; fidelity
  decision 5(b), [USER] 2026-08-31: "the deterministic maxAlloc panic
  class modeled"). gc: `runtime.maxAlloc = 1 << heapAddrBits`
  (malloc.go:220), `heapAddrBits = 48` on linux/amd64; the check is STRICT
  (`mem > maxAlloc`): exactly 2^48 bytes passes the check and then fails
  to ALLOCATE (`fatal: out of memory` — the true-OOM class, NOT modeled;
  doctrine register #7 rider / discrepancy D-001). Plausible envelope: any
  positive bound, tied to `intBits` (32-bit gc realizes `2^32 - 1`, and on
  32-bit the slice panic is live only for element sizes ≥ 3). Probe
  matrix: `docs/evidence/2026-09-02_t5-maxalloc-probes/`. TRANSFER
  CAVEAT: a claim that a given `make` panics (or does not) transfers only
  to 64-bit gc-layout targets.
* `chanHeaderBytes = 112` — gc's `hchanSize` (runtime/chan.go:30: 7 words
  + elemsize/closed + 2 waitq + bubble + lock on amd64; 64 on 386);
  `makechan` checks the BUFFER against `maxAlloc - hchanSize` (chan.go:87),
  so the channel threshold sits 112 bytes below the slice threshold
  (probe: `make(chan byte, 1<<48-111)` panics, `1<<48-112` attempts the
  allocation). -/
def gcAmd64 : Platform :=
  { intBits := 64, wordBytes := 8, maxAlign := 8
    maxAllocBytes := 2 ^ 48, chanHeaderBytes := 112 }

/-- THE one instantiation the machine reads. Every pinned number in the
core comes through this definition; a re-envelope changes it here. -/
def platform : Platform := gcAmd64

end GoLean.GoCore
