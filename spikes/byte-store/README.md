# Byte-array store proof spike

[AGENT], 2026-09-06. Bounded BUG-090 design experiment from `b34cee67`.
No runtime caller, default build target, interpreter rule, access event,
choice handler, or B7/C1 contract is changed.

`ByteStore.lean` defines a total candidate branch for
`.index (.base a) index` when the declared root type is exactly
`.array n (.int .uint8)`. Its refinement theorem assumes a found backing
array of length `n` whose members are tagged `uint8` integers in `[0,256)`.
This premise is stated independently of `storeLoc` and normalization.
It constrains neither the rest of the state nor the incoming value.

The candidate checks bounds first, normalizes the incoming element, then
uses the existing `updateCell` to install one array update. It never scans
the old array. The theorem equates the entire `Except Stop ExecState` with
the existing `storeLoc`, so exact errors, their order, the entire returned
state, and untouched data are preserved. Successful stores preserve the
local normality certificate. `storeCertifiedByteElement` threads that
certificate in a subtype; its Prop field is erased and it stores no second
copy of the array.

Raw malformed inputs allowed by the premise are exercised: an unrelated
ill-typed heap cell, incoming integers with mismatched tags, negative and
oversized integers, noninteger input, negative/high indices, and an empty
backing array. An explicit counterexample proves that the unchecked branch
does **not** refine `storeLoc` on arbitrary non-normal backing arrays.
The fallback covers other root shapes; it does not check normality for a
matching byte-array root. Production integration would therefore need a
sound certificate boundary or a fallback chosen before the uncertified
branch is called.

Run the opt-in build and audit from this directory:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 ../../scripts/capped lake build
```

The audit requires ten principal exports and checks every declaration
originating in the spike or its imported GoLean modules, including private
and generated declarations, for axioms beyond the standard classical trio.
The finite challenges are kernel proofs. No native evaluator, admissions,
new axiom, or whole-run success premise is used.

The design findings and reviewed scaled evidence are recorded in
`docs/2026-09-06_byte-store-proof-findings.md` at the repository root.
