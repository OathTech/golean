# Independent I1 package boundary review

[AGENT] 2026-09-06, recovery_customer. **PASS for the bounded repaired Lean
metadata boundary at frozen v2**, after two blocking v1 findings were
reproduced and repaired. Root retains final acceptance. This is not an
independent full producer, executable corpus or slow-certification review.

The v1 32-input manifest is
`4b478c9f920a6a60a46fbe5f3c882e218f5bce4f8c6df9e8aa26884dc2e1dcb9`;
the repaired v2 manifest is
`077e6267fadbb42a2c417730d294e5fdc4fac62b86d1b0b98502b19668aea235`.
I checked all 3,917 v1 full-source hashes against exact Git base `7ac3eb46`
plus its 32 frozen overrides. Only five of those inputs change in v2:
the package adapter, its Lean test, the Go fixture test, Python package gate
and design note. The unchanged producer and runtime bytes remain bound by
that base and snapshot. Both 32-file source snapshots are retained here.

## Findings and dispositions

**I1-PKG-R1: interface completeness could reuse an index.** Two native
interface TypeDefs named `Dup` and two interface bindings both naming index
0 decoded successfully, leaving the second final table entry unbound.
V1 compared only the resulting identity list. The exact minimal input and
fresh result are retained. V2 checks unique, nonempty native type identities
and exact ordered `(index, identity)` pairs. Independent byte-input tests
reject the original input and the variant with distinct indices but duplicate
native identities. This finding is resolved in v2.

**I1-PKG-R2: private interface identities were collapsed to bare names.**
Fresh Go/types construction and independent parsing/type-checking of actual
three-package Go source both establish that embedding `p.I` and `q.I` can
produce distinct private methods `p.m` and `q.m`. V1's positive type decoder
retained both identities, but its native-header check rejected duplicate
bare names. V2 consumes the projected header multiset once per requirement,
retaining complete positive MemberIds. It accepts both identical header
shapes and reordered distinct shapes, while rejecting reuse of one header,
a missing header and duplicate positive MemberIds. This finding is resolved.
The projection verifies names, arities and variadicness; it does not recover
package or positive type information missing from the old wire headers.

The related *defined* `Mix` producer collision is a separate existing
boundary: the author's exact base emitter produces duplicate
`main.Mix.m` dispatch identities. I independently ran that base wire through
my already-built CLI, first checking that its NativeToIR source equals
exact `7ac3eb46`. It refuses before execution with the duplicate FuncId
diagnostic. The new producer refuses earlier while sealing the envelope.
This is an existing lowering refusal moving to the frontend, not a passing
execution lost by this fixture. The explicit old/new stage movement and
cached-binary provenance are retained; no private-method runtime repair is
accepted by this review.

## Other reviewed boundaries

Source function signatures exclude receiver/binding names. Closure metadata
separates the source signature, pointer capture prefix and lowered ABI, and
the adapter checks their exact concatenation. Synthetic helpers have a
closed role and their own signature. The inspected construction-point
producer obtains these from Go types; it does not reconstruct them from
opaque executable type spellings.

Function and method bindings retain exact final order, index and identity,
including the combined uniqueness check. Source and adapter receivers remain
separate for promotions; source-role receivers must agree. The nominal
inventory checks uniqueness, arity and the exact union of declared source
origins and transitive referenced origins. Full Go-source truth remains a
separate compiler-correspondence obligation: deliberately well-formed false
metadata must not acquire that truth merely by decoding.

`decodeBytes` invokes the reviewed whole-byte strict parser before selecting
the envelope. The parsed-object API documents its caller's responsibility
for information already lost. The sole NativeToIR delta is the known unread
root key. `GoCore.DeclarationContext` contains positive signatures and
identities, without frontend construction roles, bodies or execution support
flags. Its selected-method query does not establish runtime receiver
selection, closure callability, layout, default values or marker removal.

## Independent validation and limits

The new worktree checkout failed because the filesystem reached zero free
space. No source, cache or evidence was deleted. After transient space
returned, I used a unique copied-source scratch instead of a full checkout.
Three v1 positive-channel modules were freshly elaborated, and the changed
v2 package module was freshly elaborated over the unchanged fresh modules.
Exact base dependency artifacts were reused read-only, as recorded; this
was not a fresh full dependency build. The first attempt exposed Lean's
package-directory lookup behavior and failed before proof elaboration;
read-only artifact links fixed that local review setup.

The independent selected-signature uniqueness theorem and post-import audit
pass on v2: 1,973 imported local/current declarations, allowing only the
established classical trio. Seven independent byte-input challenges have
the expected results, including both repaired boundaries and member
retention after header permutation. The actual Go source probe is a fresh
Go type-check, not executable Go-vs-Lean conformance. The author's six
actual-emitter fixtures, Go comparisons, malformed-input controls,
compiling mutation controls and base-wire preservation evidence remain
separate author evidence.

Final full CI, slow certification, pin disposition, integration with the
other lanes and root acceptance remain open. Integration with R1 must bind
the added wire field and final source inventory explicitly; this review
does not authorize changing semantic pin parameters or silently refreshing
cached corpus claims.
