# Recovery runtime contract design

Current bounded control milestone: the generic setup/invariant,
all-successor preservation and terminal-aware progress implementation is
described in [the control contract](2026-09-06_recovery-control-contract.md)
and its reviewed evidence. The design discussion below retains the earlier
storage-increment checkpoint; the shared Iris and renderer/driver obligations
remain open as described in the newer note.

[AGENT] 2026-09-06. Development checkpoint; this document does not claim O2
completion. Static admission is the reviewed `e8a665e9` increment. This lane
integrated the committed public O1 source and static profile at `212842a9`,
then rebuilt the static dependency modules from source. The six supporting
modules passed their source-bound gate and ordinary CI; independent review
PASS is sealed at parent `efc2712c` and recorded in
`docs/evidence/2026-09-06_recovery-storage/`. The complete machine-control
invariant and transition proofs remain drafts in a separate ignored scratch
tree; their final promotion, rebuild, gates and review are still required.

The invariant will describe actual storage and control, never future
successful evaluation. The source admission judgment remains separate.

## Mixed storage and environments

`World` is an array assigning each allocated root a runtime sort. A typed
address is a base address with an actual array entry; a typed live-reference
value points to a Boolean entry. `HeapTyped` ties every entry to a real typed
heap cell and value, with equal schema/heap sizes. Thus a pointer slot alone
does not establish liveness: `HeapTyped.live_reference` derives an actual
Boolean pointee cell. `HeapTyped.store` proves the real store succeeds while
preserving the same world, so every captured alias keeps its pointee type.
Allocation extends the world without changing old entries.

`EnvTyped` requires exact first-match lookup correspondence, separately from
typed addresses for every stored binding, including hidden outer bindings.
No name-union invariant substitutes for this mixed-type relationship.
The generic allocator and argument binder prove actual helper success,
world extension, typed heap/environment, unchanged non-heap context and
exact allocation count. They use `declareMany` for the runtime declaration
order; correspondence to the source function's ordered parameter/result
scope remains a separate obligation using distinct storage keys. A Boolean
reference parameter gets its own pointer slot and retains the original
pointee; this is semantic aliasing, not a duplicated exclusive Iris resource.

`StrictTyped.apply` covers real Boolean negation/equality, boxed-string/nil
payload equality, live dereference, string boxing and nil literals without
state change. Its payload equality lemma is slightly broader than source
admission: two boxed strings are dynamically comparable too. It imposes no
character, byte-validity or panic-history restriction.

## Sequence and lexical context obligations

The runtime statement judgment erases only duplicate-key freshness checks;
it retains first-match expression types, signature/capture checks, statement
effects, storage restrictions, and branch neutrality. Context inclusion
preserves sorts, not mere name membership. A declaration updates both sides
of an inclusion; there is deliberately no theorem claiming arbitrary old
sorts survive a new declaration.

The control invariant must use a joint sequence-head/tail constructor:
the tail is typed at the head's post-context, while actual bindings are
required only for the pre-context. This handles initialization and the
machine's `seqCont` splicing of nested same-environment sequences. Ordinary
execution under a saved sequence will be restricted to declaration-neutral
statements; unrestricted function bodies have a separate actual-frame entry
constructor. Blocks install a fresh scoped sequence; branches are already
neutral by static admission. This is a runtime proof organization, not a new
source restriction.

For neutral sequence splicing only, `EnvTyped.included_append_right` derives
compatible context union from shared actual first-match lookup and unique
address sort. It must never be used to carry an old heterogeneous tail
through a declaration that overwrites its name. An adversarial kernel
control will retain that distinction.

## Calls, expression delivery and unwinding still owed

Call-entry contracts must connect the actual function lookup, complete
parameter vector, captured prefix, allocated result locations and saved
caller target plans. Deferred calls discard their results but retain the
same checked input vector. Every registered callee and all its captured
Boolean pointees must remain typed through later stores and allocations.

Continuation typing needs separate intermediate return classes beyond source
value sorts: a target address may designate a payload cell, a closure value
is permitted only in callee position, and a panic argument is specifically a
boxed string. Treating the last as arbitrary nil-or-string payload would lose
the fact that explicit source panic cannot manufacture a runtime nil-panic
payload. Strict-expression operand lists carry the matching intermediate
input/output classes and evaluated/pending vectors.

Return continuations must contain an actual frame barrier. Normal terminal
continuations may end in `.stop`; `recover` traversals must retain the exact
non-wrapper-frame/direct-handler condition and rebuild the actual suspended
panic chain. Panic chains carry boxed string values and recovered flags,
including arbitrary bytes and repeated equal payloads. Uncaught panic is a
semantic terminal, separately observed from refusal and exhaustion. Raw
`stepFn` terminal refusal must not be confused with the terminal-checking
drivers' no-refusal contract.

Required remaining results are the structural complete control invariant,
generic admitted setup, all-successor preservation, terminal-aware progress,
actual readout and sequential/pool/observer bridges. Normal/recovered Iris
customers need reusable call and unwind rules plus functional reasoning;
typing cannot promise universal Iris `NotStuck` for uncaught panic under the
current adapter. No concrete full trace or future-success premise will stand
in for these obligations.
