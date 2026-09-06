# Actual driver abort observation

This bounded seam computes a record from the actual abort transition and
proves erasure to the shipped driver. It does not change ordinary execution
or establish a Go panic-rendering membership claim. The R1 apparatus consumes
the record together with separately validated native source and controls.

`AbortRecord` contains the first payload's complete `GoString` bytes and
recovery flag, followed by those fields for every remaining panic entry.
Extraction succeeds only when the actual `Config.abort?` query produces a
nonempty chain containing exclusively explicit boxed strings. It preserves
invalid bytes, bytes after LF, ordering and flags. A nonstring tail rejects
the record even when the head is a string.

`runConfigWithAbort_erasure` preserves the sequential driver's exact result
for every state, configuration, fuel and choice stream, including malformed
inputs and terminal checks before fuel. `runConfigWithAbort_witness` ties a
computed record to a bounded fixed-stream `Trace` and the actual failing
panic step. The separate typed extension obtains whole-chain typing and
unchanged choices from the structural invariant. Its completeness theorem
is conditional on an actual panic result; it does not yet remove the old
renderer refusal boundary or prove unconditional typed driver classification.

The CLI uses the pool seam. `execPoolWithAbort` uses the proved `Pool.front`
classification and the original `stepMulti`, `raceUpdate`, event-output fold
and recursive fuel decrement. Its erasure theorem is universal over all
inputs, with no singleton or admission premise. A record is attached only
when a selected thread actually changes from a running abort configuration
to an aborted tombstone, the actual renderer returns the same text, and the
remaining actual driver run returns that panic. Records do not come from
preexisting tombstones, zero-fuel frontiers or transient unwinding states.

`PoolAbortWitness.reached` exposes a counted exact prefix, selected abort
transition and suffix `Pool.Run`. It retains the original and intermediate
choices, race states, accumulated output and the equation partitioning the
original fuel. `stepAbortRecord?_some` then exposes the actual abort query,
complete chain and renderer result. The local extraction function is not
itself a proof that a supplied event happened; the computed driver's witness
provides that mandatory `stepMulti` fact.

`runProgramPoolWithAbort_erasure` and its integer-argument counterpart erase
to the exact public `runProgramPoolOutM` and `runProgramPoolOutIntsM` entries.
The program witness includes the actual same-fuel setup, external result
locations and initialized choice stream. Checked wrappers execute the
independent recovery checker, while broader wrappers make no admission
claim. Integer arguments retain the shipped integer interpretation; typed
CLI fixtures are nullary where the profile admits Boolean entry arguments.

The generic CLI dependency is three modules: `AbortObservation`,
`RecoveryPoolObservation`, and `RecoveryProgramObservation`. It contains no
Iris imports or assumptions. `RecoveryObservation` is the separate structural
typing extension. Shared Iris allocation/call/unwind proofs and complete O2
driver classification remain distinct required increments.
