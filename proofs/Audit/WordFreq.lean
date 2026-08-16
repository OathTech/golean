import Lean
import GoLeanProofs.Examples.WordFreq

/-!
# In-build axiom gate — the WordFreq example

Per-example shard of `proofs/Audit.lean` (the sharded-audit shape,
2026-08-14). The shard imports ONLY this example's module, so a change
to another example does not re-elaborate it; it is built because the
root `Audit.lean` imports it, and `scripts/ci`'s proofs-file
audit-coverage step fails if any `proofs/**/*.lean` leaves the audited
import closure.
-/

namespace GoLean.Iris.Audit

/-! ## The wordfreq example (gallery campaign unit G2.E5/wordfreq, 2026-08-16)

`✓` **`wordfreq_ok` — TOTAL harness headline, S3 relational, over the
E5 stdlib shim** (`Examples/WordFreq.lean` over the pinned
`wordfreqLowered`, which INCLUDES the injected `strings.Fields` shim's
lowered body): for every `n < 2^60`, `seed < 2^64`, `qsel < 2^64`,
running `wordfreq_harness_r(n, seed, qsel)` through the machine's
native function entry completes normally past one fuel bound
(`811·n + 582`), at every nondeterminism-choice stream (the map-range
max loop consumes one choice per iteration — `∀ ch` is load-bearing),
and returns the built text `pre` (exactly `n` words), the queried word
`q`, `multiplicity q (wordsOf pre)` and `maxMultiplicity (wordsOf
pre)` — `wordsOf` being the byte-level `strings.Fields` spec,
`#guard`-pinned in `Examples/WordFreq/Pure.lean` against the same
go-run-confirmed splits the `strings/fields-conformance/*` corpus rows
pin differentially. THE FAMILY BRIDGE is `wordsOf_textFamily`
(`Pure.lean`, axioms `[propext, Quot.sound]`): the built text's words
are exactly the `n` family letters. `wordfreq_readout` is the D1
run-conditioned twin via the shared bridge; `wordfreq_hits_eq` is the
first-order readout corollary (the hits value as pure residue
arithmetic over the inputs — the family-determination disclosure made
exact). -/
example := @GoLean.Examples.WordFreq.wordfreq_ok
example := @GoLean.Examples.WordFreq.wordfreq_readout
example := @GoLean.Examples.WordFreq.wordfreq_hits_eq
example := @GoLean.Examples.WordFreq.wordfreq_total
example := @GoLean.Examples.WordFreq.wordsOf_textFamily
/-- info: 'GoLean.Examples.WordFreq.wordfreq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordFreq.wordfreq_ok
/-- info: 'GoLean.Examples.WordFreq.wordfreq_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordFreq.wordfreq_readout
/-- info: 'GoLean.Examples.WordFreq.wordfreq_hits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordFreq.wordfreq_hits_eq
/-- info: 'GoLean.Examples.WordFreq.wordsOf_textFamily' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordFreq.wordsOf_textFamily

end GoLean.Iris.Audit
