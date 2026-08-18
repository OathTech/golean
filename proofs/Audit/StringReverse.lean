import Lean
import GoLeanProofs.Examples.StringReverse

/-!
# In-build axiom gate — the StringReverse example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every
`strrev` module and the HEADLINE (stated in the root, so the C-H4/C-H5
"the aggregator cannot see the designated theorem" shape never arises
here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`strrev_ok` — the S3 RELATIONAL headline over
`strrev_harness_r(n, seed)`** (`Examples/StringReverse.lean` over the
pinned `strrevLowered`): for every `n < 2^63` and `seed < 2^64`, past
fuel `156·n + 372`, at EVERY nondeterminism-choice stream, the harness
run over `runFunctionWithContextM` returns THREE values — a length-`n`
byte string `pre`, the string `pre.reverse`, and `palinSpec pre`,
which is `1` exactly when `pre.reverse = pre`. The postcondition is a
relation over RETURNED DATA; the setup family `strFamily` does not
appear in it.

**What is genuinely new in this entry.** It is the campaign's only
STRING example and the first whose returned data carries NO fixed-cap
toy bound: strings cross the observation boundary by contents, so all
three returns are observed at every length. The hypotheses that DO
appear are Go's own domains — `seed < 2^64` (uint64 argument),
`n < 2^63` (the subjects' `int` loop indices) — not caps of ours.
Machine-side, a Go string is a pure VALUE: `len`, `s[i]`, `+` and
every string store reduce definitionally, so the only conditioned
steps in the whole example are the three `enterFrame`s and the pure
strict-op facts (`stringFromRune` at ASCII, string `indexGet`, `%`).
The `string(rune(b))` round-trip is modeled FAITHFULLY (full UTF-8
encoder), which is why the reverse loop's invariant carries
`∀ b ∈ pre, b.toNat < 128` (`strFamily_ascii`) — on a non-ASCII byte
the Go program would NOT compute the byte reversal, and no theorem
here claims it would.

**Where the claim's strength comes from.** `palinSpec` is
`if xs.reverse = xs then 1 else 0` and the reversal claim is bare
`List.reverse` — nothing of ours between the reader and the returned
bytes. The Go decides the verdict by a half scan with an early return;
`palin_iff_half` (re-derived at `List UInt8` — the `ArrayPalindrome`
theorem one type over) is the bridge, and `strrev_verdict_iff` is the
first-order readout corollary: `v = 1 ↔ post = pre` over the returned
lists, with no `palinSpec` mentioned.

**The early return is still the shape worth noting.** The palindrome
subject leaves its loop from two places, so `p_loop` runs to the
DRIVER TERMINAL (through the frame pop AND the harness epilogue), and
the final `i`/`j` are existentially quantified — they differ between
the exits and nothing returned depends on them.

**One macro finding, recorded — and CLOSED (WP arc s2 item 6,
2026-08-18).** At landing, `derive_entry_eq` FAILED CLOSED on this
harness — its result defaults are strings, outside the macro's quoted
fragment — so `sH_entry_eq` was hand-written in exactly the emitted
shape. The string result-default arm has since been added to the
quoter, and `sH_entry_eq` is now MACRO-DERIVED (same statement, same
`with_unfolding_all rfl` closure; the pin below is unchanged).

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`strrevHarnessRFunc` (`rfl`-linked to the lowering by
`strrevHarnessRFunc_pin`) + `gs`/`palinSpec` + `List.reverse` +
`Nat`/`Int`/`UInt8` — no heap vocabulary, no Iris, no frame names.
Deletion test RUN (2026-08-15, by re-elaborating the headline with
each binder removed): both explicit hypotheses are load-bearing —
dropping `hn` breaks the run lemma's `int`-normalization goals,
dropping `hseed` breaks the entry equation's argument normalization.
No decorative hypothesis.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator
Challenge's trusted closure (gallery-campaign charter §HARD
BOUNDARIES — designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The string-reverse example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.StringReverse.palinSpec
example := @GoLean.Examples.StringReverse.gs
example := @GoLean.Examples.StringReverse.buildStrFunc
example := @GoLean.Examples.StringReverse.reverseStringFunc
example := @GoLean.Examples.StringReverse.isStringPalindromeFunc
example := @GoLean.Examples.StringReverse.strrevHarnessRFunc
-- The four lowering pins (the third link of the golden chain)
example := @GoLean.Examples.StringReverse.buildStr_pin
example := @GoLean.Examples.StringReverse.reverseString_pin
example := @GoLean.Examples.StringReverse.isStringPalindrome_pin
example := @GoLean.Examples.StringReverse.strrevHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.StringReverse.strFamily
example := @GoLean.Examples.StringReverse.strFamily_ascii
example := @GoLean.Examples.StringReverse.revPre
example := @GoLean.Examples.StringReverse.PalinUpTo
example := @GoLean.Examples.StringReverse.palin_iff_half
example := @GoLean.Examples.StringReverse.palinSpec_of_full
example := @GoLean.Examples.StringReverse.palinSpec_of_mismatch
example := @GoLean.Examples.StringReverse.applyStrictOp_stringFromRune_ascii
example := @GoLean.Examples.StringReverse.applyStrictOp_indexGet_string
example := @GoLean.Examples.StringReverse.sH_entry_eq
example := @GoLean.Examples.StringReverse.bu_loop
example := @GoLean.Examples.StringReverse.rv_loop
example := @GoLean.Examples.StringReverse.p_loop
example := @GoLean.Examples.StringReverse.p_bail
example := @GoLean.Examples.StringReverse.s_runs_generic
-- The headlines
example := @GoLean.Examples.StringReverse.strrev_ok
example := @GoLean.Examples.StringReverse.strrev_readout
example := @GoLean.Examples.StringReverse.strrev_verdict_iff

/-- info: 'GoLean.Examples.StringReverse.strrev_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.strrev_ok
/-- info: 'GoLean.Examples.StringReverse.strrev_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.strrev_readout
/-- info: 'GoLean.Examples.StringReverse.strrev_verdict_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.strrev_verdict_iff
/-- info: 'GoLean.Examples.StringReverse.s_runs_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.s_runs_generic
/-- info: 'GoLean.Examples.StringReverse.p_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.p_loop
/-- info: 'GoLean.Examples.StringReverse.bu_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.bu_loop
/-- info: 'GoLean.Examples.StringReverse.rv_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.rv_loop
/-- info: 'GoLean.Examples.StringReverse.p_bail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.p_bail
/-- info: 'GoLean.Examples.StringReverse.palin_iff_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.palin_iff_half
/-- info: 'GoLean.Examples.StringReverse.palinSpec_of_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.palinSpec_of_full
/-- info: 'GoLean.Examples.StringReverse.palinSpec_of_mismatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.palinSpec_of_mismatch
/-- info: 'GoLean.Examples.StringReverse.sH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.sH_entry_eq
/-- info: 'GoLean.Examples.StringReverse.strrevHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.strrevHarnessRFunc_pin
/-- info: 'GoLean.Examples.StringReverse.buildStr_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.buildStr_pin
/-- info: 'GoLean.Examples.StringReverse.reverseString_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.reverseString_pin
/-- info: 'GoLean.Examples.StringReverse.isStringPalindrome_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.StringReverse.isStringPalindrome_pin

end GoLean.Iris.Audit
