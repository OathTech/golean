import GoLeanProofs.Examples.WordFreq.HarnessR

/-!
# WordFreq — the `wordfreq` example (Gallery Campaign, extension E5's consumer)

Go source: `Corpus/coverage/exec/examples/wordfreq/main.go`
(differentially green against `go run`, 15 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/wordfreq-lowered.repr`
and carried in `GoLeanProofs.Examples.WordFreqProgram` — INCLUDING the
injected `strings.Fields` shim (`goleanShimStringsFields`), whose
lowered body this proof walks: the machine's `strings.Fields` IS the
frontend's shim, and the shim-vs-stdlib correspondence is
differentially validated (the `strings/fields-conformance/*` suite and
the 600k-trial fuzz — `docs/gallery-campaign-log/g2.md`, "E5 — THE
FIDELITY ARGUMENT").

THE EXAMPLE THAT PULLED EXTENSION E5: idiomatic Go writes
`words := strings.Fields(text)`, the frontend quarantined the stdlib
selector call, and this example landed BLOCKED (14 red rows) until the
shim mechanism was built under guardrails. The subject was NOT
rewritten around the gap.

The subject splits the text with `strings.Fields`, counts words in a
`map[string]uint64`, and reports the queried word's count plus the
maximum count via a `for range` over the map. The harness is the S3
RELATIONAL style: it returns the built text and the queried word
alongside both counts, so the postcondition is a relation over the
RETURNED DATA — `hits = multiplicity q (wordsOf pre)` and
`best = maxMultiplicity (wordsOf pre)` — with `wordsOf` the byte-level
Fields spec (`Pure.lean`, `#guard`-pinned against the same
go-run-confirmed splits the corpus pins).

The per-phase shards: `Pure` (the Fields spec, the family, the counts
model), `Machine` (pinned `Func`s, string strict-ops, fronts, entry
equation), `Build` (the setup loop), `Scan`/`Scan2`/`Scan3` (the shim's
byte scan, through `build_scan_chain`), `Count` (the counting loop and
the string-key map facts), `Range` (the max-over-range loop),
`HarnessR` (the assembly, `wordfreq_total`).

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.WordFreq` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n < 2^60`, `seed < 2^64` and `qsel < 2^64`, running the Go harness
`wordfreq_harness_r(n, seed, qsel)` through the machine's native
function entry — empty-heap state, all three arguments at the call
boundary — completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns FOUR values: a text `pre`
holding exactly `n` words, the queried one-letter word `q`, the
multiplicity of `q` among `pre`'s words, and the maximum multiplicity
over `pre`'s words. "Words" means `wordsOf pre` — the byte-level
`strings.Fields` spec — and the postcondition is a relation over the
RETURNED DATA.

Honesty clauses, all recorded rather than hidden:

* **The machine's `strings.Fields` is the FRONTEND'S SHIM** (extension
  E5), lowered into this program and part of its golden pin. This
  theorem is about the shim's semantics; the shim-vs-stdlib
  correspondence is differential evidence (the conformance rows, every
  harness row, the 600k fuzz), not a theorem — exactly like the
  machine's own semantics.
* **`∀ ch` is load-bearing**: the `for range counts` max loop consumes
  one choice per iteration, so the claim holds at EVERY map-iteration
  order — provable because `maxMultiplicity` is a function of the
  returned data and cannot see the order the machine chose.
* **The queried count is the map read, zero value included**:
  `counts[query]` on an absent word is `0`, and `multiplicity` is `0`
  in exactly that case (rows `lit-miss`, `harness-one-miss` pin it on
  the oracle side).
* **No fixed-cap toy bound**: strings cross the observation boundary by
  contents; the returned text is unbounded. The bounds that DO appear
  are attributed: `seed, qsel < 2^64` are Go's `uint64` argument
  domain; `n < 2^60` keeps the built text (at most `3n + 1` bytes) and
  the proof's positional arithmetic comfortably inside Go's `int`
  domain for the subjects' `int` loop indices (the exact constant is
  the proof route's, generous either way). Mathematics needs none of
  them.
* **`∃ pre q` is still family-determined**: the witnesses are
  `textFamily n seed` and `qWord qsel` — the program's own arithmetic,
  uint64 wrap included. The statement merely avoids SAYING so;
  `wordfreq_hits_eq` below says the hits value exactly.
* **Machine idealization** as in the other entries: empty-heap entry,
  unbounded heap and strings, allocation always succeeds.

Fuel bound `N = wfFuel n = 811·n + 582` — branch-uniform worst case,
composed per phase (build→scan `703·n + 402`, count `84·n + 85`, range
head `16`, pick loop `24·n + 1` — the pick loop is charged `n`
iterations rather than the at-most-`min n 3` distinct words the family
actually produces — and the exit `78`). The MEASURED minimal fuels,
recorded separately and NOT presented as the bound:
`582 / 1145 / 2007 / 2575 / 3206 / 4056 / 4612 / 5243 / 6093 / 8686`
at `n = 0…8, 12` (seed/qsel-independent at fixed `n`; the bound is
exact at `n = 0`). -/
theorem wordfreq_ok (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) :
    ∃ pre q : List UInt8, (wordsOf pre).length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
            wordfreqLowered.funcs wordfreqHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (qsel : Int) .uint64]
            wordfreqLowered.methods ch
          = .ok { values := #[.string (gs pre), .string (gs q),
                              .int (multiplicity q (wordsOf pre) : Nat) .uint64,
                              .int (maxMultiplicity (wordsOf pre) : Nat) .uint64] } := by
  refine ⟨textFamily n seed, qWord qsel, ?_, wfFuel n,
    fun fuel hfuel ch => wordfreq_total n seed qsel hn hseed hqsel fuel hfuel ch⟩
  rw [wordsOf_textFamily]
  exact letterWords_length n seed

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns that quadruple. -/
theorem wordfreq_readout (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) :
    ∃ pre q : List UInt8, (wordsOf pre).length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
            wordfreqLowered.funcs wordfreqHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (qsel : Int) .uint64]
            wordfreqLowered.methods ch
          = .ok r →
        r = { values := #[.string (gs pre), .string (gs q),
                          .int (multiplicity q (wordsOf pre) : Nat) .uint64,
                          .int (maxMultiplicity (wordsOf pre) : Nat) .uint64] } := by
  obtain ⟨pre, q, hlen, htot⟩ := wordfreq_ok n seed qsel hn hseed hqsel
  exact ⟨pre, q, hlen, harness_readout_of_total htot⟩

/-- The hits value as residue arithmetic: the multiplicity of the
queried word among the family's words is the number of positions whose
letter residue matches the query's. (The bridge behind
`wordfreq_hits_eq`.) -/
theorem multiplicity_qWord_letterWords (n seed qsel : Nat) :
    multiplicity (qWord qsel) (letterWords n seed)
      = ((List.range n).filter
          (fun i => (seed + i) % 2 ^ 64 % 3 = qsel % 3)).length := by
  unfold multiplicity letterWords
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro i _
  simp only [Function.comp_apply, qWord]
  rw [decide_eq_decide]
  constructor
  · intro h
    have hlist : letterByte seed i = UInt8.ofNat (97 + qsel % 3) :=
      List.singleton_inj.mp h
    have ht := congrArg UInt8.toNat hlist
    rw [letterByte_toNat] at ht
    have h3 : (seed + i) % 2 ^ 64 % 3 < 3 := Nat.mod_lt _ (by omega)
    have hq3 : qsel % 3 < 3 := Nat.mod_lt _ (by omega)
    have hu : (UInt8.ofNat (97 + qsel % 3)).toNat = (97 + qsel % 3) % 256 := by
      simp
    rw [hu] at ht
    omega
  · intro h
    have : letterByte seed i = UInt8.ofNat (97 + qsel % 3) := by
      unfold letterByte
      rw [h]
    rw [this]

/-- **The first-order readout of the hits value** (statement-TCB
doctrine: a headline ships a corollary a reader can check without
unfolding the spec functions): the third returned value is the number
of word positions `i < n` whose letter residue
`((seed + i) mod 2^64) mod 3` equals the query's residue `qsel mod 3`
— pure arithmetic over the three inputs, no `wordsOf`, no map
vocabulary. (This is also the family-determination disclosure made
exact.) -/
theorem wordfreq_hits_eq (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) :
    ∃ pre q : List UInt8, ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel →
      ∀ ch : Choices, ∃ best : Nat,
        runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
            wordfreqLowered.funcs wordfreqHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (qsel : Int) .uint64]
            wordfreqLowered.methods ch
          = .ok { values := #[.string (gs pre), .string (gs q),
              .int (((List.range n).filter
                  (fun i => (seed + i) % 2 ^ 64 % 3 = qsel % 3)).length : Nat)
                .uint64,
              .int (best : Nat) .uint64] } := by
  refine ⟨textFamily n seed, qWord qsel, wfFuel n, fun fuel hfuel ch =>
    ⟨maxMultiplicity (wordsOf (textFamily n seed)), ?_⟩⟩
  have hmult : multiplicity (qWord qsel) (wordsOf (textFamily n seed))
      = ((List.range n).filter
          (fun i => (seed + i) % 2 ^ 64 % 3 = qsel % 3)).length := by
    rw [wordsOf_textFamily, multiplicity_qWord_letterWords]
  rw [← hmult]
  exact wordfreq_total n seed qsel hn hseed hqsel fuel hfuel ch

end GoLean.Examples.WordFreq
