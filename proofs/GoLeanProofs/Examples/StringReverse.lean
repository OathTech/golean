import GoLeanProofs.Examples.StringReverse.HarnessR

/-!
# StringReverse — the `strrev` example (Gallery Campaign G1, lane B)

Go source: `Corpus/coverage/exec/examples/strrev/main.go`
(differentially green against `go run`, 12 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/strrev-lowered.repr`
and carried in `GoLeanProofs.Examples.StringReverseProgram`.

THE CAMPAIGN'S ONLY STRING EXAMPLE, and the first gallery entry whose
returned data is NOT capped by a fixed-size array: strings cross the
observation boundary by CONTENTS (`{"tag":"string","bytes":[...]}`),
so all three returned values — the built string, its reversal, and
the palindrome verdict — are genuinely observed at every length, and
there is no `n ≤ 8` toy bound anywhere in the statement. The `n < 2^63`
hypothesis is Go's own `int` domain (the subjects' loop indices), not
a cap of ours.

The subject `reverseString` walks the BYTES from the end, rebuilding
by concatenation (`out += string(rune(s[i]))`); the companion
`isStringPalindrome` is the two-index inward byte walk with the early
`return 0`. The harness is the S3 RELATIONAL style: it returns the
string it built alongside the reversal and the verdict, so the
postcondition is a relation over the RETURNED DATA — `post` IS
`pre` reversed, and the verdict IS `palinSpec pre` — with no family
function re-describing the setup inside the claim.

The per-phase shards: `Pure` (the byte-list specs and the half-scan
bridge), `Machine` (the four pinned `Func`s, the string strict-op
facts, layout, entry equation), `Build`/`Rev`/`Palin` (the three
frames' towers), `HarnessR` (the end-to-end run).

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.StringReverse` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n < 2^63` and `seed < 2^64`, running the Go harness
`strrev_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both arguments at the call boundary —
completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns THREE values: a length-`n`
byte string `pre`, the string `pre.reverse`, and the verdict
`palinSpec pre` — `1` exactly when `pre` reads the same both ways.
The postcondition is a relation over the RETURNED DATA; no family
function and no index arithmetic appears in it.

Honesty clauses, all recorded rather than hidden:

* **No fixed-cap toy bound.** Strings cross the observation boundary
  by contents, so the returned data is unbounded — this is the first
  gallery entry with that property. The domain bounds that DO appear
  are attributed: `seed < 2^64` is Go's `uint64` domain for the
  argument; `n < 2^63` is Go's `int` domain (the subjects run `int`
  loop indices `i`, `j` over the string, and `len` returns `int`) —
  mathematics needs neither.
* **The claim is an equation on the returned triple, and
  `List.reverse` + `palinSpec` are the whole mathematical content.**
  `palinSpec xs = if xs.reverse = xs then 1 else 0`. The Go decides
  the verdict by a half scan with an early return; that is proof
  method (`palin_iff_half`), not part of the claim. The reversal is
  BYTE reversal, which for the returned data coincides with what the
  Go computes because every family byte is ASCII — the machine models
  `string(rune(b))` faithfully (UTF-8: a byte `≥ 128` would come back
  two bytes), and the proof carries the ASCII invariant explicitly
  (`strFamily_ascii`).
* **`∃ pre` is still family-determined.** The witness is
  `strFamily n seed` — byte `i` is `97 + ((seed+i) mod 2^64) mod 26`,
  the program's own uint64 arithmetic, wrap included. The statement
  merely avoids SAYING so. The corpus rows exercise both verdict
  outcomes (`1` at `n ≤ 1`, `0` at the mismatching lengths).
* **`n = 0` is included**: both subjects set their down-index to
  `-1`/`j = -1`, no loop body runs, and the empty string is its own
  reversal and a palindrome. The corpus row pins that against
  `go run`.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds — and
  string values of unbounded length, which is exactly Go-the-language
  (a real machine would exhaust memory first; Go's spec does not cap
  string length).

Fuel bound `N = 156·n + 372` — the branch-UNIFORM worst case: `65`
per build iteration, `57` per reverse iteration, `68` per full
palindrome iteration (at most `n/2`, charged as `34·n`), plus the
fixed `372` of entry, three frame entries, three prologues, three
first dispatches, the two inter-frame exits and the worst palindrome
tail. The MEASURED counts, recorded separately and NOT presented as
the bound: `351` at `n = 0`, `473` at `n = 1`, then `122·n + 372`
for `2 ≤ n ≤ 8` measured at `616/738/860/1348` for `n = 2/3/4/8` —
the family mismatches at the first pair, so the palindrome loop's
`68·(n/2)` worst case is not exercised past its first iteration by
this family. -/
theorem strrev_ok (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List UInt8, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel strrevLowered.typeDefs.toList
            strrevLowered.funcs strrevHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            strrevLowered.methods ch
          = .ok { values := #[.string (gs pre),
                              .string (gs pre.reverse),
                              .int (palinSpec pre) .uint64] } := by
  refine ⟨strFamily n seed, strFamily_length n seed, 156 * n + 372,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, piv, pjv, hk, hrun⟩ := s_runs_generic sProg n seed hn
    (bu_enterFrame_fact ((n : Nat) : Int) ((seed : Nat) : Int)
      (unorm_nat_of_lt (by omega)) (unorm_nat_of_lt hseed))
    (fun l biv => rev_enterFrame_fact _ _ _ _ l biv)
    (fun l biv rov riv => pal_enterFrame_fact _ _ _ _ l biv rov riv) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  have hst : sHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = sSt sProg (sHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5 := rfl
  rw [sH_entry_eq, unorm_nat_of_lt (by omega : n < 2 ^ 64),
    unorm_nat_of_lt hseed, hst, hfold, runConfig_next_stop]
  rfl

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns that triple. -/
theorem strrev_readout (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List UInt8, pre.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel strrevLowered.typeDefs.toList
            strrevLowered.funcs strrevHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            strrevLowered.methods ch
          = .ok r →
        r = { values := #[.string (gs pre), .string (gs pre.reverse),
                          .int (palinSpec pre) .uint64] } := by
  obtain ⟨pre, hlen, htot⟩ := strrev_ok n seed hn hseed
  exact ⟨pre, hlen, harness_readout_of_total htot⟩

/-- **The first-order readout of the verdict** (statement-TCB
doctrine: a headline ships a corollary a reader can check against the
Go without unfolding `palinSpec`): the third returned value is `1`
exactly when the returned reversal equals the returned original —
`isPalin = 1 ↔ post = pre`, over the returned byte lists. (`post` is
itself `pre.reverse` by the headline; both are family-determined by
`(n, seed)`.) -/
theorem strrev_verdict_iff (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ pre post : List UInt8, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ v : Int,
          runFunctionWithContextM fuel strrevLowered.typeDefs.toList
              strrevLowered.funcs strrevHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              strrevLowered.methods ch
            = .ok { values := #[.string (gs pre), .string (gs post),
                                .int v .uint64] }
          ∧ (v = 1 ↔ post = pre) := by
  obtain ⟨pre, hlen, N, htot⟩ := strrev_ok n seed hn hseed
  refine ⟨pre, pre.reverse, hlen, N, fun fuel hfuel ch =>
    ⟨palinSpec pre, htot fuel hfuel ch, ?_⟩⟩
  rw [palinSpec]
  split <;> simp_all

end GoLean.Examples.StringReverse
