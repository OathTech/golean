import GoLeanProofs.Examples.SieveProgram
import GoLeanProofs.Examples.Sieve.Pure
import GoLeanProofs.Examples.Sieve.Machine
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq

/-!
# Sieve — the `sieve` example (Gallery Campaign G1, guardrails wave)

**STATUS: PROVED — the headline `sieve_ok` (and its run-conditioned
twin `sieve_readout`) is stated HERE, in this root.**
The pure specification layer (`Examples/Sieve/Pure.lean`: trial-division
`isPrime`, the loop mirrors, and `sieveTable_spec`/`sieveAnswer_eq` — the
sieve computes primality and the count is `primeCount`) is landed and in
the audited closure via this import; the MACHINE half is the open work. This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`SieveProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/sieve-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.Sieve` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/sieve/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `sieveHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.Sieve

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def sieveHarnessFunc : Func :=
{ id := { key := "sieve_harness" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2"]
                    { key := "countPrimes" }
                    #[GoLean.GoCore.Expr.var "n"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "$c2"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem sieveHarnessFunc_pin :
    findFunctionIn? sieveLowered.funcs ⟨"sieve_harness"⟩
    = some sieveHarnessFunc := rfl


open GoLean.GoCore.Machine GoLean.Surface GoLean.SliceMem

-- The entry equation (derived): the machine entry IS its post-prelude
-- `runConfig` form; `svSeed`/`svC0` are the macro's emitted spellings,
-- definitionally the same records as the machine half's hand-written
-- `svSeed0`/`svC00`.
derive_entry_eq sv_entry_eq sieveLowered sieveHarnessFunc svSeed svC0

/-- **THE HEADLINE (§11 harness form, S2 SCALAR)**: for every `n` below
`2⁶²`, running `sieve_harness(n)` — `make([]bool, n+1)`, the sieve of
Eratosthenes marking pass, and the counting pass — through the
machine's native function entry completes normally past ONE fuel bound,
at every nondeterminism-choice stream, and returns exactly
`primeCount n`, the number of primes `≤ n`.

Honesty clauses, recorded rather than hidden:

* **The specification is trial-division primality** — `primeCount` /
  `isPrime` (`Examples/Sieve/Pure.lean`), mathematics a reader checks
  by eye, NOT a restatement of the loops. The loop mirrors
  (`markFrom`/`sieveOuter`/`countFrom`) are proof-side only and are
  bridged to the mathematics by `sieveTable_spec`/`sieveAnswer_eq`
  (the sieve marks exactly the composites; the count is the prime
  count).
* **The domain bound `n < 2⁶²` keeps every machine integer below the
  uint64 wrap threshold**: the outer guard computes `i*i` where `i`
  never exceeds `√n + 1 < 2³¹ + 2` (so `i*i < 2⁶³`), and `n + 1`
  (the table length), `j + i ≤ n + i`, `i + 1`, and `count + 1 ≤ n + 2`
  all stay far below `2⁶⁴`. NEAR `2⁶⁴` the guard's `i*i` CAN wrap and
  the program itself computes something else; the theorem deliberately
  does not claim that region. Attribution: the program's own
  arithmetic (machine-integer honesty, FD-E3).
* **The fuel bound `(n+1)·(49·(n+1) + 261) + 300` is a BOUND, not a
  measurement** — a deliberately generous quadratic over-charge (each
  outer pass is charged a full inner sweep). Measured totals:
  `55/279/340/1174/3296` steps at `n = 0/2/3/10/30` (probe-verified);
  the bound at those points is `610/1524/2128/9100/55480`.
* **`∀ ch` is vacuous here and stated anyway.** The subject consumes no
  nondeterminism choice; the quantifier records that, rather than
  hiding a `Choices` argument.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds — the
  table is `n+1` bools in ONE backing cell, and each marking pass
  allocates (and retires) a fresh `j`/`$forFirst` pair. -/
theorem sieve_ok (n : Nat) (hn : n < 2 ^ 62) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel sieveLowered.typeDefs.toList
          sieveLowered.funcs sieveHarnessFunc
          #[.int (n : Int) .uint64] sieveLowered.methods ch
        = .ok { values := #[.int ((primeCount n : Nat) : Int) .uint64] } := by
  refine ⟨(n + 1) * (49 * (n + 1) + 261) + 300, fun fuel hfuel ch => ?_⟩
  rw [sv_entry_eq (n : Int) fuel ch, unorm_nat_of_lt (by omega : n < 2 ^ 64)]
  rw [show svSeed (n : Int) = svSeed0 (n : Int) from rfl,
    show svC0 = svC00 from rfl]
  obtain ⟨k, σf, hk, hrun, hread⟩ := sv_runs n hn ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  simp only [bind, Except.bind, pure, Except.pure, hread]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
`primeCount n` — derived from `sieve_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem sieve_readout (n : Nat) (hn : n < 2 ^ 62) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel sieveLowered.typeDefs.toList
          sieveLowered.funcs sieveHarnessFunc
          #[.int (n : Int) .uint64] sieveLowered.methods ch
        = .ok r →
      r = { values := #[.int ((primeCount n : Nat) : Int) .uint64] } :=
  harness_readout_of_total (sieve_ok n hn)

end GoLean.Examples.Sieve
