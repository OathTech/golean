import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.Examples.Targets

/-!
# InsertionSort — Family

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! # Harness-form groundwork (ruling 2026-08-13, §11 — the recorded
gap's completed half; module header for the gap statement)

Harness address layout (probe `.tmp/his-probe1.lean`, n=4 seed=3):
0 = `n`, 1 = `seed`, 2 = the harness `$res0` (the VERDICT cell),
3 = `$c4` (make handle), 4 = the `s` BACKING, 5 = `s`, 6/7 = the setup
`i`/`$forFirst`; the subject frame: 8 = `s` param, 9 = the subject
`i`, 10 = the outer `$forFirst`, per-pass `j`/`$forFirst` pairs from
11; then the test phase: `ok`, the sortedness scan's `i`/`ff`,
`$c5`/the `t` BACKING/`t`, the rebuild `i`/`ff`, the count loops'
`i`/`ff` + per-pass `cs`/`ct`/`j`/`ff`. -/

/-- **The input family**: the wrapped multiplicative sequence the
harness's setup phase materializes — `isFamily n seed` has entries
`(seed * (i+1)) mod 2^64` as mathematical integers; the wrap is IN the
definition, so the family needs no no-wrap hypothesis (duplicates and
non-monotone orders are exactly the interesting sort inputs). -/
def isFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int))

theorem isFamily_length (n seed : Nat) : (isFamily n seed).length = n := by
  simp [isFamily]

theorem isFamily_range (n seed : Nat) :
    ∀ v ∈ isFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [isFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := Nat.mod_lt (seed * (i + 1)) (y := 2 ^ 64) (by omega)
  omega

theorem isFamilyZ_range {n seed i : Nat} (_hin : i ≤ n) :
    ∀ v ∈ isFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact isFamily_range i seed v hv
  · rw [List.eq_of_mem_replicate hv]
    omega

/-- The one-step family extension the setup-loop invariant consumes. -/
theorem isFamily_set {n seed i : Nat} (hi : i < n) :
    (isFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int)
      = isFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hrep : List.replicate (n - i) (0 : Int)
      = 0 :: List.replicate (n - (i + 1)) 0 := by
    rw [show n - i = (n - (i + 1)) + 1 from by omega, List.replicate_succ]
  have hfam : isFamily (i + 1) seed
      = isFamily i seed ++ [(((seed * (i + 1)) % 2 ^ 64 : Nat) : Int)] := by
    rw [isFamily, isFamily, List.range_succ, List.map_append]
    rfl
  rw [hrep, hfam, List.append_assoc]
  have hlen : (isFamily i seed).length = i := isFamily_length i seed
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self]
  rfl

/-- The uint64 normalization of a `Nat` cast IS the mod-2^64 wrap (the
family's own wrap — no range hypothesis). -/
theorem unorm_nat_mod (m : Nat) :
    IntKind.normalize .uint64 ((m : Nat) : Int)
      = (((m % 2 ^ 64 : Nat)) : Int) := by
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `isortHarnessFunc` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
theorem isortHarness_pin :
    findFunctionIn? isortLowered.funcs ⟨"isort_harness"⟩
    = some isortHarnessFunc := rfl



end GoLean.Examples.InsertionSort
