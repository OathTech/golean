import GoLeanProofs.SliceMem
import GoLeanProofs.Examples.WordCount.Pure
import GoLeanProofs.Examples.Targets

/-!
# WordCount — Family

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The parameterized harness (gap G1 — CLOSED, consolidation
slice 2026-08-14)

The `(n, seed)`-parameterized §11 headline over `wordcount_harness`
(setup builds `w[i] = seed + i%3`, the call under test runs
`maxCount(w)`, the max count returns as data) is SHIPPED below as
`wordcount_ok` (+ the derived `wordcount_readout`), fuel bound
`229 + 165·n`, axioms the classical trio.

**HOW THE 2026-08-13 BLOCKER CLOSED (the record the old gap note owed
its successor).** The former storm — the harness composition proofs
(`wcH_count_iter`/`wcH_count_loop` as verbatim address-renames)
grinding the elaborator at 52 GB — was DIAGNOSED by bisection
(variants in `.tmp/prof-{A..E}.lean`; full record
`docs/2026-08-13_consolidation-slice.md` §1): postponed-elaboration
metavariables inside a big concrete-state argument defeat structural
unification, and isDefEq's delta fallback compares `Heap.lookup` over
the concrete front at a symbolic address — a stuck-`if` nest compared
without caching, ~2^N in the front length (2^9 canonical squeaked by;
2^16 harness stormed). The recorded "combination with the rw-surgered
hypothesis" theory was REFUTED (a context-minimal variant storms
identically); a full-type-ascribed application is INSTANT. Fix, made
structural: the counting AND range compositions are stated ONCE over
an abstract state family with every per-segment transition fact a
hypothesis whose type pins the intermediate states
(`wcIter_generic`/`wcLoop_generic`/`wcRange_generic`); the canonical
and harness placements consume them by instantiation, so no concrete
front ever reaches the unifier.

**THE SEED-WRAP CAVEAT, SETTLED (recorded finding, kept)**: the gap
record carried `hseed : seed + 2 < 2^64` on the theory that family
values collide near the wrap boundary and change `maxMultiplicity`.
That is WRONG: the family's values are `(seed + r) mod 2^64` for
`r ∈ {0,1,2}`, and two of those are equal iff `r ≡ r' (mod 2^64)` —
impossible for distinct `r, r' ≤ 2`. So no collision exists at ANY
seed, the wrap belongs in the family definition (`wcFamily`), the
shipped hypothesis is just the uint64 domain `hseed : seed < 2^64`
(consumed only by the entry equation's argument normalization), and
the returned value is `⌈n/3⌉ = (n+2)/3` unconditionally — proven as
`wcFamily_maxMult`, where the no-collision analysis is actually
consumed.

Address layout (probe-verified at `(n, seed) = (4, 7)`; every raw
segment below re-checks the transcription by `rfl`): 0 = `n`,
1 = `seed`, 2 = the harness `$res0`, 3 = `$c9` (the make temp),
4 = the `w` BACKING array, 5 = `w`, 6 = the setup counter (parked at
`n`), 7 = the setup flag, 8 = `$c10` (the call-result temp), 9 = the
subject's `words` parameter, 10 = the subject's `$res0`, 11 = `$c0`,
12 = the map DATA cell, 13 = `counts`, 14 = the subject's `i`,
15 = the subject's `$forFirst` — then the symbolic region from 16
(two dead cells per counting iteration, `best` at `16 + 2n`, one per
range iteration). Fuel bound: `229 + 165·n` (probe: the whole
`(4, 7)` run is 841 steps; the bound gives 889). -/

/-- **The input family**: the slice contents the setup phase builds
from `(n, seed)` — `w[i] = seed + i%3`, wrapped at `2^64`. GAP-P2
CLOSED (kit-gap closure, 2026-08-15): the pinned name is a delegation
to the kit's `SliceMem.familyMod 3`; the re-derived facts below are
one-line delegations. -/
abbrev wcFamily (n seed : Nat) : List Int :=
  GoLean.SliceMem.familyMod 3 n seed

theorem wcFamily_length (n seed : Nat) :
    (wcFamily n seed).length = n := familyMod_length 3 n seed

theorem wcFamily_range (n seed : Nat) :
    ∀ v ∈ wcFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := familyMod_range 3 n seed

theorem wcFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ wcFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := familyModZ_range

private theorem wcFamily_succ (i seed : Nat) :
    wcFamily (i + 1) seed
      = wcFamily i seed ++ [(((seed + i % 3) % 2 ^ 64 : Nat) : Int)] :=
  familyMod_succ 3 i seed

/-- One setup store advances the family prefix. -/
theorem wcFamily_set {n seed i : Nat} (hi : i < n) :
    (wcFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      = wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyMod_set hi

/-! ### The closed-form value: `maxMultiplicity (wcFamily n seed)
= ⌈n/3⌉`, at EVERY seed — the no-collision analysis, consumed -/

/-- The family's value at residue `r`. -/
def wcVal (seed r : Nat) : Int := (((seed + r) % 2 ^ 64 : Nat) : Int)

/-- **No collision at any seed**: two residue values are equal only at
equal residues — `(seed + a) ≡ (seed + b) (mod 2^64)` forces `a = b`
for `a, b < 3 ≤ 2^64`. This refutes the recorded `seed + 2 < 2^64`
caveat. -/
private theorem wcVal_inj {seed a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : wcVal seed a = wcVal seed b) : a = b := by
  have h' : (seed + a) % 2 ^ 64 = (seed + b) % 2 ^ 64 := by
    have h2 := h
    simp only [wcVal] at h2
    exact_mod_cast h2
  omega

private theorem multiplicity_append_one (v w : Int) (ws : List Int) :
    multiplicity v (ws ++ [w])
      = multiplicity v ws + (if w = v then 1 else 0) := by
  simp only [multiplicity, List.filter_append, List.length_append]
  by_cases h : w = v
  · simp [h]
  · simp [h]

/-- Residue `r`'s multiplicity in the family is the count of `i < n`
with `i % 3 = r`, in closed form. -/
private theorem multiplicity_wcVal (seed r : Nat) (hr : r < 3) :
    ∀ n : Nat, multiplicity (wcVal seed r) (wcFamily n seed)
      = (n + (2 - r)) / 3 := by
  intro n
  induction n with
  | zero =>
      have h0 : multiplicity (wcVal seed r) (wcFamily 0 seed) = 0 := rfl
      rw [h0]
      omega
  | succ m ih =>
      rw [wcFamily_succ, multiplicity_append_one, ih,
        show (((seed + m % 3) % 2 ^ 64 : Nat) : Int) = wcVal seed (m % 3)
          from rfl]
      by_cases h : m % 3 = r
      · rw [if_pos (show wcVal seed (m % 3) = wcVal seed r from by rw [h])]
        omega
      · rw [if_neg (fun hc =>
          h (wcVal_inj (Nat.mod_lt _ (by omega)) hr hc))]
        omega

private theorem mem_wcFamily_eq {n seed : Nat} {v : Int}
    (hv : v ∈ wcFamily n seed) : ∃ i, i < n ∧ v = wcVal seed (i % 3) := by
  simp only [wcFamily, familyMod, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨i, hi, rfl⟩

private theorem wcVal_mem {n seed i : Nat} (hi : i < n) :
    wcVal seed (i % 3) ∈ wcFamily n seed := by
  simp only [wcFamily, familyMod, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- **The headline's returned value in closed arithmetic form**: the
max multiplicity of the setup family is `⌈n/3⌉ = (n+2)/3`, at EVERY
seed — residue 0 is always (weakly) most frequent, and no seed makes
two residue values collide (`wcVal_inj`). -/
theorem wcFamily_maxMult (n seed : Nat) :
    maxMultiplicity (wcFamily n seed) = (n + 2) / 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · apply Nat.le_antisymm
    · apply maxMult_le
      intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_wcFamily_eq hv
      rw [multiplicity_wcVal seed (i % 3) (Nat.mod_lt _ (by omega)) n]
      omega
    · have h0 : multiplicity (wcVal seed 0) (wcFamily n seed)
          = (n + 2) / 3 := multiplicity_wcVal seed 0 (by omega) n
      rw [← h0]
      apply mult_le_maxMult
      have := wcVal_mem (seed := seed) (i := 0) hn
      simpa using this


end GoLean.Examples.WordCount
