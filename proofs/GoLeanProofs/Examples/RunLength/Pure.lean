import GoLeanProofs.SliceMem

/-!
# RunLength — Pure

The example's mathematical content: what "run-length encoding" means
(`rleSpec`, defined the way a mathematician would — group maximal runs
of equal adjacent elements), the DECODE theorem (expanding the encoding
reproduces the input — the whole point of an encoding), and the setup
family the harness builds (`s[i] = seed + i/3`).

`rleSpec` is STATEMENT vocabulary — the headline says the returned
`(runVals, runCounts, k)` ARE the projections of `rleSpec pre`, and
nothing else in this module reaches the statement layer. The family is
proof method.

## Kit-gap witnesses here (`docs/gallery-campaign-log/g1.md § KIT-GAP LIST (rle)`)

* the setup family `seed + i/3` is NOT expressible with
  `SliceMem.familyMod` (which is `seed + i%k`); `rleFamily` below is
  the local re-derivation, in exactly the shape a kit `familyF`
  (family parameterized by an index function) would close.
-/

namespace GoLean.Examples.RunLength

open GoLean
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The specification function -/

/-- **The specification**: the run-length encoding of a list — the
list of `(value, count)` pairs of its maximal runs of equal adjacent
elements, in order. Defined structurally, with no index arithmetic:
prepending `x` either extends a leading run of `x`s or opens a new
run of length 1. -/
def rleSpec : List Int → List (Int × Nat)
  | [] => []
  | x :: xs =>
    match rleSpec xs with
    | [] => [(x, 1)]
    | (y, c) :: rest =>
      if x = y then (x, c + 1) :: rest else (x, 1) :: (y, c) :: rest

/-- **The decode theorem** — the property that makes `rleSpec` an
ENCODING: expanding each `(value, count)` pair back into a run
reproduces the input exactly. This is the first-order reading the
gallery quotes; it pins `rleSpec` itself as trustworthy statement
vocabulary (a wrong `rleSpec` could not decode). -/
theorem rleSpec_decode (l : List Int) :
    (rleSpec l).flatMap (fun p => List.replicate p.2 p.1) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [rleSpec]
    cases hspec : rleSpec xs with
    | nil =>
      rw [hspec] at ih
      simp only [List.flatMap_nil] at ih
      simp [← ih]
    | cons p rest =>
      obtain ⟨y, c⟩ := p
      rw [hspec] at ih
      by_cases hxy : x = y
      · subst hxy
        simp only [if_pos rfl, List.flatMap_cons] at ih ⊢
        rw [← ih]
        simp [List.replicate_succ]
      · simp only [if_neg hxy, List.flatMap_cons] at ih ⊢
        simp only [List.replicate_one, List.singleton_append, List.cons_append,
          List.nil_append] at ih ⊢
        rw [ih]

/-- The encoding of a constant list is one run (or none). This is the
bridge the `n ≤ 3` machine run uses: the harness family `seed + i/3`
is constant on `i < 3`. -/
theorem rleSpec_replicate (n : Nat) (v : Int) :
    rleSpec (List.replicate n v)
      = if n = 0 then [] else [(v, n)] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, rleSpec, ih]
    cases m with
    | zero => simp
    | succ m' => simp

/-! ## The setup family — `s[i] = seed + i/3`, wrapped at uint64

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (rle)): `SliceMem.familyMod` is
-- `seed + i%k`; this harness's family divides instead. The lemma set
-- below mirrors `familyMod`'s exactly (`length`/`range`/`Z_range`/
-- `succ`/`set`/`getD`), which is the shape a kit-level
-- `familyF (f : Nat → Nat)` would provide once, with
-- `familyMod k = familyF (· % k)` and this file's `rleFamily =
-- familyF (· / 3)`. -/

/-- The harness setup family: `fam[i] = (seed + i / 3) % 2^64`. -/
def rleFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i / 3) % 2 ^ 64 : Nat) : Int))

theorem rleFamily_length (n seed : Nat) :
    (rleFamily n seed).length = n := by
  simp [rleFamily]

theorem rleFamily_range (n seed : Nat) :
    ∀ v ∈ rleFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [rleFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : (seed + i / 3) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem rleFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ rleFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact rleFamily_range i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem rleFamily_succ (i seed : Nat) :
    rleFamily (i + 1) seed
      = rleFamily i seed ++ [(((seed + i / 3) % 2 ^ 64 : Nat) : Int)] := by
  simp [rleFamily, List.range_succ]

/-- One setup store advances the family prefix. -/
theorem rleFamily_set {n seed i : Nat} (hi : i < n) :
    (rleFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i / 3) % 2 ^ 64 : Nat) : Int)
      = rleFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (rleFamily i seed).length = i := rleFamily_length i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, rleFamily_succ]
  simp

/-- The family's element at an in-range index. -/
theorem rleFamily_getD {n seed m : Nat} (hm : m < n) :
    (rleFamily n seed).getD m 0
      = (((seed + m / 3) % 2 ^ 64 : Nat) : Int) := by
  rw [rleFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-- On `n ≤ 3` the family is CONSTANT (`i/3 = 0`): one run. This is
what confines the shipped machine run to the single-run regime — the
`n ∈ [4,8]` regime (where the family genuinely changes value) is the
recorded honest gap, blocked on append-spill machinery, not on the
family. -/
theorem rleFamily_const {n seed : Nat} (hn : n ≤ 3) :
    rleFamily n seed = List.replicate n (((seed % 2 ^ 64 : Nat) : Int)) := by
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [rleFamily, List.range_succ]

/-! ## The copy loop's array invariant (the kit's `prefixPad`) -/

/-- The `pre` array after `m` copy steps. -/
abbrev rlePre (m seed : Nat) : List Int := prefixPad rleFamily 8 m seed

theorem rlePre_zero (seed : Nat) : rlePre 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem rlePre_length {m seed : Nat} (h : m ≤ 8) :
    (rlePre m seed).length = 8 :=
  prefixPad_length (rleFamily_length m seed) h

theorem rlePre_range {m seed : Nat} :
    ∀ v ∈ rlePre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (rleFamily_range m seed)

/-- One copy store advances the prefix. -/
theorem rlePre_set {seed m : Nat} (hm : m < 8) :
    (rlePre m seed).set m (((seed + m / 3) % 2 ^ 64 : Nat) : Int)
      = rlePre (m + 1) seed :=
  rleFamily_set hm

theorem rlePre_full {n seed : Nat} :
    rlePre n seed
      = rleFamily n seed
          ++ List.replicate (8 - (rleFamily n seed).length) 0 :=
  prefixPad_full (rleFamily_length n seed)

/-! ## Spec-side range facts for the returned data -/

/-- The head value of the single-run encoding is the wrapped seed. -/
theorem rleSpec_const_form {n seed : Nat} (hn : n ≤ 3) :
    rleSpec (rleFamily n seed)
      = if n = 0 then []
        else [((((seed % 2 ^ 64 : Nat) : Int)), n)] := by
  rw [rleFamily_const hn, rleSpec_replicate]

end GoLean.Examples.RunLength

