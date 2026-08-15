import GoLeanProofs.Examples.HistogramProgram
import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit

/-!
# Histogram — Pure

The specification layer of the `histogram` example (Gallery Campaign
G1, the flagship kit-integration exercise; charter
`docs/2026-08-15_gallery-campaign.md` §G0 item 4 / §G1).

Two layers live here, and the split matters:

* **STATEMENT vocabulary** — `occurrences` and `distinctCount`, the two
  spec functions the headline mentions. Both are first-order list
  functions a reader can check by eye, and both are ORDER-INVARIANT
  functions OF THE RETURNED DATA (the S3 relational style): they never
  mention the map, the machine, or the setup family.
* **PROOF vocabulary** — `bump`/`countsFold` (the abstract content of
  the map data cell) and `histFamily` (the setup family), plus the
  bridges from those to the statement functions.

## Kit gaps witnessed here (campaign log `g1.md`, KIT-GAP list)

* **GAP-P1 — CLOSED** (kit-gap closure, 2026-08-15): the counting-fold
  layer this module had re-derived verbatim from
  `Examples/WordCount/Pure.lean` now lives in `GoLeanProofs/MapMem.lean`
  (`bump`/`countsFold` + the lemma chain); only the `occurrences`
  bridge stays here.
* **GAP-P2 — CLOSED** (kit-gap closure, 2026-08-15): `histFamily` is
  now a one-line delegation to `SliceMem.familyMod 3`, its facts
  one-line delegations to the kit's — the re-derived proofs are
  deleted.

The `(countsList l).length = distinctCount l` bridge below is NOT a
gap — it is this example's own spec content (`countsList` is the
pinned delegation name for the kit's `countsFold`).
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-! ## The statement vocabulary (order-invariant, §10b) -/

/-- How many times `v` occurs in `l`. -/
def occurrences (v : Int) (l : List Int) : Nat :=
  (l.filter (· = v)).length

/-- How many DISTINCT values `l` holds — each value counted exactly
once, at its LAST occurrence. Order-invariant in the sense the
∀-choices quantifier needs: it is a function of `l` alone, so no
map-iteration order can be read off it. -/
def distinctCount : List Int → Nat
  | [] => 0
  | v :: rest => (if v ∈ rest then 0 else 1) + distinctCount rest

/-! ## The proof vocabulary: the counting fold

GAP-P1 CLOSED (kit-gap closure, 2026-08-15): `bump`/`countsFold` and
the lemma chain this module had re-derived verbatim (`setk_cnt_succ`,
`countsFold_append`, `cnt_countsFold`, the key-membership/nodup/`cnt`
chain, `countsFold_val_le`) now live in `GoLeanProofs/MapMem.lean`
(visible here via `open GoLean.MapMem`). What stays is histogram's own
STATEMENT vocabulary: the bridge to `occurrences` and the cardinality
bridge below. -/

/-- The pinned histogram name for the kit's counting fold (the
audit-shard roll-call names it): a pure delegation — the re-derived
definition this module carried is deleted. -/
abbrev countsList : List Int → List (Int × Nat) := GoLean.MapMem.countsFold

/-- **The queried-key bridge**: the map's count at any key is that
key's number of occurrences (0 on both sides for an absent key — Go's
zero-value read is exactly the `occurrences = 0` case); histogram's
statement function is definitionally the kit's filter-length. -/
theorem cnt_countsList' (l : List Int) (x : Int) :
    cnt (countsList l) x = occurrences x l := by
  rw [cnt_countsFold]; rfl

/-- Value bound, at the pinned histogram name (delegation to the
kit's `countsFold_val_le`). -/
theorem countsList_val_le (l : List Int) {p : Int × Nat}
    (hp : p ∈ countsList l) : p.2 ≤ l.length :=
  GoLean.MapMem.countsFold_val_le l hp

/-! ## The cardinality bridge: `(countsFold l).length = distinctCount l`

This example's own spec content — the fact that makes the `for range`
loop's answer readable. The auxiliary `newCount seen l` counts the
values of `l` that are distinct AND not already accounted for by
`seen`; `newCount []` is `distinctCount`, and the fold's length grows
by exactly `newCount` over its key column. -/

/-- Values of `l` that are neither in `seen` nor repeated later. -/
private def newCount (seen : List Int) : List Int → Nat
  | [] => 0
  | v :: rest => (if v ∈ seen ∨ v ∈ rest then 0 else 1) + newCount seen rest

private theorem newCount_nil_seen (l : List Int) :
    newCount [] l = distinctCount l := by
  induction l with
  | nil => rfl
  | cons v rest ih => simp [newCount, distinctCount, ih]

/-- `newCount` sees `seen` only through membership. -/
private theorem newCount_congr {s₁ s₂ : List Int}
    (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : ∀ l, newCount s₁ l = newCount s₂ l := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih =>
      simp only [newCount, ih]
      by_cases hv : v ∈ s₁
      · simp [hv, (h v).mp hv]
      · have hv2 : v ∉ s₂ := fun hc => hv ((h v).mpr hc)
        simp [hv, hv2]

/-- Adding a FRESH key to `seen` removes exactly the one it accounts
for. -/
private theorem newCount_cons_seen {v : Int} {seen : List Int}
    (hv : v ∉ seen) :
    ∀ l, newCount seen l = newCount (v :: seen) l + (if v ∈ l then 1 else 0) := by
  intro l
  induction l with
  | nil => simp [newCount]
  | cons w rest ih =>
      simp only [newCount, ih, List.mem_cons]
      by_cases hwv : w = v
      · subst hwv
        by_cases hwr : w ∈ rest <;> simp [hv, hwr] <;> omega
      · by_cases hws : w ∈ seen <;> by_cases hwr : w ∈ rest <;>
          by_cases hvr : v ∈ rest <;>
            simp [hwv, hws, hwr, hvr, Ne.symm hwv] <;> omega

private theorem bump_length (kvs : List (Int × Nat)) (v : Int) :
    (bump kvs v).length
      = kvs.length + (if v ∈ kvs.map Prod.fst then 0 else 1) := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp [bump, hk]
      · have hvk : ¬ (v = k) := fun hc => hk hc.symm
        simp only [bump, if_neg hk, List.length_cons, ih, List.map_cons,
          List.mem_cons]
        by_cases hm : v ∈ rest.map Prod.fst <;> simp [hm, hvk] <;> omega

private theorem bump_keys_mem (kvs : List (Int × Nat)) (v x : Int) :
    x ∈ (bump kvs v).map Prod.fst ↔ (x = v ∨ x ∈ kvs.map Prod.fst) := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp only [bump, if_pos hk, List.map_cons, List.mem_cons]
        constructor
        · intro h; rcases h with h | h
          · exact .inl (h.trans hk)
          · exact .inr (.inr h)
        · intro h; rcases h with h | h | h
          · exact .inl (h.trans hk.symm)
          · exact .inl h
          · exact .inr h
      · simp only [bump, if_neg hk, List.map_cons, List.mem_cons, ih]
        constructor
        · intro h; rcases h with h | h | h
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · intro h; rcases h with h | h | h
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

private theorem foldl_bump_length (l : List Int) :
    ∀ kvs : List (Int × Nat),
    (List.foldl bump kvs l).length
      = kvs.length + newCount (kvs.map Prod.fst) l := by
  induction l with
  | nil => intro kvs; simp [newCount]
  | cons v rest ih =>
      intro kvs
      simp only [List.foldl_cons, ih, bump_length, newCount]
      by_cases hv : v ∈ kvs.map Prod.fst
      · have hcongr : ∀ x, x ∈ (bump kvs v).map Prod.fst
            ↔ x ∈ kvs.map Prod.fst := by
          intro x
          rw [bump_keys_mem]
          constructor
          · intro h; rcases h with h | h
            · exact h ▸ hv
            · exact h
          · intro h; exact .inr h
        rw [newCount_congr hcongr rest]
        simp [hv]
      · have hcongr : ∀ x, x ∈ (bump kvs v).map Prod.fst
            ↔ x ∈ v :: kvs.map Prod.fst := by
          intro x
          rw [bump_keys_mem]
          simp [List.mem_cons]
        rw [newCount_congr hcongr rest,
          newCount_cons_seen hv rest]
        by_cases hvr : v ∈ rest <;> simp [hv, hvr] <;> omega

/-- **The cardinality bridge**: the histogram has exactly as many
entries as `l` has distinct values. This is what makes the `for range
counts` answer readable — the loop runs once per entry at EVERY
iteration order, and the entry count is a function of the data. -/
theorem countsList_length (l : List Int) :
    (countsList l).length = distinctCount l := by
  rw [show countsList l = List.foldl bump [] l from rfl,
    foldl_bump_length l []]
  simp [newCount_nil_seen]

theorem distinctCount_le (l : List Int) : distinctCount l ≤ l.length := by
  induction l with
  | nil => simp [distinctCount]
  | cons v rest ih =>
      simp only [distinctCount, List.length_cons]
      by_cases hv : v ∈ rest <;> simp [hv] <;> omega

theorem countsList_length_le (l : List Int) :
    (countsList l).length ≤ l.length := by
  rw [countsList_length]; exact distinctCount_le l

/-! ## The setup family

GAP-P2 CLOSED (kit-gap closure, 2026-08-15): the address-free
re-derivation of the family this module carried is deleted — the kit
form is `SliceMem.familyMod 3`; the pinned names below are one-line
delegations. -/

/-- The setup loop's family: `v[i] = seed + i%3`, wrapped at uint64 —
three distinct values once `n ≥ 3`, with controllable multiplicities
(delegation to the kit's `familyMod 3`). -/
abbrev histFamily (n seed : Nat) : List Int :=
  GoLean.SliceMem.familyMod 3 n seed

theorem histFamily_length (n seed : Nat) :
    (histFamily n seed).length = n := familyMod_length 3 n seed

theorem histFamily_range (n seed : Nat) :
    ∀ v ∈ histFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  familyMod_range 3 n seed

theorem histFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ histFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := familyModZ_range

theorem histFamily_set {n seed i : Nat} (hi : i < n) :
    (histFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      = histFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyMod_set hi

theorem histFamily_getD {n seed m : Nat} (hm : m < n) :
    (histFamily n seed).getD m 0
      = (((seed + m % 3) % 2 ^ 64 : Nat) : Int) := familyMod_getD hm

end GoLean.Examples.Histogram
