import GoLeanProofs.Examples.WordFreq.Scan

/-!
# WordFreq — the shim's byte scan, part 2: iterations, loop, exit

Continues `Scan.lean` (split for elaboration budget): the byte-block
prefix composition, the iteration composites (letter long/short,
separator close/skip), the word-granularity step, the scan loop, the
exit segment, and the assembled `scan_phase` (+ the build→scan chain).

Method unchanged (the W2 recipe): machine configs transcribed from the
tracer (`.tmp/e5-drafts/trace-2-1-0.txt`, `w3cfg-*.txt`), rfl chunks
between the conditioned points (symbolic-address heap ops, string
index ops, env-blocked `seqn` splices), chained by `stepFnIter_chain`.

Positional layer: the scan reads the family text by INDEX (`s[i]`), so
this file derives the positional facts (`wPos`, drop/getD at a word's
letter and separator) from the frozen Pure interface
(`textFamily_zero/succ`, `letterByte_*`, `sepBytes`), and bridges to
`letterWords` once at the loop's end.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-! ## The positional layer (pure; derived from the frozen interface) -/

/-- The byte position of word `j`'s letter in the family text (the
leading space is byte 0). -/
def wPos : Nat → Nat
  | 0 => 1
  | j + 1 => wPos j + 1 + (sepBytes j).length

theorem sepBytes_length (j : Nat) :
    (sepBytes j).length = if j % 3 = 1 then 2 else 1 := by
  unfold sepBytes
  by_cases h0 : j % 3 = 0
  · simp [h0, show j % 3 ≠ 1 from by omega]
  · by_cases h1 : j % 3 = 1
    · simp [h0, h1]
    · simp [h0, h1]

theorem sepBytes_length_le (j : Nat) : (sepBytes j).length ≤ 2 := by
  rw [sepBytes_length]; split <;> omega

theorem sepBytes_length_pos (j : Nat) : 1 ≤ (sepBytes j).length := by
  rw [sepBytes_length]; split <;> omega

theorem wPos_succ_le (j : Nat) : wPos (j + 1) ≤ wPos j + 3 := by
  have := sepBytes_length_le j
  simp only [wPos]; omega

theorem wPos_succ_ge (j : Nat) : wPos j + 2 ≤ wPos (j + 1) := by
  have := sepBytes_length_pos j
  simp only [wPos]; omega

theorem wPos_le (j : Nat) : wPos j ≤ 3 * j + 1 := by
  induction j with
  | zero => simp [wPos]
  | succ j ih =>
      have := sepBytes_length_le j
      simp only [wPos]; omega

theorem wPos_pos (j : Nat) : 1 ≤ wPos j := by
  induction j with
  | zero => simp [wPos]
  | succ j ih => simp only [wPos]; omega

theorem wPos_mono {j n : Nat} (h : j ≤ n) : wPos j ≤ wPos n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · have := ih (by omega)
        simp only [wPos]; omega
      · have hj2 : j = n + 1 := by omega
        subst hj2
        exact Nat.le_refl _

/-- The family text's length is the position past the last block. -/
theorem textFamily_length (n seed : Nat) :
    (textFamily n seed).length = wPos n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [textFamily_succ]
      simp only [List.length_append, List.length_cons, ih, wPos]
      omega

/-- Dropping to word `j`'s letter exposes the remaining blocks. -/
theorem textFamily_drop (seed : Nat) :
    ∀ n j, j ≤ n →
    (textFamily n seed).drop (wPos j)
      = ((List.range' j (n - j)).map
          (fun m => letterByte seed m :: sepBytes m)).flatten := by
  intro n
  induction n with
  | zero =>
      intro j hj
      have : j = 0 := by omega
      subst this
      simp [textFamily_zero, wPos]
  | succ n ih =>
      intro j hj
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · have hj' : j ≤ n := by omega
        have hlen : wPos j ≤ (textFamily n seed).length := by
          rw [textFamily_length]; exact wPos_mono hj'
        rw [textFamily_succ, List.drop_append_of_le_length hlen, ih j hj']
        rw [show n + 1 - j = (n - j) + 1 from by omega]
        rw [List.range'_concat]
        rw [show j + 1 * (n - j) = n from by omega]
        simp
      · have hj2 : j = n + 1 := by omega
        subst hj2
        rw [List.drop_of_length_le
          (Nat.le_of_eq (textFamily_length (n + 1) seed))]
        simp

/-- The block view at a word `j < n`: letter, separator, rest. -/
theorem textFamily_drop_word (seed : Nat) {n j : Nat} (hj : j < n) :
    (textFamily n seed).drop (wPos j)
      = letterByte seed j :: (sepBytes j
          ++ ((List.range' (j + 1) (n - (j + 1))).map
              (fun m => letterByte seed m :: sepBytes m)).flatten) := by
  rw [textFamily_drop seed n j (by omega),
    show n - j = (n - (j + 1)) + 1 from by omega, List.range'_succ]
  simp

/-- The letter byte, read by index. -/
theorem textFamily_getD_letter (seed : Nat) {n j : Nat} (hj : j < n) :
    (textFamily n seed).getD (wPos j) 0 = letterByte seed j := by
  have hd := textFamily_drop_word seed hj
  have h1 : ((textFamily n seed).drop (wPos j))[0]?
      = (textFamily n seed)[wPos j]? := by
    rw [List.getElem?_drop, Nat.add_zero]
  rw [hd] at h1
  simp only [List.getElem?_cons_zero] at h1
  rw [List.getD_eq_getElem?_getD, ← h1]
  rfl

/-- The separator's first byte, read by index. -/
theorem textFamily_getD_sep1 (seed : Nat) {n j : Nat} (hj : j < n) :
    (textFamily n seed).getD (wPos j + 1) 0 = (sepBytes j).getD 0 0 := by
  have hd := textFamily_drop_word seed hj
  have h1 : ((textFamily n seed).drop (wPos j))[1]?
      = (textFamily n seed)[wPos j + 1]? := List.getElem?_drop ..
  rw [hd] at h1
  simp only [List.getElem?_cons_succ] at h1
  rw [List.getD_eq_getElem?_getD, ← h1,
    List.getElem?_append_left (by have := sepBytes_length_pos j; omega),
    List.getD_eq_getElem?_getD]

/-- The two-space separator's second byte, read by index. -/
theorem textFamily_getD_sep2 (seed : Nat) {n j : Nat} (hj : j < n)
    (h3 : j % 3 = 1) :
    (textFamily n seed).getD (wPos j + 2) 0 = 32 := by
  have hd := textFamily_drop_word seed hj
  have h1 : ((textFamily n seed).drop (wPos j))[2]?
      = (textFamily n seed)[wPos j + 2]? := List.getElem?_drop ..
  rw [hd] at h1
  simp only [List.getElem?_cons_succ] at h1
  rw [List.getD_eq_getElem?_getD, ← h1,
    List.getElem?_append_left (by rw [sepBytes_length]; simp [h3]),
    show sepBytes j = [32, 32] from by simp [sepBytes, h3]]
  rfl

/-- The word's bytes, sliced out: `s[wPos j : wPos j + 1]`. -/
theorem textFamily_slice_word (seed : Nat) {n j : Nat} (hj : j < n) :
    ((textFamily n seed).drop (wPos j)).take 1 = [letterByte seed j] := by
  rw [textFamily_drop_word seed hj]
  rfl

/-! ## Heap-split helpers, second batch (suffix shapes the append
block reaches) -/

theorem lookup_c1of2' {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1)])
      (.base ⟨na⟩) = some c0 := lookup_c1of2 hD

/-- Setting the FIRST cell of a 2-cell suffix. -/
theorem set_c1of2 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c0' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1)])
        (.base ⟨na⟩) c0'
      = D ++ [(.base ⟨na⟩, c0'), (.base ⟨na + 1⟩, c1)] := by
  rw [set_append_right (hD na (by omega))]
  simp [Heap.set]

/-- Setting the THIRD cell of a 4-cell suffix. -/
theorem set_c3of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c2' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (.base ⟨na + 2⟩) c2'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
          (.base ⟨na + 2⟩, c2'), (.base ⟨na + 3⟩, c3)] := by
  rw [set_append_right (hD (na + 2) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 2),
    base_beq_false (by omega : na + 1 ≠ na + 2)]

theorem lookup_c1of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (.base ⟨na⟩)
      = some c0 := by
  rw [lookup_append_right (hD na (by omega))]
  simp [Heap.lookup]

theorem lookup_c3of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (.base ⟨na + 2⟩)
      = some c2 := by
  rw [lookup_append_right (hD (na + 2) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
  simp [Heap.lookup]

theorem lookup_c4of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (.base ⟨na + 3⟩)
      = some c3 := by
  rw [lookup_append_right (hD (na + 3) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
  simp [Heap.lookup]

theorem lookup_c1of5 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (.base ⟨na⟩) = some c0 := by
  rw [lookup_append_right (hD na (by omega))]
  simp [Heap.lookup]

theorem lookup_c3of5 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (.base ⟨na + 2⟩) = some c2 := by
  rw [lookup_append_right (hD (na + 2) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
  simp [Heap.lookup]

theorem lookup_c4of5 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (.base ⟨na + 3⟩) = some c3 := by
  rw [lookup_append_right (hD (na + 3) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
  simp [Heap.lookup]

theorem lookup_c5of5 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (.base ⟨na + 4⟩) = some c4 := by
  rw [lookup_append_right (hD (na + 4) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
  simp [Heap.lookup]

theorem lookup_c1of6 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 c5 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4),
        (.base ⟨na + 5⟩, c5)]) (.base ⟨na⟩) = some c0 := by
  rw [lookup_append_right (hD na (by omega))]
  simp [Heap.lookup]

/-- Setting the FIFTH cell of a 5-cell suffix. -/
theorem set_c5of5 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 c4' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (.base ⟨na + 4⟩) c4'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
          (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3),
          (.base ⟨na + 4⟩, c4')] := by
  rw [set_append_right (hD (na + 4) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 4),
    base_beq_false (by omega : na + 1 ≠ na + 4),
    base_beq_false (by omega : na + 2 ≠ na + 4),
    base_beq_false (by omega : na + 3 ≠ na + 4)]

/-- `DeadFrom` after appending 5 fresh cells. -/
theorem DeadFrom.push5 {dead : Heap} {na : Nat}
    {c0 c1 c2 c3 c4 : HeapCell} (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
      (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4)])
      (na + 5) := by
  intro x hx
  rw [lookup_append_right (h x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x))]
  rfl

/-- `DeadFrom` after appending 6 fresh cells. -/
theorem DeadFrom.push6 {dead : Heap} {na : Nat}
    {c0 c1 c2 c3 c4 c5 : HeapCell} (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
      (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4),
      (.base ⟨na + 5⟩, c5)]) (na + 6) := by
  intro x hx
  rw [lookup_append_right (h x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x))]
  rfl

/-! ## Normalization helpers -/

/-- `uint8` normalization is the identity below `2^8`. -/
theorem u8norm_nat_of_lt {x : Nat} (h : x < 2 ^ 8) :
    IntKind.normalize .uint8 ((x : Nat) : Int) = ((x : Nat) : Int) := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed]
  exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast h)

/-- Storing a byte at a `uint8` cell normalizes to itself. -/
theorem norm_u8_byte (σ : ExecState) (v : UInt8) :
    normalizeValueForTy σ tU8 (.int ((v.toNat : Nat) : Int) .uint8)
      = .ok (.int ((v.toNat : Nat) : Int) .uint8) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp only [normalizeValueForTyFuel]
  rw [u8norm_nat_of_lt (by exact v.toNat_lt)]
  rfl

/-- Int literal 0/1 stores at `int` cells normalize to themselves. -/
theorem norm_sint_lit (σ : ExecState) (v : Int)
    (h : IntKind.normalize .int v = v) :
    normalizeValueForTy σ tInt (.int v .int) = .ok (.int v .int) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp only [normalizeValueForTyFuel]
  rw [h]
  rfl

/-- Full-heap lookup through the concrete scan front into the debris
region. -/
theorem lookup_scanD (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv sv2 : Int) (fv ffv : Bool) {D : Heap}
    {x : Nat} (hx : 31 ≤ x) {c : HeapCell}
    (h : Heap.lookup D (.base ⟨x⟩) = some c) :
    Heap.lookup
        (wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv ++ D)
        (.base ⟨x⟩) = some c := by
  rw [lookup_append_right
    (lookup_wHeapScan_none nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv
      hx)]
  exact h

/-- Full-heap set through the concrete scan front into the debris
region. -/
theorem set_scanD (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv sv2 : Int) (fv ffv : Bool) (D : Heap)
    {x : Nat} (hx : 31 ≤ x) (c : HeapCell) :
    Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv ++ D)
        (.base ⟨x⟩) c
      = wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv
          ++ Heap.set D (.base ⟨x⟩) c :=
  set_append_right
    (lookup_wHeapScan_none nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv
      hx)

/-! ## The byte-block prefix (`w := 0; c := s[i]`) -/

abbrev scAsgnW0 : Stmt := .assign (.var "w") (.intLit 0 .int)
abbrev scAsgnC : Stmt :=
  .assign (.var "c") (.indexGet (.var "s") (.var "i"))
/-- A plain-cell store target. -/
abbrev bRef (a : Nat) : TargetRef := .chain (.addr (.base ⟨a⟩)) [] []

/-- Prefix chunk A: seq-pop, `w = 0` target and rhs delivered. 6
steps. -/
theorem sc_ckA (σ : ExecState) (a : Nat) (rest : List Stmt) (k : Cont)
    (ch : Choices) :
    stepFnIter 6 σ (.next (.seq (scAsgnW0 :: rest) (scEnvB a) k)) ch
      = .ok (.next (.storeK [bRef a] [.int 0 .int] (.seqn #[]) (scEnvB a)
            (.seq rest (scEnvB a) k)), σ, ch) := by
  with_unfolding_all rfl

/-- Prefix chunk E: seq-pop, `c = s[i]` target, `s` and `i` reads
(front cells), the `indexGet` apply point delivered. 8 steps. -/
theorem sc_ckE (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat) (fs : List (List UInt8))
    (iv sv2 : Int) (fv : Bool) (D : Heap) (na a : Nat)
    (rest : List Stmt) (k : Cont) (ch : Choices) :
    stepFnIter 8
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na)
      (.next (.seq (scAsgnC :: rest) (scEnvBC a) k)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [.string (gs l)] [] (scEnvBC a)
              (.rhsK .vals [bRef (a + 1)] [] [] (.seqn #[]) (scEnvBC a)
                (.seq rest (scEnvBC a) k))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na,
          ch) := by
  with_unfolding_all rfl

/-- The one-target `rhsK` hands its value to the store queue. 1
step. -/
theorem sc_ckF (σ : ExecState) (v : GoValue) (r : TargetRef)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.retV v (.rhsK .vals [r] [] [] (.seqn #[]) env k)) ch
      = .ok (.next (.storeK [r] [v] (.seqn #[]) env k), σ, ch) := by
  with_unfolding_all rfl

/-- **The byte-block prefix**: from the loop test's true delivery,
through `w := 0; c := s[i]`, to the classifier — the iteration cells
`w`/`c` materialize at `na`/`na+1`. 35 steps (7 dispatch tail + 28). -/
theorem sc_prefix (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat) (fs : List (List UInt8))
    (i : Nat) (sv2 : Int) (fv : Bool) (D : Heap) (na : Nat) (ch : Choices)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hi : i < l.length) :
    stepFnIter 35
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false D na)
      (.retV (.bool true) scCmpK) ch
      = .ok (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
            (.seq [scIfW] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0),
              (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))]) (na + 2),
          ch) := by
  -- P1: test true → the `w` initialization point (7)
  have h0 := sc_P1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv D na ch
  -- alloc w (1)
  have h1 := stepFnIter_one (sc_step_initW σ nv sv qv bnv bsv l q biv b
    cap fs ((i : Nat) : Int) sv2 fv D na
    [scAsgnW0, scSeqnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
    scPostBody ch hna hD)
  -- chunk A (6)
  have h2 := sc_ckA
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    na [scSeqnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
    scPostBody ch
  -- store w := 0 (1)
  have hlookW : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)])
        (na + 1)).heap
      (.base ⟨na⟩) = some ⟨some tInt, .int 0 .int⟩ :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c1of1 hD)
  have h3 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
      (.next (.storeK [bRef na] [.int 0 .int] (.seqn #[]) (scEnvB na)
        (.seq [scSeqnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
          (scEnvB na) scPostBody))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvB na)
            (.seq [scSeqnC, goleanShimStringsFieldsFunc.scClassify,
              scIfW] (scEnvB na) scPostBody)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)])
            (na + 1), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr hlookW (norm_sint_lit _ 0 rfl)
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false _ (by omega),
      set_c1of1 hD] at h
    exact h
  -- storeK drain, splice, pop, splice, pop (5)
  have h4 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    (body := .seqn #[]) (env := scEnvB na)
    (k := .seq [scSeqnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
      (scEnvB na) scPostBody) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    (ss := #[])
    (env := scEnvB na)
    (rest := [scSeqnC, goleanShimStringsFieldsFunc.scClassify, scIfW])
    (k := scPostBody) (ch := ch))
  have h6 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    (t := scSeqnC)
    (rest := [goleanShimStringsFieldsFunc.scClassify, scIfW])
    (env := scEnvB na) (k := scPostBody) (ch := ch))
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    (ss := #[.initialization { id := "c", typ := tU8 }, scAsgnC])
    (env := scEnvB na)
    (rest := [goleanShimStringsFieldsFunc.scClassify, scIfW])
    (k := scPostBody) (ch := ch))
  have h8 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
    (t := .initialization { id := "c", typ := tU8 })
    (rest := [scAsgnC, goleanShimStringsFieldsFunc.scClassify, scIfW])
    (env := scEnvB na) (k := scPostBody) (ch := ch))
  -- alloc c (1)
  have h9 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1))
      (.exec (.initialization { id := "c", typ := tU8 }) (scEnvB na)
        (.seq [scAsgnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
          (scEnvB na) scPostBody)) ch
      = .ok (.next (.seq
            [scAsgnC, goleanShimStringsFieldsFunc.scClassify, scIfW]
            (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
              (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2),
          ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)])
        (na + 1))
      (p := { id := "c", typ := tU8 })
      (rest := [scAsgnC, goleanShimStringsFieldsFunc.scClassify, scIfW])
      (env := scEnvB na) (k := scPostBody) (ch := ch)
      (v := .int 0 .uint8)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    rw [show Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]))
        (.base ⟨na + 1⟩) ⟨some tU8, .int 0 .uint8⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
              (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          ((i : Nat) : Int) sv2 fv false _ (by omega),
        set_fresh (DeadFrom.push hD (na + 1) (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  -- chunk E: `c = s[i]` to the indexGet apply point (8)
  have h10 := sc_ckE σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv
    (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
      (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2) na
    [goleanShimStringsFieldsFunc.scClassify, scIfW] scPostBody ch
  -- the indexGet apply (1)
  have h11 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := scEnvBC na)
    (k := .rhsK .vals [bRef (na + 1)] [] [] (.seqn #[]) (scEnvBC na)
      (.seq [goleanShimStringsFieldsFunc.scClassify, scIfW] (scEnvBC na)
        scPostBody))
    (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false
        (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
          (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2))
      (l := l) (i := i) (ik := .int) hi))
  -- rhsK → storeK (1)
  have h12 := sc_ckF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
        (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2))
    (.int ((l.getD i 0).toNat : Nat) .uint8) (bRef (na + 1))
    (scEnvBC na)
    (.seq [goleanShimStringsFieldsFunc.scClassify, scIfW] (scEnvBC na)
      scPostBody) ch
  -- store c := s[i] (1)
  have hlookC : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
          (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2)).heap
      (.base ⟨na + 1⟩) = some ⟨some tU8, .int 0 .uint8⟩ :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c2of2 hD)
  have h13 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩),
          (.base ⟨na + 1⟩, ⟨some tU8, .int 0 .uint8⟩)]) (na + 2))
      (.next (.storeK [bRef (na + 1)]
        [.int ((l.getD i 0).toNat : Nat) .uint8] (.seqn #[])
        (scEnvBC na)
        (.seq [goleanShimStringsFieldsFunc.scClassify, scIfW]
          (scEnvBC na) scPostBody))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvBC na)
            (.seq [goleanShimStringsFieldsFunc.scClassify, scIfW]
              (scEnvBC na) scPostBody)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0),
              (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))]) (na + 2),
          ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr hlookC (norm_u8_byte _ (l.getD i 0))
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false _ (by omega),
      set_c2of2 hD] at h
    exact h
  -- storeK drain, splice, pop (3)
  have h14 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0),
        (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))]) (na + 2))
    (body := .seqn #[]) (env := scEnvBC na)
    (k := .seq [goleanShimStringsFieldsFunc.scClassify, scIfW]
      (scEnvBC na) scPostBody) (ch := ch))
  have h15 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0),
        (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))]) (na + 2))
    (ss := #[]) (env := scEnvBC na)
    (rest := [goleanShimStringsFieldsFunc.scClassify, scIfW])
    (k := scPostBody) (ch := ch))
  have h16 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0),
        (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))]) (na + 2))
    (t := goleanShimStringsFieldsFunc.scClassify) (rest := [scIfW])
    (env := scEnvBC na) (k := scPostBody) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
              h10) h11) h12) h13) h14) h15) h16

/-! ## Generic one-step glue for the classifier's spine (all
state-abstract; `with_unfolding_all rfl` throughout) -/

/-- An exhausted sequence pops to its continuation. -/
theorem ck_seqNil (σ : ExecState) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.next (.seq [] env k)) ch = .ok (.next k, σ, ch) := by
  with_unfolding_all rfl

/-- `if` dispatch: evaluate the condition. -/
theorem ck_ifDesc (σ : ExecState) (c : Expr) (t e : Stmt)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.exec (.ifThenElse c t e) env k) ch
      = .ok (.evalE c env (.ifK t e env k), σ, ch) := by
  with_unfolding_all rfl

theorem ck_ifKT (σ : ExecState) (t e : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool true) (.ifK t e env k)) ch
      = .ok (.exec t env k, σ, ch) := by
  with_unfolding_all rfl

theorem ck_ifKF (σ : ExecState) (t e : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool false) (.ifK t e env k)) ch
      = .ok (.exec e env k, σ, ch) := by
  with_unfolding_all rfl

theorem ck_orDesc (σ : ExecState) (a b : Expr) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.evalE (.or a b) env k) ch
      = .ok (.evalE a env (.orK b env k), σ, ch) := by
  with_unfolding_all rfl

theorem ck_andDesc (σ : ExecState) (a b : Expr) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.evalE (.and a b) env k) ch
      = .ok (.evalE a env (.andK b env k), σ, ch) := by
  with_unfolding_all rfl

theorem ck_orT (σ : ExecState) (r : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool true) (.orK r env k)) ch
      = .ok (.retV (.bool true) k, σ, ch) := by
  with_unfolding_all rfl

theorem ck_orF (σ : ExecState) (r : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool false) (.orK r env k)) ch
      = .ok (.evalE r env (.boolK k), σ, ch) := by
  with_unfolding_all rfl

theorem ck_andF (σ : ExecState) (r : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool false) (.andK r env k)) ch
      = .ok (.retV (.bool false) k, σ, ch) := by
  with_unfolding_all rfl

theorem ck_boolK (σ : ExecState) (x : Bool) (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.retV (.bool x) (.boolK k)) ch
      = .ok (.retV (.bool x) k, σ, ch) := by
  with_unfolding_all rfl

/-- A pushed empty-decl block splices its statements over a fresh
scope. -/
theorem ck_block (σ : ExecState) (ss : Array Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 1 σ (.exec (.block #[] ss) env k) ch
      = .ok (.next (.seq ss.toList ([] :: env) k), σ, ch) := by
  with_unfolding_all rfl

/-- The `c == v` (uint8) eq test from the value-delivered point:
literal, apply. 3 steps. -/
theorem ck_eqU8 (σ : ExecState) (cv v : Int) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 3 σ
      (.retV (.int cv .uint8)
        (.strictK (.eqCmp tU8) [] [.intLit v .uint8] env k)) ch
      = .ok (.retV (.bool (cv == IntKind.normalize .uint8 v)) k, σ, ch)
      := by
  with_unfolding_all rfl

/-- The eq-expression descent: evaluate `c`. -/
abbrev scEqC (v : Int) : Expr := .eqCmp tU8 (.var "c") (.intLit v .uint8)

theorem ck_eqDesc (σ : ExecState) (v : Int) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    stepFnIter 1 σ (.evalE (scEqC v) env k) ch
      = .ok (.evalE (.var "c") env
          (.strictK (.eqCmp tU8) [] [.intLit v .uint8] env k), σ, ch)
      := by
  with_unfolding_all rfl

/-! ## The classifier's statement/continuation vocabulary -/

abbrev scArmW (v : Int) : Stmt :=
  .block #[] #[.seqn #[.assign (.var "w") (.intLit v .int)]]
abbrev scIf3 : Stmt :=
  .ifThenElse
    (.lessCmp (.add (.var "i") (.intLit 2 .int))
      (.length (.var "s") (some tStr)))
    goleanShimStringsFieldsFunc.scC3Block (.seqn #[])
abbrev scIf2 : Stmt :=
  .ifThenElse goleanShimStringsFieldsFunc.scCond2 (scArmW 2) scIf3

abbrev scEnvB3 (a : Nat) : LocalEnv := [] :: scEnvBC a
abbrev scEnvC1 (a : Nat) : LocalEnv :=
  [("c1", .base ⟨a + 2⟩)] :: scEnvBC a
abbrev scEnvC2 (a : Nat) : LocalEnv :=
  [("c2", .base ⟨a + 3⟩), ("c1", .base ⟨a + 2⟩)] :: scEnvBC a

abbrev scEqC1 (v : Int) : Expr := .eqCmp tU8 (.var "c1") (.intLit v .uint8)
abbrev scEqC2 (v : Int) : Expr := .eqCmp tU8 (.var "c2") (.intLit v .uint8)
abbrev scOr5 : Expr :=
  .or (.or (.or
    (.and (.atLeastCmp (.var "c2") (.intLit 128 .uint8))
      (.atMostCmp (.var "c2") (.intLit 138 .uint8)))
    (scEqC2 168)) (scEqC2 169)) (scEqC2 175)
abbrev scAnd226a : Expr := .and (.and (scEqC 226) (scEqC1 128)) scOr5
abbrev scAnd226b : Expr := .and (.and (scEqC 226) (scEqC1 129)) (scEqC2 159)
abbrev scAnd227 : Expr := .and (.and (scEqC 227) (scEqC1 128)) (scEqC2 128)

/-- The classify tail (the `w > 0` branch under its governing seq). -/
abbrev scKifW (a : Nat) : Cont := .seq [scIfW] (scEnvBC a) scPostBody
abbrev scKw1 (a : Nat) : Cont :=
  .ifK (scArmW 1) scIf2 (scEnvBC a) (scKifW a)
abbrev scKor13 (a : Nat) : Cont := .orK (scEqC 13) (scEnvBC a) (scKw1 a)
abbrev scKor12 (a : Nat) : Cont := .orK (scEqC 12) (scEnvBC a) (scKor13 a)
abbrev scKor11 (a : Nat) : Cont := .orK (scEqC 11) (scEnvBC a) (scKor12 a)
abbrev scKor10 (a : Nat) : Cont := .orK (scEqC 10) (scEnvBC a) (scKor11 a)
abbrev scKor9 (a : Nat) : Cont := .orK (scEqC 9) (scEnvBC a) (scKor10 a)
abbrev scKw2 (a : Nat) : Cont :=
  .ifK (scArmW 2) scIf3 (scEnvBC a) (scKifW a)
abbrev scKw3 (a : Nat) : Cont :=
  .ifK goleanShimStringsFieldsFunc.scC3Block (.seqn #[]) (scEnvBC a)
    (scKifW a)
abbrev scKifC3 (a : Nat) : Cont :=
  .ifK (scArmW 3) (.seqn #[]) (scEnvC2 a) (.seq [] (scEnvC2 a) (scKifW a))
abbrev scK3or (a : Nat) : Cont :=
  .orK scAnd226a (scEnvC2 a) (.orK scAnd226b (scEnvC2 a)
    (.orK scAnd227 (scEnvC2 a) (scKifC3 a)))

/-! ## Bespoke chunks — the classifier's head, arms, and tails -/

/-- Classify head: `if` dispatch and the `cond1` or-spine descent to
the first `c` read. 7 steps. -/
theorem ck_clsHead (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC a)
        (scKifW a)) ch
      = .ok (.evalE (.var "c") (scEnvBC a)
          (.strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC a)
            (scKor9 a)), σ, ch) := by
  with_unfolding_all rfl

/-- Separator (space): `c == 32` verdict true, bubbled to the `w := 1`
arm's seqn. 11 steps. -/
theorem ck_sep32T (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 11 σ
      (.retV (.int 32 .uint8)
        (.strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC a)
          (scKor9 a))) ch
      = .ok (.exec (.seqn #[.assign (.var "w") (.intLit 1 .int)])
          (scEnvB3 a) (.seq [] (scEnvB3 a) (scKifW a)), σ, ch) := by
  with_unfolding_all rfl

/-- Separator (tab), first leg: `c == 32` false, dispatch to the
`c == 9` read. 5 steps. -/
theorem ck_sep9a (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.retV (.int 9 .uint8)
        (.strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC a)
          (scKor9 a))) ch
      = .ok (.evalE (.var "c") (scEnvBC a)
          (.strictK (.eqCmp tU8) [] [.intLit 9 .uint8] (scEnvBC a)
            (.boolK (scKor10 a))), σ, ch) := by
  with_unfolding_all rfl

/-- Separator (tab), second leg: `c == 9` true, bubbled to the
`w := 1` arm's seqn. 11 steps. -/
theorem ck_sep9b (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 11 σ
      (.retV (.int 9 .uint8)
        (.strictK (.eqCmp tU8) [] [.intLit 9 .uint8] (scEnvBC a)
          (.boolK (scKor10 a)))) ch
      = .ok (.exec (.seqn #[.assign (.var "w") (.intLit 1 .int)])
          (scEnvB3 a) (.seq [] (scEnvB3 a) (scKifW a)), σ, ch) := by
  with_unfolding_all rfl

/-- The `w := v` arm's assign, to the store point. 6 steps. -/
theorem ck_wArm (σ : ExecState) (a : Nat) (v : Int) (rest : List Stmt)
    (k : Cont) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.seq (.assign (.var "w") (.intLit v .int) :: rest)
        (scEnvB3 a) k)) ch
      = .ok (.next (.storeK [bRef a] [.int (IntKind.normalize .int v) .int]
            (.seqn #[]) (scEnvB3 a) (.seq rest (scEnvB3 a) k)), σ, ch)
      := by
  with_unfolding_all rfl

/-- The classify exit tail: drained empty seq, pop to `scIfW`. 2
steps. -/
theorem ck_tail2 (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 2 σ (.next (.seq [] (scEnvB3 a) (scKifW a))) ch
      = .ok (.exec scIfW (scEnvBC a) (.seq [] (scEnvBC a) scPostBody),
          σ, ch) := by
  with_unfolding_all rfl

/-! ## The separator classifies (`w := 1` via the 1-byte class) -/

section ClsSep

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (iv sv2 : Int)
  (fv : Bool) (D : Heap) (na : Nat) (ch : Choices)

/-- The `w := 1` arm from its seqn, shared by both separator
classifies: splice, assign, the conditioned `w` store, exit to
`scIfW`. 12 steps. -/
private theorem sc_cls_sepArm (hna : 31 ≤ na) (hD : DeadFrom D na)
    (cv : Int) :
    stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
      (.exec (.seqn #[.assign (.var "w") (.intLit 1 .int)]) (scEnvB3 na)
        (.seq [] (scEnvB3 na) (scKifW na))) ch
      = .ok (.exec scIfW (scEnvBC na) (.seq [] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) := by
  have h3 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (ss := #[.assign (.var "w") (.intLit 1 .int)]) (env := scEnvB3 na)
    (rest := []) (k := scKifW na) (ch := ch))
  have h4 := ck_wArm
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    na 1 [] (scKifW na) ch
  have hlookW : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2)).heap
      (.base ⟨na⟩) = some ⟨some tInt, .int 0 .int⟩ :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv
      false (by omega) (lookup_c1of2 hD)
  have h5 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
      (.next (.storeK [bRef na] [.int 1 .int] (.seqn #[]) (scEnvB3 na)
        (.seq [] (scEnvB3 na) (scKifW na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvB3 na)
            (.seq [] (scEnvB3 na) (scKifW na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr hlookW (norm_sint_lit _ 1 rfl)
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv
        false _ (by omega),
      set_c1of2 hD] at h
    exact h
  have h6 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (body := .seqn #[]) (env := scEnvB3 na)
    (k := .seq [] (scEnvB3 na) (scKifW na)) (ch := ch))
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (ss := #[]) (env := scEnvB3 na) (rest := []) (k := scKifW na)
    (ch := ch))
  have h8 := ck_tail2
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    na ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h3 h4) h5) h6) h7) h8

/-- **Separator classify (space)**: `c = 32` → `w := 1`. 31 steps. -/
theorem sc_cls_sep32 (hna : 31 ≤ na) (hD : DeadFrom D na) :
    stepFnIter 31
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 32)]) (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.exec scIfW (scEnvBC na) (.seq [] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 32)])
            (na + 2), ch) := by
  have h0 := ck_clsHead
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 32)]) (na + 2))
    na ch
  have h1 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 32)]) (na + 2))
    (x := "c") (env := scEnvBC na) (a := ⟨na + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC na)
      (scKor9 na))
    (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv
      false (by omega) (lookup_c2of2 hD)))
  have h2 := ck_sep32T
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 32)]) (na + 2))
    na ch
  have h3 := sc_cls_sepArm σ nv sv qv bnv bsv l q biv b cap fs iv sv2
    fv D na ch hna hD 32
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h0 h1) h2)
    h3

/-- **Separator classify (tab)**: `c = 9` → `w := 1`. 37 steps. -/
theorem sc_cls_sep9 (hna : 31 ≤ na) (hD : DeadFrom D na) :
    stepFnIter 37
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.exec scIfW (scEnvBC na) (.seq [] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 9)])
            (na + 2), ch) := by
  have h0 := ck_clsHead
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
    na ch
  have h1 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
    (x := "c") (env := scEnvBC na) (a := ⟨na + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC na)
      (scKor9 na))
    (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv
      false (by omega) (lookup_c2of2 hD)))
  have h2 := ck_sep9a
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
    na ch
  have h3 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
    (x := "c") (env := scEnvBC na) (a := ⟨na + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 9 .uint8] (scEnvBC na)
      (.boolK (scKor10 na)))
    (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv
      false (by omega) (lookup_c2of2 hD)))
  have h4 := ck_sep9b
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
      (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 9)]) (na + 2))
    na ch
  have h5 := sc_cls_sepArm σ nv sv qv bnv bsv l q biv b cap fs iv sv2
    fv D na ch hna hD 9
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h0 h1) h2) h3) h4) h5

end ClsSep

/-! ## The letter classify (all classes miss; the long variant probes
`c1`/`c2`) -/

abbrev scAsgnC1 : Stmt :=
  .assign (.var "c1")
    (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
abbrev scAsgnC2 : Stmt :=
  .assign (.var "c2")
    (.indexGet (.var "s") (.add (.var "i") (.intLit 2 .int)))

/-- A failed uint8 eq test from the value-delivered point. 3 steps. -/
theorem ck_eqU8F (σ : ExecState) (cv v : Int) (env : LocalEnv) (k : Cont)
    (ch : Choices) (hv : (cv == IntKind.normalize .uint8 v) = false) :
    stepFnIter 3 σ
      (.retV (.int cv .uint8)
        (.strictK (.eqCmp tU8) [] [.intLit v .uint8] env k)) ch
      = .ok (.retV (.bool false) k, σ, ch) := by
  rw [← hv]
  exact ck_eqU8 σ cv v env k ch

/-- One failed `cond1` or-arm (`c == v` at the byte-block env):
dispatch, read, test, verdict false handed on. 7 steps. -/
theorem ck_c1TestF (σ : ExecState) (a : Nat) (cv v : Int) (k : Cont)
    (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨a + 1⟩) = some (su8 cv))
    (hv : (cv == IntKind.normalize .uint8 v) = false) :
    stepFnIter 7 σ (.retV (.bool false) (.orK (scEqC v) (scEnvBC a) k))
      ch
      = .ok (.retV (.bool false) k, σ, ch) := by
  have h0 := ck_orF σ (scEqC v) (scEnvBC a) k ch
  have h1 := ck_eqDesc σ v (scEnvBC a) (.boolK k) ch
  have h2 := stepFnIter_one (stepFn_var (σ := σ) (x := "c")
    (env := scEnvBC a) (a := ⟨a + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit v .uint8] (scEnvBC a)
      (.boolK k)) (ch := ch) rfl hlook)
  have h3 := ck_eqU8F σ cv v (scEnvBC a) (.boolK k) ch hv
  have h4 := ck_boolK σ false k ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h0 h1) h2) h3) h4

/-- **The whole failed `cond1`** (a letter byte): head, six failed
1-byte tests, verdict at the first `if`. 46 steps. -/
theorem ck_cls1F (σ : ExecState) (a : Nat) (cv : Int) (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨a + 1⟩) = some (su8 cv))
    (h32 : (cv == 32) = false) (h9 : (cv == 9) = false)
    (h10 : (cv == 10) = false) (h11 : (cv == 11) = false)
    (h12 : (cv == 12) = false) (h13 : (cv == 13) = false) :
    stepFnIter 46 σ
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC a)
        (scKifW a)) ch
      = .ok (.retV (.bool false) (scKw1 a), σ, ch) := by
  have h0 := ck_clsHead σ a ch
  have h1 := stepFnIter_one (stepFn_var (σ := σ) (x := "c")
    (env := scEnvBC a) (a := ⟨a + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 32 .uint8] (scEnvBC a)
      (scKor9 a)) (ch := ch) rfl hlook)
  have h2 := ck_eqU8F σ cv 32 (scEnvBC a) (scKor9 a) ch h32
  have h3 := ck_c1TestF σ a cv 9 (scKor10 a) ch hlook h9
  have h4 := ck_c1TestF σ a cv 10 (scKor11 a) ch hlook h10
  have h5 := ck_c1TestF σ a cv 11 (scKor12 a) ch hlook h11
  have h6 := ck_c1TestF σ a cv 12 (scKor13 a) ch hlook h12
  have h7 := ck_c1TestF σ a cv 13 (scKw1 a) ch hlook h13
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h0 h1) h2) h3) h4) h5) h6) h7

/-- **The failed `cond2`** (`c ≠ 194` short-circuits the 2-byte
class): to the third `if`'s exec point. 12 steps. -/
theorem ck_c2F (σ : ExecState) (a : Nat) (cv : Int) (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨a + 1⟩) = some (su8 cv))
    (h194 : (cv == 194) = false) :
    stepFnIter 12 σ (.retV (.bool false) (scKw1 a)) ch
      = .ok (.exec scIf3 (scEnvBC a) (scKifW a), σ, ch) := by
  have h0 := ck_ifKF σ (scArmW 1) scIf2 (scEnvBC a) (scKifW a) ch
  have h1 := ck_ifDesc σ goleanShimStringsFieldsFunc.scCond2 (scArmW 2)
    scIf3 (scEnvBC a) (scKifW a) ch
  have h2 := ck_andDesc σ
    (.and (scEqC 194)
      (.lessCmp (.add (.var "i") (.intLit 1 .int))
        (.length (.var "s") (some tStr))))
    (.or
      (.eqCmp tU8
        (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
        (.intLit 133 .uint8))
      (.eqCmp tU8
        (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
        (.intLit 160 .uint8)))
    (scEnvBC a) (scKw2 a) ch
  have h3 := ck_andDesc σ (scEqC 194)
    (.lessCmp (.add (.var "i") (.intLit 1 .int))
      (.length (.var "s") (some tStr)))
    (scEnvBC a)
    (.andK
      (.or
        (.eqCmp tU8
          (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
          (.intLit 133 .uint8))
        (.eqCmp tU8
          (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
          (.intLit 160 .uint8)))
      (scEnvBC a) (scKw2 a)) ch
  have h4 := ck_eqDesc σ 194 (scEnvBC a)
    (.andK
      (.lessCmp (.add (.var "i") (.intLit 1 .int))
        (.length (.var "s") (some tStr)))
      (scEnvBC a)
      (.andK
        (.or
          (.eqCmp tU8
            (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
            (.intLit 133 .uint8))
          (.eqCmp tU8
            (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
            (.intLit 160 .uint8)))
        (scEnvBC a) (scKw2 a))) ch
  have h5 := stepFnIter_one (stepFn_var (σ := σ) (x := "c")
    (env := scEnvBC a) (a := ⟨a + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 194 .uint8] (scEnvBC a)
      (.andK
        (.lessCmp (.add (.var "i") (.intLit 1 .int))
          (.length (.var "s") (some tStr)))
        (scEnvBC a)
        (.andK
          (.or
            (.eqCmp tU8
              (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
              (.intLit 133 .uint8))
            (.eqCmp tU8
              (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
              (.intLit 160 .uint8)))
          (scEnvBC a) (scKw2 a)))) (ch := ch) rfl hlook)
  have h6 := ck_eqU8F σ cv 194 (scEnvBC a)
    (.andK
      (.lessCmp (.add (.var "i") (.intLit 1 .int))
        (.length (.var "s") (some tStr)))
      (scEnvBC a)
      (.andK
        (.or
          (.eqCmp tU8
            (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
            (.intLit 133 .uint8))
          (.eqCmp tU8
            (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
            (.intLit 160 .uint8)))
        (scEnvBC a) (scKw2 a))) ch h194
  have h7 := ck_andF σ
    (.lessCmp (.add (.var "i") (.intLit 1 .int))
      (.length (.var "s") (some tStr)))
    (scEnvBC a)
    (.andK
      (.or
        (.eqCmp tU8
          (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
          (.intLit 133 .uint8))
        (.eqCmp tU8
          (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
          (.intLit 160 .uint8)))
      (scEnvBC a) (scKw2 a)) ch
  have h8 := ck_andF σ
    (.or
      (.eqCmp tU8
        (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
        (.intLit 133 .uint8))
      (.eqCmp tU8
        (.indexGet (.var "s") (.add (.var "i") (.intLit 1 .int)))
        (.intLit 160 .uint8)))
    (scEnvBC a) (scKw2 a) ch
  have h9 := ck_ifKF σ (scArmW 2) scIf3 (scEnvBC a) (scKifW a) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h0 h1) h2)
        h3) h4) h5) h6) h7) h8) h9

/-- The third `if`'s bound test (`i+2 < len(s)`): front reads only.
12 steps. -/
theorem ck_if3 (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat) (fs : List (List UInt8))
    (iv sv2 : Int) (fv : Bool) (D₂ : Heap) (na₂ a : Nat) (ch : Choices) :
    stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.exec scIf3 (scEnvBC a) (scKifW a)) ch
      = .ok (.retV (.bool (decide (IntKind.normalize .int (iv + 2)
              < ((l.length : Nat) : Int)))) (scKw3 a),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- The `c1 := s[i+1]` chunk: pop, target, `s`/`i` front reads, the
wrapped sum delivered at the `indexGet` apply point. 12 steps. -/
theorem ck_idx1 (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat) (fs : List (List UInt8))
    (iv sv2 : Int) (fv : Bool) (D₂ : Heap) (na₂ a : Nat)
    (rest : List Stmt) (k : Cont) (ch : Choices) :
    stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (scAsgnC1 :: rest) (scEnvC1 a) k)) ch
      = .ok (.retV (.int (IntKind.normalize .int (iv + 1)) .int)
            (.strictK .indexGet [.string (gs l)] [] (scEnvC1 a)
              (.rhsK .vals [bRef (a + 2)] [] [] (.seqn #[]) (scEnvC1 a)
                (.seq rest (scEnvC1 a) k))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- The `c2 := s[i+2]` chunk. 12 steps. -/
theorem ck_idx2 (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat) (fs : List (List UInt8))
    (iv sv2 : Int) (fv : Bool) (D₂ : Heap) (na₂ a : Nat)
    (rest : List Stmt) (k : Cont) (ch : Choices) :
    stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (scAsgnC2 :: rest) (scEnvC2 a) k)) ch
      = .ok (.retV (.int (IntKind.normalize .int (iv + 2)) .int)
            (.strictK .indexGet [.string (gs l)] [] (scEnvC2 a)
              (.rhsK .vals [bRef (a + 3)] [] [] (.seqn #[]) (scEnvC2 a)
                (.seq rest (scEnvC2 a) k))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- The 3-byte class test's head: `if` dispatch, or/and descent to the
first `c` read. 7 steps. -/
theorem ck_c3Head (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.exec (.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])) (scEnvC2 a) (.seq [] (scEnvC2 a) (scKifW a))) ch
      = .ok (.evalE (.var "c") (scEnvC2 a)
          (.strictK (.eqCmp tU8) [] [.intLit 225 .uint8] (scEnvC2 a)
            (.andK (scEqC1 154) (scEnvC2 a)
              (.andK (scEqC2 128) (scEnvC2 a) (scK3or a)))), σ, ch) := by
  with_unfolding_all rfl

/-- The failed 3-byte class head: `if` dispatch, descent, read, the
`c == 225` test fails, short-circuit to the or-spine. 13 steps. -/
theorem ck_c3FirstF (σ : ExecState) (a : Nat) (cv : Int) (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨a + 1⟩) = some (su8 cv))
    (h225 : (cv == 225) = false) :
    stepFnIter 13 σ
      (.exec (.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])) (scEnvC2 a) (.seq [] (scEnvC2 a) (scKifW a))) ch
      = .ok (.retV (.bool false) (scK3or a), σ, ch) := by
  have h0 := ck_c3Head σ a ch
  have h1 := stepFnIter_one (stepFn_var (σ := σ) (x := "c")
    (env := scEnvC2 a) (a := ⟨a + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit 225 .uint8] (scEnvC2 a)
      (.andK (scEqC1 154) (scEnvC2 a)
        (.andK (scEqC2 128) (scEnvC2 a) (scK3or a))))
    (ch := ch) rfl hlook)
  have h2 := ck_eqU8F σ cv 225 (scEnvC2 a)
    (.andK (scEqC1 154) (scEnvC2 a)
      (.andK (scEqC2 128) (scEnvC2 a) (scK3or a))) ch h225
  have h3 := ck_andF σ (scEqC1 154) (scEnvC2 a)
    (.andK (scEqC2 128) (scEnvC2 a) (scK3or a)) ch
  have h4 := ck_andF σ (scEqC2 128) (scEnvC2 a) (scK3or a) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h0 h1) h2) h3) h4

/-- One failed 3-byte and-arm: dispatch, read, `c` test fails,
short-circuit out. 11 steps. -/
theorem ck_c3TestF (σ : ExecState) (a : Nat) (cv v : Int)
    (e1 r5 : Expr) (k : Cont) (ch : Choices)
    (hlook : Heap.lookup σ.heap (.base ⟨a + 1⟩) = some (su8 cv))
    (hv : (cv == IntKind.normalize .uint8 v) = false) :
    stepFnIter 11 σ
      (.retV (.bool false)
        (.orK (.and (.and (scEqC v) e1) r5) (scEnvC2 a) k)) ch
      = .ok (.retV (.bool false) k, σ, ch) := by
  have h0 := ck_orF σ (.and (.and (scEqC v) e1) r5) (scEnvC2 a) k ch
  have h1 := ck_andDesc σ (.and (scEqC v) e1) r5 (scEnvC2 a) (.boolK k)
    ch
  have h2 := ck_andDesc σ (scEqC v) e1 (scEnvC2 a)
    (.andK r5 (scEnvC2 a) (.boolK k)) ch
  have h3 := ck_eqDesc σ v (scEnvC2 a)
    (.andK e1 (scEnvC2 a) (.andK r5 (scEnvC2 a) (.boolK k))) ch
  have h4 := stepFnIter_one (stepFn_var (σ := σ) (x := "c")
    (env := scEnvC2 a) (a := ⟨a + 1⟩)
    (k := .strictK (.eqCmp tU8) [] [.intLit v .uint8] (scEnvC2 a)
      (.andK e1 (scEnvC2 a) (.andK r5 (scEnvC2 a) (.boolK k))))
    (ch := ch) rfl hlook)
  have h5 := ck_eqU8F σ cv v (scEnvC2 a)
    (.andK e1 (scEnvC2 a) (.andK r5 (scEnvC2 a) (.boolK k))) ch hv
  have h6 := ck_andF σ e1 (scEnvC2 a)
    (.andK r5 (scEnvC2 a) (.boolK k)) ch
  have h7 := ck_andF σ r5 (scEnvC2 a) (.boolK k) ch
  have h8 := ck_boolK σ false k ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h0 h1) h2) h3) h4) h5) h6)
        h7) h8

/-- `DeadFrom` after appending 3 fresh cells. -/
theorem DeadFrom.push3 {dead : Heap} {na : Nat} {c0 c1 c2 : HeapCell}
    (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
      (.base ⟨na + 2⟩, c2)]) (na + 3) := by
  intro x hx
  rw [lookup_append_right (h x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x))]
  rfl

section ClsLetter

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (sv2 : Int)
  (fv : Bool) (D : Heap) (na : Nat) (ch : Choices)

/-- **Letter classify, LONG variant** (`i+2 < len(s)`): every class
misses, the 3-byte probe block loads `c1`/`c2` into fresh cells,
`w` stays 0. 165 steps. -/
theorem sc_cls_letter_long (i : Nat) (cv : Int)
    (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hi2 : i + 2 < l.length) (hlen : l.length < 2 ^ 62)
    (h32 : (cv == 32) = false) (h9 : (cv == 9) = false)
    (h10 : (cv == 10) = false) (h11 : (cv == 11) = false)
    (h12 : (cv == 12) = false) (h13 : (cv == 13) = false)
    (h194 : (cv == 194) = false) (h225 : (cv == 225) = false)
    (h226 : (cv == 226) = false) (h227 : (cv == 227) = false) :
    stepFnIter 165
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.exec scIfW (scEnvBC na) (.seq [] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) := by
  have hlookc : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2)).heap
      (.base ⟨na + 1⟩) = some (su8 cv) :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c2of2 hD)
  have h0 : stepFnIter 46
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.retV (.bool false) (scKw1 na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) :=
    ck_cls1F _ na cv ch hlookc h32 h9 h10 h11 h12 h13
  have h1 : stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.retV (.bool false) (scKw1 na)) ch
      = .ok (.exec scIf3 (scEnvBC na) (scKifW na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) :=
    ck_c2F _ na cv ch hlookc h194
  have h2 := ck_if3 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv
    (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2) na
    ch
  rw [show ((i : Nat) : Int) + 2 = ((i + 2 : Nat) : Int) from by omega,
    inorm_nat_of_lt (show i + 2 < 2 ^ 63 by omega),
    show (decide (((i + 2 : Nat) : Int) < ((l.length : Nat) : Int)))
        = true from decide_eq_true (by exact_mod_cast hi2)] at h2
  have h3 := ck_ifKT
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2)) goleanShimStringsFieldsFunc.scC3Block (.seqn #[])
    (scEnvBC na) (scKifW na) ch
  have h4 := ck_block
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    #[.seqn #[.initialization { id := "c1", typ := tU8 }, scAsgnC1],
      .seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])]
    (scEnvBC na) (scKifW na) ch
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    (t := .seqn #[.initialization { id := "c1", typ := tU8 }, scAsgnC1])
    (rest := [.seqn #[.initialization { id := "c2", typ := tU8 },
        scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])])
    (env := scEnvB3 na) (k := scKifW na) (ch := ch))
  have h6 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    (ss := #[.initialization { id := "c1", typ := tU8 }, scAsgnC1])
    (env := scEnvB3 na)
    (rest := [.seqn #[.initialization { id := "c2", typ := tU8 },
        scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])])
    (k := scKifW na) (ch := ch))
  have h7 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    (t := .initialization { id := "c1", typ := tU8 })
    (rest := [scAsgnC1,
      .seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])])
    (env := scEnvB3 na) (k := scKifW na) (ch := ch))
  have h8 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec (.initialization { id := "c1", typ := tU8 }) (scEnvB3 na)
        (.seq [scAsgnC1,
          .seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2],
          .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
            (.seqn #[])]
          (scEnvB3 na) (scKifW na))) ch
      = .ok (.next (.seq [scAsgnC1,
            .seqn #[.initialization { id := "c2", typ := tU8 },
              scAsgnC2],
            .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
              (.seqn #[])]
            (scEnvC1 na) (scKifW na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 0)]) (na + 3), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
      (p := { id := "c1", typ := tU8 })
      (rest := [scAsgnC1,
        .seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2],
        .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
          (.seqn #[])])
      (env := scEnvB3 na) (k := scKifW na) (ch := ch)
      (v := .int 0 .uint8)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    rw [show Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]))
        (.base ⟨na + 2⟩) ⟨some tU8, .int 0 .uint8⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 0)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          ((i : Nat) : Int) sv2 fv false _ (by omega),
        set_fresh (DeadFrom.push2 hD (na + 2) (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  have h9 := ck_idx1 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv
    (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
      (.base ⟨na + 2⟩, su8 0)]) (na + 3) na
    [.seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2],
     .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
       (.seqn #[])]
    (scKifW na) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (show i + 1 < 2 ^ 63 by omega)] at h9
  have h10 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := scEnvC1 na)
    (k := .rhsK .vals [bRef (na + 2)] [] [] (.seqn #[]) (scEnvC1 na)
      (.seq [.seqn #[.initialization { id := "c2", typ := tU8 },
          scAsgnC2],
        .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
          (.seqn #[])]
        (scEnvC1 na) (scKifW na)))
    (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 0)]) (na + 3))
      (l := l) (i := i + 1) (ik := .int) (by omega)))
  have h11 := sc_ckF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 0)]) (na + 3))
    (.int ((l.getD (i + 1) 0).toNat : Nat) .uint8) (bRef (na + 2))
    (scEnvC1 na)
    (.seq [.seqn #[.initialization { id := "c2", typ := tU8 },
        scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])]
      (scEnvC1 na) (scKifW na)) ch
  have h12 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 0)]) (na + 3))
      (.next (.storeK [bRef (na + 2)]
        [.int ((l.getD (i + 1) 0).toNat : Nat) .uint8] (.seqn #[])
        (scEnvC1 na)
        (.seq [.seqn #[.initialization { id := "c2", typ := tU8 },
            scAsgnC2],
          .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
            (.seqn #[])]
          (scEnvC1 na) (scKifW na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvC1 na)
            (.seq [.seqn #[.initialization { id := "c2", typ := tU8 },
                scAsgnC2],
              .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
                (.seqn #[])]
              (scEnvC1 na) (scKifW na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
            (na + 3), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have hlkc1 : Heap.lookup
        (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
          fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, su8 0)]) (na + 3)).heap
        (.base ⟨na + 2⟩) = some ⟨some tU8, .int 0 .uint8⟩ :=
      lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c3of3 hD)
    have h := storeTarget_addr hlkc1 (norm_u8_byte _ (l.getD (i + 1) 0))
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false _ (by omega),
      set_c3of3 hD] at h
    exact h
  have h13 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
      (na + 3))
    (body := .seqn #[]) (env := scEnvC1 na)
    (k := .seq [.seqn #[.initialization { id := "c2", typ := tU8 },
        scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])]
      (scEnvC1 na) (scKifW na)) (ch := ch))
  have h14 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
      (na + 3))
    (ss := #[]) (env := scEnvC1 na)
    (rest := [.seqn #[.initialization { id := "c2", typ := tU8 },
        scAsgnC2],
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])])
    (k := scKifW na) (ch := ch))
  have h15 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
      (na + 3))
    (t := .seqn #[.initialization { id := "c2", typ := tU8 }, scAsgnC2])
    (rest := [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
      (.seqn #[])])
    (env := scEnvC1 na) (k := scKifW na) (ch := ch))
  have h16 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
      (na + 3))
    (ss := #[.initialization { id := "c2", typ := tU8 }, scAsgnC2])
    (env := scEnvC1 na)
    (rest := [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
      (.seqn #[])])
    (k := scKifW na) (ch := ch))
  have h17 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
      (na + 3))
    (t := .initialization { id := "c2", typ := tU8 })
    (rest := [scAsgnC2,
      .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])])
    (env := scEnvC1 na) (k := scKifW na) (ch := ch))
  have h18 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
        (na + 3))
      (.exec (.initialization { id := "c2", typ := tU8 }) (scEnvC1 na)
        (.seq [scAsgnC2,
          .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
            (.seqn #[])]
          (scEnvC1 na) (scKifW na))) ch
      = .ok (.next (.seq [scAsgnC2,
            .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
              (.seqn #[])]
            (scEnvC2 na) (scKifW na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 0)]) (na + 4), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))])
        (na + 3))
      (p := { id := "c2", typ := tU8 })
      (rest := [scAsgnC2,
        .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
          (.seqn #[])])
      (env := scEnvC1 na) (k := scKifW na) (ch := ch)
      (v := .int 0 .uint8)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    rw [show Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat))]))
        (.base ⟨na + 3⟩) ⟨some tU8, .int 0 .uint8⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 fv false
          ++ (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 0)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          ((i : Nat) : Int) sv2 fv false _ (by omega),
        set_fresh (DeadFrom.push3 hD (na + 3) (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  have h19 := ck_idx2 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv
    (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
      (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
      (.base ⟨na + 3⟩, su8 0)]) (na + 4) na
    [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
      (.seqn #[])]
    (scKifW na) ch
  rw [show ((i : Nat) : Int) + 2 = ((i + 2 : Nat) : Int) from by omega,
    inorm_nat_of_lt (show i + 2 < 2 ^ 63 by omega)] at h19
  have h20 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := scEnvC2 na)
    (k := .rhsK .vals [bRef (na + 3)] [] [] (.seqn #[]) (scEnvC2 na)
      (.seq [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
          (.seqn #[])]
        (scEnvC2 na) (scKifW na)))
    (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        sv2 fv false
        (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 0)]) (na + 4))
      (l := l) (i := i + 2) (ik := .int) hi2))
  have h21 := sc_ckF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 0)]) (na + 4))
    (.int ((l.getD (i + 2) 0).toNat : Nat) .uint8) (bRef (na + 3))
    (scEnvC2 na)
    (.seq [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])]
      (scEnvC2 na) (scKifW na)) ch
  have h22 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 0)]) (na + 4))
      (.next (.storeK [bRef (na + 3)]
        [.int ((l.getD (i + 2) 0).toNat : Nat) .uint8] (.seqn #[])
        (scEnvC2 na)
        (.seq [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
            (.seqn #[])]
          (scEnvC2 na) (scKifW na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvC2 na)
            (.seq [.ifThenElse goleanShimStringsFieldsFunc.scCond3
                (scArmW 3) (.seqn #[])]
              (scEnvC2 na) (scKifW na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have hlkc2 : Heap.lookup
        (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
          fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
            (.base ⟨na + 3⟩, su8 0)]) (na + 4)).heap
        (.base ⟨na + 3⟩) = some ⟨some tU8, .int 0 .uint8⟩ :=
      lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c4of4 hD)
    have h := storeTarget_addr hlkc2 (norm_u8_byte _ (l.getD (i + 2) 0))
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 fv false _ (by omega),
      set_c4of4 hD] at h
    exact h
  have h23 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (body := .seqn #[]) (env := scEnvC2 na)
    (k := .seq [.ifThenElse goleanShimStringsFieldsFunc.scCond3
        (scArmW 3) (.seqn #[])]
      (scEnvC2 na) (scKifW na)) (ch := ch))
  have h24 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (ss := #[]) (env := scEnvC2 na)
    (rest := [.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
      (.seqn #[])])
    (k := scKifW na) (ch := ch))
  have h25 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (t := .ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
      (.seqn #[]))
    (rest := []) (env := scEnvC2 na) (k := scKifW na) (ch := ch))
  have hlookc4 : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
        (na + 4)).heap
      (.base ⟨na + 1⟩) = some (su8 cv) :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c2of4 hD)
  have h26 : stepFnIter 13
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
        (na + 4))
      (.exec (.ifThenElse goleanShimStringsFieldsFunc.scCond3 (scArmW 3)
        (.seqn #[])) (scEnvC2 na) (.seq [] (scEnvC2 na) (scKifW na))) ch
      = .ok (.retV (.bool false) (scK3or na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) :=
    ck_c3FirstF _ na cv ch hlookc4 h225
  have h31 : stepFnIter 11
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
        (na + 4))
      (.retV (.bool false) (scK3or na)) ch
      = .ok (.retV (.bool false)
            (.orK scAnd226b (scEnvC2 na)
              (.orK scAnd227 (scEnvC2 na) (scKifC3 na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) :=
    ck_c3TestF _ na cv 226 (scEqC1 128) scOr5
      (.orK scAnd226b (scEnvC2 na)
        (.orK scAnd227 (scEnvC2 na) (scKifC3 na))) ch hlookc4 h226
  have h32' : stepFnIter 11
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
        (na + 4))
      (.retV (.bool false)
        (.orK scAnd226b (scEnvC2 na)
          (.orK scAnd227 (scEnvC2 na) (scKifC3 na)))) ch
      = .ok (.retV (.bool false)
            (.orK scAnd227 (scEnvC2 na) (scKifC3 na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) :=
    ck_c3TestF _ na cv 226 (scEqC1 129) (scEqC2 159)
      (.orK scAnd227 (scEnvC2 na) (scKifC3 na)) ch hlookc4 h226
  have h33 : stepFnIter 11
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
          (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
        (na + 4))
      (.retV (.bool false)
        (.orK scAnd227 (scEnvC2 na) (scKifC3 na))) ch
      = .ok (.retV (.bool false) (scKifC3 na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) :=
    ck_c3TestF _ na cv 227 (scEqC1 128) (scEqC2 128) (scKifC3 na) ch
      hlookc4 h227
  have h34 := ck_ifKF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (scArmW 3) (.seqn #[]) (scEnvC2 na)
    (.seq [] (scEnvC2 na) (scKifW na)) ch
  have h35 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (ss := #[]) (env := scEnvC2 na) (rest := []) (k := scKifW na)
    (ch := ch))
  have h36 := ck_seqNil
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (scEnvC2 na) (scKifW na) ch
  have h37 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
        (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
      (na + 4))
    (t := scIfW) (rest := []) (env := scEnvBC na) (k := scPostBody)
    (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                  (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                    (stepFnIter_chain (stepFnIter_chain
                      (stepFnIter_chain (stepFnIter_chain
                        (stepFnIter_chain (stepFnIter_chain h0 h1)
                          h2) h3) h4) h5) h6) h7) h8) h9) h10) h11)
                    h12) h13) h14) h15) h16) h17) h18) h19) h20) h21)
              h22) h23) h24) h25) h26) h31) h32')
        h33) h34) h35) h36) h37

/-- **Letter classify, SHORT variant** (`i+2 ≥ len(s)`, the text's
last byte reached without room for a 3-byte probe): every class
misses, no probe cells, `w` stays 0. 73 steps. -/
theorem sc_cls_letter_short (i : Nat) (cv : Int)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hi : i < l.length)
    (hi2 : ¬ (i + 2 < l.length)) (hlen : l.length < 2 ^ 62)
    (h32 : (cv == 32) = false) (h9 : (cv == 9) = false)
    (h10 : (cv == 10) = false) (h11 : (cv == 11) = false)
    (h12 : (cv == 12) = false) (h13 : (cv == 13) = false)
    (h194 : (cv == 194) = false) :
    stepFnIter 73
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.exec scIfW (scEnvBC na) (.seq [] (scEnvBC na) scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) := by
  have hlookc : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2)).heap
      (.base ⟨na + 1⟩) = some (su8 cv) :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 fv false (by omega) (lookup_c2of2 hD)
  have h0 : stepFnIter 46
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec goleanShimStringsFieldsFunc.scClassify (scEnvBC na)
        (scKifW na)) ch
      = .ok (.retV (.bool false) (scKw1 na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) :=
    ck_cls1F _ na cv ch hlookc h32 h9 h10 h11 h12 h13
  have h1 : stepFnIter 12
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
        false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.retV (.bool false) (scKw1 na)) ch
      = .ok (.exec scIf3 (scEnvBC na) (scKifW na),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
            fv false
            (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
            (na + 2), ch) :=
    ck_c2F _ na cv ch hlookc h194
  have h2 := ck_if3 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 fv
    (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)]) (na + 2) na
    ch
  rw [show ((i : Nat) : Int) + 2 = ((i + 2 : Nat) : Int) from by omega,
    inorm_nat_of_lt (show i + 2 < 2 ^ 63 by omega),
    show (decide (((i + 2 : Nat) : Int) < ((l.length : Nat) : Int)))
        = false from decide_eq_false (by exact_mod_cast hi2)] at h2
  have h3 := ck_ifKF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2 fv
      false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2)) goleanShimStringsFieldsFunc.scC3Block (.seqn #[])
    (scEnvBC na) (scKifW na) ch
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    (ss := #[]) (env := scEnvBC na) (rest := [scIfW])
    (k := scPostBody) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      fv false (D ++ [(.base ⟨na⟩, sint 0), (.base ⟨na + 1⟩, su8 cv)])
      (na + 2))
    (t := scIfW) (rest := []) (env := scEnvBC na) (k := scPostBody)
    (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h0 h1) h2) h3) h4) h5

end ClsLetter

/-! ## The arm layer: heap helpers, statements, envs, chunks -/

/-- A set at a present key is looked up as the new cell. -/
theorem lookup_set_self (h : Heap) (l : Loc) (c : HeapCell) :
    Heap.lookup (Heap.set h l c) l = some c := by
  induction h with
  | nil =>
      simp [Heap.set, Heap.lookup]
  | cons kv rest ih =>
      obtain ⟨k, c₀⟩ := kv
      simp only [Heap.set]
      by_cases hk : (k == l) = true
      · rw [if_pos hk]
        simp [Heap.lookup, hk]
      · rw [if_neg hk]
        simp only [Heap.lookup, hk, Bool.false_eq_true, if_false]
        exact ih

theorem lookup_c6of6 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 c5 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4),
        (.base ⟨na + 5⟩, c5)]) (.base ⟨na + 5⟩) = some c5 := by
  rw [lookup_append_right (hD (na + 5) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 5)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 5)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 5)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 5)),
    lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 5))]
  simp [Heap.lookup]

/-- Setting the FIFTH cell of a 6-cell suffix. -/
theorem set_c5of6 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 c5 c4' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4),
        (.base ⟨na + 5⟩, c5)]) (.base ⟨na + 4⟩) c4'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
          (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3),
          (.base ⟨na + 4⟩, c4'), (.base ⟨na + 5⟩, c5)] := by
  rw [set_append_right (hD (na + 4) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 4),
    base_beq_false (by omega : na + 1 ≠ na + 4),
    base_beq_false (by omega : na + 2 ≠ na + 4),
    base_beq_false (by omega : na + 3 ≠ na + 4)]

abbrev scEnvA1 (a : Nat) : LocalEnv := [] :: scEnvBC a
abbrev scEnvA2 (a : Nat) : LocalEnv := [] :: [] :: scEnvBC a
abbrev scEnvS16 (a : Nat) : LocalEnv :=
  [("$c16", .base ⟨a + 2⟩)] :: [] :: scEnvBC a
abbrev scEnvS17 (a : Nat) : LocalEnv :=
  [("$c17", .base ⟨a + 4⟩), ("$c16", .base ⟨a + 2⟩)] :: [] :: scEnvBC a

abbrev scKPost1 (a : Nat) : Cont := .seq [] (scEnvBC a) scPostBody
abbrev scKArm (a : Nat) : Cont :=
  .ifK goleanShimStringsFieldsFunc.scSepArm
    goleanShimStringsFieldsFunc.scLetterArm (scEnvBC a) (scKPost1 a)
abbrev scAsgnI1 : Stmt :=
  .assign (.var "i") (.add (.var "i") (.intLit 1 .int))
abbrev scAsgnIW : Stmt :=
  .assign (.var "i") (.add (.var "i") (.var "w"))
abbrev scKL1 (a : Nat) : Cont := .seq [scAsgnI1] (scEnvA1 a) (scKPost1 a)
abbrev scKClose (a : Nat) : Cont :=
  .seq [scAsgnIW] (scEnvA1 a) (scKPost1 a)
abbrev scStStart : Stmt := .seqn #[.assign (.var "start") (.var "i")]
abbrev scStInFT : Stmt :=
  .seqn #[.assign (.var "inField") (.boolLit true)]
abbrev scStInFF : Stmt :=
  .seqn #[.assign (.var "inField") (.boolLit false)]
abbrev scMkSl16 : Stmt :=
  .makeSlice (.var "$c16") tStr (.intLit 1 .int) (some (.intLit 1 .int))
abbrev scAsgnAddr16 : Stmt :=
  .assign (.addr (.indexAddr (.var "$c16") (.intLit 0 .int)))
    (.slice (.var "s") (.var "start") (.var "i") none)
abbrev scStC16 : Stmt :=
  .seqn #[.initialization { id := "$c16", typ := tSlS }, scMkSl16,
    scAsgnAddr16]
abbrev scApp17 : Stmt :=
  .appendSlice (.var "$c17") tStr (.var "out") (.var "$c16")
abbrev scStC17 : Stmt :=
  .seqn #[.initialization { id := "$c17", typ := tSlS }, scApp17]
abbrev scAsgnOut : Stmt := .assign (.var "out") (.var "$c17")
abbrev scStOut : Stmt := .seqn #[scAsgnOut]

/-- Arm head: `if` dispatch, the `w > 0` read point. 2 steps. -/
theorem ck_armDesc (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 2 σ (.exec scIfW (scEnvBC a) (scKPost1 a)) ch
      = .ok (.evalE (.var "w") (scEnvBC a)
          (.strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
            (scKArm a)), σ, ch) := by
  with_unfolding_all rfl

section ArmChunks

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (iv sv2 : Int)
  (fv : Bool) (D₂ : Heap) (na₂ a : Nat) (rest : List Stmt) (k : Cont)
  (ch : Choices)

/-- Letter arm entry (`w = 0`, not in field): verdict false, the
letter arm's open-field block reached. 13 steps. -/
theorem ck_armLet1 :
    stepFnIter 13
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 false false D₂
        na₂)
      (.retV (.int 0 .int)
        (.strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
          (scKArm a))) ch
      = .ok (.exec scStStart (scEnvA2 a)
            (.seq [scStInFT] (scEnvA2 a) (scKL1 a)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 false false
            D₂ na₂, ch) := by
  with_unfolding_all rfl

/-- `start = i` (front store). 8 steps. -/
theorem ck_armStart :
    stepFnIter 8
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (.assign (.var "start") (.var "i") :: rest)
        (scEnvA2 a) k)) ch
      = .ok (.exec (.seqn #[]) (scEnvA2 a) (.seq rest (scEnvA2 a) k),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv
            (IntKind.normalize .int iv) fv false D₂ na₂, ch) := by
  with_unfolding_all rfl

/-- `inField = true` (front store). 8 steps. -/
theorem ck_armInF :
    stepFnIter 8
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (.assign (.var "inField") (.boolLit true) :: rest)
        (scEnvA2 a) k)) ch
      = .ok (.exec (.seqn #[]) (scEnvA2 a) (.seq rest (scEnvA2 a) k),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- The letter arm's `i = i + 1` (front). 13 steps. -/
theorem ck_armIncL :
    stepFnIter 13
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq [] (scEnvA2 a) (scKL1 a))) ch
      = .ok (.exec (.seqn #[]) (scEnvA1 a)
            (.seq [] (scEnvA1 a) (scKPost1 a)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            sv2 fv false D₂ na₂, ch) := by
  with_unfolding_all rfl

/-- Arm exit: drained scopes, back to the loop head. 4 steps. -/
theorem ck_armEnd (a : Nat) :
    stepFnIter 4 σ (.next (.seq [] (scEnvA1 a) (scKPost1 a))) ch
      = .ok (scHeadCfg, σ, ch) := by
  with_unfolding_all rfl

/-- Separator arm entry, NOT in field (`w = 1`): verdict true, the
append `if` skipped. 9 steps. -/
theorem ck_skip1 :
    stepFnIter 9
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 false false D₂
        na₂)
      (.retV (.int 1 .int)
        (.strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
          (scKArm a))) ch
      = .ok (.exec (.seqn #[]) (scEnvA1 a) (scKClose a),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 false false
            D₂ na₂, ch) := by
  with_unfolding_all rfl

/-- `i = i + w`, to the `w` read. 7 steps. -/
theorem ck_skip2 :
    stepFnIter 7
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (scAsgnIW :: rest) (scEnvA1 a) k)) ch
      = .ok (.evalE (.var "w") (scEnvA1 a)
            (.strictK .add [.int iv .int] [] (scEnvA1 a)
              (.rhsK .vals [bRef 27] [] [] (.seqn #[]) (scEnvA1 a)
                (.seq rest (scEnvA1 a) k))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- `i = i + w` completes (`w` delivered as 1, front store). 4
steps. -/
theorem ck_skip3 :
    stepFnIter 4
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.retV (.int 1 .int)
        (.strictK .add [.int iv .int] [] (scEnvA1 a)
          (.rhsK .vals [bRef 27] [] [] (.seqn #[]) (scEnvA1 a)
            (.seq rest (scEnvA1 a) k)))) ch
      = .ok (.exec (.seqn #[]) (scEnvA1 a) (.seq rest (scEnvA1 a) k),
          scSt σ nv sv qv bnv bsv l q biv b cap fs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            sv2 fv false D₂ na₂, ch) := by
  with_unfolding_all rfl

/-- Separator arm entry, IN field (`w = 1`): verdict true, the append
block reached. 11 steps. -/
theorem ck_close1 :
    stepFnIter 11
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false D₂
        na₂)
      (.retV (.int 1 .int)
        (.strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
          (scKArm a))) ch
      = .ok (.exec scStC16 (scEnvA2 a)
            (.seq [scStC17, scStOut, scStInFF] (scEnvA2 a)
              (scKClose a)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- `make([]string, 1, 1)` to the apply point. 7 steps. -/
theorem ck_mkSl (a : Nat) :
    stepFnIter 7 σ (.next (.seq (scMkSl16 :: rest) (scEnvS16 a) k)) ch
      = .ok (.retV (.int 1 .int)
          (.stmtOpK (.makeSlice tStr true) 1
            [.int 1 .int, .addr (.base ⟨a + 2⟩)] [] (scEnvS16 a)
            (.seq rest (scEnvS16 a) k)), σ, ch) := by
  with_unfolding_all rfl

/-- The `$c16[0] = …` target evaluation head. 2 steps. -/
theorem ck_c16a (a : Nat) :
    stepFnIter 2 σ (.next (.seq (scAsgnAddr16 :: rest) (scEnvS16 a) k))
      ch
      = .ok (.evalE (.var "$c16") (scEnvS16 a)
          (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
            [.slice (.var "s") (.var "start") (.var "i") none] []
            (.seqn #[]) (scEnvS16 a) (.seq rest (scEnvS16 a) k)),
          σ, ch) := by
  with_unfolding_all rfl

/-- The slice `s[start:i]` argument reads (front), to the slice apply
point. 9 steps. -/
theorem ck_c16b :
    stepFnIter 9
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.retV (.slice ⟨some (.base ⟨a + 3⟩), 0, 1, 1⟩)
        (.tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
          [.slice (.var "s") (.var "start") (.var "i") none] []
          (.seqn #[]) (scEnvS16 a) (.seq rest (scEnvS16 a) k))) ch
      = .ok (.retV (.int iv .int)
            (.strictK (.sliceExpr false) [.int sv2 .int, .string (gs l)]
              [] (scEnvS16 a)
              (.rhsK .vals
                [.chain (slsVal (a + 3) 0 1 1) [.int 0 .int] [.index]]
                [] [] (.seqn #[]) (scEnvS16 a)
                (.seq rest (scEnvS16 a) k))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- `$c17 = append(out, $c16...)`: target and `out` read (front), to
the `$c16` read. 6 steps. -/
theorem ck_c17a :
    stepFnIter 6
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (scApp17 :: rest) (scEnvS17 a) k)) ch
      = .ok (.evalE (.var "$c16") (scEnvS17 a)
            (.stmtOpK (.appendSlice tStr) 1
              [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
                .addr (.base ⟨a + 4⟩)] [] (scEnvS17 a)
              (.seq rest (scEnvS17 a) k)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- `out = $c17`: target head, to the `$c17` read. 3 steps. -/
theorem ck_outa (a : Nat) :
    stepFnIter 4 σ (.next (.seq (scAsgnOut :: rest) (scEnvS17 a) k)) ch
      = .ok (.evalE (.var "$c17") (scEnvS17 a)
          (.rhsK .vals [bRef 26] [] [] (.seqn #[]) (scEnvS17 a)
            (.seq rest (scEnvS17 a) k)), σ, ch) := by
  with_unfolding_all rfl

/-- `out = $c17` completes: the delivered handle lands at front cell
26. 3 steps. -/
theorem ck_outb (b' cap' : Nat) (fs' : List (List UInt8)) :
    stepFnIter 3
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.retV (.slice ⟨some (.base ⟨b'⟩), 0, fs'.length, cap'⟩)
        (.rhsK .vals [bRef 26] [] [] (.seqn #[]) (scEnvS17 a)
          (.seq rest (scEnvS17 a) k))) ch
      = .ok (.exec (.seqn #[]) (scEnvS17 a) (.seq rest (scEnvS17 a) k),
          scSt σ nv sv qv bnv bsv l q biv b' cap' fs' iv sv2 fv false D₂
            na₂, ch) := by
  with_unfolding_all rfl

/-- `inField = false` (front store, at the append env). 8 steps. -/
theorem ck_closeInF :
    stepFnIter 8
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D₂ na₂)
      (.next (.seq (.assign (.var "inField") (.boolLit false) :: rest)
        (scEnvS17 a) k)) ch
      = .ok (.exec (.seqn #[]) (scEnvS17 a) (.seq rest (scEnvS17 a) k),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 false false D₂
            na₂, ch) := by
  with_unfolding_all rfl

end ArmChunks

/-! ## The arm composites -/

section Arms

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (sv2 : Int)
  (D₂ : Heap) (na₂ a : Nat) (ch : Choices)

/-- **The letter arm** (`w = 0`, not in field): open the field
(`start := i`, `inField := true`), `i := i + 1`, loop head. 55
steps. -/
theorem sc_arm_letter (i : Nat) (ha31 : 31 ≤ a)
    (hw : Heap.lookup D₂ (.base ⟨a⟩) = some (sint 0))
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 55
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false false D₂ na₂)
      (.exec scIfW (scEnvBC a) (scKPost1 a)) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs
            ((i + 1 : Nat) : Int) ((i : Nat) : Int) true false D₂ na₂,
          ch) := by
  have h0 := ck_armDesc
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      false false D₂ na₂) a ch
  have h1 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 false false D₂ na₂)
    (x := "w") (env := scEnvBC a) (a := ⟨a⟩)
    (k := .strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
      (scKArm a)) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 false false ha31 hw))
  have h2 := ck_armLet1 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 D₂ na₂ a ch
  have h3 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 false false D₂ na₂)
    (ss := #[.assign (.var "start") (.var "i")]) (env := scEnvA2 a)
    (rest := [scStInFT]) (k := scKL1 a) (ch := ch))
  have h4 := ck_armStart σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D₂ na₂ a [scStInFT] (scKL1 a) ch
  rw [inorm_nat_of_lt (show i < 2 ^ 63 by omega)] at h4
  have h5 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((i : Nat) : Int) false false D₂ na₂)
    (ss := #[]) (env := scEnvA2 a) (rest := [scStInFT]) (k := scKL1 a)
    (ch := ch))
  have h6 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((i : Nat) : Int) false false D₂ na₂)
    (t := scStInFT) (rest := []) (env := scEnvA2 a) (k := scKL1 a)
    (ch := ch))
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((i : Nat) : Int) false false D₂ na₂)
    (ss := #[.assign (.var "inField") (.boolLit true)])
    (env := scEnvA2 a) (rest := []) (k := scKL1 a) (ch := ch))
  have h8 := ck_armInF σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((i : Nat) : Int) false D₂ na₂ a [] (scKL1 a) ch
  have h9 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((i : Nat) : Int) true false D₂ na₂)
    (ss := #[]) (env := scEnvA2 a) (rest := []) (k := scKL1 a)
    (ch := ch))
  have h10 := ck_armIncL σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((i : Nat) : Int) true D₂ na₂ a ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt hi63, inorm_nat_of_lt hi63] at h10
  have h11 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs
      ((i + 1 : Nat) : Int) ((i : Nat) : Int) true false D₂ na₂)
    (ss := #[]) (env := scEnvA1 a) (rest := []) (k := scKPost1 a)
    (ch := ch))
  have h12 := ck_armEnd
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int)
      ((i : Nat) : Int) true false D₂ na₂) ch a
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h0 h1)
          h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12

/-- **The separator skip arm** (`w = 1`, not in field): `i := i + 1`,
loop head. 30 steps. -/
theorem sc_arm_skip (i : Nat) (ha31 : 31 ≤ a)
    (hw : Heap.lookup D₂ (.base ⟨a⟩) = some (sint 1))
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 30
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false false D₂ na₂)
      (.exec scIfW (scEnvBC a) (scKPost1 a)) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs
            ((i + 1 : Nat) : Int) sv2 false false D₂ na₂, ch) := by
  have h0 := ck_armDesc
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      false false D₂ na₂) a ch
  have h1 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 false false D₂ na₂)
    (x := "w") (env := scEnvBC a) (a := ⟨a⟩)
    (k := .strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC a)
      (scKArm a)) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 false false ha31 hw))
  have h2 := ck_skip1 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 D₂ na₂ a ch
  have h3 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 false false D₂ na₂)
    (ss := #[]) (env := scEnvA1 a) (rest := [scAsgnIW])
    (k := scKPost1 a) (ch := ch))
  have h4 := ck_skip2 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D₂ na₂ a [] (scKPost1 a) ch
  have h5 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 false false D₂ na₂)
    (x := "w") (env := scEnvA1 a) (a := ⟨a⟩)
    (k := .strictK .add [.int ((i : Nat) : Int) .int] [] (scEnvA1 a)
      (.rhsK .vals [bRef 27] [] [] (.seqn #[]) (scEnvA1 a)
        (.seq [] (scEnvA1 a) (scKPost1 a)))) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 false false ha31 hw))
  have h6 := ck_skip3 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D₂ na₂ a [] (scKPost1 a) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt hi63, inorm_nat_of_lt hi63] at h6
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs
      ((i + 1 : Nat) : Int) sv2 false false D₂ na₂)
    (ss := #[]) (env := scEnvA1 a) (rest := []) (k := scKPost1 a)
    (ch := ch))
  have h8 := ck_armEnd
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int) sv2
      false false D₂ na₂) ch a
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h0 h1) h2) h3) h4) h5) h6)
        h7) h8

end Arms

theorem lookup_c5of6 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c4 c5 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3), (.base ⟨na + 4⟩, c4),
        (.base ⟨na + 5⟩, c5)]) (.base ⟨na + 4⟩) = some c4 := by
  rw [lookup_append_right (hD (na + 4) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
  simp [Heap.lookup]

/-- Collapsing nested state pins (structure eta). -/
theorem wSt_wSt (σ : ExecState) (H₀ H : Heap) (n₀ n : Nat) :
    wSt (wSt σ H₀ n₀) H n = wSt σ H n := rfl

/-- The `$c15` backing (front cell 25) is always the empty 0-cap
array. -/
theorem lookup_scan25 (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv sv2 : Int) (fv ffv : Bool)
    (D : Heap) :
    Heap.lookup
        (wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 fv ffv ++ D)
        (.base ⟨25⟩) = some (strArrCell [] 0) := by
  with_unfolding_all rfl

section CloseTail

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (sv2 : Int)
  (D₅ : Heap) (na₅ a : Nat) (ch : Choices)

/-- **The append block's tail**: `out = $c17`, `inField = false`,
`i = i + w`, loop head — generic in the debris and in the new handle.
40 steps. -/
theorem sc_closeTail (i : Nat) (b' cap' : Nat) (fs' : List (List UInt8))
    (ha31 : 31 ≤ a)
    (h17 : Heap.lookup D₅ (.base ⟨a + 4⟩)
      = some ⟨some tSlS, slsVal b' 0 fs'.length cap'⟩)
    (hw : Heap.lookup D₅ (.base ⟨a⟩) = some (sint 1))
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 40
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false D₅ na₅)
      (.next (.seq [scStOut, scStInFF] (scEnvS17 a) (scKClose a))) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b' cap' fs'
            ((i + 1 : Nat) : Int) sv2 false false D₅ na₅, ch) := by
  have h0 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (t := scStOut) (rest := [scStInFF]) (env := scEnvS17 a)
    (k := scKClose a) (ch := ch))
  have h1 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (ss := #[scAsgnOut]) (env := scEnvS17 a) (rest := [scStInFF])
    (k := scKClose a) (ch := ch))
  have h2 := ck_outa
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
      true false D₅ na₅) [scStInFF] (scKClose a) ch a
  have h3 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (x := "$c17") (env := scEnvS17 a) (a := ⟨a + 4⟩)
    (k := .rhsK .vals [bRef 26] [] [] (.seqn #[]) (scEnvS17 a)
      (.seq [scStInFF] (scEnvS17 a) (scKClose a))) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 true false (by omega) h17))
  have h4 := ck_outb σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 true D₅ na₅ a [scStInFF] (scKClose a) ch
    b' cap' fs'
  have h5 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (ss := #[]) (env := scEnvS17 a) (rest := [scStInFF])
    (k := scKClose a) (ch := ch))
  have h6 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (t := scStInFF) (rest := []) (env := scEnvS17 a) (k := scKClose a)
    (ch := ch))
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int)
      sv2 true false D₅ na₅)
    (ss := #[.assign (.var "inField") (.boolLit false)])
    (env := scEnvS17 a) (rest := []) (k := scKClose a) (ch := ch))
  have h8 := ck_closeInF σ nv sv qv bnv bsv l q biv b' cap' fs'
    ((i : Nat) : Int) sv2 true D₅ na₅ a [] (scKClose a) ch
  have h9 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int)
      sv2 false false D₅ na₅)
    (ss := #[]) (env := scEnvS17 a) (rest := []) (k := scKClose a)
    (ch := ch))
  have h10 := ck_seqNil
    (scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int) sv2
      false false D₅ na₅) (scEnvS17 a) (scKClose a) ch
  have h11 := ck_skip2 σ nv sv qv bnv bsv l q biv b' cap' fs'
    ((i : Nat) : Int) sv2 false D₅ na₅ a [] (scKPost1 a) ch
  have h12 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i : Nat) : Int)
      sv2 false false D₅ na₅)
    (x := "w") (env := scEnvA1 a) (a := ⟨a⟩)
    (k := .strictK .add [.int ((i : Nat) : Int) .int] [] (scEnvA1 a)
      (.rhsK .vals [bRef 27] [] [] (.seqn #[]) (scEnvA1 a)
        (.seq [] (scEnvA1 a) (scKPost1 a)))) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b' fs'.length cap'
      ((i : Nat) : Int) sv2 false false ha31 hw))
  have h13 := ck_skip3 σ nv sv qv bnv bsv l q biv b' cap' fs'
    ((i : Nat) : Int) sv2 false D₅ na₅ a [] (scKPost1 a) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt hi63, inorm_nat_of_lt hi63] at h13
  have h14 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b' cap' fs'
      ((i + 1 : Nat) : Int) sv2 false false D₅ na₅)
    (ss := #[]) (env := scEnvA1 a) (rest := []) (k := scKPost1 a)
    (ch := ch))
  have h15 := ck_armEnd
    (scSt σ nv sv qv bnv bsv l q biv b' cap' fs' ((i + 1 : Nat) : Int)
      sv2 false false D₅ na₅) ch a
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h0 h1)
            h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14)
              h15

end CloseTail

/-! ## The separator CLOSE arm (the append, in-place or spill) -/

/-- The spill append MACHINE STEP, state-abstract: conditioned on the
cell facts, one step consumes a capacity choice and lands the fresh
backing at the allocator. -/
theorem sc_spillStep (σ₀ : ExecState) (a b cap : Nat)
    (fs : List (List UInt8)) (f : List UInt8) (env : LocalEnv)
    (k : Cont) (ch : Choices)
    (hna : σ₀.nextAddr = a + 5)
    (hb : Heap.lookup σ₀.heap (.base ⟨b⟩) = some (strArrCell fs cap))
    (he : Heap.lookup σ₀.heap (.base ⟨a + 3⟩)
      = some ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)
    (ht : Heap.lookup σ₀.heap (.base ⟨a + 4⟩) = some slsNil)
    (heq : fs.length = cap) :
    ∃ (newCap : Nat) (ch' : Choices), fs.length + 1 ≤ newCap ∧
    stepFnIter 1 σ₀
      (.retV (.slice ⟨some (.base ⟨a + 3⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice tStr) 1
          [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
            .addr (.base ⟨a + 4⟩)] [] env k)) ch
      = .ok (.next k,
          wSt σ₀
            (Heap.set
              (Heap.set σ₀.heap (.base ⟨a + 5⟩)
                (strArrCell (fs ++ [f]) newCap))
              (.base ⟨a + 4⟩)
              ⟨some tSlS, slsVal (a + 5) 0 (fs.length + 1) newCap⟩)
            (a + 6), ch') := by
  obtain ⟨newCap, ch', hbound, happly⟩ :=
    applyStmtOp_append_str_spill (σ := σ₀) (t := a + 4) (b := b)
      (e := a + 3) (fs := fs) (cap := cap) (f := f) (ch := ch)
      hb he ht (by omega) heq
  rw [hna] at happly
  exact ⟨newCap, ch', hbound,
    stepFnIter_one (stepFn_stmtOp_apply
      (done := [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
        .addr (.base ⟨a + 4⟩)])
      (env := env) (k := k) happly)⟩

/-! ## FORMER PARKED BOUNDARY (W3, 2026-08-16) — UN-PARKED by W4a
(same day): the close-arm composite and everything after it now live
in `Scan3.lean` (`sc_arm_close`, the iteration composites, `sc_word`/
`sc_loop`, `sc_exit_raw`, `scan_phase`, `build_scan_chain` — all
green, 16 s module build). ROOT CAUSE of the 50-min storm below, found
by W4a via a forced type-mismatch print: in a POSITIONAL big-state
argument of a term application (`sc_spillStep (scSt … (D ++ [(.base
⟨na⟩, …), …]) …) …`), the pair-position `.base` dot-notation stays a
POSTPONED metavariable when the expected `hb` argument type is formed,
so isDefEq falls back to whnf-reducing `Heap.lookup`/`BEq` over the
symbolic heap (502k `BEq.beq` unfoldings measured under
`set_option diagnostics true`). Fix: write `Loc.base` explicitly (or
pin the application's type) in proof-body state arguments — the split
chains + opaque-substring repair below is also applied in `Scan3` and
keeps each theorem cheap, but the qualification is what removed the
storm (12 s for the whole close arm). The historical analysis follows,
kept for the record.

Everything ABOVE is green: the positional pure layer (`wPos`,
`textFamily_length/drop/getD_letter/getD_sep1/getD_sep2/slice_word`),
the second heap-helper batch (`set_c1of2` … `lookup_c6of6`,
`DeadFrom.push3/5/6`, `lookup_set_self`, `wSt_wSt`, `lookup_scan25`),
the byte-block prefix `sc_prefix` (35 steps), all four classifies
(`sc_cls_sep32` 31, `sc_cls_sep9` 37, `sc_cls_letter_long` 165,
`sc_cls_letter_short` 73), the letter/skip arms (`sc_arm_letter` 55,
`sc_arm_skip` 30), the append tail `sc_closeTail` (40) and the
state-abstract spill step `sc_spillStep`.

PARKED HERE: the close-arm COMPOSITE (`sc_arm_close_pre`, 53 steps to
the append apply point, + `sc_arm_close`, 94 steps with the
in-place/spill case split). Full drafts, believed mathematically
correct and mechanically complete, in
`.tmp/e5-drafts/w3-close-arm-draft.lean`. They elaborate without any
reported unification FAILURE but at pathological cost, and NOT as an
LSP artifact: a standalone BATCH `lake env lean` of the draft
(`.tmp/e5-drafts/w3closearm-batchtest.lean`) ran 50 min at 100 % CPU
without finishing (killed by timeout), while the WHOLE shipped module
batch-builds in 1 min 50 s / 2.0 GiB peak. The equally-long
`sc_cls_letter_long` (37 links) checks in minutes. What is known:

* the storm is NOT in the rfl chunks (all its chunks are shipped green
  above) — it is in the big-state `have`-chains of the composite;
* pinning every `have`'s full result type (the StepKit E-form) fixed
  the identical storms in `sc_cls_letter_long` — applied here it moved
  the timeout forward but did not resolve it;
* the remaining suspects are (a) the 22-link `stepFnIter_chain` fold
  over states embedding `gs ((l.drop s).take (i - s))` (chain links
  re-unify the full state each application), (b) the ∃-obtain on
  `applyStmtOp_append_str_spill`/`sc_spillStep` at a concrete state.
  Recommended repair for the successor: split the prefix into 3–4
  SEPARATE theorems of ≤ 8 links each (each new theorem resets the
  cost and keeps every chain-unification small), and/or abstract the
  substring `f := (l.drop s).take (i - s)` as an opaque `(f : List
  UInt8)` parameter of the composite (nothing in the machine steps
  inspects it — only `gs f` is carried), which shrinks every state
  term substantially.

After `sc_arm_close`, the remaining plan (unchanged from the estimate):
1. iteration composites: `sc_iter0` (first pass, A0 27 + prefix 35 +
   cls32 31 + skip 30 = 123), `sc_iter_skip` (A1 20 + … = 116),
   `sc_iter_close32/9` (180/186), `sc_iter_letter_long/short`
   (275/183) — each = dispatch rewrite (`decide` via
   `textFamily_length`/`wPos` bounds) + `sc_prefix` + classify (letter
   uses `beqF`-style facts from `textFamily_getD_letter` +
   `letterByte_ge/le`) + arm;
2. the word composite (`i%3` split via `sepBytes_length`, positions via
   `wPos_succ_*`, words via `textFamily_slice_word` +
   `letterWords_succ`) and the ∃k ≤ 600·(n−j) loop (bt_loop shape,
   carrying ∃ b cap D na ch and the `hbOr` backing disjunction);
3. the exit segment (A1 20 + 28 steps from `.retV (.bool false)
   scCmpK` to `.exec (.seqn #[]) wfEnvW wfAfterShim`, all front-cell
   ops — one rfl chunk against a new 31-cell `wHeapCount` former) and
   the assembled `scan_phase` (79 + 123 + 600·n + 20 + 28 ≤
   600·n + 250 from the shim-body exec at `wHeapShim`), then the
   build→scan chain at the `wfAfterShim` seam.
-/

end GoLean.Examples.WordFreq
