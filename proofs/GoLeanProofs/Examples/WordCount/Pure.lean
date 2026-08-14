import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.Targets

/-!
# WordCount — Pure

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The specification layer (order-independent, per §10b) -/

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `multiplicity` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

-- HOISTED to `GoLeanProofs/Examples/Targets.lean` (designation, 2026-08-14):
-- `maxMultiplicity` is statement vocabulary of a DESIGNATED gallery headline, so it must
-- live in a def-only module inside the Comparator Challenge's trusted import
-- closure. The definition is unchanged and still visible here via the import.

-- PROMOTED to `GoLeanProofs/MapMem.lean` (Gallery Campaign G0 item 3b,
-- 2026-08-15): the §10a map-in-memory vocabulary (`mapCells`/`mapVal`)
-- now lives in the shared MapMem module beside the executable map-op
-- facts; visible here via the import + `open GoLean.MapMem`.

/-! ## The program-side statement vocabulary -/

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def maxCountFunc : Func :=
  { id := { key := "maxCount" },
    args := #[{ id := "words", typ := .slice (.int .uint64) }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization
              { id := "$c0", typ := .map (.int .uint64) (.int .uint64) },
            .makeMap (.var "$c0") (.int .uint64) (.int .uint64) none],
        .seqn
          #[.initialization
              { id := "counts", typ := .map (.int .uint64) (.int .uint64) },
            .assign (.var "counts") (.var "$c0")],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 0 .int)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true)
                  (.block
                    #[]
                    #[.ifThenElse (.var "$forFirst")
                        (.assign (.var "$forFirst") (.boolLit false))
                        (.assign (.var "i")
                          (.add (.var "i") (.intLit 1 .int))),
                      .seqn #[],
                      .ifThenElse
                        (.lessCmp (.var "i")
                          (.length (.var "words")
                            (some (.slice (.int .uint64)))))
                        (.seqn #[])
                        .breakStmt,
                      .block
                        #[]
                        #[.seqn
                            #[.initialization
                                { id := "$c1",
                                  typ := .map (.int .uint64) (.int .uint64) },
                              .assign (.var "$c1") (.var "counts")],
                          .seqn
                            #[.initialization
                                { id := "$c2", typ := .int .uint64 },
                              .assign (.var "$c2")
                                (.indexGet (.var "words") (.var "i"))],
                          .mapAssign (.var "$c1") (.var "$c2")
                            (.add
                              (.mapGet (.var "$c1") (.var "$c2")
                                (.int .uint64) (.int .uint64))
                              (.intLit 1 .uint64))
                            (.int .uint64) (.int .uint64)]])]],
        .seqn
          #[.initialization { id := "best", typ := .int .uint64 },
            .assign (.var "best") (.intLit 0 .uint64)],
        .mapRange none (some "c") (.var "counts") (.int .uint64) (.int .uint64)
          (.block
            #[]
            #[.ifThenElse (.greaterCmp (.var "c") (.var "best"))
                (.block
                  #[]
                  #[.seqn #[.assign (.var "best") (.var "c")]])
                (.seqn #[])]),
        .seqn
          #[.assign (.var "$res0") (.var "best"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? wordCountLowered.funcs ⟨"maxCount"⟩
    = some maxCountFunc := rfl

/-- The harness cell the differential runner also reads. -/
def wcEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The zeroed uint64 result cell at address `0`. -/
def wcResCell : Heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

/-- The driver: `$callres = maxCount(words)` — the words slice enters
as a slice expression over the backing array at `base` (the §9a
memory-input convention). -/
def wcCall (ws : List Int) (base : Nat) : Stmt :=
  .call #[.var "$callres"] ⟨"maxCount"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit ws.length .int) none]

/-- The framed seed: result cell, the input's backing cell at `base`,
an arbitrary frame `fr`, allocator at `na`. The canonical placement is
`wcSeed ws 1 [] 2` — TIGHT (dom = {0, 1}, na₀ = 2), as the frame
theorem's seed discharge requires. -/
def wcSeed (ws : List Int) (base : Nat) (fr : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := wcResCell ++ sliceCells ws base ++ fr, nextAddr := na }

/-! ## The counts encoding and the machine map facts — PROMOTED

The whole family — `idxOf?`/`cnt`/`setk`/`toEntries`, the model
lemmas, `scan_generic`, `mapEntryIndex?_toEntries`,
`applyStrictOp_mapGet`, `mapAssignValue_toEntries`,
`snapshot_toEntries`, and the `toEntries` bridges — was born here
flagged as a "SliceMem promotion candidate" and is now
`GoLeanProofs/MapMem.lean` (Gallery Campaign G0 item 3b, 2026-08-15;
landed consumer: this example, chartered: histogram + fibonacci-memo).
Everything below consumes it via `open GoLean.MapMem`; only
wordcount's own spec layer (`bump`/`countsList`/the max fold) stays. -/

/-! ## The heap-append kit (symbolic-address algebra, §10c)

The in-loop cells live at length-dependent addresses past the nine
concrete front cells, so their reads/writes are discharged by this
small append algebra instead of definitional reduction. -/

/-! ## The pure counts layer: `bump`, `countsList`, and the max fold -/

/-- One word lands in the counts list: increment the first occurrence
of the key, or append `(v, 1)` — first-occurrence insertion order,
matching the machine's `mapAssign`. -/
def bump : List (Int × Nat) → Int → List (Int × Nat)
  | [], v => [(v, 1)]
  | (k, c) :: rest, v =>
      if k = v then (k, c + 1) :: rest else (k, c) :: bump rest v

/-- The counts list after processing `ws`, in first-occurrence
insertion order — the abstract content of the map data cell. -/
def countsList (ws : List Int) : List (Int × Nat) :=
  ws.foldl bump []

/-- What the machine's write computes is `bump`: the value written is
`counts[w] + 1` at the first occurrence (or `0 + 1` fresh). -/
theorem setk_cnt_succ :
    ∀ (kvs : List (Int × Nat)) (w : Int),
    setk kvs w (cnt kvs w + 1) = bump kvs w := by
  intro kvs
  induction kvs with
  | nil => intro w; rfl
  | cons kv rest ih =>
      intro w
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp [setk, cnt, bump, hk]
      · simp [setk, cnt, bump, hk, ih w]

theorem countsList_append_word (p : List Int) (w : Int) :
    countsList (p ++ [w]) = bump (countsList p) w := by
  simp [countsList, List.foldl_append]

private theorem multiplicity_nil (v : Int) : multiplicity v [] = 0 := rfl

private theorem multiplicity_cons (v w : Int) (ws : List Int) :
    multiplicity v (w :: ws)
      = (if w = v then 1 else 0) + multiplicity v ws := by
  simp only [multiplicity, List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

/-- `cnt` after a `bump`. -/
private theorem cnt_bump (kvs : List (Int × Nat)) (w x : Int) :
    cnt (bump kvs w) x
      = if x = w then cnt kvs w + 1 else cnt kvs x := by
  induction kvs with
  | nil =>
      by_cases hx : x = w
      · simp [bump, cnt, hx]
      · simp [bump, cnt, hx, Ne.symm hx]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · subst hk
        by_cases hx : x = k
        · simp [bump, cnt, hx]
        · simp [bump, cnt, Ne.symm hx, hx]
      · by_cases hxk : k = x
        · subst hxk
          simp [bump, cnt, hk]
        · simp [bump, cnt, hk, hxk, ih]

/-- **The counts-list invariant**: after processing `ws`, `cnt` at any
key is its multiplicity (0 included on both sides for absent keys). -/
private theorem cnt_countsList (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (x : Int),
    cnt (List.foldl bump kvs ws) x = cnt kvs x + multiplicity x ws := by
  induction ws with
  | nil => intro kvs x; simp [multiplicity_nil]
  | cons w rest ih =>
      intro kvs x
      simp only [List.foldl_cons, ih, cnt_bump, multiplicity_cons]
      by_cases hx : x = w
      · subst hx
        have h1 : (if x = x then cnt kvs x + 1 else cnt kvs x)
            = cnt kvs x + 1 := if_pos rfl
        have h2 : (if x = x then 1 else 0) = 1 := if_pos rfl
        omega
      · have h1 : (if x = w then cnt kvs w + 1 else cnt kvs x)
            = cnt kvs x := if_neg hx
        have h2 : (if w = x then 1 else 0) = 0 := if_neg (Ne.symm hx)
        omega

theorem cnt_countsList' (ws : List Int) (x : Int) :
    cnt (countsList ws) x = multiplicity x ws := by
  simpa [countsList, cnt] using cnt_countsList ws [] x

/-- Every entry of a `bump`-fold has its key in the processed words (or
in the seed). -/
private theorem mem_bump {kvs : List (Int × Nat)} {w : Int}
    {p : Int × Nat} (h : p ∈ bump kvs w) :
    p.1 = w ∨ p ∈ kvs := by
  induction kvs with
  | nil =>
      simp only [bump, List.mem_singleton] at h
      exact .inl (by rw [h])
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp only [bump, if_pos hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inl (by rw [h1]; exact hk)
        · exact .inr (List.mem_cons.mpr (.inr h1))
      · simp only [bump, if_neg hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inr (List.mem_cons.mpr (.inl h1))
        · rcases ih h1 with h2 | h2
          · exact .inl h2
          · exact .inr (List.mem_cons.mpr (.inr h2))

theorem countsList_key_mem (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (p : Int × Nat),
    p ∈ List.foldl bump kvs ws → p.1 ∈ ws ∨ p ∈ kvs := by
  induction ws with
  | nil => intro kvs p h; exact .inr h
  | cons w rest ih =>
      intro kvs p h
      simp only [List.foldl_cons] at h
      rcases ih (bump kvs w) p h with h | h
      · exact .inl (by simp [h])
      · rcases mem_bump h with h | h
        · exact .inl (by simp [h])
        · exact .inr h

/-- Distinct keys (`Nodup` on the key column) — `bump` preserves it. -/
private theorem nodup_keys_bump {kvs : List (Int × Nat)} {w : Int}
    (h : (kvs.map Prod.fst).Nodup) :
    ((bump kvs w).map Prod.fst).Nodup := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at h
      by_cases hk : k = w
      · simpa [bump, hk, List.nodup_cons] using h
      · simp only [bump, if_neg hk, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hc
        rcases List.mem_map.mp hc with ⟨p, hp, hpk⟩
        rcases mem_bump hp with h1 | h1
        · exact hk (hpk ▸ h1)
        · exact h.1 (List.mem_map.mpr ⟨p, h1, hpk⟩)

private theorem nodup_keys_countsList (ws : List Int) :
    ∀ kvs : List (Int × Nat), (kvs.map Prod.fst).Nodup →
    ((List.foldl bump kvs ws).map Prod.fst).Nodup := by
  induction ws with
  | nil => intro kvs h; exact h
  | cons w rest ih =>
      intro kvs h
      exact ih (bump kvs w) (nodup_keys_bump h)

/-- With distinct keys, membership pins the count: `(k, c) ∈ kvs →
cnt kvs k = c`. -/
private theorem cnt_of_mem_nodup :
    ∀ {kvs : List (Int × Nat)} {k : Int} {c : Nat},
    (kvs.map Prod.fst).Nodup → (k, c) ∈ kvs → cnt kvs k = c := by
  intro kvs
  induction kvs with
  | nil => intro k c _ h; cases h
  | cons kv rest ih =>
      intro k c hnd h
      obtain ⟨k', c'⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with h | h
      · injection h with h1 h2
        subst h1; subst h2
        simp [cnt]
      · have hk : k' ≠ k := by
          intro hc
          subst hc
          exact hnd.1 (List.mem_map.mpr ⟨(k', c), h, rfl⟩)
        simp only [cnt, if_neg hk]
        exact ih hnd.2 h

/-- Positive `cnt` means the key is present. -/
private theorem cnt_pos_mem {kvs : List (Int × Nat)} {x : Int}
    (h : 0 < cnt kvs x) : (x, cnt kvs x) ∈ kvs := by
  induction kvs with
  | nil => simp [cnt] at h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = x
      · subst hk
        simp only [cnt, if_pos rfl] at h ⊢
        exact List.mem_cons.mpr (.inl rfl)
      · simp only [cnt, if_neg hk] at h ⊢
        exact List.mem_cons.mpr (.inr (ih h))

/-! ### The max fold -/

/-- Max over a `Nat` list (base 0) — the value-column aggregate. -/
def maxOf (l : List Nat) : Nat := l.foldr max 0

theorem maxOf_nil : maxOf [] = 0 := rfl

private theorem maxOf_cons (a : Nat) (l : List Nat) :
    maxOf (a :: l) = max a (maxOf l) := rfl

private theorem mem_le_maxOf {l : List Nat} {c : Nat} (h : c ∈ l) :
    c ≤ maxOf l := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
      rcases List.mem_cons.mp h with h | h
      · rw [maxOf_cons, h]
        exact Nat.le_max_left _ _
      · simp only [maxOf_cons]
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem maxOf_le {l : List Nat} {B : Nat} (h : ∀ c ∈ l, c ≤ B) :
    maxOf l ≤ B := by
  induction l with
  | nil => simp [maxOf_nil]
  | cons a rest ih =>
      simp only [maxOf_cons, Nat.max_le]
      exact ⟨h a (by simp), ih (fun c hc => h c (by simp [hc]))⟩

/-- **The pick-and-erase law** (§10b): removing the picked entry and
maxing it back in recovers the whole fold — the per-iteration invariant
step, invariant under EVERY pick. -/
theorem maxOf_eraseIdx :
    ∀ (l : List Nat) (i : Nat), i < l.length →
    max l[i]! (maxOf (l.eraseIdx i)) = maxOf l := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a rest ih =>
      intro i hi
      cases i with
      | zero =>
          show max (a :: rest)[0]! (maxOf rest) = maxOf (a :: rest)
          rw [show (a :: rest)[0]! = a from by simp, maxOf_cons]
      | succ n =>
          have hn : n < rest.length := by simpa using hi
          simp only [List.eraseIdx_cons_succ, maxOf_cons]
          rw [show (a :: rest)[n + 1]! = rest[n]! from by
            simp [List.getElem!_cons_succ]]
          rw [← ih n hn]
          omega

/-! ### The spec bridge: `maxOf` of the counts equals
`maxMultiplicity` -/

private theorem foldl_max_le {f : Int → Nat} {B : Nat} :
    ∀ (l : List Int) (a : Nat), a ≤ B → (∀ v ∈ l, f v ≤ B) →
    l.foldl (fun acc v => max acc (f v)) a ≤ B := by
  intro l
  induction l with
  | nil => intro a ha _; simpa using ha
  | cons v rest ih =>
      intro a ha h
      simp only [List.foldl_cons]
      exact ih _ (Nat.max_le.mpr ⟨ha, h v (by simp)⟩)
        (fun x hx => h x (by simp [hx]))

private theorem foldl_max_ge_init {f : Int → Nat} :
    ∀ (l : List Int) (a : Nat),
    a ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons w rest ih =>
      intro a
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem le_foldl_max {f : Int → Nat} :
    ∀ (l : List Int) (a : Nat) {v : Int}, v ∈ l →
    f v ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a v h; cases h
  | cons w rest ih =>
      intro a v h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init rest _)
      · exact ih _ h

theorem mult_le_maxMult {ws : List Int} {v : Int} (h : v ∈ ws) :
    multiplicity v ws ≤ maxMultiplicity ws :=
  le_foldl_max (f := fun v => multiplicity v ws) ws 0 h

theorem maxMult_le {ws : List Int} {B : Nat}
    (h : ∀ v ∈ ws, multiplicity v ws ≤ B) : maxMultiplicity ws ≤ B :=
  foldl_max_le (f := fun v => multiplicity v ws) ws 0 (Nat.zero_le _) h

private theorem mem_mult_pos {ws : List Int} {v : Int} (h : v ∈ ws) :
    0 < multiplicity v ws := by
  induction ws with
  | nil => cases h
  | cons w rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [multiplicity_cons]
        have h1 : (if v = v then 1 else 0) = 1 := if_pos rfl
        omega
      · rw [multiplicity_cons]
        have := ih h
        omega

/-- **The spec bridge**: the max over the counts-list value column IS
`maxMultiplicity`. -/
theorem maxOf_countsList (ws : List Int) :
    maxOf ((countsList ws).map Prod.snd) = maxMultiplicity ws := by
  have hnd : ((countsList ws).map Prod.fst).Nodup :=
    nodup_keys_countsList ws [] (by simp)
  apply Nat.le_antisymm
  · -- every count is some key's multiplicity, ≤ the max
    apply maxOf_le
    intro c hc
    rcases List.mem_map.mp hc with ⟨⟨k, c'⟩, hp, hsnd⟩
    have hkey : k ∈ ws := by
      rcases countsList_key_mem ws [] (k, c') hp with h | h
      · exact h
      · cases h
    have hcnt : cnt (countsList ws) k = c' := cnt_of_mem_nodup hnd hp
    have : c' = multiplicity k ws := by
      rw [← hcnt, cnt_countsList' ws k]
    subst hsnd
    show c' ≤ maxMultiplicity ws
    rw [this]
    exact mult_le_maxMult hkey
  · -- the max multiplicity is attained by some entry's count
    apply maxMult_le
    intro v hv
    have hpos : 0 < multiplicity v ws := mem_mult_pos hv
    have hcnt : cnt (countsList ws) v = multiplicity v ws :=
      cnt_countsList' ws v
    have hmem : (v, cnt (countsList ws) v) ∈ countsList ws :=
      cnt_pos_mem (by omega)
    have : cnt (countsList ws) v
        ∈ (countsList ws).map Prod.snd :=
      List.mem_map.mpr ⟨(v, cnt (countsList ws) v), hmem, rfl⟩
    rw [← hcnt]
    exact mem_le_maxOf this

/-- Value bound: counts never exceed the word count. -/
theorem countsList_val_le (ws : List Int) {p : Int × Nat}
    (hp : p ∈ countsList ws) : p.2 ≤ ws.length := by
  obtain ⟨k, c⟩ := p
  have hnd := nodup_keys_countsList ws [] (by simp)
  have hcnt : cnt (countsList ws) k = c := cnt_of_mem_nodup hnd hp
  have := cnt_countsList' ws k
  rw [hcnt] at this
  simp only [multiplicity] at this
  have hle : (ws.filter (· = k)).length ≤ ws.length :=
    List.length_filter_le _ _
  omega


end GoLean.Examples.WordCount
