import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
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

open GoLean GoLean.GoCore GoLean.GoCore.Machine
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
private def wcResCell : Heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

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
wordcount's own spec layer (`bump`/`countsFold`/the max fold) stays. -/

/-! ## The heap-append kit (symbolic-address algebra, §10c)

The in-loop cells live at length-dependent addresses past the nine
concrete front cells, so their reads/writes are discharged by this
small append algebra instead of definitional reduction. -/

/-! ## The pure counts layer

GAP-P1 CLOSED (kit-gap closure, 2026-08-15): `bump`/`countsFold` and
the whole lemma chain (`setk_cnt_succ`, `countsFold_append`,
`cnt_countsFold`, the key-membership/nodup/`cnt` chain,
`countsFold_val_le`) now live in `GoLeanProofs/MapMem.lean` (visible
here via `open GoLean.MapMem`). What stays is wordcount's own
STATEMENT vocabulary: the bridge to `multiplicity` and the max fold. -/

/-- **The queried-count bridge**: the fold's count at any key is that
key's `multiplicity` — wordcount's statement function is
definitionally the kit's filter-length. -/
private theorem cnt_countsFold' (ws : List Int) (x : Int) :
    cnt (countsFold ws) x = multiplicity x ws := by
  rw [cnt_countsFold]; rfl

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

private theorem multiplicity_cons (v w : Int) (ws : List Int) :
    multiplicity v (w :: ws)
      = (if w = v then 1 else 0) + multiplicity v ws := by
  simp only [multiplicity, List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

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
theorem maxOf_countsFold (ws : List Int) :
    maxOf ((countsFold ws).map Prod.snd) = maxMultiplicity ws := by
  have hnd : ((countsFold ws).map Prod.fst).Nodup :=
    countsFold_nodup_keys ws
  apply Nat.le_antisymm
  · -- every count is some key's multiplicity, ≤ the max
    apply maxOf_le
    intro c hc
    rcases List.mem_map.mp hc with ⟨⟨k, c'⟩, hp, hsnd⟩
    have hkey : k ∈ ws := countsFold_key_mem hp
    have hcnt : cnt (countsFold ws) k = c' := cnt_of_mem_nodup hnd hp
    have : c' = multiplicity k ws := by
      rw [← hcnt, cnt_countsFold' ws k]
    subst hsnd
    show c' ≤ maxMultiplicity ws
    rw [this]
    exact mult_le_maxMult hkey
  · -- the max multiplicity is attained by some entry's count
    apply maxMult_le
    intro v hv
    have hpos : 0 < multiplicity v ws := mem_mult_pos hv
    have hcnt : cnt (countsFold ws) v = multiplicity v ws :=
      cnt_countsFold' ws v
    have hmem : (v, cnt (countsFold ws) v) ∈ countsFold ws :=
      cnt_pos_mem (by omega)
    have : cnt (countsFold ws) v
        ∈ (countsFold ws).map Prod.snd :=
      List.mem_map.mpr ⟨(v, cnt (countsFold ws) v), hmem, rfl⟩
    rw [← hcnt]
    exact mem_le_maxOf this

-- (`countsFold_val_le` is the kit's, via `open GoLean.MapMem` —
-- the local copy was deleted in the GAP-P1 closure.)


end GoLean.Examples.WordCount
