import GoLean.GoCore.MachineSound

/-!
# Map-in-memory vocabulary + the executable map-op facts
(Gallery Campaign G0 item 3b, 2026-08-15 — the MapMem promotion)

The `map[uint64]uint64` analogue of `SliceMem`: the §10a
map-in-memory vocabulary (`mapCells`/`mapVal`), the abstract
association-list model (`idxOf?`/`cnt`/`setk` with `toEntries`, the
machine encoding), and the executable map-operation facts — what
`applyStrictOp`/`mapAssignValue`/`mapRangeSnapshotEntries` compute on
this fragment, conditioned on the lookup/normal-form hypotheses.

Promoted VERBATIM from `Examples/WordCount/Pure.lean` (where the
family was recorded as a "SliceMem promotion candidate" at birth,
scale-out slice 2026-08-13) under the §12 active-abstraction loop in
its campaign form: the landed consumer is WordCount (retrofitted in
this commit — the example-local copies are DELETED, the P6 rule);
the chartered consumers are the G1 candidates histogram and
fibonacci-memo, whose map phases state exactly these facts.

Everything speaks the private counts encoding `List (Int × Nat)` —
keys with `Nat` values (the machine stores values as wrapped uint64
`Int`s; `toEntries` is the encoding). The counting fold
(`bump`/`countsFold`) joined in the GAP-P1 lift (kit-gap closure,
2026-08-15) once histogram — the chartered consumer — had re-derived
it verbatim: the fold is map-counting machinery after all, and only
each example's STATEMENT functions (the max fold, `distinctCount`)
stay example-local.

## PUBLIC API — the sealed interface (the W6 convention, as in
`SliceMem`)

**What consumers may depend on** (and nothing else). The groups are
indexed by PROOF SITUATION (the WP arc s3 convention: a group is
"what you are trying to do", not "which lift landed it"); the in-file
`/-! ## … -/` section headers carry the group number, and one group
may span more than one section.

**Group 1** — *you are naming a Go `map[uint64]uint64` that lives in
memory*: `mapCells` (the data cell), `mapVal` (the handle the program
carries).

**Group 2** — *you are reasoning about the map ABSTRACTLY* (the
association-list model that plays the role `List Int` plays for
slices): `idxOf?` (key position), `cnt` (multiplicity), `setk`
(update-or-append), `toEntries` (the machine encoding), with the
model lemmas `idxOf?_none_cnt`, `idxOf?_none_setk`,
`idxOf?_some_snd`, `idxOf?_some_setk`.

**Group 3** — *you must move between the model and the machine's
`Array` of entries* — the `toEntries` bridges: `toEntries_getElem?`,
`toEntries_size`, `toEntries_eraseIdx`, `map_eraseIdx`.

**Group 4** — *you are COUNTING with a map* (`m[k]++` folded over a
slice; GAP-P1 lift, 2026-08-15): `bump`, `countsFold`, `nilMapCell`,
with `setk_cnt_succ`, `countsFold_nil`, `countsFold_append`,
`cnt_countsFold`, `countsFold_key_mem`, `countsFold_nodup_keys`,
`cnt_of_mem_nodup`, `cnt_pos_mem`, `countsFold_val_le`,
`take_succ_getD`, `cnt_take_le`.

**Group 5** — *you need what a map OPERATION computes*, each fact
conditioned on exactly its lookup/normal-form hypotheses:
`applyStrictOp_mapGet` (read, with Go's zero-value-on-absent),
`mapAssignValue_toEntries` (write, update-or-append = `setk`),
`snapshot_toEntries` (the `mapRangeK` snapshot),
`mapEntryIndex?_toEntries` (the key scan) and its engine
`scan_generic` (body-abstract, so `rw` unifies it with the
do-elaborated lambda).

**Group 6** — *the range loop PICKS the next entry* (the `mapIterK`
choice-consumption step; GAP-M1 lift, 2026-08-15): `stepFn_pick_bind`
(binder-generic, allocation via `bindIterVars`) with its corollaries
`stepFn_pick_value`, `stepFn_pick_novars`.

**Internal** (`private` — spelling may change without notice):
`valueEq_u64`, `filter_len_cons`, `toEntries_setk`, `snapshot_norm`,
`cnt_bump`, `cnt_countsFold_aux`, `mem_bump`,
`countsFold_key_mem_aux`, `nodup_keys_bump`,
`countsFold_nodup_keys_aux`.

**Naming note** (WP arc s3): executable-fact lemmas are named
`<executable function>_<operand or result shape>` at the function's
shortest UNAMBIGUOUS spelling — `snapshot_toEntries` is
`mapRangeSnapshotEntries` at that spelling, and `scan_generic` is the
`mapEntryIndex?` scan; both are unambiguous inside this namespace.
No alias added (`docs/wp-arc-log/s3.md` § Near-misses).

**The API discipline** (as `SliceMem`'s, verbatim in substance):

1. Everything here is UNTRUSTED METHOD except the vocabulary defs,
   and even those enter a headline only under the §11 statement
   closure rules — a kit lemma NAME never appears in a headline
   statement (form note §12b).
2. Additions follow the §12 active-abstraction loop (≥2 consumers
   retrofitted in the lifting commit, measured deltas).
3. Lean's `private` hides names without sealing definitional
   transparency; the seal is name-level + this contract, and the
   statement layer has its own gate.
4. Every public THEOREM above carries an exact `#print axioms` pin in
   `Audit/Kit.lean` § MapMem; the nine vocabulary/model/fold defs
   (`mapCells`, `mapVal`, `idxOf?`, `cnt`, `setk`, `toEntries`,
   `bump`, `countsFold`, `nilMapCell`) are unpinned by the standing
   convention. A new public lemma lands with its pin in the same
   commit.
5. **Storm/signature discipline: StepKit rules 1–5** (that module's
   `## THE FIVE RULES` section is the kit's single copy — cite, never
   restate). Group 5/6 members take the cell fact as a D-relative
   hypothesis (rule 4) over an abstract `σ` (rule 1), which is why
   they instantiate at any placement.

## WHAT LIVES WHERE (the kit map — WP arc s3, 2026-08-18)

THIS module: what the machine computes when the OPERAND is a map,
plus the abstract model those facts are stated against. One step at
most (group 6); no loops, no fuel.

Siblings, and the boundary with each:

* `MapLoops` — the whole map-LOOP schemas (counting loop, range pick
  loop) built by composing our group 5/6 facts with `StepKit`'s
  steps and `FuelMeasure`'s chaining. If it iterates, it is there.
* `SliceMem` — the identical shape for `[]uint64`; the model half
  there is plain `List Int`, which is why this module carries an
  explicit `idxOf?`/`cnt`/`setk` layer and that one does not.
* `StringMem` — the same shape for string values (no heap half).
* `StepKit` — the machine step consuming our facts as its
  `applyStrictOp`/`applyStmtOp` hypothesis; its footprint algebra
  (`DeadFrom`/`FreshFrom`) is what a map-range loop's per-iteration
  allocation is argued with.

Future `docs/kit-guide.md` (slice 6) sections fed by this module:
**Values in memory: maps**, **Map counting** (the model/fold half of
**Map count loop**), **Map range** (the pick step).
-/

namespace GoLean.MapMem

open GoLean GoLean.GoCore GoLean.GoCore.Machine

-- The unusedSimpArgs linter false-flags `letFun` (mapEntryIndex?) and
-- `valueAsMap` (snapshot) — removing either breaks the proof (verified
-- 2026-08-15); same suppression the example modules carry.
set_option linter.unusedSimpArgs false

/-! ## API group 1 — the map-in-memory vocabulary (§10a) -/

/-- The heap representation of a `map[uint64]uint64` holding the
association list `kvs` (insertion order = list order): one data cell at
`base`. The handle the program carries is `mapVal base`. -/
def mapCells (kvs : List (Int × Int)) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨none, .mapData ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int kv.2 .uint64))⟩⟩)]

def mapVal (base : Nat) : GoValue := .map ⟨some (.base ⟨base⟩)⟩

/-! ## API group 2 — the abstract association-list model -/

/-- First index of key `w` (the machine's `mapEntryIndex?` order). -/
def idxOf? : List (Int × Nat) → Int → Option Nat
  | [], _ => none
  | (k, _) :: rest, w => if k = w then some 0 else (idxOf? rest w).map (· + 1)

/-- Assoc lookup at the FIRST occurrence, `0` when absent — exactly a
Go map read's zero-value semantics on this fragment. -/
def cnt : List (Int × Nat) → Int → Nat
  | [], _ => 0
  | (k, c) :: rest, w => if k = w then c else cnt rest w

/-- Update the first occurrence of `w`, or append — exactly
`mapAssignValue`'s update-or-insert on the entry list. -/
def setk : List (Int × Nat) → Int → Nat → List (Int × Nat)
  | [], w, v => [(w, v)]
  | (k, c) :: rest, w, v =>
      if k = w then (k, v) :: rest else (k, c) :: setk rest w v

/-- The machine encoding of a counts list: insertion-ordered
`mapData` entries of wrapped uint64 pairs. -/
def toEntries (kvs : List (Int × Nat)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int (kv.2 : Int) .uint64))⟩

/-- The §10a vocabulary coheres with the counts encoding. -/
example (kvs : List (Int × Nat)) (base : Nat) :
    mapCells (kvs.map (fun p => (p.1, (p.2 : Int)))) base
      = [(.base ⟨base⟩, ⟨none, .mapData (toEntries kvs)⟩)] := by
  simp [mapCells, toEntries, List.map_map, Function.comp]

private theorem valueEq_u64 (σ : ExecState) (l r : Int) :
    valueEq σ (.int .uint64) (.int l .uint64) (.int r .uint64)
      = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

/-! ### API group 5, stated early — the key scan and its engine.
(They live here, beside the model, because both are stated over
`toEntries`; the rest of group 5 is the `## API group 5, continued`
section below.) -/

/-- The key-scan loop of `mapEntryIndex?` over an abstract body `f`
(pinned only by its action on wrapped-integer entry pairs — the
abstraction is what lets `rw` unify it with the do-elaborated lambda),
generalized over the starting counter. -/
theorem scan_generic {w : Int}
    (f : GoValue × GoValue → MProd (Option (Option Nat)) Nat →
      Except GoError (ForInStep (MProd (Option (Option Nat)) Nat)))
    (hf : ∀ (k : Int) (v : GoValue) (r : MProd (Option (Option Nat)) Nat),
      f (.int k .uint64, v) r
        = .ok (if k = w then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (Int × Nat)) (i : Nat),
    (forIn (m := Except GoError) (toEntries kvs)
      (⟨none, i⟩ : MProd (Option (Option Nat)) Nat) f)
      = pure (match idxOf? kvs w with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntries, idxOf?]
  | cons kv rest ih =>
      intro i
      obtain ⟨k, c⟩ := kv
      simp only [toEntries, List.map_cons, ← Array.forIn_toList] at ih ⊢
      rw [List.forIn_cons, hf]
      by_cases hk : k = w
      · simp [hk, idxOf?, Bind.bind, Except.bind]
      · simp only [if_neg hk, idxOf?, Bind.bind, Except.bind]
        rw [ih (i + 1)]
        cases hidx : idxOf? rest w with
        | none =>
            simp only [Option.map_none, List.length_cons]
            rw [show i + 1 + rest.length = i + (rest.length + 1) from by omega]
        | some j =>
            simp only [Option.map_some]
            rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over an abstract `uint64 → uint64`
association list is the list-model first-index scan. -/
theorem mapEntryIndex?_toEntries (σ : ExecState)
    (kvs : List (Int × Nat)) (w : Int) (b : Bool) :
    mapEntryIndex? σ (.int .uint64) (toEntries kvs) (.int w .uint64) b
      = .ok (idxOf? kvs w) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.int w .uint64) b (!(toEntries kvs).isEmpty)
      = .ok () from by simp [checkKeyHashable, valueHashability]]
  simp only [letFun]
  rw [scan_generic (w := w) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_u64, Bind.bind, Except.bind]
    by_cases hk : k = w
    · simp [hk]
    · have hkb : (k == w) = false := by simpa using hk
      simp [hkb, hk]
  cases h : idxOf? kvs w <;> simp [Bind.bind, Except.bind, pure, Except.pure]

/-! ### API group 2, continued — the model lemmas: `idxOf?` against
`cnt` and `setk` -/

theorem idxOf?_none_cnt {kvs : List (Int × Nat)} {w : Int}
    (h : idxOf? kvs w = none) : cnt kvs w = 0 := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [cnt, if_neg hk]
        exact ih (by cases hidx : idxOf? rest w <;> simp [hidx] at h ⊢)

theorem idxOf?_none_setk {kvs : List (Int × Nat)} {w : Int}
    (h : idxOf? kvs w = none) (v : Nat) : kvs ++ [(w, v)] = setk kvs w v := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [List.cons_append, setk, if_neg hk]
        exact congrArg _
          (ih (by cases hidx : idxOf? rest w <;> simp [hidx] at h ⊢))

theorem idxOf?_some_snd {kvs : List (Int × Nat)} {w : Int} {j : Nat}
    (h : idxOf? kvs w = some j) :
    kvs[j]? = some (w, cnt kvs w) := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [cnt, hk]
      · simp only [if_neg hk] at h
        cases hidx : idxOf? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.getElem?_cons_succ, cnt, if_neg hk]
            exact ih hidx

theorem idxOf?_some_setk {kvs : List (Int × Nat)} {w : Int} {j : Nat}
    (h : idxOf? kvs w = some j) (v : Nat) :
    kvs.set j (w, v) = setk kvs w v := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [setk, hk, List.set]
      · simp only [if_neg hk] at h
        cases hidx : idxOf? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.set, setk, if_neg hk]
            exact congrArg _ (ih hidx)

/-! ## API group 3 — the `toEntries` bridges -/

theorem toEntries_getElem? (kvs : List (Int × Nat)) (j : Nat)
    {p : Int × Nat} (h : kvs[j]? = some p) :
    (toEntries kvs)[j]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) := by
  simp [toEntries, List.getElem?_map, h]

theorem toEntries_size (kvs : List (Int × Nat)) :
    (toEntries kvs).size = kvs.length := by
  simp [toEntries]

theorem map_eraseIdx {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a rest ih =>
      intro i
      cases i with
      | zero => simp [List.eraseIdx]
      | succ n => simp [List.eraseIdx, ih n]

theorem toEntries_eraseIdx (kvs : List (Int × Nat)) (i : Nat)
    (h : i < (toEntries kvs).size) :
    (toEntries kvs).eraseIdx i h = toEntries (kvs.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [toEntries, map_eraseIdx]

/-! ## API group 4 — counting with a map: the counting fold
(Gallery Campaign kit-gap closure GAP-P1,
2026-08-15)

`bump`/`countsFold` — the abstract content of a counting map's data
cell (`m[k]++` folded over a value list) and its lemma chain, lifted
from the verbatim copies in `Examples/WordCount/Pure.lean` and
`Examples/Histogram/Pure.lean`. G0 item 3b deliberately left the
family in wordcount as "spec vocabulary, not map machinery"; the
chartered consumer (histogram) then re-derived it wholesale, showing
that boundary call wrong — corrected here, recorded in the campaign
log. Each example keeps only its own STATEMENT functions
(`multiplicity` / `occurrences`, `distinctCount`) and a one-line
bridge to `cnt_countsFold`. The addendum members (`take_succ_getD`,
`cnt_take_le`, `nilMapCell`) are the counting-loop plumbing the same
gap record listed. -/

/-- One value lands in the counts list: increment the first occurrence
of the key, or append `(v, 1)` — first-occurrence insertion order,
matching the machine's `mapAssign`. -/
def bump : List (Int × Nat) → Int → List (Int × Nat)
  | [], v => [(v, 1)]
  | (k, c) :: rest, v =>
      if k = v then (k, c + 1) :: rest else (k, c) :: bump rest v

/-- The counts list after processing `l`, in first-occurrence
insertion order — the abstract content of the map data cell. -/
def countsFold (l : List Int) : List (Int × Nat) :=
  l.foldl bump []

/-- The nil-map cell — a `map[uint64]uint64` variable's default value
before a handle is stored over it. -/
abbrev nilMapCell : HeapCell :=
  ⟨some (.map (.int .uint64) (.int .uint64)), .map ⟨none⟩⟩

/-- What the machine's write computes is `bump`: the value written is
`counts[v] + 1` at the first occurrence (or `0 + 1` fresh). -/
theorem setk_cnt_succ :
    ∀ (kvs : List (Int × Nat)) (v : Int),
    setk kvs v (cnt kvs v + 1) = bump kvs v := by
  intro kvs
  induction kvs with
  | nil => intro v; rfl
  | cons kv rest ih =>
      intro v
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp [setk, cnt, bump, hk]
      · simp [setk, cnt, bump, hk, ih v]

theorem countsFold_nil : countsFold [] = [] := rfl

theorem countsFold_append (p : List Int) (v : Int) :
    countsFold (p ++ [v]) = bump (countsFold p) v := by
  simp [countsFold, List.foldl_append]

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

private theorem filter_len_cons (v w : Int) (l : List Int) :
    ((w :: l).filter (· = v)).length
      = (if w = v then 1 else 0) + (l.filter (· = v)).length := by
  simp only [List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

private theorem cnt_countsFold_aux (l : List Int) :
    ∀ (kvs : List (Int × Nat)) (x : Int),
    cnt (List.foldl bump kvs l) x
      = cnt kvs x + (l.filter (· = x)).length := by
  induction l with
  | nil => intro kvs x; simp
  | cons w rest ih =>
      intro kvs x
      simp only [List.foldl_cons, ih, cnt_bump, filter_len_cons]
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

/-- **The counting-fold invariant**: the fold's count at any key is
that key's number of occurrences (0 on both sides for an absent key —
Go's zero-value read is exactly the absent case). Each example bridges
this to its own statement function (`multiplicity` / `occurrences`),
both of which are definitionally this filter-length. -/
theorem cnt_countsFold (l : List Int) (x : Int) :
    cnt (countsFold l) x = (l.filter (· = x)).length := by
  simpa [countsFold, cnt] using cnt_countsFold_aux l [] x

/-- Every entry of a `bump` has its key at the bumped value or in the
seed. -/
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

private theorem countsFold_key_mem_aux (l : List Int) :
    ∀ (kvs : List (Int × Nat)) (p : Int × Nat),
    p ∈ List.foldl bump kvs l → p.1 ∈ l ∨ p ∈ kvs := by
  induction l with
  | nil => intro kvs p h; exact .inr h
  | cons w rest ih =>
      intro kvs p h
      simp only [List.foldl_cons] at h
      rcases ih (bump kvs w) p h with h | h
      · exact .inl (by simp [h])
      · rcases mem_bump h with h | h
        · exact .inl (by simp [h])
        · exact .inr h

/-- Every key of the fold occurs in the folded list. -/
theorem countsFold_key_mem {l : List Int} {p : Int × Nat}
    (hp : p ∈ countsFold l) : p.1 ∈ l := by
  rcases countsFold_key_mem_aux l [] p hp with h | h
  · exact h
  · cases h

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

private theorem countsFold_nodup_keys_aux (l : List Int) :
    ∀ kvs : List (Int × Nat), (kvs.map Prod.fst).Nodup →
    ((List.foldl bump kvs l).map Prod.fst).Nodup := by
  induction l with
  | nil => intro kvs h; exact h
  | cons w rest ih =>
      intro kvs h
      exact ih (bump kvs w) (nodup_keys_bump h)

/-- The fold's key column is duplicate-free. -/
theorem countsFold_nodup_keys (l : List Int) :
    ((countsFold l).map Prod.fst).Nodup :=
  countsFold_nodup_keys_aux l [] (by simp)

/-- With distinct keys, membership pins the count: `(k, c) ∈ kvs →
cnt kvs k = c`. -/
theorem cnt_of_mem_nodup :
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
theorem cnt_pos_mem {kvs : List (Int × Nat)} {x : Int}
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

/-- Value bound: no count exceeds the number of values folded. -/
theorem countsFold_val_le (l : List Int) {p : Int × Nat}
    (hp : p ∈ countsFold l) : p.2 ≤ l.length := by
  obtain ⟨k, c⟩ := p
  have hnd := countsFold_nodup_keys l
  have hcnt : cnt (countsFold l) k = c := cnt_of_mem_nodup hnd hp
  have := cnt_countsFold l k
  rw [hcnt] at this
  have hle : (l.filter (· = k)).length ≤ l.length :=
    List.length_filter_le _ _
  omega

/-- A take extended by one step is the take plus the element (the
counting loop's per-iteration list identity). -/
theorem take_succ_getD {α : Type} {l : List α} {i : Nat}
    (hi : i < l.length) {d : α} :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The running count is bounded by the number of values folded so far
(the counting loop's no-overflow bound). -/
theorem cnt_take_le {ws : List Int} {i : Nat} (w : Int) :
    cnt (countsFold (ws.take i)) w ≤ i := by
  rw [cnt_countsFold]
  have h1 : ((ws.take i).filter (· = w)).length ≤ (ws.take i).length :=
    List.length_filter_le _ _
  have h2 : (ws.take i).length ≤ i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  omega

/-! ## API group 5, continued — the executable map-op facts -/

/-- **The map-elem read** (`counts[w]`, expression position): a present
key answers its count, an absent key the ZERO VALUE — which is exactly
how `counts[w]++` starts a fresh key at 1. -/
theorem applyStrictOp_mapGet {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {w : Int} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntries kvs)⟩)
    (hw : IntKind.normalize .uint64 w = w) :
    applyStrictOp σ (.mapGet (.int .uint64) (.int .uint64))
      [.map ⟨some (.base a)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64, σ) := by
  simp only [applyStrictOp, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int w .uint64)
      = .ok (.int w .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hw]]
  simp only [loadLoc, hlook, pure, Except.pure]
  rw [mapEntryIndex?_toEntries]
  cases hidx : idxOf? kvs w with
  | none =>
      rw [idxOf?_none_cnt hidx]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]
  | some j =>
      have hj := idxOf?_some_snd hidx
      simp [toEntries_getElem? kvs j hj]

private theorem toEntries_setk {kvs : List (Int × Nat)} {w : Int} {v : Nat} :
    (match idxOf? kvs w with
      | some i =>
          (toEntries kvs).set! i (.int w .uint64, .int (v : Int) .uint64)
      | none => (toEntries kvs).push (.int w .uint64, .int (v : Int) .uint64))
      = toEntries (setk kvs w v) := by
  cases hidx : idxOf? kvs w with
  | none =>
      show (toEntries kvs).push _ = _
      apply Array.toList_inj.mp
      simp [toEntries, ← idxOf?_none_setk hidx v]
  | some j =>
      show (toEntries kvs).set! j _ = _
      apply Array.toList_inj.mp
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
        toEntries, ← idxOf?_some_setk hidx v, List.map_set]

/-- **The map-elem write** (`counts[w] = v`): `mapAssignValue`'s
update-or-append on the abstract association list is `setk`. -/
theorem mapAssignValue_toEntries {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {w : Int} {v : Nat}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntries kvs)⟩)
    (hw : IntKind.normalize .uint64 w = w)
    (hv : IntKind.normalize .uint64 (v : Int) = (v : Int)) :
    mapAssignValue σ (.int .uint64) (.int .uint64)
      (.map ⟨some (.base a)⟩) (.int w .uint64) (.int (v : Int) .uint64)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntries (setk kvs w v))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int w .uint64)
      = .ok (.int w .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hw]]
  rw [show normalizeValueForTy σ (.int .uint64) (.int (v : Int) .uint64)
      = .ok (.int (v : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hv]]
  simp only [mapEntries, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntries]
  cases hidx : idxOf? kvs w with
  | some j =>
      show storeLoc σ (.base a)
        (.mapData ((toEntries kvs).set! j
          (.int w .uint64, .int (v : Int) .uint64))) = _
      rw [show (toEntries kvs).set! j
          ((.int w .uint64 : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntries (setk kvs w v) from by
        have h := toEntries_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]
  | none =>
      show storeLoc σ (.base a)
        (.mapData ((toEntries kvs).push
          (.int w .uint64, .int (v : Int) .uint64))) = _
      rw [show (toEntries kvs).push
          ((.int w .uint64 : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntries (setk kvs w v) from by
        have h := toEntries_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]

private theorem snapshot_norm (types : TypeEnv) :
    ∀ kvs : List (Int × Nat),
    (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) →
    snapshotEntriesSelfNormalizedList types (.int .uint64) (.int .uint64)
      (kvs.map (fun kv =>
        ((.int kv.1 .uint64 : GoValue), (.int (kv.2 : Int) .uint64 : GoValue))))
      = true := by
  intro kvs
  induction kvs with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro hkv
      have hp := hkv p (by simp)
      have hrest := ih (fun q hq => hkv q (by simp [hq]))
      simp only [List.map_cons, snapshotEntriesSelfNormalizedList]
      rw [hrest]
      simp [isNormalForTy, isNormalForTyFuel, typeResolutionFuel, hp.1, hp.2]

/-! ## API group 6 — the range loop PICKS: the `mapIterK`
choice-pick step (Gallery Campaign kit-gap
closure GAP-M1, 2026-08-15)

The §10b pick, lifted from the two binder-specialized per-example
copies (wordcount's `none`/`some "c"`, histogram's `none`/`none`): ONE
lemma parameterized over `(keyVar valVar : Option String)` with the
allocation described by `bindIterVars` (`stepFn_pick_bind`), plus the
two corollaries at the binder shapes that actually occur. -/

/-- **The choice-pick step, at any binder shape** (§10b): at a
nonempty snapshot ONE choice is consumed (`idx < size` from
`Choices.consume`'s `% bound` contract), the picked entry is erased,
and the iteration's bindings/allocation are whatever `bindIterVars`
says — supplied as the `hbind` fact. -/
theorem stepFn_pick_bind {σ σ' : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {ko vo : Option String} {body : Stmt}
    {env env' : LocalEnv} {k : Cont} {p : Int × Nat}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length)
    (hp : rem[idx]? = some p)
    (hbind : bindIterVars env.pushScope σ ko vo (.int .uint64) (.int .uint64)
      (.int p.1 .uint64) (.int (p.2 : Int) .uint64) = .ok (env', σ')) :
    stepFn σ
      (.next (.mapIterK ko vo (.int .uint64) (.int .uint64) body
        (toEntries rem) env k)) ch
      = .ok (.exec body env'
          (.mapIterK ko vo (.int .uint64) (.int .uint64) body
            (toEntries (rem.eraseIdx idx)) env k),
        σ', ch') := by
  have hne : (toEntries rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntries rem).size = rem.length := toEntries_size rem
  have hget : (toEntries rem)[idx]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) :=
    toEntries_getElem? rem idx hp
  have hidx' : idx < (toEntries rem).size := by rw [hsz]; exact hidx
  simp only [stepFn, hne, Bool.false_eq_true, if_false]
  split
  · rename_i hnone
    rw [hsz, hconsume] at hnone
    simp only at hnone
    rw [hget] at hnone
    cases hnone
  · rename_i key value hsome
    rw [hsz, hconsume] at hsome
    simp only at hsome
    rw [hget] at hsome
    injection hsome with h1
    injection h1 with hk hv2
    subst hk
    subst hv2
    simp only [Bind.bind, Except.bind, hbind, pure, Except.pure, hsz,
      hconsume, toEntries_eraseIdx rem idx hidx']

/-- The pick at a VALUE-ONLY binder (`for _, v := range m`): the
picked entry's value cell is freshly allocated at the current
`nextAddr` and the binder declared over a pushed scope. -/
theorem stepFn_pick_value {σ : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {v : String} {body : Stmt}
    {env : LocalEnv} {k : Cont} {p : Int × Nat}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length)
    (hp : rem[idx]? = some p)
    (hv : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    stepFn σ
      (.next (.mapIterK none (some v) (.int .uint64) (.int .uint64) body
        (toEntries rem) env k)) ch
      = .ok (.exec body (env.pushScope.declare v (.base ⟨σ.nextAddr⟩))
          (.mapIterK none (some v) (.int .uint64) (.int .uint64) body
            (toEntries (rem.eraseIdx idx)) env k),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.int .uint64), .int (p.2 : Int) .uint64⟩,
            nextAddr := σ.nextAddr + 1 },
        ch') := by
  refine stepFn_pick_bind hconsume hidx hp ?_
  simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int (p.2 : Int) .uint64)
      = .ok (.int (p.2 : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hv]]
  simp only [Bind.bind, Except.bind, pure, Except.pure, ExecState.alloc,
    ExecState.freshLoc]

/-- The pick at a VARIABLE-FREE range (`for range m {}`):
`bindIterVars` with neither binder allocates NOTHING — the state is
unchanged and only the scope is pushed. This is why a variable-free
range loop is state-stable, and why order-invariance is so visible
there: the machine's only per-iteration effect is "one fewer
entry". -/
theorem stepFn_pick_novars {σ : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length) :
    stepFn σ
      (.next (.mapIterK none none (.int .uint64) (.int .uint64) body
        (toEntries rem) env k)) ch
      = .ok (.exec body env.pushScope
          (.mapIterK none none (.int .uint64) (.int .uint64) body
            (toEntries (rem.eraseIdx idx)) env k),
        σ, ch') := by
  obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
    ⟨rem[idx]'hidx, List.getElem?_eq_getElem hidx⟩
  exact stepFn_pick_bind hconsume hidx hp rfl

/-- **The range snapshot** (`mapRangeK`): reads the data cell and
validates every entry self-normalized — on the in-range fragment, the
identity. -/
theorem snapshot_toEntries {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntries kvs)⟩)
    (hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    mapRangeSnapshotEntries σ (.int .uint64) (.int .uint64)
      (.map ⟨some (.base a)⟩)
      = .ok (toEntries kvs) := by
  have hnorm := snapshot_norm σ.types kvs hkv
  simp only [mapRangeSnapshotEntries, mapRangeEntries, valueAsMap, Bind.bind,
    Except.bind, pure, Except.pure, loadLoc, hlook,
    snapshotEntriesSelfNormalized]
  rw [show (toEntries kvs).toList
      = kvs.map (fun kv =>
        ((.int kv.1 .uint64 : GoValue), (.int (kv.2 : Int) .uint64 : GoValue)))
      from rfl, hnorm]
  simp

end GoLean.MapMem
