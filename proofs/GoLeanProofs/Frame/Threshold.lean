import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.StepKit

/-!
# The threshold shift/rebase layer (WP arc s1 lift 4, 2026-08-16)

The FIVE hand instantiations of the per-pass frame/rebase pattern
(isort `ρsh`/`ρ11`/`ρ21`, selsort `ρ16`, bubble `ρ16` — found
independently by both sort lanes; the campaign ledger's promotion
item #1), lifted threshold- and retire-generic, exactly the shape
drafted at g1.md §THE KIT-GAP LIST (selsort)/(bubble):

* `ρT T d` — identity below the threshold `T`, shift by `d` above it —
  with `shiftSpec_ρT` and the small `lt`/`ge` laws;
* `bumpAt T r` + `renameLoc_ρT_bump` — the bump transport between
  consecutive shifts (the generic `renameLoc_bump2`/`bump3`);
* `frameSim_seed` — the TRIVIAL frame at the loop entry, generic
  (kills the per-example `frameSim_zero` cell enumeration: only the
  allocator position and the bodies fact remain per example);
* `rebaseSimT` — retire the pass-local cells into the frame: the
  front's per-cell obligations enter as ONE hypothesis (`hfront`),
  dischargeable per example by `rfl`s/cell lemmas; the retired-cell
  LIST is a parameter and lands in the frame as `retiredFrame`;
* `transfer_segT` — the transfer corollary, verbatim from the copies.

The per-example residue is genuinely the fixed-cell enumeration (the
`hfront`/`hret` discharges) plus the program's own `bodies` fact —
what the ledger predicted and nothing more.

## PUBLIC API — the sealed interface (the W6 convention, as in
`StepKit`/`SliceMem`; section added WP arc s3, 2026-08-18)

**Every declaration in this module is public API** — the module has
no `private` names. The groups are indexed by PROOF SITUATION (the
WP arc s3 convention: a group is "what you are trying to do", not
"which lift landed it"); the in-file `/-! ## … -/` section headers
carry the group number.

**Group 1** — *you need the per-pass SHIFT itself*: `ρT T d`
(identity below the threshold `T`, `+d` above it) with `ρT_lt`,
`ρT_ge`, and `shiftSpec_ρT` (the shift meets the frame layer's
`ShiftSpec` contract).

**Group 2** — *you must show the shift is the IDENTITY at `d = 0`*
(the loop-entry case): `ρT_zero_app`, `base_ne_of_ne`,
`renameLoc_ρT_zero`, `renameValue_id`, `renameCell_ρT_zero`.

**Group 3** — *a cell must survive every shift* (it holds no
address): `CellFixed` with `CellFixed.of_locFree`.

**Group 4** — *you are transporting between CONSECUTIVE shifts*:
`bumpAt T r` with `renameLoc_ρT_bump` — the generic form of the
per-example `renameLoc_bump2`/`bump3`.

**Group 5** — *you are naming the RETIRED pass-local cells*:
`retiredFrame` with `retiredFrame_lookup_base_none`,
`retiredFrame_lookup_field`, `retiredFrame_lookup_index`,
`retiredFrame_lookup_some_inv`.

**Group 6** — *you are at the loop ENTRY and need the trivial frame*:
`frameSim_seed` (generic; it kills the per-example `frameSim_zero`
cell enumeration — only the allocator position and the `bodies` fact
remain per example).

**Group 7** — *the pass ENDED and you must retire its cells into the
frame*: `rebaseSimT` — the front's per-cell obligations enter as ONE
hypothesis (`hfront`), the retired-cell LIST is a parameter and lands
in the frame as `retiredFrame`.

**Group 8** — *you must TRANSFER a segment across the rebase*:
`transfer_segT`, the corollary the five hand copies all ended at.

**Internal**: none — this module has no `private` declarations.

**Naming note** (WP arc s3): the `T` suffix marks the
THRESHOLD-generic form of a composite the examples had spelled at a
fixed threshold (`rebaseSimT`, `transfer_segT`, `ρT`); transport
lemmas read `<renamed thing>_<shift>_<situation>`
(`renameLoc_ρT_bump`, `renameCell_ρT_zero`), and `CellFixed.of_locFree`
follows the kit-wide dot rule (a lemma that PRODUCES a predicate from
a non-predicate premise would be snake-cased, but this one is a
constructor-style view of `CellFixed` and dot notation is the point).
No aliases added (`docs/wp-arc-log/s3.md` § Near-misses).

**The API discipline**:

1. Everything here is UNTRUSTED METHOD (proof-side): no name from
   this module may appear in a headline statement closure (§12b).
   The frames it builds are existential in the headline, which is why
   parameterizing them moved no statement.
2. What consumers may rely on is each lemma's STATEMENT — in
   particular that `hfront`/`hret` are the ONLY per-example
   obligations and that the retired list is a parameter.
3. Additions follow the §12 active-abstraction loop (≥2 consumers
   retrofitted in the lifting commit, measured deltas).
4. Every public THEOREM above carries an exact `#print axioms` pin in
   `Audit/Kit.lean` § Frame/Threshold; the vocabulary defs `ρT`,
   `bumpAt`, `retiredFrame`, `CellFixed` are unpinned by the standing
   convention. A new public lemma lands with its pin in the same
   commit.
5. **Storm/signature discipline: StepKit rules 1–5** (that module's
   `## THE FIVE RULES` section is the kit's single copy — cite, never
   restate). Rule 3 is the one that bites here: pass `retiredFrame`
   in the outer inductions' frame arguments rather than an explicit
   cell list — the consecutive addresses `b+1+1` are NOT defeq to the
   examples' `17+d`/`18+d` spellings (s1 lift-4 gotcha 3), and rule 3's
   fully-pinned `have` is what keeps that from becoming a storm.

## WHAT LIVES WHERE (the kit map — WP arc s3, 2026-08-18)

THIS module: the ADDRESS half of a loop whose body ALLOCATES — the
per-pass shift, the rebase that retires pass-local cells, and the
transfer corollary. It knows nothing about values or step counts.

Siblings, and the boundary with each:

* `Frame/Transfer`, `Frame/RenameId`, `Frame/Sim`, `Frame/…` — the
  general frame/rename THEORY this layer instantiates. A fact about
  renaming in general belongs there; a fact about the per-pass
  THRESHOLD shape belongs here.
* `FuelMeasure` — the counting half of the same loop. A loop whose
  body allocates needs BOTH: its iteration schema for the steps, our
  rebase for the addresses.
* `StepKit` — the heap algebra (`DeadFrom`/`FreshFrom`, the symbolic
  split) the front obligations are discharged with; `lookup_append`
  is the match form this module's pins reference.
* `SliceMem` / `MapMem` — values. Untouched by renaming, which is
  precisely why the two halves compose.

`docs/kit-guide.md` — THE SITUATION INDEX; read it before writing a
new proof. Section fed by this module:
**Loop-local allocation → threshold frame**.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-! ## API group 1 — the per-pass threshold shift -/

/-- The per-pass shift: identity on the fixed cells `0..T-1`, shift by
`d` on the pass-local region. -/
def ρT (T d : Nat) : Nat → Nat := fun x => if x < T then x else x + d

theorem ρT_lt {T d a : Nat} (h : a < T) : ρT T d a = a := if_pos h

theorem ρT_ge {T d a : Nat} (h : T ≤ a) : ρT T d a = a + d :=
  if_neg (by omega)

theorem shiftSpec_ρT (T d : Nat) : ShiftSpec (ρT T d) T (T + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρT] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρT]
    rw [if_neg (by omega)]
    omega

theorem ρT_zero_app (T a : Nat) : ρT T 0 a = a := by
  simp only [ρT]
  split <;> omega

/-- `Loc.base` disagreement from address disagreement. -/
theorem base_ne_of_ne {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := by
  intro hc
  simp only [Loc.base.injEq, Addr.mk.injEq] at hc
  exact h hc

/-! ## API group 2 — rename identity at the zero shift -/

theorem renameLoc_ρT_zero (T : Nat) (l : Loc) :
    renameLoc (ρT T 0) l = l :=
  renameLoc_id (n := Loc.locSup l) (fun x _ => ρT_zero_app T x) l
    (Nat.le_refl _)

/-- A ∀-identity renaming fixes every value (the unbounded sibling of
`renameValue_locFree`, by the same induction). -/
theorem renameValue_id {ρ : Nat → Nat} (hid : ∀ x, ρ x = x) :
    ∀ v : GoValue, renameValue ρ v = v := by
  have hloc : ∀ l : Loc, renameLoc ρ l = l := fun l =>
    renameLoc_id (n := Loc.locSup l) (fun x _ => hid x) l (Nat.le_refl _)
  refine fun v => renameValue.induct
    (motive_1 := fun v => renameValue ρ v = v)
    (motive_2 := fun l => renameValueEntries ρ l = l)
    (motive_3 := fun l => renameValueList ρ l = l)
    (motive_4 := fun l => renameValueFields ρ l = l)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  · rfl
  · intro b; rfl
  · intro n k; rfl
  · intro b k; rfl
  · intro s; rfl
  · rfl
  · intro l; simp [renameValue, hloc]
  · intro t v ih; simp [renameValue, ih]
  · intro tid fields ih; simp [renameValue, ih]
  · intro vs ih; simp [renameValue, ih]
  · intro s
    cases s with
    | mk base off len cap =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [renameValue, hloc]
  · intro m
    cases m with
    | mk base =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [renameValue, hloc]
  · intro es ih; simp [renameValue, ih]
  · intro c
    cases c with
    | mk base =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [renameValue, hloc]
  · intro buf cap closed ih; simp [renameValue, ih]
  · intro fid cap ih; simp [renameValue, ih]
  · intro p; rfl
  · rfl
  · intro v vs ihv ihl; simp [renameValueList, ihv, ihl]
  · rfl
  · intro n v rest ihv ihl; simp [renameValueFields, ihv, ihl]
  · rfl
  · intro k v rest ihk ihv ihl; simp [renameValueEntries, ihk, ihv, ihl]

theorem renameCell_ρT_zero (T : Nat) (c : HeapCell) :
    renameCell (ρT T 0) c = c := by
  simp [renameCell, renameValue_id (ρT_zero_app T)]

/-! ## API group 3 — threshold-fixed cells -/

/-- A heap cell fixed by EVERY threshold-`T` shift — the per-cell
obligation of the rebase (data cells are fixed under any `ρ`; handles
into the sub-`T` front are fixed because the front does not move). -/
def CellFixed (T : Nat) (c : HeapCell) : Prop :=
  ∀ d, renameCell (ρT T d) c = c

/-- Loc-free values give threshold-fixed cells at any threshold. -/
theorem CellFixed.of_locFree {T : Nat} {c : HeapCell}
    (h : GoValue.locSup c.value = 0) : CellFixed T c := by
  intro d
  simp [renameCell, renameValue_locFree _ _ h]

/-! ## API group 4 — the bump transport between consecutive shifts -/

/-- Root bump by `r` above the fixed cells. -/
def bumpAt (T r : Nat) : Loc → Loc
  | .base a => .base ⟨if a.id < T then a.id else a.id + r⟩
  | .field b tid f => .field (bumpAt T r b) tid f
  | .index b i => .index (bumpAt T r b) i

/-- The bump transport: a `d + r` shift is a `d` shift of the bumped
location (the generic `renameLoc_bump2`/`bump3`). -/
theorem renameLoc_ρT_bump (T d r : Nat) (l : Loc) :
    renameLoc (ρT T (d + r)) l = renameLoc (ρT T d) (bumpAt T r l) := by
  induction l with
  | base a =>
      have h : ρT T (d + r) a.id
          = ρT T d (if a.id < T then a.id else a.id + r) := by
        by_cases ha : a.id < T
        · rw [if_pos ha, ρT_lt ha, ρT_lt ha]
        · rw [if_neg ha, ρT_ge (d := d + r) (a := a.id) (by omega),
            ρT_ge (d := d) (a := a.id + r) (by omega)]
          omega
      simp only [renameLoc, bumpAt, h]
  | field b tid f ih => simp only [renameLoc, bumpAt, ih]
  | index b i ih => simp only [renameLoc, bumpAt, ih]

/-! ## API group 5 — the retired-cell frame -/

/-- The retired cells laid out consecutively from `base`. -/
def retiredFrame (base : Nat) : List HeapCell → Heap
  | [] => []
  | c :: rest => (.base ⟨base⟩, c) :: retiredFrame (base + 1) rest

theorem retiredFrame_lookup_base_none {base : Nat} {cs : List HeapCell}
    {a : Nat} (h : a < base ∨ base + cs.length ≤ a) :
    Heap.lookup (retiredFrame base cs) (.base ⟨a⟩) = none := by
  induction cs generalizing base with
  | nil => rfl
  | cons c rest ih =>
      simp only [retiredFrame, Heap.lookup,
        beq_false_of_ne (base_ne_of_ne
          (show base ≠ a by simp [List.length_cons] at h; omega))]
      exact ih (by simp [List.length_cons] at h; omega)

theorem retiredFrame_lookup_field (base : Nat) (cs : List HeapCell)
    (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (retiredFrame base cs) (.field b tid f) = none := by
  induction cs generalizing base with
  | nil => rfl
  | cons c rest ih =>
      simp only [retiredFrame, Heap.lookup]
      rw [show ((Loc.base ⟨base⟩ : Loc) == .field b tid f) = false from rfl]
      exact ih (base + 1)

theorem retiredFrame_lookup_index (base : Nat) (cs : List HeapCell)
    (b : Loc) (i : Int) :
    Heap.lookup (retiredFrame base cs) (.index b i) = none := by
  induction cs generalizing base with
  | nil => rfl
  | cons c rest ih =>
      simp only [retiredFrame, Heap.lookup]
      rw [show ((Loc.base ⟨base⟩ : Loc) == .index b i) = false from rfl]
      exact ih (base + 1)

/-- The inversion: a hit in the retired frame is one of the retired
cells at its laid-out address. -/
theorem retiredFrame_lookup_some_inv {base : Nat} {cs : List HeapCell}
    {l : Loc} {c : HeapCell}
    (h : Heap.lookup (retiredFrame base cs) l = some c) :
    ∃ j, ∃ hj : j < cs.length, l = .base ⟨base + j⟩ ∧ c = cs[j] := by
  induction cs generalizing base with
  | nil => cases h
  | cons c₀ rest ih =>
      simp only [retiredFrame, Heap.lookup] at h
      by_cases hb : (Loc.base ⟨base⟩ : Loc) == l
      · rw [if_pos hb] at h
        injection h with h
        exact ⟨0, by simp, (eq_of_beq hb).symm ▸ rfl, h.symm⟩
      · rw [if_neg hb] at h
        obtain ⟨j, hj, hl, hc⟩ := ih (base := base + 1) h
        exact ⟨j + 1, by simpa using hj,
          by rw [hl]; congr 1; simp; omega, by simpa using hc⟩

/-! ## API group 6 — the trivial frame at the loop entry (generic seed) -/

/-- **The zero-shift seed**: any state whose allocator sits exactly at
the threshold simulates itself under the zero shift with the empty
frame. The per-example `frameSim_zero` cell enumeration disappears —
only the allocator position and the program's `bodies` fact remain. -/
theorem frameSim_seed {T : Nat} {σ : ExecState}
    (hnext : σ.nextAddr = T)
    (hbodies : ∀ f ∈ σ.functions.toList,
      renameStmt (ρT T 0) f.body = f.body) :
    FrameSim (ρT T 0) T T [] σ σ := by
  refine ⟨by simpa using shiftSpec_ρT T 0, rfl, rfl, rfl, rfl, ?_,
    by omega, ?_, ?_, fun a => rfl, hbodies⟩
  · show σ.nextAddr = ρT T 0 σ.nextAddr
    rw [ρT_zero_app]
  · intro l
    rw [renameLoc_ρT_zero]
    cases hl : Heap.lookup σ.heap l with
    | some c =>
        show some c = some (renameCell (ρT T 0) c)
        rw [renameCell_ρT_zero]
    | none => rfl
  · intro l c hl
    cases hl

/-! ## API group 7 — the frame REBASE (retire the pass-local cells) -/

/-- **The generic rebase**: the pass's retired cells (canonical
`T..T+r-1`) move INTO the frame at their true addresses
(`T+d..T+d+r-1`), the shift widens by `r`, and the canonical state
drops back to the `T`-cell shape. The true state `σA` is untouched —
pure re-description.

Hypotheses, grouped: `h` is the incoming simulation at the WIDE
canonical state `σIn`; `hstatic`/`hnext*` say `σOut` is the same
machine with the retired region dropped; `hfront` is THE one front
hypothesis (per-cell agreement + threshold-fixedness, dischargeable by
`rfl`s and cell lemmas); `hret` locates the retired cells; `hhi`/`hnb`
say both canonical heaps are flat base-keyed heaps that end where they
should. -/
theorem rebaseSimT {T d : Nat} {fr : Heap} {retired : List HeapCell}
    {σIn σOut σA : ExecState}
    (h : FrameSim (ρT T d) T (T + d) fr σIn σA)
    (htypes : σOut.types = σIn.types)
    (hfuncs : σOut.functions = σIn.functions)
    (hmethods : σOut.methods = σIn.methods)
    (hmsets : σOut.methodSets = σIn.methodSets)
    (hnextIn : σIn.nextAddr = T + retired.length)
    (hnextOut : σOut.nextAddr = T)
    (hfront : ∀ a : Nat, a < T →
      Heap.lookup σOut.heap (.base ⟨a⟩) = Heap.lookup σIn.heap (.base ⟨a⟩)
      ∧ ∀ c, Heap.lookup σIn.heap (.base ⟨a⟩) = some c → CellFixed T c)
    (hret : ∀ j : Nat, (hj : j < retired.length) →
      Heap.lookup σIn.heap (.base ⟨T + j⟩) = some retired[j]
      ∧ CellFixed T retired[j])
    (hinHi : ∀ a : Nat, T + retired.length ≤ a →
      Heap.lookup σIn.heap (.base ⟨a⟩) = none)
    (houtHi : ∀ a : Nat, T ≤ a →
      Heap.lookup σOut.heap (.base ⟨a⟩) = none)
    (hinNB : (∀ b tid f, Heap.lookup σIn.heap (.field b tid f) = none)
      ∧ (∀ b i, Heap.lookup σIn.heap (.index b i) = none))
    (houtNB : (∀ b tid f, Heap.lookup σOut.heap (.field b tid f) = none)
      ∧ (∀ b i, Heap.lookup σOut.heap (.index b i) = none))
    (hbodies : ∀ f ∈ σIn.functions.toList,
      renameStmt (ρT T (d + retired.length)) f.body = f.body) :
    FrameSim (ρT T (d + retired.length)) T (T + (d + retired.length))
      (fr ++ retiredFrame (T + d) retired) σOut σA := by
  refine ⟨shiftSpec_ρT T (d + retired.length),
    htypes ▸ h.types_eq, hfuncs ▸ h.funcs_eq, hmethods ▸ h.methods_eq,
    hmsets ▸ h.methodSets_eq, ?_, by omega, ?_, ?_, ?_, hfuncs ▸ hbodies⟩
  · -- next_eq
    have hne := h.next_eq
    rw [hnextIn, ρT_ge (T := T) (d := d) (a := T + retired.length)
      (by omega)] at hne
    show σA.nextAddr = ρT T (d + retired.length) σOut.nextAddr
    rw [hnextOut, ρT_ge (T := T) (d := d + retired.length) (a := T)
      (by omega)]
    omega
  · -- lookup_img
    intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < T
        · -- the fixed front
          obtain ⟨hagree, hfix⟩ := hfront a ha
          rw [show renameLoc (ρT T (d + retired.length)) (.base ⟨a⟩)
              = .base ⟨a⟩ from by
            simp [renameLoc, ρT_lt (T := T) (d := d + retired.length) ha]]
          cases hl : Heap.lookup σIn.heap (.base ⟨a⟩) with
          | some c =>
              have himg := h.lookup_some hl
              rw [show renameLoc (ρT T d) (.base ⟨a⟩) = .base ⟨a⟩ from by
                simp [renameLoc, ρT_lt (T := T) (d := d) ha],
                hfix c hl d] at himg
              rw [hagree, hl]
              show Heap.lookup σA.heap (.base ⟨a⟩)
                = some (renameCell (ρT T (d + retired.length)) c)
              rw [hfix c hl (d + retired.length)]
              exact himg
          | none =>
              have hfrA : Heap.lookup fr (.base ⟨a⟩) = none := by
                have := h.fr_avoid a
                rwa [ρT_lt (T := T) (d := d) ha] at this
              have himg := h.lookup_img (.base ⟨a⟩)
              rw [hl, show renameLoc (ρT T d) (.base ⟨a⟩) = .base ⟨a⟩
                from by simp [renameLoc, ρT_lt (T := T) (d := d) ha]]
                at himg
              have himgA : Heap.lookup σA.heap (.base ⟨a⟩)
                  = Heap.lookup fr (.base ⟨a⟩) := himg
              rw [hagree, hl]
              show Heap.lookup σA.heap (.base ⟨a⟩)
                = Heap.lookup (fr ++ retiredFrame (T + d) retired)
                    (.base ⟨a⟩)
              rw [lookup_append_right hfrA,
                retiredFrame_lookup_base_none (by omega), himgA, hfrA]
        · -- the shifted region
          have himg := h.lookup_img (.base ⟨a + retired.length⟩)
          rw [hinHi (a + retired.length) (by omega),
            show renameLoc (ρT T d) (.base ⟨a + retired.length⟩)
              = .base ⟨a + retired.length + d⟩ from by
            simp [renameLoc, ρT_ge (T := T) (d := d)
              (a := a + retired.length) (by omega)]] at himg
          have himgA : Heap.lookup σA.heap
              (.base ⟨a + retired.length + d⟩)
              = Heap.lookup fr (.base ⟨a + retired.length + d⟩) := himg
          rw [show renameLoc (ρT T (d + retired.length)) (.base ⟨a⟩)
              = .base ⟨a + (d + retired.length)⟩ from by
            simp [renameLoc, ρT_ge (T := T) (d := d + retired.length)
              (a := a) (by omega)],
            houtHi a (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + retired.length)⟩)
            = Heap.lookup (fr ++ retiredFrame (T + d) retired)
                (.base ⟨a + (d + retired.length)⟩)
          rw [show a + (d + retired.length) = a + retired.length + d
            from by omega, himgA, lookup_append]
          cases hfr : Heap.lookup fr
              (.base ⟨a + retired.length + d⟩) with
          | some c => rfl
          | none =>
              rw [retiredFrame_lookup_base_none (by omega)]
    | .field b tid f =>
        have himg := h.lookup_img (bumpAt T retired.length
          (.field b tid f))
        rw [← renameLoc_ρT_bump] at himg
        rw [show Heap.lookup σIn.heap
              (bumpAt T retired.length (.field b tid f))
            = Heap.lookup σIn.heap
                (.field (bumpAt T retired.length b) tid f) from rfl,
          hinNB.1 _ tid f] at himg
        have himgA : Heap.lookup σA.heap
            (renameLoc (ρT T (d + retired.length)) (.field b tid f))
            = Heap.lookup fr
                (renameLoc (ρT T (d + retired.length)) (.field b tid f))
          := himg
        rw [houtNB.1 b tid f]
        show Heap.lookup σA.heap
            (renameLoc (ρT T (d + retired.length)) (.field b tid f))
          = Heap.lookup (fr ++ retiredFrame (T + d) retired)
              (renameLoc (ρT T (d + retired.length)) (.field b tid f))
        rw [himgA, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρT T (d + retired.length)) (.field b tid f)) with
        | some c => rfl
        | none =>
            exact (retiredFrame_lookup_field (T + d) retired
              (renameLoc (ρT T (d + retired.length)) b) tid f).symm
    | .index b i =>
        have himg := h.lookup_img (bumpAt T retired.length (.index b i))
        rw [← renameLoc_ρT_bump] at himg
        rw [show Heap.lookup σIn.heap
              (bumpAt T retired.length (.index b i))
            = Heap.lookup σIn.heap
                (.index (bumpAt T retired.length b) i) from rfl,
          hinNB.2 _ i] at himg
        have himgA : Heap.lookup σA.heap
            (renameLoc (ρT T (d + retired.length)) (.index b i))
            = Heap.lookup fr
                (renameLoc (ρT T (d + retired.length)) (.index b i))
          := himg
        rw [houtNB.2 b i]
        show Heap.lookup σA.heap
            (renameLoc (ρT T (d + retired.length)) (.index b i))
          = Heap.lookup (fr ++ retiredFrame (T + d) retired)
              (renameLoc (ρT T (d + retired.length)) (.index b i))
        rw [himgA, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρT T (d + retired.length)) (.index b i)) with
        | some c => rfl
        | none =>
            exact (retiredFrame_lookup_index (T + d) retired
              (renameLoc (ρT T (d + retired.length)) b) i).symm
  · -- frame_pres
    intro loc c hc
    rw [lookup_append] at hc
    cases hfr : Heap.lookup fr loc with
    | some c₀ =>
        rw [hfr] at hc
        injection hc with hcc
        exact hcc ▸ h.frame_pres loc c₀ hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup (retiredFrame (T + d) retired) loc
            = some c := hc
        obtain ⟨j, hj, rfl, rfl⟩ := retiredFrame_lookup_some_inv hc'
        obtain ⟨hlk, hfix⟩ := hret j hj
        have himg := h.lookup_some hlk
        rw [show renameLoc (ρT T d) (.base ⟨T + j⟩) = .base ⟨T + j + d⟩
          from by simp [renameLoc, ρT_ge (T := T) (d := d) (a := T + j)
            (by omega)],
          hfix d] at himg
        rw [show T + d + j = T + j + d from by omega]
        exact himg
  · -- fr_avoid
    intro a
    rw [lookup_append]
    by_cases ha : a < T
    · have h2 := h.fr_avoid a
      rw [ρT_lt (T := T) (d := d) ha] at h2
      rw [ρT_lt (T := T) (d := d + retired.length) ha, h2,
        retiredFrame_lookup_base_none (by omega)]
    · have h2 := h.fr_avoid (a + retired.length)
      rw [ρT_ge (T := T) (d := d) (a := a + retired.length) (by omega)]
        at h2
      rw [ρT_ge (T := T) (d := d + retired.length) (a := a) (by omega),
        show a + (d + retired.length) = a + retired.length + d
          from by omega, h2,
        retiredFrame_lookup_base_none (by omega)]

/-! ## API group 8 — the transfer corollary -/

/-- A canonical segment between shift-fixed configurations transfers to
the true placement (verbatim from the five per-example copies,
threshold-generic). -/
theorem transfer_segT {T d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρT T d) T (T + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρT T d) c = c)
    (hc' : renameConfig (ρT T d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρT T d) T (T + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

end GoLean.Frame
