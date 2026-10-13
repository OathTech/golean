import GoLean.GoCore.Machine

/-!
# Memory contracts, separate from race instrumentation

Root-cell support is deliberately conservative: a write through a path has
its entire root cell in its write support. No claim about distinct paths
within that cell follows. Allocation is above the old allocator bound.
These are semantic operation laws, not an Iris frame rule or a whole-step
effect census. Normalization and all operation failures stay explicit.
-/

namespace GoLean.GoCore.Relational

open Machine

/-- Every old cell outside a declared write support is preserved. Reads,
allocation, control and synchronization require their own contracts. -/
def PreservesOutside (before after : Store) (writes : Nat → Prop) : Prop :=
  ∀ i, i < before.heap.size → ¬ writes i → after.heap[i]? = before.heap[i]?

theorem PreservesOutside.refl (s : Store) (writes : Nat → Prop) :
    PreservesOutside s s writes := fun _ _ _ => rfl

theorem PreservesOutside.trans {a b c : Store} {p q : Nat → Prop}
    (h : PreservesOutside a b p) (k : PreservesOutside b c q)
    (grows : a.heap.size ≤ b.heap.size) :
    PreservesOutside a c (fun i => p i ∨ q i) := by
  intro i hi hn
  rw [k i (Nat.lt_of_lt_of_le hi grows) (fun hq => hn (.inr hq)),
    h i hi (fun hp => hn (.inl hp))]

/-- Root cell reading is a value read; payload cells are outside this domain. -/
theorem read_root {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {v : GoValue}
    (h : Heap.lookup s.heap (.base a) = some (.value ty v)) :
    loadRoot ctx s (.base a) = .ok v := by
  simp [loadRoot, loadLoc, h, pure, Except.pure]

/-- Root writes store the normalized value, not necessarily the supplied value. -/
theorem write_root {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {old v w : GoValue}
    (h : Heap.lookup s.heap (.base a) = some (.value ty old))
    (hn : normalizeValueForTy ctx ty v = .ok w) :
    storeLoc ctx s (.base a) v = .ok { heap := s.heap.set a.id (.value ty w) (Heap.lookup_lt h) } := by
  have hi := Heap.lookup_lt h
  have hcell : s.heap[a.id] = .value ty old := by
    obtain ⟨i⟩ := a
    exact (Array.getElem?_eq_some_iff.mp h).2
  unfold storeLoc Store.updateCell
  simp only [Loc.rootPath, hi, ↓reduceDIte, hcell, writeAt]
  have : normalizeValueForTyTy (normalizeValueForTyAt ctx.types ctx.types.size) ty v = .ok w := hn
  simp [this, Bind.bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- Any successful update changes only its selected root. This includes
payload and metadata changes; no race-trace premise is used. -/
theorem update_support {s t : Store} {a : Addr} {f : HeapCell → Except Stop HeapCell}
    (h : Store.updateCell s a f = .ok t) :
    t.heap.size = s.heap.size ∧ PreservesOutside s t (· = a.id) := by
  unfold Store.updateCell at h
  split at h
  · rename_i hi
    cases hf : f s.heap[a.id] with
    | error e => simp [hf, Bind.bind, Except.bind] at h
    | ok cell =>
      simp only [hf, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst t
      refine ⟨by simp, ?_⟩
      intro i _ hn
      simp [Ne.symm hn]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The entire root cell is a sound write support for every successful
path write, including overlapping or noncanonical path spellings. -/
theorem write_support {ctx : ProgramCtx} {s t : Store} {l : Loc} {v : GoValue}
    (h : storeLoc ctx s l v = .ok t) :
    t.heap.size = s.heap.size ∧ PreservesOutside s t (· = (Loc.rootPath l).1.id) := by
  unfold storeLoc at h
  exact update_support h

theorem write_read_root {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {old v w : GoValue}
    (h : Heap.lookup s.heap (.base a) = some (.value ty old))
    (hn : normalizeValueForTy ctx ty v = .ok w) :
    ∃ t, storeLoc ctx s (.base a) v = .ok t ∧ loadRoot ctx t (.base a) = .ok w ∧
      t.heap.size = s.heap.size ∧ PreservesOutside s t (· = a.id) := by
  have hw := write_root h hn
  refine ⟨_, hw, read_root (ty := ty) ?_, (write_support hw).1, (write_support hw).2⟩
  simp [Heap.lookup]

/-- Allocation both preserves every old cell and exposes the normalized new
one at the old bound. No well-formedness premise is needed for this law. -/
theorem allocate {ctx : ProgramCtx} {s t : Store} {v : GoValue} {ty : Ty} {l : Loc}
    (h : Store.alloc ctx s v ty = .ok (l, t)) :
    l = .base ⟨s.heap.size⟩ ∧ t.heap.size = s.heap.size + 1 ∧
    PreservesOutside s t (fun _ => False) ∧
    ∃ w, normalizeValueForTy ctx ty v = .ok w ∧ Heap.lookup t.heap l = some (.value ty w) := by
  obtain ⟨hl, hsize⟩ := Store.alloc_shape h
  obtain ⟨w, hn, hh⟩ := Store.alloc_cell h
  refine ⟨hl, hsize, ?_, w, hn, ?_⟩
  · intro i hi _
    simp [hh, Array.getElem?_push, hi, Nat.ne_of_lt hi]
  · simp [hh, hl, Heap.lookup]

/-- Two deterministic root writes to distinct existing cells commute.
Their normalized values are fixed in the same program context. This law
introduces no allocation, output, control transfer or choice. It does not
equate ordered access traces, and is not yet an `unseq` schedule theorem. -/
theorem root_writes_commute {ctx : ProgramCtx} {s : Store} {a b : Addr}
    {ta tb : Ty} {oldA oldB va vb wa wb : GoValue}
    (different : a.id ≠ b.id)
    (ha : Heap.lookup s.heap (.base a) = some (.value ta oldA))
    (hb : Heap.lookup s.heap (.base b) = some (.value tb oldB))
    (hna : normalizeValueForTy ctx ta va = .ok wa)
    (hnb : normalizeValueForTy ctx tb vb = .ok wb) :
    ∃ sa sb final,
      storeLoc ctx s (.base a) va = .ok sa ∧ storeLoc ctx s (.base b) vb = .ok sb ∧
      storeLoc ctx sa (.base b) vb = .ok final ∧ storeLoc ctx sb (.base a) va = .ok final := by
  have hwa := write_root ha hna
  have hwb := write_root hb hnb
  have hb' : Heap.lookup (s.heap.set a.id (.value ta wa) (Heap.lookup_lt ha)) (.base b) =
      some (.value tb oldB) := by simpa [Heap.lookup, different] using hb
  have ha' : Heap.lookup (s.heap.set b.id (.value tb wb) (Heap.lookup_lt hb)) (.base a) =
      some (.value ta oldA) := by simpa [Heap.lookup, Ne.symm different] using ha
  have hab := write_root (s := ⟨s.heap.set a.id (.value ta wa) (Heap.lookup_lt ha)⟩) hb' hnb
  have hba := write_root (s := ⟨s.heap.set b.id (.value tb wb) (Heap.lookup_lt hb)⟩) ha' hna
  refine ⟨_, _, _, hwa, hwb, hab, ?_⟩
  rw [hba]
  congr 2
  exact (Array.set_comm (.value ta wa) (.value tb wb)
    (hi := Heap.lookup_lt ha) (hj := by simpa using Heap.lookup_lt hb) different).symm

end GoLean.GoCore.Relational
