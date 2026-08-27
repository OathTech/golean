import GoLeanProofs.Sym.Conc
import GoLeanProofs.Sym.Mirror

/-!
# Reflection is the embedding's inverse (W1; the Mirror block's
recorded claim, now a theorem)

`Sym/Mirror.lean`'s reflection block states "at the concrete domain
the reflection is the embedding's inverse" — as a comment. W1 needs
the theorem (for ANY Sound interpretation, since literal payloads
concretize by the `litI`/`litB` laws): the judgment's ∀-continuation
instances are produced by reflecting an arbitrary machine
continuation into the mirror and running the open-tail window there,
so the γ-image of the reflected tail must be the tail itself —
`concK I (reflectK D k) = k`, and its payload companions.

LINEAGE: the retraction half of a Galois insertion (abstract
interpretation's γ ∘ α = id on the exactly-representable elements —
reflection's image is literal-only, so the retraction is exact).

Consumers (triage landing, 2026-08-27): the original consumer (the
BecomeFollowerSpec pilot's CallSpec instances) died with the
CallSpec calculus (archived at `archive/callspec-era`); these are
UNCONDITIONAL equations strengthening the landed `Sym/Conc`/`Mirror`
pair (no premise to witness — no vacuity exposure), consumed by any
mirror-side reflection of a machine continuation. Pins:
`Audit/W1.lean`.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore

variable {D : ScalarDom} {I : Interp D}

/-- Attach-map elimination at the pair shape `concV`/`reflectV` use. -/
private theorem attach_map_fst_snd {α β : Type} (xs : Array (String × α))
    (g : α → β) :
    xs.attach.map (fun ⟨(n, v), _⟩ => (n, g v))
      = xs.map (fun p => (p.1, g p.2)) := by
  have h : (fun (i : {x // x ∈ xs}) => (fun p => (p.1, g p.2)) i.val)
      = (fun ⟨(n, v), _⟩ => ((n, g v) : String × β)) := by
    funext ⟨⟨n, v⟩, h⟩
    rfl
  rw [← h]
  exact Array.attach_map_val xs (fun p => (p.1, g p.2))

private theorem attach_map_plain {α β : Type} (xs : Array α) (g : α → β) :
    xs.attach.map (fun ⟨v, _⟩ => g v) = xs.map g := by
  have h : (fun (i : {x // x ∈ xs}) => g i.val)
      = (fun ⟨v, _⟩ => g v) := by
    funext ⟨v, h⟩
    rfl
  rw [← h]
  exact Array.attach_map_val ..

private theorem attach_map_pair {α β : Type} (xs : Array (α × α))
    (g : α → β) :
    xs.attach.map (fun ⟨(k, v), _⟩ => (g k, g v))
      = xs.map (fun p => (g p.1, g p.2)) := by
  have h : (fun (i : {x // x ∈ xs}) => ((fun p => (g p.1, g p.2)) i.val))
      = (fun ⟨(k, v), _⟩ => ((g k, g v) : β × β)) := by
    funext ⟨⟨k, v⟩, h⟩
    rfl
  rw [← h]
  exact Array.attach_map_val xs (fun p => (g p.1, g p.2))

private theorem attach_map_plain_list {α β : Type} (xs : List α)
    (g : α → β) :
    xs.attach.map (fun ⟨v, _⟩ => g v) = xs.map g := by
  have h : (fun (i : {x // x ∈ xs}) => g i.val)
      = (fun ⟨v, _⟩ => g v) := by
    funext ⟨v, h⟩
    rfl
  rw [← h]
  exact List.attach_map_val ..

private theorem list_map_id_of_mem {α : Type} :
    ∀ {xs : List α} {f : α → α}, (∀ x ∈ xs, f x = x) → xs.map f = xs := by
  intro xs f h
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem array_map_id_of_mem {α : Type} {xs : Array α} {f : α → α}
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  apply Array.ext'
  rw [Array.toList_map]
  exact list_map_id_of_mem (fun x hx => h x (by simpa using hx))

/-- **The value retraction**: concretizing a reflected value gives the
value back, for every Sound interpretation (payloads are literals, so
only the `litI`/`litB` laws are consumed). -/
theorem reflectV_conc (hI : I.Sound) :
    ∀ v : GoValue, concV I (reflectV D v) = v := by
  intro v
  induction v using reflectV.induct
  case case1 => simp [reflectV, concV]
  case case2 b => simp [reflectV, concV, hI.litB]
  case case3 n kind => simp [reflectV, concV, hI.litI]
  case case4 bits kind => simp [reflectV, concV]
  case case5 s => simp [reflectV, concV]
  case case6 loc => simp [reflectV, concV]
  case case7 => simp [reflectV, concV]
  case case8 dynTy inner ih => simp [reflectV, concV, ih]
  case case9 tid fields ih =>
      simp only [reflectV, concV, attach_map_fst_snd, Array.map_map]
      congr 1
      apply array_map_id_of_mem
      intro p hp
      obtain ⟨n, v⟩ := p
      simp [Function.comp, ih n v hp]
  case case10 values ih =>
      simp only [reflectV, concV, attach_map_plain, Array.map_map]
      congr 1
      apply array_map_id_of_mem
      intro x hx
      simp [Function.comp, ih x hx]
  case case11 sv => simp [reflectV, concV]
  case case12 mv => simp [reflectV, concV]
  case case13 entries ihk ihv =>
      simp only [reflectV, concV, attach_map_pair, Array.map_map]
      congr 1
      apply array_map_id_of_mem
      intro p hp
      obtain ⟨a, b⟩ := p
      simp [Function.comp, ihk a b hp, ihv a b hp]
  case case14 cv => simp [reflectV, concV]
  case case15 buf capacity closed ih =>
      simp only [reflectV, concV, attach_map_plain, Array.map_map]
      congr 1
      apply array_map_id_of_mem
      intro x hx
      simp [Function.comp, ih x hx]
  case case16 fid captured ih =>
      simp only [reflectV, concV, attach_map_plain_list, List.map_map]
      congr 1
      apply list_map_id_of_mem
      intro x hx
      simp [Function.comp, ih x hx]
  case case17 p => simp [reflectV, concV]

/-- The panic-entry retraction. -/
theorem reflectEntry_conc (hI : I.Sound) (e : Machine.PanicEntry) :
    concEntry I (reflectEntry D e) = e := by
  simp [reflectEntry, concEntry, reflectV_conc hI]

/-- The target-ref retraction. -/
theorem reflectRef_conc (hI : I.Sound) (r : Machine.TargetRef) :
    concRef I (reflectRef D r) = r := by
  cases r <;>
    simp [reflectRef, concRef, reflectV_conc hI, List.map_map,
      Function.comp_def]

/-- The heap-cell retraction. -/
theorem reflectCell_conc (hI : I.Sound) (c : GoCore.HeapCell) :
    concCell I (reflectCell D c) = c := by
  simp [reflectCell, concCell, reflectV_conc hI]

/-- The heap retraction. -/
theorem reflectHeap_conc (hI : I.Sound) (h : GoCore.Heap) :
    concHeap I (reflectHeap D h) = h := by
  simp [reflectHeap, concHeap, List.map_map, Function.comp_def,
    reflectCell_conc hI]

/-- **The continuation retraction** — the lemma the judgment's
∀-continuation instances ride: reflecting an arbitrary machine
continuation into the mirror and concretizing gives it back
verbatim. -/
theorem reflectK_conc (hI : I.Sound) :
    ∀ k : Machine.Cont, concK I (reflectK D k) = k := by
  intro k
  induction k <;>
    simp [reflectK, concK, reflectV_conc hI, reflectEntry_conc hI,
      reflectRef_conc hI, List.map_map, Array.map_map,
      Function.comp_def, *]

end GoLean.Sym
