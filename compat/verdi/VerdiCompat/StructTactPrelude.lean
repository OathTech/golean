/-!
# StructTact / Coq-stdlib helpers used by Verdi and verdi-raft

1:1 ports of exactly the helper functions the Raft spec depends on.
Each definition cites its source in the reference checkouts
(`deps/StructTact/theories/...`). Coq's explicit sumbool deciders
(`forall x y, {x = y} + {x <> y}`) become `DecidableEq` instance arguments;
that is the one systematic transformation in this file.
-/

namespace VerdiCompat

/-- StructTact `update` (`Update.v:6-7`). -/
def update {A B : Type} [DecidableEq A] (st : A → B) (h : A) (v : B) : A → B :=
  fun nm => if nm = h then v else st nm

/-- StructTact `update_same` (`Update.v` lemma section). -/
@[simp] theorem update_same {A B : Type} [DecidableEq A] (st : A → B) (h : A) (v : B) :
    update st h v h = v := by
  simp [update]

/-- StructTact `update_neq`. -/
theorem update_neq {A B : Type} [DecidableEq A] (st : A → B) {x h : A} (v : B)
    (hne : x ≠ h) : update st h v x = st x := by
  simp [update, hne]

/-- StructTact `update_overwrite`-style collapse: two writes at the same key
keep only the second. -/
@[simp] theorem update_update_same {A B : Type} [DecidableEq A] (st : A → B) (h : A)
    (v w : B) : update (update st h v) h w = update st h w := by
  funext x
  simp only [update]
  split <;> rfl

/-- StructTact `assoc` (`Assoc.v:13-21`). -/
def assoc {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (k', v) :: l', k => if k = k' then some v else assoc l' k

/-- StructTact `assoc_default` (`Assoc.v:23-27`). -/
def assoc_default {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (default : V) : V :=
  match assoc l k with
  | some x => x
  | none => default

/-- StructTact `assoc_set` (`Assoc.v:29-37`). -/
def assoc_set {K V : Type} [DecidableEq K] : List (K × V) → K → V → List (K × V)
  | [], k, v => [(k, v)]
  | (k', v') :: l', k, v =>
    if k = k' then (k, v) :: l' else (k', v') :: assoc_set l' k v

/-- StructTact `dedup` (`Dedup.v:14-22`). Keeps the LAST occurrence of each
element — order matters to `wonElection`'s vote counting. -/
def dedup {A : Type} [DecidableEq A] : List A → List A
  | [] => []
  | x :: xs =>
    let tail := dedup xs
    if x ∈ xs then tail else x :: tail

/-- Coq stdlib `List.remove` (used by `step_failure`'s reboot rule,
`Net.v:451`): removes ALL occurrences. NOT Lean's `List.erase`, which
removes only the first — that would be a silent semantic drift. -/
def removeAll {A : Type} [DecidableEq A] (x : A) : List A → List A
  | [] => []
  | y :: tl => if x = y then removeAll x tl else y :: removeAll x tl

/-- StructTact `all_fin` (`Fin.v:46-50`), transported to Lean's `Fin`.
StructTact encodes `fin (S n) := option (fin n)` with `None ↦ 0` and
`Some x ↦ x+1`; under that isomorphism their
`all_fin (S n) = None :: map Some (all_fin n)` is exactly this
enumeration `[0, 1, ..., n]`. This is a REPRESENTATION CHANGE (recorded
in the design note): any future mechanical Rocq↔Lean check must carry
the `fin n ≅ Fin n` isomorphism through. -/
def allFin : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.succ_pos n⟩ :: (allFin n).map Fin.succ

/-- StructTact `all_fin_all` (`Fin.v:52-54`): the enumeration is complete.
Discharges the `all_names_nodes` obligation of `MultiParams`. -/
theorem allFin_all : ∀ {n : Nat} (x : Fin n), x ∈ allFin n
  | n + 1, ⟨0, _⟩ => List.mem_cons_self ..
  | _ + 1, ⟨i + 1, h⟩ => by
    apply List.mem_cons_of_mem
    exact List.mem_map_of_mem (allFin_all ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- StructTact `all_fin_NoDup` (`Fin.v:60`): the enumeration has no
duplicates. Discharges the `no_dup_nodes` obligation of `MultiParams`. -/
theorem allFin_NoDup : ∀ n, (allFin n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [allFin, List.nodup_cons]
    refine ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨x, -, hx⟩ := List.mem_map.mp hmem
      exact absurd (congrArg Fin.val hx) (Nat.succ_ne_zero x.val)
    · exact (allFin_NoDup n).map Fin.succ
        fun a b h hab => h (Fin.ext (Nat.succ.inj (congrArg Fin.val hab)))

end VerdiCompat
