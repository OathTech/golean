import GoLeanProofs.Specs.Raft.SpanS1Walk

/-!
# `s1_span_computes` discharge witnesses (witness-in-same-slice)

The non-vacuity gate for the span theorem: both the FIRE shape (term
5 already claimed by node 1, node 2 claiming — the U23 bridge
witness's event `(5,2)` after `(5,1)`) and the CLEAN shape (empty
claim map) instantiate `s1_span_computes` at a CONCRETE five-cell
checker state with every premise discharged. The fire instance's
model readout is `s1Fires` at the same event the U23 `s1w_fire`
witness uses, tying the span witness to the bridge witness's
vocabulary.

The compiled cross-check: the same two states walked by the compiled
interpreter reach `.next .stop` in 74 (clean) / 646 (fire, one-digit
arguments) steps (`artifacts/probe/s1block.out`) — both under the
theorem's 5200 bound, the clean count matching the composed
47+4+3+20 exactly.
-/

namespace GoLean.RaftSeam.SpanS1

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.NativeSpec (s1Fires)
open GoLean.StringMem (gs)
open GoLean.MapMem (toEntries setk)

set_option maxRecDepth 100000

/-- The witness node struct (`id = 2`, `term = 5`, leader state). -/
def wNdFs : Array (String × GoValue) :=
  #[("id", .int 2 .uint64), ("rn", .nil), ("st", .nil),
    ("term", .int 5 .uint64), ("commit", .int 0 .uint64),
    ("state", .int 2 .uint64), ("applied", .int 0 .uint64),
    ("lastTrm", .int 0 .uint64), ("got", .nil)]

/-- The witness heap: `t`-pointer at 40, `nd`-pointer at 41, the twin
struct at 50 (map data at 55), the node struct at 52. -/
def wHeap (kvs : List (Int × Nat)) : Heap :=
  [(.base ⟨40⟩, ⟨some (.pointer tyTwinD), .addr (.base ⟨50⟩)⟩),
   (.base ⟨41⟩, ⟨some (.pointer tyNodeD), .addr (.base ⟨52⟩)⟩),
   (.base ⟨50⟩, twCell .nil .nil .nil 55 .nil 3 1 0 .nil .nil 9
     (gs [97]) .nil),
   (.base ⟨52⟩, ⟨some tyNodeD, .struct tidN wNdFs⟩),
   (.base ⟨55⟩, ⟨none, .mapData (toEntries kvs)⟩)]

def wEnvS : LocalEnv := [[("t", .base ⟨40⟩), ("nd", .base ⟨41⟩)]]

/-- Freshness of the witness heap above its frontier. -/
theorem wHeap_fresh (kvs : List (Int × Nat)) :
    ∀ x, 60 ≤ x →
      Heap.lookup (wHeap kvs) (.base ⟨x⟩) = none := by
  intro x hx
  show Heap.lookup (wHeap kvs) (.base ⟨x⟩) = none
  unfold wHeap
  rw [lookup_cons_ne (base_beq_false (by omega : 40 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 41 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 50 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 52 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 55 ≠ x))]
  rfl

/-- **THE FIRE WITNESS**: node 2 claims term 5 already held by node
1 — every premise of `s1_span_computes` discharged at the concrete
state; the machine's violation counter lands at `0 + 1` with the
model's `s1Fires` deciding it. -/
theorem s1w_span_fire :
    ∃ m ≤ 5200, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m (twinSt (wHeap [(5, 1)]) 60)
          (.exec s1Block wEnvS .stop) []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55 .nil ((3 + 1 : Nat) : Int)
              1 ((0 + (if s1Fires ⟨projLOf [(5, 1)], 3, 0⟩ (5, 2)
                  then 1 else 0) : Nat) : Int)
              .nil .nil 9 tr' .nil)
      ∧ Heap.lookup σ'.heap (.base ⟨55⟩)
          = some ⟨none, .mapData (toEntries (setk [(5, 1)] 5 2))⟩
      ∧ (∀ x, x < 60 → x ≠ 50 → x ≠ 55 →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup (wHeap [(5, 1)]) (.base ⟨x⟩))
      ∧ 60 + 2 ≤ σ'.nextAddr
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  exact s1_span_computes (cN := 3) (wN := 0) (tm := 5) (idv := 2)
    (cm := 1) (sq := 9) (tr := gs [97]) (kvs := [(5, 1)])
    rfl rfl (twinSt (wHeap [(5, 1)]) 60) [] rfl rfl rfl rfl rfl rfl
    rfl (wHeap_fresh [(5, 1)]) ⟨rfl, rfl, rfl, rfl⟩
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      constructor <;> omega)
    (by
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The fire witness FIRES: the model predicate at the witness event
is `true` (the U23 `s1w_fire` event, span-side). -/
theorem s1w_span_fire_fires :
    s1Fires ⟨projLOf [(5, 1)], 3, 0⟩ (5, 2) = true := rfl

/-- **THE CLEAN WITNESS**: empty claim map — no fire, counter stays. -/
theorem s1w_span_clean :
    ∃ m ≤ 5200, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m (twinSt (wHeap []) 60)
          (.exec s1Block wEnvS .stop) []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55 .nil ((3 + 1 : Nat) : Int)
              1 ((0 + (if s1Fires ⟨projLOf [], 3, 0⟩ (5, 2)
                  then 1 else 0) : Nat) : Int)
              .nil .nil 9 tr' .nil)
      ∧ Heap.lookup σ'.heap (.base ⟨55⟩)
          = some ⟨none, .mapData (toEntries (setk [] 5 2))⟩
      ∧ (∀ x, x < 60 → x ≠ 50 → x ≠ 55 →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup (wHeap []) (.base ⟨x⟩))
      ∧ 60 + 2 ≤ σ'.nextAddr
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  exact s1_span_computes (cN := 3) (wN := 0) (tm := 5) (idv := 2)
    (cm := 1) (sq := 9) (tr := gs [97]) (kvs := [])
    rfl rfl (twinSt (wHeap []) 60) [] rfl rfl rfl rfl rfl rfl
    rfl (wHeap_fresh []) ⟨rfl, rfl, rfl, rfl⟩
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro p hp; cases hp)
    (by intro p hp; cases hp)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The clean witness does NOT fire. -/
theorem s1w_span_clean_silent :
    s1Fires ⟨projLOf [], 3, 0⟩ (5, 2) = false := rfl

end GoLean.RaftSeam.SpanS1
