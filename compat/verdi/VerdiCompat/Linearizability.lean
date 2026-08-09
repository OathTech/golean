/-!
# verdi-raft's linearizability vocabulary (K-generic half)

1:1 port of the STATEMENT slice of
`deps/verdi-raft/theories/Raft/Linearizability.v:7-270` — the vocabulary
the end-to-end linearizability theorem (`EndToEndLinearizability.v:471`)
is stated in: operation traces (`op`), intermediate representations
(`IR`), the acknowledgment relation, the reordering equivalence
(`good_move`/`IR_equivalent`), well-formed sequential traces
(`good_trace`), and `equivalent` itself. The file's proof-side lemma
corpus (its lines 272-1428: `get_*_keys`, `op_equivalent`,
`equivalent_intro`, …) is proof machinery for re-proving
`raft_linearizable'` and is a recorded gap for the attachment phase, not
part of this statement slice (lane log, delta ledger).

Mapping decisions (lane log `docs/2026-08-09_verdi-p1-lane.md`):
sumbool deciders (`acknowledged_op_dec`, `in_dec`) become `Decidable`
instances feeding `if`; everything else is verbatim. The section
variable `K` (client-request keys) stays a section variable.
-/

namespace VerdiCompat

section Linearizability
variable {K : Type} [K_eq_dec : DecidableEq K]

/-- `Linearizability.v:7-9` — a client-visible operation event: `I k` =
request keyed `k` submitted, `O k` = response keyed `k` delivered. -/
inductive op (K : Type) : Type where
  | I : K → op K
  | O : K → op K
deriving DecidableEq

/-- `Linearizability.v:17-20` — intermediate representation of a
linearized trace: `IRI` = invocation, `IRO` = response, `IRU` = an
invocation acknowledged only virtually (its response never surfaced). -/
inductive IR (K : Type) : Type where
  | IRI : K → IR K
  | IRO : K → IR K
  | IRU : K → IR K
deriving DecidableEq

/-- `Linearizability.v:32-33` -/
def acknowledged_op (k : K) (trace : List (op K)) : Prop :=
  op.O k ∈ trace

/-- `Linearizability.v:35-36` (`acknowledged_op_dec`), as an instance. -/
instance (k : K) (tr : List (op K)) : Decidable (acknowledged_op k tr) :=
  inferInstanceAs (Decidable (op.O k ∈ tr))

/-- `Linearizability.v:38-54` -/
inductive acknowledge_all_ops : List (op K) → List (IR K) → Prop where
  | AAO_nil : acknowledge_all_ops [] []
  | AAO_IU : ∀ k tr out,
      ¬ acknowledged_op k tr →
      acknowledge_all_ops tr out →
      acknowledge_all_ops (.I k :: tr) (.IRI k :: .IRU k :: out)
  | AAO_I_dorp : ∀ k tr out,  -- sic, their constructor name
      ¬ acknowledged_op k tr →
      acknowledge_all_ops tr out →
      acknowledge_all_ops (.I k :: tr) out
  | AAO_IO : ∀ k tr out,
      acknowledged_op k tr →
      acknowledge_all_ops tr out →
      acknowledge_all_ops (.I k :: tr) (.IRI k :: out)
  | AAO_O : ∀ k tr out,
      acknowledge_all_ops tr out →
      acknowledge_all_ops (.O k :: tr) (.IRO k :: out)

/-- `Linearizability.v:66-77` — the functional witness for
`acknowledge_all_ops`, target-directed on the `IRU` choice. -/
def acknowledge_all_ops_func : List (op K) → List (IR K) → List (IR K)
  | [], _ => []
  | x :: xs, target =>
    match x with
    | .I k =>
      if acknowledged_op k xs then
        .IRI k :: acknowledge_all_ops_func xs target
      else if IR.IRU k ∈ target then
        .IRI k :: .IRU k :: acknowledge_all_ops_func xs target
      else
        acknowledge_all_ops_func xs target
    | .O k => .IRO k :: acknowledge_all_ops_func xs target

/-- `Linearizability.v:97-102` — the function realizes the relation
(their `acknowledge_all_ops_func_correct`, same induction). -/
theorem acknowledge_all_ops_func_correct (l : List (op K)) (target : List (IR K)) :
    acknowledge_all_ops l (acknowledge_all_ops_func l target) := by
  induction l with
  | nil => exact .AAO_nil
  | cons x xs ih =>
    cases x with
    | I k =>
      by_cases hack : acknowledged_op k xs
      · simpa [acknowledge_all_ops_func, hack] using .AAO_IO k xs _ hack ih
      · by_cases htgt : IR.IRU k ∈ target
        · simpa [acknowledge_all_ops_func, hack, htgt] using .AAO_IU k xs _ hack ih
        · simpa [acknowledge_all_ops_func, hack, htgt] using .AAO_I_dorp k xs _ hack ih
    | O k => simpa [acknowledge_all_ops_func] using .AAO_O k xs _ ih

/-- `Linearizability.v:114-117` — which adjacent swaps preserve client
observation: never move a response before an invocation, never reorder an
invocation past its own (real or virtual) response. -/
def good_move (x y : IR K) : Prop :=
  (∀ k k', ¬ (x = .IRO k ∧ y = .IRI k')) ∧
  (∀ k, ¬ (x = .IRI k ∧ y = .IRO k)) ∧
  (∀ k, ¬ (x = .IRI k ∧ y = .IRU k))

/-- `Linearizability.v:119-131` -/
inductive IR_equivalent : List (IR K) → List (IR K) → Prop where
  | IR_equiv_nil : IR_equivalent [] []
  | IR_equiv_cons : ∀ x xs ys,
      IR_equivalent xs ys →
      IR_equivalent (x :: xs) (x :: ys)
  | IR_equiv_move : ∀ x y xs ys,
      IR_equivalent xs ys →
      good_move x y →
      IR_equivalent (x :: y :: xs) (y :: x :: ys)
  | IR_equiv_trans : ∀ l1 l2 l3,
      IR_equivalent l1 l2 →
      IR_equivalent l2 l3 →
      IR_equivalent l1 l3

omit K_eq_dec in
/-- `Linearizability.v:134-139` -/
theorem IR_equivalent_refl : ∀ l : List (IR K), IR_equivalent l l
  | [] => .IR_equiv_nil
  | x :: xs => .IR_equiv_cons x xs xs (IR_equivalent_refl xs)

/-- `Linearizability.v:249-255` — a good linearized trace: strictly
alternating invocation/response pairs on matching keys (`IRU` closing a
pair whose response never surfaced). Clause order as in the source; the
wildcard covers everything else, including a trailing lone `IRI`. -/
def good_trace : List (IR K) → Prop
  | [] => True
  | .IRI k :: .IRO k' :: l' => k = k' ∧ good_trace l'
  | .IRI k :: .IRU k' :: l' => k = k' ∧ good_trace l'
  | _ => False

/-- `Linearizability.v:257-261` — THE definition the headline theorem
speaks through: the observed operation trace `l` has a good linearized
witness `ir` reachable by acknowledgment + observation-preserving
reordering. -/
def equivalent (l : List (op K)) (ir : List (IR K)) : Prop :=
  good_trace ir ∧
  ∃ ir', acknowledge_all_ops l ir' ∧ IR_equivalent ir' ir

/-- Non-vacuity witness (house doctrine): `equivalent` holds of a
concrete request/response trace and its evident linearization — the
definitions compose and are inhabited. Not in the Coq source. -/
example : equivalent (K := Nat) [.I 0, .O 0] [.IRI 0, .IRO 0] :=
  ⟨⟨rfl, trivial⟩,
   [.IRI 0, .IRO 0],
   .AAO_IO 0 [.O 0] [.IRO 0] (List.mem_singleton.mpr rfl)
     (.AAO_O 0 [] [] .AAO_nil),
   IR_equivalent_refl _⟩

end Linearizability

end VerdiCompat
