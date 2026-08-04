import GoLeanProofs.Surface

/-!
# Quorum-pilot phase-0 targets (statement first — targets, NOT results)

The sprint arc's step-0 statements (`docs/2026-07-30_quorum-pilot-arc.md`
phase 0), pinned against the REAL source in `deps/raft/quorum/`:

- `majority.go` `(MajorityConfig).CommittedIndex(l AckedIndexer) Index`:
  n = len(c); empty config returns `math.MaxUint64`; otherwise the
  acked-or-zero indexes are sorted and the `n - (n/2+1)`-th (0-indexed,
  ascending) is returned — the (n/2+1)-th LARGEST, missing acks counting
  as zero.
- `quick_test.go` `alternativeMajorityCommittedIndex` — etcd's own
  reference implementation (quickchecked against the main one, 50k
  cases): the largest index acked by ≥ n/2+1 voters, 0 if none.

The spec below (`IsCommittedIndex`) is the declarative form both
implementations satisfy: committedness + maximality + the empty-config
convention. Ids and indexes are uint64 values modeled as `Nat`; the
machine bridge (phase 4) carries the `< 2^64` normalization.

Layers in this file:
1. Pure math: `ackedOrZero`/`supporters`/`quorumSize`, the spec
   `IsCommittedIndex`, and the executable reference `committedIndexRef`
   (structural insertion sort, so instances compute by `rfl`/`decide`).
2. Non-vacuity pins: etcd's own datadriven values
   (`testdata/majority_commit.txt`) as decidable instances, plus the
   spec discharged on a concrete 3-voter instance (committedness AND
   maximality), plus negative twins.
3. TARGETS (`def … : Prop`, unproven by design):
   `committedIndexRef_meets_spec_statement` (the general agreement
   theorem — phase-4 critical path: the machine walk lands on the ref,
   this upgrades it to the spec).
4. `GoFuncSpec2` — the multi-result statement form the pilot forces
   (`AckedIndex` returns `(Index, bool)`; W1/prediction-3). A statement
   SHAPE: defining it is the arity-widening design decision; its
   discharge machinery (multi-target call laws, two-cell frame exit)
   lands in phase 4 with witnesses. The machine-level CommittedIndex
   composition target is deliberately NOT yet a `def` — its shape needs
   the phase-1/2 outputs (method receivers, interface-value passing);
   it is recorded in the arc doc and instantiated the moment the pin
   exists, per the golden-pin precedent.
-/

namespace GoLean.Quorum

/-- A voter's acked index, with Go's convention: a voter that has not
reported counts as zero (`majority.go`: "Any unused slots will be left
as zero; these correspond to voters that may report in, but haven't
yet."). -/
def ackedOrZero (acked : Nat → Option Nat) (v : Nat) : Nat :=
  (acked v).getD 0

/-- Number of voters in `c` supporting index `j` (acked-or-zero ≥ j). -/
def supporters (c : List Nat) (acked : Nat → Option Nat) (j : Nat) : Nat :=
  (c.filter (fun v => decide (j ≤ ackedOrZero acked v))).length

/-- Majority quorum size: `n/2 + 1` (`majority.go` line 161,
`quick_test.go` line 113). -/
def quorumSize (n : Nat) : Nat := n / 2 + 1

/-- `math.MaxUint64` — the empty-config convention's return value. -/
def uint64Max : Nat := 2 ^ 64 - 1

/-- **THE SPEC**: `r` is the committed index for config `c` and acked
data `acked`. Nonempty case: a quorum supports `r` (committedness) and
no strictly larger index has quorum support (maximality). Empty case:
the `math.MaxUint64` convention (joint-quorum identity).

It determines `r` UNIQUELY — mechanized as
`QuorumRefSpec.isCommittedIndex_unique`, with the full characterization
(`IsCommittedIndex c acked r ↔ r = committedIndexRef c acked`) as
`isCommittedIndex_iff`. That equivalence is what licenses reading "the
machine's answer is a committed index" as "the machine computes Go's
`CommittedIndex`"; before 2026-07-31 it was asserted here and proven
nowhere (pre-merge audit, finding 5).

UNMECHANIZED, and marked so: the claim that BOTH etcd implementations
satisfy this. `majority.go`'s is discharged
(`committedIndexRef_meets_spec`, via the verbatim-pinned reference);
`quick_test.go`'s `alternativeMajorityCommittedIndex` is not modeled in
Lean at all, so its agreement is an argued reading of the source ("the
largest index acked by ≥ n/2+1 voters, 0 if none" is exactly the
characterization above), not a theorem. -/
def IsCommittedIndex (c : List Nat) (acked : Nat → Option Nat) (r : Nat) : Prop :=
  (c = [] ∧ r = uint64Max) ∨
  (c ≠ [] ∧
    quorumSize c.length ≤ supporters c acked r ∧
    ∀ j, r < j → supporters c acked j < quorumSize c.length)

/-- Structural insertion (ascending) — the sort is hand-rolled so the
reference computes by `rfl` (Lean core's `mergeSort` does not reduce
definitionally). -/
def insertAsc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertAsc x ys

def sortAsc : List Nat → List Nat
  | [] => []
  | x :: xs => insertAsc x (sortAsc xs)

/-- **The executable reference**: the `(n/2+1)`-th largest acked-or-zero
index — the shape of BOTH etcd implementations (`majority.go` sorts
ascending and reads position `n - (n/2+1)`; this is that, verbatim). -/
def committedIndexRef (c : List Nat) (acked : Nat → Option Nat) : Nat :=
  match c with
  | [] => uint64Max
  | _ =>
    let sorted := sortAsc (c.map (ackedOrZero acked))
    sorted.getD (c.length - quorumSize c.length) 0

/-! ## Non-vacuity pins: etcd's own datadriven values
(`testdata/majority_commit.txt`), computed by the reference. -/

/-- `committed` (empty config) → `∞`. -/
example : committedIndexRef [] (fun _ => none) = uint64Max := rfl

/-- `committed cfg=(1) idx=(_)` → `0`. -/
example : committedIndexRef [1] (fun _ => none) = 0 := rfl

/-- `committed cfg=(1) idx=(12)` → `12`. -/
example : committedIndexRef [1] (fun v => if v = 1 then some 12 else none)
    = 12 := rfl

/-- The 3-voter `Describe` example (101/102/103): median wins. -/
def acked3 : Nat → Option Nat :=
  fun v => if v = 1 then some 101 else if v = 2 then some 102
           else if v = 3 then some 103 else none

example : committedIndexRef [1, 2, 3] acked3 = 102 := rfl

/-- Missing-ack example (`cfg=(1 2 3) idx=(101 _ 103)`): the missing
voter counts as zero, so the quorum value is 101. -/
example : committedIndexRef [1, 2, 3]
    (fun v => if v = 1 then some 101 else if v = 3 then some 103 else none)
    = 101 := rfl

/-- **The spec itself is satisfiable and bites** (non-vacuity of
`IsCommittedIndex`, maximality included — the ∀ is discharged by case
analysis on the three voters' thresholds): 102 IS the committed index
of the 3-voter instance. -/
theorem isCommittedIndex_acked3 : IsCommittedIndex [1, 2, 3] acked3 102 := by
  refine Or.inr ⟨by decide, by decide, ?_⟩
  intro j hj
  have h1 : ¬ (j ≤ 101) := by omega
  have h2 : ¬ (j ≤ 102) := by omega
  by_cases h3 : j ≤ 103 <;>
    simp [supporters, acked3, ackedOrZero, List.filter, h1, h2, h3, quorumSize]

/-- Negative twin: 103 is NOT committed (only one supporter). -/
theorem not_committedIndex_acked3_103 :
    ¬ IsCommittedIndex [1, 2, 3] acked3 103 := by
  rintro (⟨h, -⟩ | ⟨-, hq, -⟩)
  · simp at h
  · revert hq
    decide

/-- Negative twin: 101 is not committed either (maximality fails at
102). -/
theorem not_committedIndex_acked3_101 :
    ¬ IsCommittedIndex [1, 2, 3] acked3 101 := by
  rintro (⟨h, -⟩ | ⟨-, -, hmax⟩)
  · simp at h
  · exact absurd (hmax 102 (by omega)) (by decide)

/-! ## Targets (statements, NOT results — the widening-loop discipline) -/

/-- **TARGET (phase 4 critical path)**: the executable reference meets
the declarative spec, for every duplicate-free config. The machine walk
will land on `committedIndexRef`'s value; this theorem upgrades that to
`IsCommittedIndex` — together they are the tier-1 claim. -/
def committedIndexRef_meets_spec_statement : Prop :=
  ∀ (c : List Nat) (acked : Nat → Option Nat),
    c.Nodup → IsCommittedIndex c acked (committedIndexRef c acked)

end GoLean.Quorum

namespace GoLean.Surface

open GoLean.GoCore

/-- **The multi-result function-spec form** (the arity widening the
pilot forces — `AckedIndex(id)` returns `(Index, bool)`; W1 owed row,
prediction 3). `GoFuncSpec2 funcs fid kind argEnv args P Q` reads:
*calling `fid(args)` into any two caller target cells (int-kind first,
bool second, any prior values, distinct addresses) in any admissible heap
satisfying `P` — with any frame — terminates only in states where the
cells received `n` and `b` with `Q n b`, beside `P`'s leftovers, frame
intact.* Binding point as in `GoFuncSpec`: the caller's target cells,
written at frame exit from the callee's pinned result locations
(`Step.frameReturn`/`frameFall` on the two-element lists).

`argEnv` is the CALLER's ambient bindings that the argument expressions
read — the receiver's cell for a method call, exactly as a Go callsite
`m.AckedIndex(id)` names a local `m`. It sits in the same (innermost)
scope as the two result-target bindings, and `argEnv = []` is the phase-0
shape verbatim.

*Why it exists (defect found and fixed 2026-07-31, phase 4 slice 5, and
recorded rather than quietly patched):* the phase-0 shape hardcoded the
caller environment to the two `$callres` bindings, so an argument
expression could denote nothing but a literal — and a method whose
receiver is a heap value (every Go method) was UNSTATEABLE. The FIRST
`quorumAckedIndexFuncSpec2_statement` (written at `39891ae` — in phase 4,
NOT at phase 0; provenance corrected 2026-07-31 per pre-merge audit
finding 6, since only the SHAPE above is phase-0) consequently passed
`#[]` arguments to a two-parameter method, which `enterFrame`'s arity
check rejects: the
configuration is STUCK, so the judgment's safety half (`ProgressExec`
since sem-adequacy slice 4) — hence the whole statement — was
FALSE, not merely unproven. Widening the caller environment is the
minimal fix that makes the intended claim stateable; the statement is
re-pinned in `Specs/GoldenQuorumWP.lean` and now PROVEN. -/
def GoFuncSpec2 (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (fid : FuncId) (kind : IntKind)
    (argEnv : Scope) (args : Array Expr) (P : HProp)
    (Q : Int → Bool → HProp) : Prop :=
  ∀ (ra rb : Nat) (w₁ w₂ : GoValue),
    ra ≠ rb →
    GoSpec types funcs methods
      [("$callres0", Loc.base ⟨ra⟩) :: ("$callres1", Loc.base ⟨rb⟩) :: argEnv]
      (.sep (.pointsTo ra ⟨some (.int kind), w₁⟩)
        (.sep (.pointsTo rb ⟨some .bool, w₂⟩) P))
      (.call #[.var "$callres0", .var "$callres1"] fid args)
      (.ex fun (n : Int) => .ex fun (b : Bool) =>
        .sep (.pointsTo ra ⟨some (.int kind), .int n kind⟩)
          (.sep (.pointsTo rb ⟨some .bool, .bool b⟩) (Q n b)))

end GoLean.Surface
