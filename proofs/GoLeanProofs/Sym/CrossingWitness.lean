import GoLeanProofs.Sym.Crossing
import GoLeanProofs.FuelMeasure

/-!
# The crossing kit's discharge witnesses (triage landing, 2026-08-27)

Judgment-free mini-witnesses for `Sym/Crossing.lean` (amendment A5 of
the triage plan's L-4 landing work): small named theorems that
consume representative kit lemmas in REAL kernel-span derivations
over an ABSTRACT state `σ` and a SYMBOLIC length/index — the kit's
own consumption discipline (StepKit rules 1–5; nothing here is
anchored to a subject run).

Coverage:
- `crossing_witness_lenNeg` — a 2-step span: the symbolic
  length read (`applyStrict_length_slice`, whose engine is
  `validateSlice_ok`) then the unary-minus step with the
  `IntKind.normalize` collapse (`normalize_int_eq` +
  `int_ofNat_cast`) under literal-bound hypotheses discharged by
  `omega` — the Class 1 crossing shape.
- `crossing_witness_ifSplit` — the `ifK` branch crossing
  (`stepFn_ifK_true`) consumed as a span prefix under a path
  condition — the Class A shape.
- `crossing_witness_read` — the symbolic slice read at a symbolic
  index: `loadLoc_base` (the heap-fact load) feeding
  `applyStrict_indexGet_slice` (which crosses `validateSlice` +
  range checks via `validateSlice_ok`/`int_ofNat_not_neg`) in one
  conditioned step.

The prior consumers (three `LogReadSpecs` CallSpec members) died
with the CallSpec calculus; their discharges are archived at
`archive/callspec-era`. These witnesses keep the kit's non-vacuity
in-tree until the tier-1/tier-2 correspondence work (the G-units'
∃-side discharges) consumes it live.

Audit pins: `proofs/Audit/Landing.lean`.
-/

open GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-- **Witness 1 — length read + normalize collapse**: over an
abstract `σ` and a symbolic-length live slice, the 2-step span
reading `len(s)` and negating it: the length read crosses
`validateSlice` (via `applyStrict_length_slice` ←
`validateSlice_ok`), and the negation's store-kind normalization
collapses by the Class 1 range lemma. -/
theorem crossing_witness_lenNeg {σ : ExecState} {sb : Loc} {o n c : Nat}
    {ty : Ty} {env : LocalEnv} {k : Cont} {ch : Choices}
    (hval : n ≤ c) (hn : n < 9223372036854775808) :
    stepFnIter 2 σ
      (.retV (.slice ⟨some sb, o, n, c⟩)
        (.strictK (.lengthOf (some (.slice ty))) [] [] env
          (.strictK .neg [] [] env k))) ch
      = .ok (.retV (.int (-(n : Int)) .int) k, σ, ch) := by
  -- step 1: the length read (the validateSlice crossing)
  have h1 : stepFn σ (.retV (.slice ⟨some sb, o, n, c⟩)
      (.strictK (.lengthOf (some (.slice ty))) [] [] env
        (.strictK .neg [] [] env k))) ch
      = .ok (.retV (.int (Int.ofNat n) .int)
          (.strictK .neg [] [] env k), σ, ch) :=
    stepFn_strict_apply (applyStrict_length_slice hval)
  -- step 2: unary minus with the normalize collapse (Class 1)
  have hneg : applyStrictOp σ .neg [.int (Int.ofNat n) .int]
      = .ok (.int (IntKind.normalize .int (0 - Int.ofNat n)) .int, σ) := rfl
  have hnorm : IntKind.normalize .int (0 - Int.ofNat n) = -(n : Int) := by
    rw [int_ofNat_cast, normalize_int_eq (by omega) (by omega)]
    omega
  have h2 : stepFn σ (.retV (.int (Int.ofNat n) .int)
      (.strictK .neg [] [] env k)) ch
      = .ok (.retV (.int (-(n : Int)) .int) k, σ, ch) := by
    refine stepFn_strict_apply ?_
    show applyStrictOp σ .neg [.int (Int.ofNat n) .int] = _
    rw [hneg, hnorm]
  exact stepFnIter_chain (stepFnIter_one h1) (stepFnIter_one h2)

/-- **Witness 2 — the ifK split as a span prefix**: under the path
condition `b = true` the branch-crossing step enters the then-branch
and any successful continuation span completes behind it (the
split-recombine discipline of the module docstring, at the split
step itself). -/
theorem crossing_witness_ifSplit {σ : ExecState} {b : Bool} {t e : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} {m : Nat}
    {r : Config × ExecState × Choices}
    (hb : b = true)
    (hrest : stepFnIter m σ (.exec t env k) ch = .ok r) :
    stepFnIter (1 + m) σ (.retV (.bool b) (.ifK t e env k)) ch
      = .ok r := by
  obtain ⟨c₂, σ₂, ch₂⟩ := r
  exact stepFnIter_chain (stepFnIter_one (stepFn_ifK_true hb)) hrest

/-- **Witness 3 — the symbolic slice read**: `loadLoc_base` turns a
reader-vocabulary heap fact into the backing-array load consumed by
`applyStrict_indexGet_slice` (crossing `validateSlice` and both
range checks) — one conditioned machine step at a symbolic index
into a symbolic-length slice. -/
theorem crossing_witness_read {σ : ExecState} {a : Addr}
    {tyo : Option Ty} {o n c j : Nat} {kind : IntKind}
    {values : Array GoValue} {v : GoValue}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (hval : n ≤ c) (hj : j < n)
    (hlook : Heap.lookup σ.heap (.base a) = some ⟨tyo, .array values⟩)
    (hget : values[o + j]? = some v) :
    stepFn σ (.retV (.int (Int.ofNat j) kind)
      (.strictK .indexGet [.slice ⟨some (.base a), o, n, c⟩] [] env k)) ch
      = .ok (.retV v k, σ, ch) := by
  have hload : loadLoc σ (.base a) = .ok (.array values) :=
    loadLoc_base (cell := ⟨tyo, .array values⟩) hlook
  exact stepFn_strict_apply (applyStrict_indexGet_slice hval hj hload hget)

end GoLean.Surface
