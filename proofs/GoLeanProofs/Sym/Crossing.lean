import GoLeanProofs.StepKit

/-!
# The data-branch crossing kit (W3 mechanism unit)

Design note: `docs/2026-08-27_crossing-kit-design.md` (LINEAGE: the
path-condition mechanism of classic symbolic execution — King 1976 —
realized as WINDOW SPLITS in the kernel-reduction setting; the
divergences and the quantifier-audit line live there).

When kernel reduction of a span reaches a data branch it cannot
decide (a symbolic-scalar comparison, a store-time
`IntKind.normalize` on a symbolic value, `validateSlice`'s
symbolic Nat-Nat `len > cap`, a read at a symbolic index), the span
is SPLIT at the last config boundary before the stuck step; the path
condition enters as a hypothesis consumed either by a conditioned
step lemma (the `StepKit` idiom — `stepFn_strict_apply` is the
workhorse this module feeds) or by a rewrite of the window's exit
term; each arm's windows then continue by `kernel_rfl` under the
assumption, and arms recombine by case analysis at the spec
statement (the split is over the reflected program's own branch
structure — never over a subject run).

Everything here is UNTRUSTED METHOD (proof-side; StepKit's banner
applies): no name below may appear in a headline statement closure.
Every lemma is over an ABSTRACT `σ : ExecState` (StepKit rules 1–5).

Non-vacuity (≥2 genuinely different consumers, in-unit):
`unstable_maybeLastIndex_nonempty_callSpecR` (normalize collapse +
the length crossing), `unstable_maybeTerm_*` (the symbolic two-scalar
comparison + the in-range entry read), `MemoryStorage.firstIndex`'s
member (the symbolic-length index read) —
`Specs/RaftPilot/LogReadSpecs.lean`.
-/

open GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-! ## Class A — branch crossings (config-boundary `Bool` matches) -/

/-- The `ifK` step under a true branch condition (path condition
consumed as `hb`). -/
theorem stepFn_ifK_true {σ : ExecState} {b : Bool} {t e : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} (hb : b = true) :
    stepFn σ (.retV (.bool b) (.ifK t e env k)) ch
      = .ok (.exec t env k, σ, ch) := by
  subst hb; rfl

/-- The `ifK` step under a false branch condition. -/
theorem stepFn_ifK_false {σ : ExecState} {b : Bool} {t e : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} (hb : b = false) :
    stepFn σ (.retV (.bool b) (.ifK t e env k)) ch
      = .ok (.exec e env k, σ, ch) := by
  subst hb; rfl

/-! ## Class 1 — `IntKind.normalize` collapses (range-premise
rewrites for store-time/arithmetic normalization on symbolic
scalars). Hypotheses use LITERAL bounds so consumers discharge them
by `omega`. -/

/-- `normalize .int` is the identity in signed-64 range. -/
theorem normalize_int_eq {v : Int}
    (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    IntKind.normalize .int v = v := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [if_pos trivial]
  omega

/-- `normalize .uint64` is the identity in unsigned-64 range. -/
theorem normalize_uint64_eq {v : Int}
    (h0 : 0 ≤ v) (h1 : v < 18446744073709551616) :
    IntKind.normalize .uint64 v = v := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [Bool.false_eq_true, if_false]
  omega

/-- `Int.ofNat` is the `Nat` coercion (the definitional bridge `omega`
needs when the machine's terms carry the constructor spelling). -/
theorem int_ofNat_cast (n : Nat) : Int.ofNat n = (n : Int) := rfl

/-- An embedded `Nat` is never negative (constructor spelling). -/
theorem int_ofNat_not_neg (n : Nat) : ¬ (Int.ofNat n < 0) := by
  rw [int_ofNat_cast]; omega

/-- `normalize .int` on an embedded `Nat` (the machine's slice-length
reads land here). -/
theorem normalize_int_ofNat {n : Nat} (h : n < 9223372036854775808) :
    IntKind.normalize .int (Int.ofNat n) = Int.ofNat n := by
  rw [int_ofNat_cast]
  exact normalize_int_eq (by omega) (by omega)

/-- `normalize .uint64` on an embedded `Nat`. -/
theorem normalize_uint64_ofNat {n : Nat}
    (h : n < 18446744073709551616) :
    IntKind.normalize .uint64 (Int.ofNat n) = Int.ofNat n := by
  rw [int_ofNat_cast]
  exact normalize_uint64_eq (by omega) (by omega)

/-! ## Class 2 — `validateSlice` and the slice read ops -/

/-- `validateSlice` collapses on a live backing slice under the
well-formedness premise (the invariant's C1/C2 vocabulary supplies
`len ≤ cap` at consumption sites). -/
theorem validateSlice_ok {b : Loc} {o n c : Nat} (h : n ≤ c) :
    validateSlice ⟨some b, o, n, c⟩ = .ok () := by
  unfold validateSlice
  rw [if_neg (by omega : ¬ (n > c))]
  rfl

/-- The `len` builtin on a live slice of symbolic length: the
`applyStrictOp` fact feeding `stepFn_strict_apply` at the length-read
crossing. The result kind is the machine's `.int` default. -/
theorem applyStrict_length_slice {σ : ExecState} {ty : Ty} {b : Loc}
    {o n c : Nat} (h : n ≤ c) :
    applyStrictOp σ (.lengthOf (some (.slice ty)))
      [.slice ⟨some b, o, n, c⟩]
      = .ok (.int (Int.ofNat n) .int, σ) := by
  have h1 : applyStrictOp σ (.lengthOf (some (.slice ty)))
      [.slice ⟨some b, o, n, c⟩]
      = (validateSlice ⟨some b, o, n, c⟩ *>
          (pure (GoValue.int (Int.ofNat n) .int, σ) :
            Except GoError (GoValue × ExecState))) := rfl
  rw [h1, validateSlice_ok h]
  rfl

/-- The slice index read at a symbolic Nat index `j` into a live
slice with a symbolic-length backing array: crosses `sliceIndexLoc`'s
validation + range checks and the backing-array read in one
`applyStrictOp` fact. Hypotheses are reader-vocabulary heap/range
facts (the symbolic-heap-read discipline: the family carries the
read's outcome). -/
theorem applyStrict_indexGet_slice {σ : ExecState} {sb : Loc}
    {o n c j : Nat} {kind : IntKind} {values : Array GoValue}
    {v : GoValue}
    (hval : n ≤ c) (hj : j < n)
    (hload : loadLoc σ sb = .ok (.array values))
    (hget : values[o + j]? = some v) :
    applyStrictOp σ .indexGet
      [.slice ⟨some sb, o, n, c⟩, .int (Int.ofNat j) kind]
      = .ok (v, σ) := by
  have hsz : o + j < values.size := by
    cases Nat.lt_or_ge (o + j) values.size with
    | inl hlt => exact hlt
    | inr hge =>
        rw [Array.getElem?_eq_none hge] at hget
        exact nomatch hget
  have htn : (Int.ofNat j).toNat = j := rfl
  have htn2 : (Int.ofNat (o + j)).toNat = o + j := rfl
  have hloc : sliceIndexLoc ⟨some sb, o, n, c⟩ (Int.ofNat j)
      = .ok (.index sb (Int.ofNat (o + j))) := by
    unfold sliceIndexLoc
    rw [validateSlice_ok hval]
    simp only [Bind.bind, Except.bind]
    rw [if_neg (int_ofNat_not_neg j)]
    simp only [pure, Except.pure, htn]
    rw [if_pos hj]
  have h3 : arrayGet values (Int.ofNat (o + j)) = .ok v := by
    unfold arrayGet arrayIndexNat
    simp only [Bind.bind, Except.bind]
    rw [if_neg (int_ofNat_not_neg (o + j))]
    simp only [pure, Except.pure, htn2]
    rw [if_pos hsz]
    show (match values[o + j]? with
      | some value => Except.ok value
      | none => indexOutOfRangePanic (Int.ofNat (o + j)) values.size)
      = Except.ok v
    rw [hget]
  have h2 : loadLoc σ (.index sb (Int.ofNat (o + j))) = .ok v := by
    unfold loadLoc
    rw [hload]
    simp only [Bind.bind, Except.bind]
    exact h3
  have h1 : applyStrictOp σ .indexGet
      [.slice ⟨some sb, o, n, c⟩, .int (Int.ofNat j) kind]
      = (sliceIndexLoc ⟨some sb, o, n, c⟩ (Int.ofNat j) >>= fun loc =>
          loadLoc σ loc >>= fun out => pure (out, σ)) := rfl
  rw [h1, hloc]
  simp only [Bind.bind, Except.bind]
  rw [h2]
  rfl

/-- The pointer dereference on a symbolic location: the
`applyStrictOp` fact for the deref crossing (the read's outcome
carried by the family). -/
theorem applyStrict_deref {σ : ExecState} {ty : Ty} {loc : Loc}
    {v : GoValue} (hload : loadLoc σ loc = .ok v) :
    applyStrictOp σ (.deref ty) [.addr loc] = .ok (v, σ) := by
  have h1 : applyStrictOp σ (.deref ty) [.addr loc]
      = (loadLoc σ loc >>= fun out => pure (out, σ)) := rfl
  rw [h1, hload]
  rfl

/-- `loadLoc` at a base address, from the heap fact. -/
theorem loadLoc_base {σ : ExecState} {a : Addr} {cell : HeapCell}
    (h : Heap.lookup σ.heap (.base a) = some cell) :
    loadLoc σ (.base a) = .ok cell.value := by
  unfold loadLoc
  rw [h]
  rfl

end GoLean.Surface
