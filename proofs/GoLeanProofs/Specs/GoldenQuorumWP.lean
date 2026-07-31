import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.QuorumOps
import GoLeanProofs.Specs.QuorumRefSpec

/-!
# The quorum walk — the FIRST machine discharge, and the math link
(quorum pilot phase 4, 2026-07-31)

Honest status, stated once and not softened anywhere below:

- **PROVEN, machine-level**: `quorumAckedIndexFuncSpec2` — the real
  `main.mapAckIndexer.AckedIndex` of the PINNED lowering, at
  `GoFuncSpec2` strength (the multi-result surface judgment), called on a
  concrete one-entry `mapAckIndexer`: the caller's two cells receive
  `(12, true)`. This is the first `GoFuncSpec2` discharge — the W1 arity
  widening's first instance — and it walks real Go machinery end to end:
  a two-target/two-argument call, a frame entry that allocates four cells
  at named types, a comma-ok map read, two writes at a defined type, and
  a TWO-result frame exit.
- **PROVEN, pure math**: the value the full `CommittedIndex` walk must
  land on, and its upgrade to the declarative spec.
- **NOT PROVEN, still a target**: `quorumOneKnownFuncSpec_statement` —
  the whole `committedOneKnown → run → CommittedIndex` composition. What
  it still needs beyond what now exists: an ALLOCATING wide-op apply core
  (`makeMap`/`makeSlice` allocate inside `applyStmtOp`), array-to-slice
  (`stk[:n]`), the nondeterministic map-range composition, and the
  ~200-step assembly. Each is tracked in the arc doc's build log.

The claim shape, for the record: the machine result `12` equals
`GoLean.Quorum.committedIndexRef [1] (fun v => if v = 1 then some 12
else none)` (proven by `rfl` below), and `committedIndexRef_meets_spec`
(PROVEN, `Specs/QuorumRefSpec.lean`) upgrades that to
`IsCommittedIndex` — so the ONLY missing link between the pinned real
etcd-io/raft lowering and the declarative quorum spec is the machine
walk. That is the point of stating the targets here rather than in chat.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

set_option linter.unusedSimpArgs false

namespace GoLean.Quorum

/-! ## The math half — PROVEN

These are theorems, not targets. They pin the value the machine walk must
land on and immediately upgrade it to the declarative spec. -/

/-- The one-voter instance's acked data: voter `1` reported index `12`
(the `committedOneKnown` driver's map literal). -/
def ackedOneKnown : Nat → Option Nat := fun v => if v = 1 then some 12 else none

/-- **The value the machine must produce**, from the reference — `rfl`,
so it is a computation, not a claim. -/
theorem committedIndexRef_oneKnown :
    committedIndexRef [1] ackedOneKnown = 12 := rfl

/-- **The declarative spec holds at 12** for this instance: committedness
and maximality, via the proven general agreement theorem. Together with a
machine walk landing on `12`, this is the tier-1 statement on a one-voter
config. -/
theorem isCommittedIndex_oneKnown : IsCommittedIndex [1] ackedOneKnown 12 :=
  committedIndexRef_oneKnown ▸ committedIndexRef_meets_spec [1] ackedOneKnown
    (by decide)

/-- Negative twin: `11` is NOT the committed index of this instance
(maximality fails at 12) — the guard against a spec that accepts anything
below the true value. -/
theorem not_isCommittedIndex_oneKnown_11 :
    ¬ IsCommittedIndex [1] ackedOneKnown 11 := by
  rintro (⟨h, -⟩ | ⟨-, -, hmax⟩)
  · simp at h
  · exact absurd (hmax 12 (by omega)) (by decide)

end GoLean.Quorum


namespace GoLean.Iris.GoldenQuorum

/-! ## The `AckedIndex` machine walk (quorum pilot phase 4, slice 5)

The real `main.mapAckIndexer.AckedIndex` of the pinned lowering, walked
end to end: the callsite's two targets and two arguments, the frame
entry, the body (two declarations at named types, the comma-ok read, the
two result writes, `return`), and the two-result frame exit. Every step
is one of the general laws; the only quorum-specific inputs are the pin
projections (`QuorumPin.*`, all `rfl`) and the concrete map. -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- The D1 splice (same-env governing sequence), restated locally so this
file does not depend on the golden-slice walk. -/
theorem seqCont_splice {ss rest : List Stmt} {env : LocalEnv} {k : Cont} :
    seqCont ss env (.seq rest env k) = .seq (ss ++ rest) env k := by
  simp [seqCont]

/-- **The `AckedIndex` body walk** on the CONCRETE receiver map
`{3 ↦ 12}`, under the frame environment frame entry produces. Declares
`idx : main.Index` and `ok : bool` (the named-type declaration is what
needs `wp_init`'s type-environment pin), performs the comma-ok read
(`wp_map_lookup_ackedIndex`, the witness on the REAL statement), writes
both results and returns. The parameter and map cells are dropped
affinely at the end; the two RESULT cells are handed to the continuation
holding `12` and `true`. -/
theorem wp_ackedIndex_body {ma ida mba ra₀ ra₁ : Addr} {k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int 3 .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                   .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ ra₁.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          ∗ ra₁.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.ackedIndexImpl.body
            [[("$res1", Loc.base ra₁), ("$res0", Loc.base ra₀),
              ("id", Loc.base ida), ("m", Loc.base ma)]] k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hid, Hmb, Hr0, Hr1, Hcont⟩
  rw [QuorumPin.ackedIndexImpl_body_eq]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  iintro %ta Ht
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_init (v := .bool false) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %oa Ho
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_map_lookup_ackedIndex (mba := mba) htypes rfl rfl rfl rfl)
  isplitl [Hm]
  · iexact Hm
  isplitl [Hid]
  · iexact Hid
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Ht]
  · iexact Ht
  isplitl [Ho]
  · iexact Ho
  iintro ⟨Hm, Hid, Hmb, Ht, Ho⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  -- `$res0 = idx` (a store at the DEFINED type `main.Index`)
  iapply (wp_assign_start (te := .ref "$res0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply (wp_eval_ref (loc := Loc.base ra₀) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.Index"⟩),
    .int 12 .uint64⟩) rfl)
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (fun σ ht hl => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hl ⊢
      have n12 : IntKind.uint64.normalize 12 = 12 := by rfl
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, n12, Bind.bind,
        Except.bind]))
  isplitl [Hr0]
  · iexact Hr0
  iintro Hr0
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  -- `$res1 = ok`
  iapply (wp_assign_start (te := .ref "$res1") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_eval_ref (loc := Loc.base ra₁) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply (wp_eval_var (cell := ⟨some .bool, .bool true⟩) rfl)
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  iapply (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hr1]
  · iexact Hr1
  iintro Hr1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc17
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc18
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc19
  iapply Hcont $$ [$Hr0 $Hr1]

/-- **The `AckedIndex` call walk**, end to end: two target addresses, the
receiver and the index argument, the STATIC frame entry
(`wp_call_enter_ackedIndexImpl`), the body, and the TWO-result frame exit
(`wp_frame_return₂`) that writes `12` and `true` into the caller's cells.
Generic in the caller's environment, target cells and their prior values;
the map is the concrete `{3 ↦ 12}` receiver. -/
theorem wp_ackedIndexCall {ma mba ta tb : Addr} {w₁ w₂ : GoValue} {env k}
    (hres0 : LocalEnv.lookup env "$callres0" = some (Loc.base ta))
    (hres1 : LocalEnv.lookup env "$callres1" = some (Loc.base tb))
    (hm : LocalEnv.lookup env "m" = some (Loc.base ma))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                   .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int .uint64), w₁⟩ : HeapCell)
      ∗ tb.id ↦ (⟨some .bool, w₂⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          ∗ tb.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$callres0", .var "$callres1"]
              ⟨"main.mapAckIndexer.AckedIndex"⟩
              #[.var "m", .intLit 3 .uint64]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hmb, Ht, Htb, Hcont⟩
  iapply (wp_call_first_target (te := .ref "$callres0")
    (rest := [.ref "$callres1"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply (wp_eval_ref hres0)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply (wp_call_target_next (loc := Loc.base ta) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply (wp_eval_ref hres1)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_call_targets_done_arg (loc := Loc.base tb) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
    .map ⟨some (.base mba)⟩⟩) hm)
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  simp only [List.nil_append]
  rw [show IntKind.uint64.normalize 3 = 3 from by decide]
  iapply (wp_call_enter_ackedIndexImpl (n := 3) (mba := mba) hprog hmeths htypes)
  iintro %a₀ %a₁ %a₂ %a₃ ⟨Hp0, Hp1, Hq0, Hq1⟩
  rw [show IntKind.uint64.normalize 3 = 3 from by decide] at *
  iapply (wp_ackedIndex_body htypes)
  isplitl [Hp0]
  · iexact Hp0
  isplitl [Hp1]
  · iexact Hp1
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Hq1]
  · iexact Hq1
  iintro ⟨Hq0, Hq1⟩
  simp only [List.singleton_append, List.cons_append, List.nil_append]
  iapply (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.int .uint64), w₁⟩)
    (tcell₀' := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (tcell₁ := ⟨some .bool, w₂⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ _ht hl => by
      have h := storeLoc_int_any (mkind := .uint64) hl 12
      rw [show IntKind.uint64.normalize 12 = 12 from by decide] at h
      exact h)
    (hstore₁ := fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Hq1]
  · iexact Hq1
  isplitl [Ht]
  · iexact Ht
  isplitl [Htb]
  · iexact Htb
  iintro ⟨Hq0, Hq1, Ht, Htb⟩
  iapply Hcont $$ [$Ht $Htb]

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-- **TARGET (phase 4, item 3 — NOT PROVEN).** The `GoFuncSpec` form over
the PINNED ACTUAL LOWERING of the real etcd-io/raft quorum source:
"`committedOneKnown()` takes no arguments, needs no heap, and returns
12" — ∀-quantified over the caller's target cell, its prior value, and
the frame, exactly as `recoverFuncSpec_statement`/
`goldenFuncSpec_statement`. The driver builds `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}` and calls `run → CommittedIndex`, so discharging
this walks the real interface dispatch, the real map range, the real sort
extern and the real defined-type conversions.

`12` is `committedIndexRef [1] ackedOneKnown` (`committedIndexRef_oneKnown`,
`rfl`), so discharging this target plus `committedIndexRef_meets_spec`
(PROVEN) yields `IsCommittedIndex` on this instance — the tier-1 claim.
No theorem names this def yet and no docstring may claim it is
dischargeable today. -/
def quorumOneKnownFuncSpec_statement : Prop :=
  GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
    quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
    (fun n => .pure (n = 12))

/-- **TARGET — the negative twin.** The same spec must FAIL at 11; once
the positive target is proven this is the usual two-line corollary
(`.pure` injectivity), and stating it now is what stops a trivialized
postcondition from passing for the real one. -/
def quorumOneKnownNotEleven_statement : Prop :=
  ¬ GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (n = 11))

/-- The concrete receiver the `AckedIndex` spec is stated on: a
`mapAckIndexer` cell at `ma` holding a map whose data cell at `mba` is
the single entry `3 ↦ 12` — the smallest instance that makes the comma-ok
answer non-trivial (a HIT, so the `found` result is `true` and the value
is the map's, not the zero default). -/
def ackedIndexerPre (ma mba : Nat) : HProp :=
  .sep (.pointsTo ma ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                      .map ⟨some (.base ⟨mba⟩)⟩⟩)
    (.pointsTo mba ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                    .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩)

/-- **TARGET, now PROVEN below** (`quorumAckedIndexFuncSpec2`): the
implementation method `main.mapAckIndexer.AckedIndex` of the PINNED
lowering at `GoFuncSpec2` strength — its `(Index, bool)` result pair is
the arity widening the pilot forces. Reads: *`m.AckedIndex(3)` on the
`{3 ↦ 12}` receiver, into any two caller cells (int-kind and bool, any
prior values), in any admissible heap with any frame, terminates only in
states where those cells hold `12` and `true`.*

**Statement corrected 2026-07-31 (recorded, not quietly patched).** The
phase-0 form passed `#[]` arguments to a two-parameter method: the arity
check in `enterFrame` fails closed, so the configuration is STUCK, so
`Progress` — and with it the whole statement — was FALSE, not merely
unproven; and its postcondition `b = true → n = 12` was satisfiable by a
method that never finds anything. Both are fixed here: the receiver and
index are real arguments (`GoFuncSpec2`'s new caller-environment
parameter is what makes a heap-carried receiver denotable at all), and
the postcondition pins BOTH results positively. -/
def quorumAckedIndexFuncSpec2_statement : Prop :=
  ∀ ma mba : Nat,
    GoFuncSpec2 quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"main.mapAckIndexer.AckedIndex"⟩ .uint64
      [("m", Loc.base ⟨ma⟩)] #[.var "m", .intLit 3 .uint64]
      (ackedIndexerPre ma mba)
      (fun n b => .pure (n = 12 ∧ b = true))


/-! ### Non-vacuity of the discharge

A `GoSpec` quantifies over *admissible* initial states (`InitialSplit`).
If no state were admissible the judgment would be true of anything — the
vacuity class the project's gate exists to catch. The lemmas below
exhibit one: a concrete four-cell heaplet satisfying the discharged
precondition at distinct addresses. (`goldenReturnsTwo` plays the same
role for the unary golden spec, by reading a concrete run out of it.) -/

/-! The three `Heaplet` facts these need, stated over the bridge's
`PartialMap` API (the surface's `ExtTreeMap` operations ARE the bridge's,
`SurfaceBridge.heaplet_get?_eq`/`heaplet_insert_eq`). -/

theorem heaplet_get?_empty {k : Nat} : (∅ : Heaplet).get? k = none := by
  rw [heaplet_get?_eq]
  exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)

theorem heaplet_get?_insert_self {m : Heaplet} {k : Nat} {v : HeapCell} :
    (m.insert k v).get? k = some v := by
  rw [heaplet_get?_eq, heaplet_insert_eq]
  exact LawfulPartialMap.get?_insert_eq rfl

theorem heaplet_get?_insert_ne {m : Heaplet} {k k' : Nat} {v : HeapCell}
    (h : k ≠ k') : (m.insert k v).get? k' = m.get? k' := by
  rw [heaplet_get?_eq, heaplet_insert_eq, heaplet_get?_eq]
  exact get?_insert_ne h

/-- Prepending a FRESH cell to a satisfying heaplet satisfies the
separating conjunction with that cell's points-to. General — no program,
no address, no assertion fixed. -/
theorem sat_sep_insert {h : Heaplet} {ℓ : Nat} {c : HeapCell} {P : HProp}
    (hfresh : h.get? ℓ = none) (hP : sat h P) :
    sat (h.insert ℓ c) (.sep (.pointsTo ℓ c) P) := by
  refine ⟨(∅ : Heaplet).insert ℓ c, h, rfl, hP, ?_, ?_⟩
  · intro k
    by_cases hk : k = ℓ
    · exact Or.inr (hk ▸ hfresh)
    · exact Or.inl (by
        rw [heaplet_get?_insert_ne (fun he => hk he.symm), heaplet_get?_empty])
  · intro k c'
    by_cases hk : k = ℓ
    · subst hk
      rw [heaplet_get?_insert_self, heaplet_get?_insert_self, hfresh]
      simp
    · rw [heaplet_get?_insert_ne (fun he => hk he.symm),
        heaplet_get?_insert_ne (fun he => hk he.symm), heaplet_get?_empty]
      simp

/-- **The discharged precondition is satisfiable** (at `ra = 0`,
`rb = 1`, `ma = 2`, `mba = 3`, and ANY prior target values): the
`quorumAckedIndexFuncSpec2` statement speaks about states that exist, so
its `∀`-over-admissible-states is not vacuous. -/
theorem quorumAckedIndexPre_satisfiable (w₁ w₂ : GoValue) :
    ∃ h : Heaplet, sat h
      (.sep (.pointsTo 0 ⟨some (.int .uint64), w₁⟩)
        (.sep (.pointsTo 1 ⟨some .bool, w₂⟩) (ackedIndexerPre 2 3))) := by
  refine ⟨((((∅ : Heaplet).insert 3
      ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
       .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩).insert 2
      ⟨some (.defined ⟨"main.mapAckIndexer"⟩), .map ⟨some (.base ⟨3⟩)⟩⟩).insert 1
      ⟨some .bool, w₂⟩).insert 0 ⟨some (.int .uint64), w₁⟩, ?_⟩
  refine sat_sep_insert ?_ (sat_sep_insert ?_ (sat_sep_insert ?_ rfl))
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_insert_ne (by omega),
      heaplet_get?_insert_ne (by omega), heaplet_get?_empty]
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_insert_ne (by omega),
      heaplet_get?_empty]
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_empty]

/-- **THE DISCHARGE — the first `GoFuncSpec2` result** (quorum pilot
phase 4, slice 5). The per-program obligation is exactly the WP proof
(`wp_ackedIndexCall`), as for every surface discharge; the exit pipe
(`goSpec_of_wp`) supplies the frame closure and progress. What this
proves about REAL Go: a method called on a concrete receiver, its
`(T, bool)` comma-ok result pair delivered to the caller's cells by the
machine's own frame-exit protocol, over the frontend's actual lowering of
etcd-io/raft's `quorum` package. -/
theorem quorumAckedIndexFuncSpec2 : quorumAckedIndexFuncSpec2_statement := by
  unfold quorumAckedIndexFuncSpec2_statement GoFuncSpec2 ackedIndexerPre
  intro ma mba ra rb w₁ w₂ _hne
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨Hta, Htb, Hm, Hmb⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_ackedIndexCall (ma := ⟨ma⟩) (mba := ⟨mba⟩)
    (ta := ⟨ra⟩) (tb := ⟨rb⟩) (w₁ := w₁) (w₂ := w₂) rfl rfl rfl
    hprog hmeths htypes)
  isplitl [Hm]
  · iexact Hm
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Hta]
  · iexact Hta
  isplitl [Htb]
  · iexact Htb
  iintro ⟨Hta, Htb⟩
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  iexists true
  isplitl [Hta]
  · iexact Hta
  isplitl [Htb]
  · iexact Htb
  · ipureintro
    exact ⟨rfl, rfl⟩

end GoLean.Surface
