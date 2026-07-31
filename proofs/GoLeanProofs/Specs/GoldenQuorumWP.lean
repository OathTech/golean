import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.QuorumOps
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Specs.QuorumRefSpec

/-!
# The quorum walk — the FIRST machine discharge, and the math link
(quorum pilot phase 4, 2026-07-31)

Honest status, stated once and not softened anywhere below:

- **PROVEN, THE ARC'S NAMED GOAL (2026-07-31, the summit slice)**:
  `quorumOneKnownFuncSpec` — the pinned lowering of the REAL etcd-io/raft
  quorum driver, `committedOneKnown()`, returns `12` at `GoFuncSpec`
  strength; and `quorumOneKnownMeetsSpec` restates that with the
  DECLARATIVE quorum spec as the postcondition (`IsCommittedIndex [1]
  ackedOneKnown`). The walk goes through the real `run`,
  `main.MajorityConfig.CommittedIndex` and `main.mapAckIndexer.AckedIndex`
  — two `make(map…)`s that allocate inside the apply step, a map length
  read, the on-stack `[7]uint64` scratch array and its reslice, the
  nondeterministic map range, interface dispatch, comma-ok, a store
  through a slice index, `slices.Sort`, and the `n - (n/2+1)` readout.
  **Scope: n = 1** — the range's nondeterminism is degenerate and the
  fit test takes the reslice branch; the three-voter widening is
  recorded in the arc doc.
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
- **NOT PROVEN, and recorded as such**: the phase-0
  `quorumOneKnownNotEleven_statement` — the UNCONDITIONAL
  `¬ GoFuncSpec … (n = 11)`. It is not refutable from the triple: a
  `GoTriple` is vacuously true of a program that fails to terminate, so
  refuting it demands EXHIBITING a terminating run (a kernel evaluation
  of the interpreter over the whole pinned program). The run-conditioned
  twin `quorumOneKnownNotEleven` — the golden precedent's shape
  (`goldenNotThree`) — is proven below instead.

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
theorem wp_ackedIndex_body {ma ida mba ra₀ ra₁ : Addr} {mty : Option Ty}
    {q v : Int} {k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ ra₁.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
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
  iapply (wp_map_lookup_ackedIndex (mba := mba) (mty := mty) (q := q) (v := v)
    htypes hq hv rfl rfl rfl rfl)
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
    .int v .uint64⟩) rfl)
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (fun σ ht hl => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hl ⊢
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, hv, Bind.bind,
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
theorem wp_ackedIndexCall {ma mba ta tb : Addr} {mty : Option Ty} {q v : Int}
    {w₁ w₂ : GoValue} {env k}
    (hres0 : LocalEnv.lookup env "$callres0" = some (Loc.base ta))
    (hres1 : LocalEnv.lookup env "$callres1" = some (Loc.base tb))
    (hm : LocalEnv.lookup env "m" = some (Loc.base ma))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int .uint64), w₁⟩ : HeapCell)
      ∗ tb.id ↦ (⟨some .bool, w₂⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int v .uint64⟩ : HeapCell)
          ∗ tb.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$callres0", .var "$callres1"]
              ⟨"main.mapAckIndexer.AckedIndex"⟩
              #[.var "m", .intLit q .uint64]) env k) @ s ; E {{ Φ }} := by
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
  rw [hq]
  iapply (wp_call_enter_ackedIndexImpl (n := q) (mba := mba) hprog hmeths htypes)
  iintro %a₀ %a₁ %a₂ %a₃ ⟨Hp0, Hp1, Hq0, Hq1⟩
  rw [hq]
  iapply (wp_ackedIndex_body (mty := mty) (q := q) (v := v) htypes hq hv)
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
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.int .uint64), w₁⟩)
    (tcell₀' := ⟨some (.int .uint64), .int v .uint64⟩)
    (tcell₁ := ⟨some .bool, w₂⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ _ht hl => by
      have h := storeLoc_int_any (mkind := .uint64) hl v
      rw [hv] at h
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


/-! ## THE SUMMIT WALK: `main.MajorityConfig.CommittedIndex` at n = 1
(quorum pilot phase 4, the summit slice)

The real etcd-io/raft `CommittedIndex`, walked over the PINNED lowering on
a one-voter config. Each theorem below covers one statement (or one
statement group) of the body and is generic in the surrounding
environment, the continuation and the addresses; the composition
`wp_committedIndex_body` chains them. -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin

/-- `n := len(c)` — the declaration, the map-length read (a state-READING
strict op on the config's data cell) and the store. Generic in the config
map's contents: `n` is its entry count. -/
theorem wp_ci_len {ca cba : Addr} {cty : Option Ty}
    {entries : Array (GoValue × GoValue)} {rest env k}
    (hsize : IntKind.int.normalize (Int.ofNat entries.size)
      = Int.ofNat entries.size)
    (hc : LocalEnv.lookup env "c" = some (.base ca)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData entries⟩ : HeapCell)
      ∗ iprop(∀ na : Addr,
          ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                    .map ⟨some (.base cba)⟩⟩ : HeapCell)
            ∗ cba.id ↦ (⟨cty, .mapData entries⟩ : HeapCell)
            ∗ na.id ↦ (⟨some (.int .int),
                        .int (Int.ofNat entries.size) .int⟩ : HeapCell) -∗
          WP (Config.next (.seq rest (env.declare "n" (.base na)) k))
            @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLenStmt env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hcont⟩
  rw [ciLenStmt_eq]
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply wp_init_int
  iintro %na Hn
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply (wp_assign_start (te := .ref "n") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_eval_ref (loc := Loc.base na) lookup_declare_self)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_eval_strict (op := .lengthOf (some (.defined ⟨"main.MajorityConfig"⟩)))
    (e₁ := .var "c") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.MajorityConfig"⟩),
    .map ⟨some (.base cba)⟩⟩)
    ((lookup_declare_ne (by decide)).trans hc))
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply (wp_strict_apply_read (a := cba) (cell := ⟨cty, .mapData entries⟩)
    (out := .int (Int.ofNat entries.size) .int)
    (happly := fun σ _ht hl => by
      simp [applyStrictOp, loadLoc, hl, Bind.bind, Except.bind]))
  isplitl [Hcb]
  · iexact Hcb
  iintro Hcb
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (Int.ofNat entries.size) .int⟩)
    (fun σ _ht hl => by
      have h := storeLoc_int_any (mkind := .int) hl (Int.ofNat entries.size)
      rw [hsize] at h
      simpa using h))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply Hcont $$ %na [$Hc $Hcb $Hn]

/-- `if n == 0 { return math.MaxUint64 }` — the empty-config early
return, on the NOT-taken branch. Generic in `n`; the premise is the
machine's own comparison, which at any nonzero `n` is `false`. -/
theorem wp_ci_emptyIf {na : Addr} {n : Int} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hcmp : ∀ σ : ExecState,
      applyStrictOp σ (.eqCmp (.int .int)) [.int n .int, .int 0 .int]
        = .ok (.bool false, σ)) :
    na.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell) -∗
          WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciEmptyIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hcont⟩
  rw [ciEmptyIf_eq]
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He1
  iapply (wp_eval_strict (op := .eqCmp (.int .int)) (e₁ := .var "n")
    (rest := [.intLit 0 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He2
  iapply (wp_eval_var (cell := ⟨some (.int .int), .int n .int⟩) hn)
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He3
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He4
  rw [show IntKind.int.normalize 0 = 0 from by decide]
  iapply (wp_strict_apply_pure (out := .bool false) hcmp)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He5
  iapply wp_if_bool
  simp only [Bool.false_eq_true, if_false]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He6
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro He7
  iapply Hcont $$ Hn

/-- `var stk [7]uint64` — the on-stack scratch declaration. Zero
premises: the array default is state-independent. -/
theorem wp_ci_stkDecl {rest env k} :
    iprop(∀ sta : Addr, sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare "stk" (.base sta)) k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciStkDecl env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro Hcont
  rw [ciStkDecl_eq]
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hs1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hs2
  iapply (wp_init (v := stkZero) (hdef := fun σ _ => defaultValue_stk σ))
  iexact Hcont

/-- `var srt []uint64` — the result slice declaration (nil slice). -/
theorem wp_ci_srtDecl {rest env k} :
    iprop(∀ sra : Addr,
        sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨none, 0, 0, 0⟩⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare "srt" (.base sra)) k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciSrtDecl env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro Hcont
  rw [ciSrtDecl_eq]
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hs1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hs2
  iapply (wp_init (v := .slice ⟨none, 0, 0, 0⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iexact Hcont

/-- `if len(stk) >= n { srt = stk[:n] }` at `n = 1` — the TAKEN branch:
the on-stack array is resliced, so no allocation happens (the
`make([]uint64, n)` else-branch is the widening's other side). `stk[:n]`
is a state-READING strict op: it loads the array to learn its size, which
becomes the resulting slice's capacity (7). -/
theorem wp_ci_fitIf_one {na sta sra : Addr} {w : GoValue} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hstk : LocalEnv.lookup env "stk" = some (.base sta))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)), w⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          -∗ WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciFitIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hstk, Hsrt, Hcont⟩
  rw [ciFitIf_eq]
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf1
  iapply (wp_eval_strict (op := .atLeastCmp) (e₁ := .intLit 7 .int)
    (rest := [.var "n"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf2
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf3
  rw [show IntKind.int.normalize 7 = 7 from by decide]
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf4
  iapply (wp_eval_var (cell := ⟨some (.int .int), .int 1 .int⟩) hn)
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply (wp_strict_apply_pure (out := .bool true) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf5
  iapply wp_if_bool
  simp only [reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf6
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf7
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf8
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf9
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf10
  iapply (wp_assign_start (te := .ref "srt") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf11
  iapply (wp_eval_ref (loc := Loc.base sra) (lookup_pushScope.trans hsrt))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf12
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf13
  iapply (wp_eval_strict (op := .sliceExpr false) (e₁ := .ref "stk")
    (rest := [.intLit 0 .int, .var "n"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf14
  iapply (wp_eval_ref (loc := Loc.base sta) (lookup_pushScope.trans hstk))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf15
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf16
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf17
  rw [show IntKind.int.normalize 0 = 0 from by decide]
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf18
  iapply (wp_eval_var (cell := ⟨some (.int .int), .int 1 .int⟩)
    (lookup_pushScope.trans hn))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply (wp_strict_apply_read (a := sta) (cell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
    (out := .slice ⟨some (.base sta), 0, 1, 7⟩)
    (happly := fun σ _ht hl => by
      simp [applyStrictOp, applySlice, loadLoc, hl, stkZero, valueAsInt,
        sliceFromArray, checkSliceBounds, Bind.bind, Except.bind]))
  isplitl [Hstk]
  · iexact Hstk
  iintro Hstk
  iapply (wp_assign_store
    (oldcell := ⟨some (.slice (.int .uint64)), w⟩)
    (newcell := ⟨some (.slice (.int .uint64)),
                 .slice ⟨some (.base sta), 0, 1, 7⟩⟩)
    (fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hsrt]
  · iexact Hsrt
  iintro Hsrt
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hf19
  iapply Hcont $$ [$Hn $Hstk $Hsrt]

/-- **The voter loop at ONE entry** — `for id := range c { if idx, ok :=
l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- } }`. This is the walk's
semantic centre: the nondeterministic map range (degenerate at one
entry — the choice quantifier is discharged by `i < 1`), the real
INTERFACE dispatch through the `main.AckedIndexer.AckedIndex` anchor into
`main.mapAckIndexer.AckedIndex`, the comma-ok read inside it, the
two-result frame exit, and the store THROUGH A SLICE INDEX into the
on-stack backing array. -/
theorem wp_ci_loop_one {na ca cba la lba sra sta : Addr}
    {cty lty : Option Ty} {rest env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                  .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                      .map ⟨some (.base cba)⟩⟩ : HeapCell)
          ∗ cba.id ↦ (⟨cty, .mapData
              #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
          ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                      .interface (.defined ⟨"main.mapAckIndexer"⟩)
                        (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell)
          -∗ WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLoopBlock env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hc, Hcb, Hl, Hlb, Hsr, Hst, Hcont⟩
  rw [ciLoopBlock_eq]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl2
  unfold ciIDecl
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl4
  iapply wp_init_int
  iintro %ia Hi
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl5
  -- `i = n - 1`
  iapply (wp_assign_start (te := .ref "i") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl6
  iapply (wp_eval_ref (loc := Loc.base ia) lookup_declare_self)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl7
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl8
  iapply (wp_eval_strict (op := .sub) (e₁ := .var "n")
    (rest := [.intLit 1 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl9
  iapply (wp_eval_var (a := na) (cell := ⟨some (.int .int), .int 1 .int⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup, hn]))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl10
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl11
  rw [show IntKind.int.normalize 1 = 1 from by decide]
  iapply (wp_strict_apply_pure (out := .int 0 .int) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl12
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 0 .int⟩)
    (fun σ _ht hl' => by
      have h := storeLoc_int_any (mkind := .int) hl' 0
      rw [show IntKind.int.normalize 0 = 0 from by decide] at h
      exact h))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl13
  -- the range itself
  rw [rangeStmt_eq]
  iapply wp_map_range_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hl14
  iapply (wp_eval_var (a := ca) (cell := ⟨some (.defined ⟨"main.MajorityConfig"⟩),
    .map ⟨some (.base cba)⟩⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup, hc]))
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply (wp_map_range_snapshot (ba := cba) (mty := cty)
    (entries := #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]))
  isplitl [Hcb]
  · iexact Hcb
  iintro Hcb
  iapply (wp_map_iter_next_key (hne := by decide)
    (hnorm := fun σ i h => by
      have hi : i = 0 := Nat.lt_one_iff.mp (by simpa using h)
      subst hi
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        show IntKind.uint64.normalize 1 = 1 from by decide]))
  iintro %i %hi %pa Hid
  have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
  subst hi0
  have herase : (#[((GoValue.int 1 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[]))]
      : Array (GoValue × GoValue)).eraseIdx 0 hi = #[] := by
    simp
  simp only [herase, List.getElem_toArray, List.getElem_cons_zero]
  -- the body
  rw [rangeBody_eq]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb2
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb4
  unfold ciCallSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb5
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb6
  iapply (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  iintro %idxa Hidx
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb7
  iapply (wp_init (v := .bool false) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %oka Hok
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb8
  -- `idx, ok = l.AckedIndex(id)` — the interface call
  iapply (wp_call_first_target (te := .ref "idx") (rest := [.ref "ok"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb9
  iapply (wp_eval_ref (loc := Loc.base idxa)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb10
  iapply (wp_call_target_next (loc := Loc.base idxa) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb11
  iapply (wp_eval_ref (loc := Loc.base oka) lookup_declare_self)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb12
  iapply (wp_call_targets_done_arg (loc := Loc.base oka) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb13
  iapply (wp_eval_var (a := la) (cell := ⟨some (.interface ⟨"main.AckedIndexer"⟩),
    .interface (.defined ⟨"main.mapAckIndexer"⟩) (.map ⟨some (.base lba)⟩)⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup, hl]))
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb14
  iapply (wp_eval_var (a := pa) (cell := ⟨some (.int .uint64), .int 1 .uint64⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  isplitl [Hid]
  · iexact Hid
  iintro Hid
  simp only [List.nil_append, List.singleton_append, List.cons_append]
  iapply (wp_call_dynamic_enter_ackedIndex (n := 1) (mba := lba)
    hprog hmeths htypes)
  iintro %a₀ %a₁ %a₂ %a₃ ⟨Hp0, Hp1, Hq0, Hq1⟩
  rw [show IntKind.uint64.normalize 1 = 1 from by decide]
  iapply (wp_ackedIndex_body (mty := lty) (q := 1) (v := 12) htypes
    (by decide) (by decide))
  isplitl [Hp0]
  · iexact Hp0
  isplitl [Hp1]
  · iexact Hp1
  isplitl [Hlb]
  · iexact Hlb
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Hq1]
  · iexact Hq1
  iintro ⟨Hq0, Hq1⟩
  iapply (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell₀' := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (tcell₁ := ⟨some .bool, .bool false⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide])
    (hstore₁ := fun σ _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Hq1]
  · iexact Hq1
  isplitl [Hidx]
  · iexact Hidx
  isplitl [Hok]
  · iexact Hok
  iintro ⟨Hq0, Hq1, Hidx, Hok⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb15
  -- `if ok { srt[i] = uint64(idx); i-- }`
  unfold ciOkIf
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb16
  iapply (wp_eval_var (cell := ⟨some .bool, .bool true⟩) lookup_declare_self)
  isplitl [Hok]
  · iexact Hok
  iintro Hok
  iapply wp_if_bool
  simp only [reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb17
  unfold ciOkThen
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb18
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb19
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb20
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb21
  -- `srt[i] = uint64(idx)`
  iapply (wp_assign_start (te := .indexAddr (.var "srt") (.var "i")) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb22
  iapply (wp_eval_strict (op := .indexAddr) (e₁ := .var "srt")
    (rest := [.var "i"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb23
  iapply (wp_eval_var (a := sra) (cell := ⟨some (.slice (.int .uint64)),
    .slice ⟨some (.base sta), 0, 1, 7⟩⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup, hsrt]))
  isplitl [Hsr]
  · iexact Hsr
  iintro Hsr
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb24
  iapply (wp_eval_var (a := ia) (cell := ⟨some (.int .int), .int 0 .int⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  iapply (wp_strict_apply_pure (out := .addr (.index (.base sta) 0))
    (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb25
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb26
  iapply (wp_eval_strict (op := .convert (.int .uint64)) (e₁ := .var "idx")
    (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb27
  iapply (wp_eval_var (a := idxa) (cell := ⟨some (.defined ⟨"main.Index"⟩),
    .int 12 .uint64⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  isplitl [Hidx]
  · iexact Hidx
  iintro Hidx
  iapply (wp_strict_apply_pure (out := .int 12 .uint64) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb28
  iapply (wp_assign_store_loc (a := sta)
    (oldcell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
    (newcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (fun σ _ht hlk => by
      simp [storeLoc, loadLoc, hlk, stkZero, stkOne, arrayIndexNat, arraySet,
        coerceStoredValue, normalizeValueForTy, normalizeValueForTyFuel,
        normalizeArrayForTy, Bind.bind, Except.bind, Functor.map, Except.map,
        show IntKind.uint64.normalize 12 = 12 from by decide,
        show IntKind.uint64.normalize 0 = 0 from by decide]))
  isplitl [Hst]
  · iexact Hst
  iintro Hst
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb29
  -- `i--`
  iapply (wp_assign_start (te := .ref "i") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb30
  iapply (wp_eval_ref (loc := Loc.base ia)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb31
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb32
  iapply (wp_eval_strict (op := .sub) (e₁ := .var "i")
    (rest := [.intLit 1 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb33
  iapply (wp_eval_var (a := ia) (cell := ⟨some (.int .int), .int 0 .int⟩)
    (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope, Scope.lookup]))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb34
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb35
  rw [show IntKind.int.normalize 1 = 1 from by decide]
  iapply (wp_strict_apply_pure (out := .int (-1) .int) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb36
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (-1) .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk (-1)
      rw [show IntKind.int.normalize (-1) = -1 from by decide] at h
      exact h))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  -- unwind the two pushed scopes of the `if` body, the two of the range body
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb37
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb38
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb39
  iapply wp_map_iter_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb41
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hb42
  iapply Hcont $$ [$Hn $Hc $Hcb $Hl $Hsr $Hst]

/-- **The tail** — `slices.Sort(srt)`, `pos := n - (n/2+1)`,
`return Index(srt[pos])`. At `n = 1` the sort is over a one-element
window (so the backing array is unchanged, but the machine still performs
the write-back), `pos` is `1 - (0 + 1) = 0`, and `srt[0]` is the acked
index — Go's `n/2+1`-th largest, read out of the on-stack array. -/
theorem wp_ci_tail_one {na sra sta ra : Addr} {env k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hres : LocalEnv.lookup env "$res0" = some (.base ra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec sortStmt env
            (.seq [ciPosStmt, ciResStmt] env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hsr, Hst, Hr, Hcont⟩
  -- `slices.Sort(srt)`
  rw [sortStmt_eq]
  iapply (wp_stmt_op_first (op := .sortSlice (.int .uint64)) (nt := 0)
    (e := .var "srt") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht1
  iapply (wp_eval_var (a := sra) (cell := ⟨some (.slice (.int .uint64)),
    .slice ⟨some (.base sta), 0, 1, 7⟩⟩) hsrt)
  isplitl [Hsr]
  · iexact Hsr
  iintro Hsr
  iapply (wp_sort_slice (a := sta)
    (oldcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (newcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (happly := by
      intro σ ch _ht hlk
      simp [applyStmtOp, valueAsSlice, validateSlice, sliceIndexLoc, loadLoc,
        hlk, stkOne, heap_lookup_set_base_self, Bind.bind, Except.bind,
        List.range', List.forIn_cons, List.forIn_nil, arrayGet, arrayIndexNat,
        storeLoc, arraySet, coerceStoredValue, normalizeValueForTy,
        normalizeValueForTyFuel, normalizeArrayForTy, List.mergeSort,
        heap_set_set_of_lookup hlk, Functor.map, Except.map,
        show IntKind.uint64.normalize 12 = 12 from by decide,
        show IntKind.uint64.normalize 0 = 0 from by decide]))
  isplitl [Hst]
  · iexact Hst
  iintro Hst
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht2
  -- `pos := n - (n/2 + 1)`
  rw [ciPosStmt_eq]
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht4
  iapply wp_init_int
  iintro %pa Hp
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht5
  iapply (wp_assign_start (te := .ref "pos") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht6
  iapply (wp_eval_ref (loc := Loc.base pa) lookup_declare_self)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht7
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht8
  iapply (wp_eval_strict (op := .sub) (e₁ := .var "n")
    (rest := [.add (.div (.var "n") (.intLit 2 .int)) (.intLit 1 .int)]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht9
  iapply (wp_eval_var (a := na) (cell := ⟨some (.int .int), .int 1 .int⟩)
    ((lookup_declare_ne (by decide)).trans hn))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht10
  iapply (wp_eval_strict (op := .add) (e₁ := .div (.var "n") (.intLit 2 .int))
    (rest := [.intLit 1 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht11
  iapply (wp_eval_strict (op := .div) (e₁ := .var "n")
    (rest := [.intLit 2 .int]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht12
  iapply (wp_eval_var (a := na) (cell := ⟨some (.int .int), .int 1 .int⟩)
    ((lookup_declare_ne (by decide)).trans hn))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht13
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht14
  rw [show IntKind.int.normalize 2 = 2 from by decide]
  iapply (wp_strict_apply_pure (out := .int 0 .int) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht15
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht16
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht17
  rw [show IntKind.int.normalize 1 = 1 from by decide]
  iapply (wp_strict_apply_pure (out := .int 1 .int) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht18
  iapply (wp_strict_apply_pure (out := .int 0 .int) (fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht19
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 0 .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk 0
      rw [show IntKind.int.normalize 0 = 0 from by decide] at h
      exact h))
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht20
  -- `return Index(srt[pos])`
  rw [ciResStmt_eq]
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht21
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht22
  iapply (wp_assign_start (te := .ref "$res0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht23
  iapply (wp_eval_ref (loc := Loc.base ra)
    ((lookup_declare_ne (by decide)).trans hres))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht24
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht25
  iapply (wp_eval_strict (op := .convert (.defined ⟨"main.Index"⟩))
    (e₁ := .indexGet (.var "srt") (.var "pos")) (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht26
  iapply (wp_eval_strict (op := .indexGet) (e₁ := .var "srt")
    (rest := [.var "pos"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht27
  iapply (wp_eval_var (a := sra) (cell := ⟨some (.slice (.int .uint64)),
    .slice ⟨some (.base sta), 0, 1, 7⟩⟩)
    ((lookup_declare_ne (by decide)).trans hsrt))
  isplitl [Hsr]
  · iexact Hsr
  iintro Hsr
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht28
  iapply (wp_eval_var (a := pa) (cell := ⟨some (.int .int), .int 0 .int⟩)
    lookup_declare_self)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_strict_apply_read (a := sta)
    (cell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (out := .int 12 .uint64)
    (happly := fun σ _ht hlk => by
      simp [applyStrictOp, valueAsInt, sliceIndexLoc, validateSlice, loadLoc,
        hlk, stkOne, arrayGet, arrayIndexNat, Bind.bind, Except.bind]))
  isplitl [Hst]
  · iexact Hst
  iintro Hst
  iapply (wp_strict_apply_pin (out := .int 12 .uint64)
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, convertValueToTy, convertValueToTyFuel,
        typeResolutionFuel, resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  iapply (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht29
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht30
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Ht31
  iapply Hcont $$ Hr

/-- **THE `CommittedIndex` BODY WALK** — the real
`main.MajorityConfig.CommittedIndex` of the pinned etcd-io/raft lowering,
executed end to end on the one-voter instance `MajorityConfig{1:{}}` with
`mapAckIndexer{1:12}`, under the frame environment frame entry produces.
Every statement of `majority.go`'s algorithm is walked: `n := len(c)`,
the empty-config early return (not taken), the on-stack `[7]uint64`
scratch array, the `len(stk) >= n` reslice, the voter range with its
interface dispatch and comma-ok, `slices.Sort`, `pos := n - (n/2+1)` and
the `Index(srt[pos])` readout. It leaves `12` in the result cell —
`GoLean.Quorum.committedIndexRef [1] ackedOneKnown`. -/
theorem wp_committedIndex_body {ca cba la lba ra : Addr}
    {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec committedIndexImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [committedIndexImpl_body_eq]
  iapply wp_block_nil
  simp only [committedIndexStmts_toList]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz2
  iapply (wp_ci_len (cba := cba) (cty := cty)
    (entries := #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]) (by decide) rfl)
  isplitl [Hc]
  · iexact Hc
  isplitl [Hcb]
  · iexact Hcb
  iintro %na ⟨Hc, Hcb, Hn⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz3
  iapply (wp_ci_emptyIf (na := na) (n := 1) rfl
    (fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz4
  iapply wp_ci_stkDecl
  iintro %sta Hst
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz5
  iapply wp_ci_srtDecl
  iintro %sra Hsr
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz6
  iapply (wp_ci_fitIf_one (na := na) (sta := sta) (sra := sra) rfl rfl rfl)
  isplitl [Hn]
  · iexact Hn
  isplitl [Hst]
  · iexact Hst
  isplitl [Hsr]
  · iexact Hsr
  iintro ⟨Hn, Hst, Hsr⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz7
  iapply (wp_ci_loop_one (na := na) (ca := ca) (cba := cba) (la := la)
    (lba := lba) (sra := sra) (sta := sta) (cty := cty) (lty := lty)
    hprog hmeths htypes rfl rfl rfl rfl)
  isplitl [Hn]
  · iexact Hn
  isplitl [Hc]
  · iexact Hc
  isplitl [Hcb]
  · iexact Hcb
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlb]
  · iexact Hlb
  isplitl [Hsr]
  · iexact Hsr
  isplitl [Hst]
  · iexact Hst
  iintro ⟨Hn, Hc, Hcb, Hl, Hsr, Hst⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hz8
  iapply (wp_ci_tail_one (na := na) (sra := sra) (sta := sta) (ra := ra) htypes
    rfl rfl rfl)
  isplitl [Hn]
  · iexact Hn
  isplitl [Hsr]
  · iexact Hsr
  isplitl [Hst]
  · iexact Hst
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply Hcont $$ Hr

/-- **The `CommittedIndex` callsite** inside `run` — the STATIC frame
entry into a method on a concrete receiver, with the second argument BOXED
at the callsite (`.toInterface`: `mapAckIndexer` values become
`AckedIndexer` interface values, the boxing the later dynamic dispatch
unboxes), the body walk, and the one-result frame exit at a NAMED result
type. -/
theorem wp_committedIndexCall {ca cba la lba ta : Addr} {cty lty : Option Ty}
    {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hres : LocalEnv.lookup env "$c3" = some (.base ta))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$c3"] ⟨"main.MajorityConfig.CommittedIndex"⟩
              #[.var "c",
                .toInterface (.interface ⟨"main.AckedIndexer"⟩)
                  (.defined ⟨"main.mapAckIndexer"⟩) (.var "l")]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Ht, Hcont⟩
  iapply (wp_call_first_target (te := .ref "$c3") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hv1
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hv2
  iapply (wp_call_targets_done_arg (loc := Loc.base ta) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hv3
  iapply (wp_eval_var (a := ca) (cell := ⟨some (.defined ⟨"main.MajorityConfig"⟩),
    .map ⟨some (.base cba)⟩⟩) hc)
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hv4
  iapply (wp_eval_strict
    (op := .toInterface (.interface ⟨"main.AckedIndexer"⟩)
      (.defined ⟨"main.mapAckIndexer"⟩))
    (e₁ := .var "l") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hv5
  iapply (wp_eval_var (a := la) (cell := ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
    .map ⟨some (.base lba)⟩⟩) hl)
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  iapply (wp_strict_apply_pin
    (out := .interface (.defined ⟨"main.mapAckIndexer"⟩)
      (.map ⟨some (.base lba)⟩))
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, canonicalDynamicTy, canonicalTy, canonicalTyFuel,
        resolveDefinedAliases, resolveDefinedAliasesFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer, Ty.mentionsUnsupported,
        Bind.bind, Except.bind]))
  simp only [List.nil_append, List.singleton_append, List.cons_append]
  iapply (wp_call_enter₂₁ (func := QuorumPin.committedIndexImpl)
    (w₀ := .map ⟨some (.base cba)⟩)
    (w₁ := .interface (.defined ⟨"main.mapAckIndexer"⟩)
      (.map ⟨some (.base lba)⟩))
    (dv₀ := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.committedIndexImpl_find)
    (hargs := QuorumPin.committedIndexImpl_args)
    (hres := QuorumPin.committedIndexImpl_results)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?,
        methodRecvInterfaceName?, resolveDefinedAliases,
        resolveDefinedAliasesFuel, QuorumPin.quorumMethods_eq,
        QuorumPin.typeEnv_MajorityConfig, Bind.bind, Except.bind]
      split <;> rfl)
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_MajorityConfig])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index]))
  iintro %a₀ %a₁ %a₂ ⟨Hp0, Hp1, Hq0⟩
  iapply (wp_committedIndex_body (ca := a₀) (cba := cba) (la := a₁) (lba := lba)
    (ra := a₂) (cty := cty) (lty := lty) hprog hmeths htypes)
  isplitl [Hp0]
  · iexact Hp0
  isplitl [Hcb]
  · iexact Hcb
  isplitl [Hp1]
  · iexact Hp1
  isplitl [Hlb]
  · iexact Hlb
  isplitl [Hq0]
  · iexact Hq0
  iintro Hq0
  iapply (wp_frame_return₁ (ta := ta) (ra := a₂)
    (rcell := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (tcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell' := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (hstore := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Ht]
  · iexact Ht
  iintro ⟨Hq0, Ht⟩
  iapply Hcont $$ Ht

/-- **`run`'s body** — the thin wrapper the corpus driver calls: declare
`$c3 : main.Index`, call `c.CommittedIndex(l)`, convert the named result
back to `uint64` and return it. -/
theorem wp_run_body {ca cba la lba ra : Addr} {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec runImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [runImpl_body_eq]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr2
  unfold runCallSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr4
  iapply (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  iintro %c3a Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr5
  iapply (wp_committedIndexCall (ca := ca) (cba := cba) (la := la) (lba := lba)
    (ta := c3a) (cty := cty) (lty := lty) hprog hmeths htypes rfl rfl rfl)
  isplitl [Hc]
  · iexact Hc
  isplitl [Hcb]
  · iexact Hcb
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlb]
  · iexact Hlb
  isplitl [Hc3]
  · iexact Hc3
  iintro Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr6
  unfold runResSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr7
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr8
  iapply (wp_assign_start (te := .ref "$res0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr9
  iapply (wp_eval_ref (loc := Loc.base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr10
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr11
  iapply (wp_eval_strict (op := .convert (.int .uint64)) (e₁ := .var "$c3")
    (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr12
  iapply (wp_eval_var (a := c3a) (cell := ⟨some (.defined ⟨"main.Index"⟩),
    .int 12 .uint64⟩) rfl)
  isplitl [Hc3]
  · iexact Hc3
  iintro Hc3
  iapply (wp_strict_apply_pin (out := .int 12 .uint64)
    (happly := fun σ _ht => by
      simp [applyStrictOp, convertValueToTy, convertValueToTyFuel,
        typeResolutionFuel, resolveDefinedAliases, resolveDefinedAliasesFuel,
        Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 12
      rw [show IntKind.uint64.normalize 12 = 12 from by decide] at h
      exact h))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr13
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr14
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hr15
  iapply Hcont $$ Hr

/-- **The driver body** — `committedOneKnown`: build `MajorityConfig{1:{}}`
and `mapAckIndexer{1:12}` with two `make(map…)`s (each ALLOCATING its data
cell inside the apply step) and two `m[k] = v` writes, call `run`, return
its answer. -/
theorem wp_oneKnown_body {ra : Addr} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec oneKnownImpl.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  rw [oneKnownImpl_body_eq]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd2
  -- `c := MajorityConfig{1: {}}`
  unfold okCfgSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd4
  iapply (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %c10a Hc10
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd5
  iapply (wp_stmt_op_first (op := .makeMap false) (nt := 1)
    (e := .ref "$c10") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd6
  iapply (wp_eval_ref (loc := Loc.base c10a) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd7
  iapply (wp_make_map (a := c10a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hc10]
  · iexact Hc10
  iintro %cfgba ⟨Hcfgb, Hc10⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd8
  -- `c[1] = struct{}{}`
  iapply (wp_stmt_op_first
    (op := .mapAssign (.int .uint64) (.defined ⟨"struct{}"⟩)) (nt := 0)
    (e := .var "$c10")
    (rest := [.intLit 1 .uint64, .structLit (.defined ⟨"struct{}"⟩) #[]]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd9
  iapply (wp_eval_var (a := c10a)
    (cell := ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
              .map ⟨some (.base cfgba)⟩⟩) rfl)
  isplitl [Hc10]
  · iexact Hc10
  iintro Hc10
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd10
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd11
  rw [show IntKind.uint64.normalize 1 = 1 from by decide]
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd12
  iapply (wp_eval_strict_nullary_pin (v := .struct ⟨"struct{}"⟩ #[]) rfl
    (fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, buildStructValue, buildStructValueFuel,
        buildStructFields, typeResolutionFuel, QuorumPin.typeEnv_structEmpty,
        Functor.map, Except.map, Bind.bind, Except.bind]))
  iapply (wp_stmt_op_apply_store (a := cfgba)
    (oldcell := ⟨none, .mapData #[]⟩)
    (newcell := ⟨none, .mapData
      #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_structEmpty, normalizeStructValueForFields,
        normalizeStructFieldsForTy, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Functor.map, Except.map,
        Bind.bind, Except.bind,
        show IntKind.uint64.normalize 1 = 1 from by decide]))
  isplitl [Hcfgb]
  · iexact Hcfgb
  iintro Hcfgb
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd14
  -- `l := mapAckIndexer{1: 12}`
  unfold okAckSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd15
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd16
  iapply (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %c11a Hc11
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd17
  iapply (wp_stmt_op_first (op := .makeMap false) (nt := 1)
    (e := .ref "$c11") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd18
  iapply (wp_eval_ref (loc := Loc.base c11a) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd19
  iapply (wp_make_map (a := c11a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hc11]
  · iexact Hc11
  iintro %ackba ⟨Hackb, Hc11⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd20
  iapply (wp_stmt_op_first
    (op := .mapAssign (.int .uint64) (.defined ⟨"main.Index"⟩)) (nt := 0)
    (e := .var "$c11")
    (rest := [.intLit 1 .uint64, .intLit 12 .uint64]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd21
  iapply (wp_eval_var (a := c11a)
    (cell := ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
              .map ⟨some (.base ackba)⟩⟩) rfl)
  isplitl [Hc11]
  · iexact Hc11
  iintro Hc11
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd22
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd23
  rw [show IntKind.uint64.normalize 1 = 1 from by decide]
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd24
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd25
  rw [show IntKind.uint64.normalize 12 = 12 from by decide]
  iapply (wp_stmt_op_apply_store (a := ackba)
    (oldcell := ⟨none, .mapData #[]⟩)
    (newcell := ⟨none, .mapData #[(.int 1 .uint64, .int 12 .uint64)]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk, mapEntryIndex?,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 1 = 1 from by decide,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  isplitl [Hackb]
  · iexact Hackb
  iintro Hackb
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd26
  -- `r := run(c, l)`
  unfold okCallSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd27
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd28
  iapply wp_init_int
  iintro %c12a Hc12
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd29
  iapply (wp_call_first_target (te := .ref "$c12") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd30
  iapply (wp_eval_ref (loc := Loc.base c12a) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd31
  iapply (wp_call_targets_done_arg (loc := Loc.base c12a) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd32
  iapply (wp_eval_var (a := c10a)
    (cell := ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
              .map ⟨some (.base cfgba)⟩⟩) rfl)
  isplitl [Hc10]
  · iexact Hc10
  iintro Hc10
  iapply wp_call_arg_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd33
  iapply (wp_eval_var (a := c11a)
    (cell := ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
              .map ⟨some (.base ackba)⟩⟩) rfl)
  isplitl [Hc11]
  · iexact Hc11
  iintro Hc11
  simp only [List.nil_append, List.singleton_append, List.cons_append]
  iapply (wp_call_enter₂₁ (func := QuorumPin.runImpl)
    (w₀ := .map ⟨some (.base cfgba)⟩)
    (w₁ := .map ⟨some (.base ackba)⟩)
    (dv₀ := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.runImpl_find)
    (hargs := QuorumPin.runImpl_args)
    (hres := QuorumPin.runImpl_results)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?,
        QuorumPin.quorumMethods_eq, Bind.bind, Except.bind])
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_MajorityConfig])
    (hnorm₁ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hdef₀ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %b₀ %b₁ %b₂ ⟨Hq0, Hq1, Hq2⟩
  iapply (wp_run_body (ca := b₀) (cba := cfgba) (la := b₁) (lba := ackba)
    (ra := b₂) hprog hmeths htypes)
  isplitl [Hq0]
  · iexact Hq0
  isplitl [Hcfgb]
  · iexact Hcfgb
  isplitl [Hq1]
  · iexact Hq1
  isplitl [Hackb]
  · iexact Hackb
  isplitl [Hq2]
  · iexact Hq2
  iintro Hq2
  iapply (wp_frame_return_int (ta := c12a) (ra := b₂) (kind := .uint64)
    (tkind := .uint64) (m := 12))
  isplitl [Hq2]
  · iexact Hq2
  isplitl [Hc12]
  · iexact Hc12
  iintro ⟨Hq2, Hc12⟩
  rw [show IntKind.uint64.normalize 12 = 12 from by decide]
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd34
  -- `return r`
  unfold okResSeq
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd35
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd36
  iapply (wp_assign_start (te := .ref "$res0") rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd37
  iapply (wp_eval_ref (loc := Loc.base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd38
  iapply wp_assign_target
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd39
  iapply (wp_eval_var (a := c12a) (cell := ⟨some (.int .uint64),
    .int 12 .uint64⟩) rfl)
  isplitl [Hc12]
  · iexact Hc12
  iintro Hc12
  iapply (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 12
      rw [show IntKind.uint64.normalize 12 = 12 from by decide] at h
      exact h))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd40
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd41
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hd42
  iapply Hcont $$ Hr

/-- **The `committedOneKnown()` callsite** — the outermost frame: one
target cell, no arguments, `wp_call_enter_ret1` in, the driver body, and
the int frame exit that delivers `12` to the caller's cell. -/
theorem wp_oneKnownCall {ta : Addr} {w : GoValue} {env k}
    (hres : LocalEnv.lookup env "$callres" = some (.base ta))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ta.id ↦ (⟨some (.int .uint64), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
            env k) @ s ; E {{ Φ }} := by
  iintro ⟨Ht, Hcont⟩
  iapply (wp_call_first_target (te := .ref "$callres") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hk1
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hk2
  iapply (wp_call_enter_ret1 (func := QuorumPin.oneKnownImpl)
    (dv := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.oneKnownImpl_find)
    (hargs := QuorumPin.oneKnownImpl_args)
    (hres := QuorumPin.oneKnownImpl_results)
    (hnodisp := fun σ hm => by
      simp only [dynamicDispatch?, methodInfoByFuncId?, hm.trans hmeths]
      simp +decide [QuorumPin.quorumMethods_eq, Bind.bind, Except.bind])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %rra Hrr
  iapply (wp_oneKnown_body (ra := rra) hprog hmeths htypes)
  isplitl [Hrr]
  · iexact Hrr
  iintro Hrr
  iapply (wp_frame_return_int (ta := ta) (ra := rra) (kind := .uint64)
    (tkind := .uint64) (m := 12))
  isplitl [Hrr]
  · iexact Hrr
  isplitl [Ht]
  · iexact Ht
  iintro ⟨Hrr, Ht⟩
  rw [show IntKind.uint64.normalize 12 = 12 from by decide]
  iapply Hcont $$ Ht

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-- **THE ARC'S NAMED GOAL — now a THEOREM** (`quorumOneKnownFuncSpec`
below, quorum pilot phase 4 summit, 2026-07-31). The `GoFuncSpec` form
over the PINNED ACTUAL LOWERING of the real etcd-io/raft quorum source:
"`committedOneKnown()` takes no arguments, needs no heap, and returns
12" — ∀-quantified over the caller's target cell, its prior value, and
the frame, exactly as `recoverFuncSpec_statement`/
`goldenFuncSpec_statement`. The driver builds `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}` and calls `run → CommittedIndex`, so discharging
this walks the real interface dispatch, the real map range, the real sort
extern and the real defined-type conversions.

`12` is `committedIndexRef [1] ackedOneKnown` (`committedIndexRef_oneKnown`,
`rfl`), so this discharge plus `committedIndexRef_meets_spec` (PROVEN)
yields `IsCommittedIndex` on this instance — the tier-1 claim, packaged
as `quorumOneKnownMeetsSpec`. -/
def quorumOneKnownFuncSpec_statement : Prop :=
  GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
    quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
    (fun n => .pure (n = 12))

/-- **TARGET — the negative twin, and the one thing this slice did NOT
prove.** Stated in phase 0 as an UNCONDITIONAL refutation. It does not
follow from the positive discharge: `GoTriple` quantifies over
TERMINATING runs, so both the `= 12` and the `= 11` spec are vacuously
true of a program with no terminating run, and refuting this def requires
exhibiting one — a kernel evaluation of the interpreter over the whole
pinned program, a separate cost. The run-conditioned twin
`quorumOneKnownNotEleven` (the `goldenNotThree` shape) IS proven below;
this def stays a target and no theorem names it. Recorded, not
quietly restated. -/
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
    (ta := ⟨ra⟩) (tb := ⟨rb⟩) (w₁ := w₁) (w₂ := w₂)
    (mty := some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)))
    (q := 3) (v := 12) rfl rfl rfl
    hprog hmeths htypes (by decide) (by decide))
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


/-! ## THE ARC'S NAMED GOAL

`docs/2026-07-30_quorum-pilot-arc.md` THE GOAL: a kernel-checked theorem
about the REAL `etcd-io/raft` `(MajorityConfig).CommittedIndex`, over the
frontend's ACTUAL lowering, whose answer is the declarative quorum spec's.
Scope, stated once and not softened: **one voter** (`n = 1`), so the map
range's nondeterminism is degenerate (a single iteration order) and the
`len(stk) >= n` branch is the reslice one. The three-voter walk — real
branching in the range, a non-trivial sort, the `pos` arithmetic biting —
is the recorded next widening. -/

/-- **THE THEOREM.** `committedOneKnown()` — the pinned lowering of the
real quorum driver — returns `12`, at `GoFuncSpec` strength: into any
caller cell, over any prior value, in any admissible heap, beside any
frame, through the exit pipe (triple + progress). The per-program
obligation is the WP walk `wp_oneKnownCall`, which composes only general
laws over `GoldenQuorum.quorumLowered`. -/
theorem quorumOneKnownFuncSpec : quorumOneKnownFuncSpec_statement := by
  unfold quorumOneKnownFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_oneKnownCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H12
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  isplitl [H12]
  · iexact H12
  · ipureintro
    rfl

/-- **THE COROLLARY THAT NAMES THE GOAL**: the machine's answer *is* a
committed index. The postcondition is no longer a number but the
declarative spec of `deps/raft/quorum/majority.go` — committedness plus
maximality (`GoLean.Quorum.IsCommittedIndex`) — discharged on the
one-voter instance by `isCommittedIndex_oneKnown`, which is itself the
proven general agreement theorem `committedIndexRef_meets_spec` applied to
the reference. So the chain is closed end to end: real Go source →
frontend lowering (pinned) → machine walk (this WP proof) → declarative
quorum spec, with no unproven link. -/
theorem quorumOneKnownMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1] GoLean.Quorum.ackedOneKnown
          n.toNat)) := by
  unfold GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_oneKnownCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H12
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  isplitl [H12]
  · iexact H12
  · ipureintro
    exact ⟨by decide, GoLean.Quorum.isCommittedIndex_oneKnown⟩


/-! ### The first-order readout, and the negative twin

`GoFuncSpec` is a separation-logic statement; the corpus-facing claim is
first-order ("this run leaves 12 at this address"). The pair below is the
golden precedent's (`goldenReturnsTwo`/`goldenNotThree`) at the quorum
driver: read the triple out at a pinned address, then refute 11 in two
lines. Both are run-CONDITIONED — a `GoTriple` says nothing about a
program that fails to terminate, so the unconditional `¬ GoFuncSpec` form
of the phase-0 target `quorumOneKnownNotEleven_statement` is not
refutable from the triple alone: refuting it demands EXHIBITING a
terminating run (a kernel evaluation of the interpreter over the whole
pinned program), which is a separate cost and stays recorded as owed. -/

/-- The initial heap the readout runs against: one cell at base 0 holding
the caller's target, exactly as `GoFuncSpec` quantifies it. -/
def quorumOut : Heap := [(Loc.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

def quorumOutEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- **The first-order readout**: every terminating run of
`$callres = committedOneKnown()` from the seeded one-cell state leaves
`uint64(12)` at base address 0. -/
theorem quorumOneKnownReturnsTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) := by
  have htriple := (quorumOneKnownFuncSpec 0 (.int 0 .uint64)).1
  have hres := htriple quorumOut 1 (heapletOf quorumOut) (∅ : Heaplet)
    { bounded := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rfl
      disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := ⟨heapletOf quorumOut, ∅, rfl, rfl,
        fun k => .inr (by
          rw [heaplet_get?_eq]
          exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)),
        fun k c => ⟨fun h => .inl h, fun h => h.elim id (fun h0 => by
          rw [heaplet_get?_eq,
            LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h0
          cases h0)⟩⟩ }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn12, rfl⟩ := hp2
  subst hn12
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 12 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have := hsub 0 ⟨some (.int .uint64), .int 12 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at this
  exact loadLoc_base_of_lookup this

/-- **The negative twin** — the two-line corollary the golden precedent
predicts: no terminating run leaves `11`. This is what stops a trivialized
postcondition from passing for the real one. -/
theorem quorumOneKnownNotEleven
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 11 .uint64) := by
  intro h11
  have h12 := quorumOneKnownReturnsTwelve fuel ch σf ch' hrun
  have := h12.symm.trans h11
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Surface
