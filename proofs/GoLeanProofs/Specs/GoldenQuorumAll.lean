import GoLeanProofs.Specs.GoldenQuorumThree
import GoLeanProofs.Specs.QuorumRefSpec
import GoLeanProofs.Specs.Statements

/-!
# `CommittedIndex` for EVERY config — the ∀-config theorem
(proof-automation arc phase 4, 2026-08-01)

Plan of record: `docs/2026-08-01_proof-automation-arc.md`. This file
discharges `Specs/AutomationTargets.committedIndexAllConfigs_statement`:
the pinned lowering of the real etcd-io/raft
`main.MajorityConfig.CommittedIndex`, called on an ARBITRARY
`MajorityConfig` and an ARBITRARY `AckedIndexer` supplied through the
caller's heap, delivers a value satisfying the declarative quorum spec
`IsCommittedIndex`.

## What this rung adds over the 3-voter one

* **Both branches of the fit test** (`wp_ci_fitIf_all`): the on-stack
  `[7]uint64` reslice at `n ≤ 7` AND the `make([]uint64, n)` allocation
  above it. The scratch array's ADDRESS and CAPACITY become existential;
  nothing after the fit test knows which branch ran.
* **Voters with NO acked entry** (`wp_ci_range_body_miss`,
  `wp_ci_loop_all`): `if idx, ok := l.AckedIndex(id); ok { … }` skips the
  write AND the decrement, so a missing voter leaves a zero in a LOW
  slot. The 3-voter rung's loop law assumed every voter reports; the
  `∀`-config statement quantifies over `acked : Nat → Option Nat` with no
  such promise, so the invariant carries the number of zeros explicitly.
* **The sort and the readout at a symbolic `n`** (`wp_ci_tail_all`):
  `slices.Sort`'s transition through `Laws/Values.applyStmtOp_sortSlice_ints`
  (the machine's own `for i in [:len]` loops, discharged by induction
  rather than unrolling), the sorted answer identified with the
  reference's `sortAsc` by sorted-permutation uniqueness, and
  `pos = n - (n/2+1)` shown to be `committedIndexRef`'s index.
* **The encoding bridge**: `EncodesConfig`/`EncodesAcked` — predicates on
  the map SNAPSHOTS the machine sees — turned into the loop law's
  `cfgSnapshot`/lookup premises.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

set_option linter.unusedSimpArgs false

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- The on-stack scratch array, split at the fill boundary: seven zeros
are `n` unwritten slots and a `7 - n` tail. -/
theorem stkZero_split {n : Nat} (h : n ≤ 7) :
    (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell) = stkCell 7 n [] (7 - n) := by
  rw [stkCell, stkArr, stkZero, List.map_nil, List.append_nil,
    List.replicate_append_replicate, show n + (7 - n) = 7 from by omega]
  rfl

/-- The freshly made backing array is the same shape at capacity `n`. -/
theorem makeSlice_cell {n : Nat} :
    (⟨some (.array n (.int .uint64)),
      .array (List.replicate n (GoValue.int 0 .uint64)).toArray⟩ : HeapCell)
      = stkCell n n [] 0 := by
  rw [stkCell, stkArr]
  congr 2
  simp [u64]

/-- **`if len(stk) >= n { srt = stk[:n] } else { srt = make([]uint64, n) }`
at a SYMBOLIC voter count** — BOTH branches. Whichever is taken, the
continuation gets a slice of length `n` over a zeroed backing array of
some capacity `cap = n + trail`: the on-stack `[7]uint64` resliced (`n ≤
7`, `cap = 7`), or a freshly allocated `[n]uint64` (`n > 7`, `cap = n`).
The scratch array's ADDRESS is existential — that is exactly the
difference between the branches, and the rest of the walk never needs to
know which one it took. -/
theorem wp_ci_fitIf_all {na sta sra : Addr} {w : GoValue} {n : Nat} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hstk : LocalEnv.lookup env "stk" = some (.base sta))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int (n : Int) .int⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)), w⟩ : HeapCell)
      ∗ iprop(∀ (ba : Addr) (cap trail : Nat), ⌜n + trail = cap⌝
            ∗ na.id ↦ (⟨some (.int .int), .int (n : Int) .int⟩ : HeapCell)
            ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                         .slice ⟨some (.base ba), 0, n, cap⟩⟩ : HeapCell)
            ∗ ba.id ↦ stkCell cap n [] trail -∗
          WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciFitIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hstk, Hsrt, Hcont⟩
  rw [ciFitIf_eq]
  by_cases hfit : n ≤ 7
  · -- the RESLICE branch: the on-stack array is big enough
    go_walk
    rw [if_pos (show (decide (7 ≥ (n : Int)) = true) from by
      simp only [decide_eq_true_eq, ge_iff_le]; exact_mod_cast hfit)]
    go_walk
    go_walk_step (wp_strict_apply_read (a := sta)
      (cell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
      (out := .slice ⟨some (.base sta), 0, n, 7⟩)
      (v := .int (n : Int) .int) (done := [.int 0 .int, .addr (.base sta)])
      (happly := fun σ _ht hl => by
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, applyStrictOp, applySlice, loadLoc, hl, stkZero,
          valueAsInt, sliceFromArray, Bind.bind, Except.bind, pure, Except.pure]
        rw [show (#[GoValue.int 0 IntKind.uint64, GoValue.int 0 IntKind.uint64,
              GoValue.int 0 IntKind.uint64, GoValue.int 0 IntKind.uint64,
              GoValue.int 0 IntKind.uint64, GoValue.int 0 IntKind.uint64,
              GoValue.int 0 IntKind.uint64] : Array GoValue).size = 7 from rfl,
          checkSliceBounds_prefix (limit := 7) hfit]
        simp))
    go_walk_step (wp_assign_store
      (oldcell := ⟨some (.slice (.int .uint64)), w⟩)
      (newcell := ⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, n, 7⟩⟩)
      (fun σ _ht hl => by
        simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
          Bind.bind, Except.bind, typeResolutionFuel]))
    go_walk 1
    rw [stkZero_split hfit]
    iapply Hcont $$ %sta %7 %(7 - n)
    isplitl []
    · ipureintro
      omega
    · iframe
  · -- the ALLOCATING branch: `make([]uint64, n)`
    go_walk
    rw [if_neg (show ¬ (decide (7 ≥ (n : Int)) = true) from by
      simp only [decide_eq_true_eq, ge_iff_le]
      intro hcon
      exact hfit (by exact_mod_cast hcon))]
    go_walk
    go_walk_step (wp_init (v := .slice ⟨none, 0, 0, 0⟩) (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [c2a, Hc2]
    go_walk
    go_walk_step (wp_make_slice (elem := .int .uint64) (a := c2a) (n := n)
      (backing := .array (List.replicate n (GoValue.int 0 .uint64)).toArray)
      (newcell := fun fa => ⟨some (.slice (.int .uint64)),
                             .slice ⟨some (.base fa), 0, n, n⟩⟩)
      (hbacking := fun σ _ht => buildDefaultArrayValue_int σ .uint64 n)
      (oldcell := ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩)
      (hstore := fun σ fa _ht hlk => by
        simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
          Bind.bind, Except.bind, typeResolutionFuel])) as [fa, Hfa, Hc2]
    go_walk
    go_walk_step (wp_assign_store
      (oldcell := ⟨some (.slice (.int .uint64)), w⟩)
      (newcell := ⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base fa), 0, n, n⟩⟩)
      (fun σ _ht hl => by
        simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
          Bind.bind, Except.bind, typeResolutionFuel]))
    go_walk 1
    rw [makeSlice_cell (n := n)]
    iapply Hcont $$ %fa %n %0
    isplitl []
    · ipureintro
      omega
    · iframe

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- **The voter loop's body at a voter the `AckedIndexer` does NOT
know** — `if idx, ok := l.AckedIndex(id); ok { … }` with `ok` false. Go's
"has not reported yet": the comma-ok read delivers the zero `Index` and
`false`, the `if` is not taken, and NEITHER the scratch slot NOR the fill
index `i` moves — which is why the missing voters' zeros end up in the
LOW slots and get sorted like any other acked-or-zero value.

The law touches only the receiver's cells and the key cell: the scratch
array, the fill index and the slice are not read on this path, so
demanding them would be a lie about the step's footprint. -/
theorem wp_ci_range_body_miss {la lba pa : Addr} {lty : Option Ty}
    {aentries : Array (GoValue × GoValue)} {q : Int}
    {rem' : Array (GoValue × GoValue)} {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hpair : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int 0 .uint64, false))
    (hl : LocalEnv.lookup env "l" = some (.base la)) :
    pa.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ (la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
          -∗ WP (Config.next (.mapIterK (some "id") none (.int .uint64)
                  (.defined ⟨"struct{}"⟩) rangeBody rem' env k))
              @ s ; E {{ Φ }})
      ⊢ WP (Config.exec rangeBody (env.pushScope.declare "id" (.base pa))
            (.mapIterK (some "id") none (.int .uint64)
              (.defined ⟨"struct{}"⟩) rangeBody rem' env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hid, Hl, Hlb, Hk⟩
  rw [rangeBody_eq]
  go_walk
  unfold ciCallSeq
  go_walk
  go_walk_step (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  go_walk
  go_walk_step (wp_init (v := .bool false) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk with [hq]
  go_walk_step (wp_ackedIndex_body_entries (mty := lty) (entries := aentries)
    (q := q) (v := 0) (b := false) htypes hq (by decide) hpair)
  go_walk_step (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool false⟩)
    (tcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell₀' := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell₁ := ⟨some .bool, .bool false⟩)
    (tcell₁' := ⟨some .bool, .bool false⟩)
    (hstore₀ := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 0 = 0 from by decide])
    (hstore₁ := fun σ _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  -- `if ok { … }` — NOT taken
  go_walk
  unfold ciOkIf
  go_walk_finish Hk

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-! ## THE VOTER LOOP at an arbitrary config AND a PARTIAL acked map

`wp_ci_loop_all` covers `var i int; i = n-1; for id := range c { … }` for
an ARBITRARY voter list `ks₀` and an ARBITRARY PARTIAL acked function
`ack : Int → Option Int`. It is `Specs/GoldenQuorumThree.wp_ci_loop`'s
widening: that law's `ack : Int → Int` promises every voter reports,
which `majority.go` does not (`AckedIndex` returns `(_, false)` for a
voter that has not), and the ∀-config statement quantifies over
`acked : Nat → Option Nat` with no such promise.

**THE INVARIANT.** Over the remaining snapshot `rem`:

```
∃ ks filled zeros,
  ⌜rem = cfgSnapshot ks ∧ ks ⊆ ks₀
    ∧ ((ks.map ack).reduceOption ++ filled) ~ (ks₀.map ack).reduceOption
    ∧ zeros + filled.length = ks₀.length ∧ ks.length ≤ zeros⌝
  ∗ … ∗ i ↦ ⟨int, zeros - 1⟩ ∗ stk ↦ stkArr zeros filled trail
```

Three changes from the total-ack invariant, each forced by the missing
voters: the `List.Perm` is over the REPORTED values only
(`reduceOption`); the number of unwritten slots `zeros` is its own
existential (it is no longer `ks.length` — a missing voter shrinks `ks`
and leaves `zeros` alone), pinned to the fill index by `i = zeros - 1`;
and `ks.length ≤ zeros` is what keeps the next write in bounds. At
exhaustion `filled` is a permutation of the whole reported multiset and
`zeros` counts the voters that never reported — the zeros `slices.Sort`
then sorts in among the acked values, which is exactly `ackedOrZero`. -/
theorem wp_ci_loop_all {na ca cba la lba sra sta : Addr} {cty lty : Option Ty}
    {ks₀ : List Int} {ack : Int → Option Int}
    {aentries : Array (GoValue × GoValue)} {trail cap : Nat} {rest env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hcap : ks₀.length + trail = cap)
    (hsmall : ks₀.length < 2 ^ 63)
    (hnormk : ∀ q ∈ ks₀, IntKind.uint64.normalize q = q)
    (hnormv : ∀ q ∈ ks₀, ∀ v : Int, ack q = some v →
      IntKind.uint64.normalize v = v)
    (hlook : ∀ q ∈ ks₀, ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int ((ack q).getD 0) .uint64, (ack q).isSome))
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int (ks₀.length : Int) .int⟩ : HeapCell)
      ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                  .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap ks₀.length [] trail
      ∗ iprop(∀ (filled : List Int) (zeros : Nat),
          ⌜filled.Perm ((ks₀.map ack).reduceOption)
            ∧ zeros + filled.length = ks₀.length⌝
            ∗ na.id ↦ (⟨some (.int .int), .int (ks₀.length : Int) .int⟩ : HeapCell)
            ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                        .map ⟨some (.base cba)⟩⟩ : HeapCell)
            ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
            ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                        .interface (.defined ⟨"main.mapAckIndexer"⟩)
                          (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
            ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
            ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                         .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
            ∗ sta.id ↦ stkCell cap zeros filled trail -∗
          WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLoopBlock env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hc, Hcb, Hl, Hlb, Hsr, Hst, Hcont⟩
  have hdecn : IntKind.int.normalize ((ks₀.length : Int) - 1)
      = (ks₀.length : Int) - 1 := int_normalize_of_range (by omega) (by omega)
  rw [ciLoopBlock_eq]
  go_walk
  unfold ciIDecl
  go_walk 2
  go_walk_step wp_init_int as [ia]
  go_walk with [hdecn]
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int ((ks₀.length : Int) - 1) .int⟩)
    (fun σ _ht hl' => by
      have h := storeLoc_int_any (mkind := .int) hl' ((ks₀.length : Int) - 1)
      rw [hdecn] at h
      exact h)) as [Hi]
  rw [rangeStmt_eq]
  go_walk
  go_walk_step (wp_map_range_snapshot (ba := cba) (mty := cty)
    (entries := cfgSnapshot ks₀)
    (hnorm := by
      rw [htypes]
      refine snapshotEntriesSelfNormalizedList_of_mem fun e he => ?_
      obtain ⟨q, hq, rfl⟩ : ∃ q, q ∈ ks₀ ∧ voterEntry q = e := by
        simpa [cfgSnapshot] using he
      refine ⟨?_, show isNormalForTy quorumLowered.typeDefs.toList
        (.defined ⟨"struct{}"⟩) (.struct ⟨"struct{}"⟩ #[]) = true
        by decide +kernel⟩
      simp [voterEntry, u64, isNormalForTy, isNormalForTyFuel,
        typeResolutionFuel, hnormk q hq]))
  -- THE RANGE, through the INDUCTIVE RANGE RULE
  iapply (wp_map_iter_inv
    (I := fun rem => iprop(∃ ks : List Int, ∃ filled : List Int, ∃ zeros : Nat,
      ⌜rem = cfgSnapshot ks ∧ (∀ x ∈ ks, x ∈ ks₀)
        ∧ ((ks.map ack).reduceOption ++ filled).Perm ((ks₀.map ack).reduceOption)
        ∧ zeros + filled.length = ks₀.length ∧ ks.length ≤ zeros⌝
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
      ∗ ia.id ↦ (⟨some (.int .int), .int ((zeros : Int) - 1) .int⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap zeros filled trail))
    (hnorm := fun σ _htypes p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (by simpa [cfgSnapshot] using hp)
      simp [voterEntry, u64, normalizeValueForTy, normalizeValueForTyFuel,
        hnormk x hx, typeResolutionFuel])
    (Hbody := by
      intro rem i hidx pa
      iintro ⟨⟨%ks, %filled, %zeros, %hpure, Hl, Hlb, Hsr, Hi, Hst⟩, Hid, Hk⟩
      obtain ⟨hrem, hsub, hperm, hzf, hkz⟩ := hpure
      subst hrem
      have hik : i < ks.length := by
        rw [cfgSnapshot_size] at hidx; exact hidx
      have hqmem : ks[i] ∈ ks₀ := hsub _ (List.getElem_mem hik)
      have herase : (ks.eraseIdx i).length = ks.length - 1 := by
        rw [List.length_eraseIdx, if_pos hik]
      have hgetmap : (ks.map ack)[i]? = some (ack ks[i]) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hik]
        rfl
      rw [cfgSnapshot_getElem, cfgSnapshot_eraseIdx]
      simp only [voterEntry, u64]
      -- the voter either reported or did not: the two body laws
      cases hack : ack ks[i] with
      | some v =>
        obtain ⟨m, hm⟩ : ∃ m, zeros = m + 1 := ⟨zeros - 1, by omega⟩
        have hicast : ((zeros : Int) - 1) = (m : Int) := by omega
        have hfil : ∀ f ∈ filled, IntKind.uint64.normalize f = f := by
          intro f hf
          have hmem : f ∈ (ks₀.map ack).reduceOption :=
            hperm.mem_iff.mp (List.mem_append_right _ hf)
          obtain ⟨q, hq, hqf⟩ := mem_reduceOption_map hmem
          exact hnormv q hq f hqf
        rw [hicast, show stkCell cap zeros filled trail
            = stkCell cap (m + 1) filled trail from by rw [hm]]
        iapply (wp_ci_range_body (ia := ia) (la := la) (lba := lba) (sra := sra)
          (sta := sta) (pa := pa) (lty := lty) (aentries := aentries)
          (q := ks[i]) (v := v) (zeros := m) (trail := trail) (cap := cap)
          (slen := ks₀.length) (filled := filled) hprog hmeths htypes
          (hnormk _ hqmem) (hnormv _ hqmem v hack)
          (int_normalize_of_range (by omega) (by omega))
          hfil (by omega) (by omega) (by omega)
          (fun σ ht hlk => by
            have h := hlook _ hqmem σ ht hlk
            rw [hack] at h
            exact h)
          (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup, hl])
          (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup, hsrt])
          (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup]))
        iframe
        iintro ⟨Hl, Hlb, Hsr, Hi, Hst⟩
        iapply Hk
        iexists (ks.eraseIdx i)
        iexists (v :: filled)
        iexists m
        isplitl []
        · ipureintro
          refine ⟨rfl, fun x hx => hsub x (List.mem_of_mem_eraseIdx hx), ?_, ?_, ?_⟩
          · refine List.Perm.trans ?_ hperm
            have hp := perm_eraseIdx_reduceOption filled (ks.map ack) i v
              (by rw [hgetmap, hack])
            rw [list_map_eraseIdx] at hp
            exact hp
          · simp only [List.length_cons]; omega
          · rw [herase]; omega
        · rw [show ((m : Int) - 1) = ((m : Int) - 1) from rfl]
          iframe
      | none =>
        iapply (wp_ci_range_body_miss (la := la) (lba := lba) (pa := pa)
          (lty := lty) (aentries := aentries) (q := ks[i]) hprog hmeths htypes
          (hnormk _ hqmem)
          (fun σ ht hlk => by
            have h := hlook _ hqmem σ ht hlk
            rw [hack] at h
            exact h)
          (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup, hl]))
        iframe
        iintro ⟨Hl, Hlb⟩
        iapply Hk
        iexists (ks.eraseIdx i)
        iexists filled
        iexists zeros
        isplitl []
        · ipureintro
          refine ⟨rfl, fun x hx => hsub x (List.mem_of_mem_eraseIdx hx), ?_, hzf, ?_⟩
          · refine List.Perm.trans ?_ hperm
            have hp := reduceOption_eraseIdx_none (ks.map ack) i
              (by rw [hgetmap, hack])
            rw [list_map_eraseIdx] at hp
            rw [hp]
          · rw [herase]; omega
        · iframe))
  -- the invariant at ENTRY
  isplitl [Hl Hlb Hsr Hi Hst]
  · iexists ks₀
    iexists ([] : List Int)
    iexists ks₀.length
    isplitl []
    · ipureintro
      exact ⟨rfl, fun _ h => h, by simp, by simp, by omega⟩
    · iframe
  · iintro ⟨%ks, %filled, %zeros, %hpure, Hl, Hlb, Hsr, Hi, Hst⟩
    obtain ⟨hrem, -, hperm, hzf, -⟩ := hpure
    obtain rfl : ks = [] := by
      have hnil : (ks.map voterEntry) = [] := by
        have h := congrArg Array.toList hrem.symm
        simpa [cfgSnapshot] using h
      simpa using hnil
    rw [List.map_nil, show ([] : List (Option Int)).reduceOption = [] from rfl,
      List.nil_append] at hperm
    go_walk 1
    iapply Hcont $$ %filled %zeros
    isplitl []
    · ipureintro
      exact ⟨hperm, hzf⟩
    · iframe

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris

/-- The scratch array as the sort sees it: `zeros` unwritten slots and
the written values are one list of visible elements, the untouched slots
the tail. -/
theorem stkCell_as_intArray (zeros : Nat) (filled : List Int) (trail cap : Nat) :
    stkCell cap zeros filled trail
      = intArrayCell cap .uint64
          (intVals .uint64 (List.replicate zeros (0 : Int) ++ filled)
            ++ List.replicate trail (u64 0)) := by
  rw [stkCell, stkArr, intArrayCell, intVals]
  congr 2
  rw [List.map_append, List.map_replicate, List.append_assoc]
  simp [u64]

/-- ... and after the sort, at the sorted image. -/
theorem stkCell_sorted (srt : List Int) (trail cap : Nat) :
    intArrayCell cap .uint64 (intVals .uint64 srt ++ List.replicate trail (u64 0))
      = stkCell cap 0 srt trail := by
  rw [stkCell, stkArr, intArrayCell, intVals]
  congr 2


end GoLean.Quorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- **The tail at a SYMBOLIC voter count**: `slices.Sort(srt)`,
`pos := n - (n/2+1)`, `return Index(srt[pos])`.

The array the loop leaves holds an arbitrary permutation of the
acked-or-zero multiset; `srt` is ANY sorted permutation of it, which by
sorted-permutation uniqueness (`Laws/Values.sortLe_pairs_eq_of_perm`)
is what the machine's `slices.Sort` computes — at any length, through
the machine's own `for i in [:len]` loops
(`Laws/Values.applyStmtOp_sortSlice_ints`), with no unrolling. -/
theorem wp_ci_tail_all {na sra sta ra : Addr} {filled srt : List Int}
    {zeros trail cap n : Nat} {res : Int} {env k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hlen : zeros + filled.length = n)
    (hcap : n + trail = cap)
    (hpos : 0 < n) (hsmall : n < 2 ^ 63)
    (hperm : (List.replicate zeros (0 : Int) ++ filled).Perm srt)
    (hsorted : srt.Pairwise (· ≤ ·))
    (hnorm : ∀ v ∈ srt, IntKind.uint64.normalize v = v)
    (hget : srt[n - (n / 2 + 1)]? = some res)
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hres : LocalEnv.lookup env "$res0" = some (.base ra)) :
    na.id ↦ (⟨some (.int .int), .int (n : Int) .int⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, n, cap⟩⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap zeros filled trail
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int res .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec sortStmt env
            (.seq [ciPosStmt, ciResStmt] env k)) @ s ; E {{ Φ }} := by
  have hvlen : (List.replicate zeros (0 : Int) ++ filled).length = n := by
    simp; omega
  have hnormv : ∀ v ∈ List.replicate zeros (0 : Int) ++ filled,
      IntKind.uint64.normalize v = v := by
    intro v hv
    exact hnorm v (hperm.mem_iff.mp hv)
  have hmerge := sortLe_pairs_eq_of_perm (kind := IntKind.uint64) hperm hsorted
  iintro ⟨Hn, Hsr, Hst, Hr, Hcont⟩
  rw [stkCell_as_intArray, sortStmt_eq]
  go_walk
  -- `slices.Sort(srt)` at a symbolic length: ONE apply step, computed by
  -- induction over the machine's own read/write loops
  go_walk_step (wp_sort_slice (a := sta)
    (oldcell := intArrayCell cap .uint64
      (intVals .uint64 (List.replicate zeros (0 : Int) ++ filled)
        ++ List.replicate trail (u64 0)))
    (newcell := intArrayCell cap .uint64
      (intVals .uint64 srt ++ List.replicate trail (u64 0)))
    (slice := ⟨some (.base sta), 0, n, cap⟩)
    (happly := by
      intro σ ch _ht hlk
      rw [show ((⟨some (.base sta), 0, n, cap⟩ : SliceValue))
          = ⟨some (.base sta), 0, (List.replicate zeros (0 : Int) ++ filled).length, cap⟩ from by
        rw [hvlen]]
      refine applyStmtOp_sortSlice_ints ?_ hnormv ?_ hmerge ?_
      · simp only [List.length_append, List.length_replicate]
        omega
      · intro x hx
        exact ⟨0, List.eq_of_mem_replicate hx, by decide⟩
      · exact hlk))
  -- `pos := n - (n/2 + 1)` — Go's `int` arithmetic, in range throughout
  have hd : ((n : Int)).tdiv 2 = ((n / 2 : Nat) : Int) := rfl
  have h1 : IntKind.int.normalize ((n / 2 : Nat) : Int) = ((n / 2 : Nat) : Int) :=
    int_normalize_of_range (by omega) (by omega)
  have h2 : IntKind.int.normalize (((n / 2 : Nat) : Int) + 1)
      = ((n / 2 + 1 : Nat) : Int) := by
    rw [show (((n / 2 : Nat) : Int) + 1) = ((n / 2 + 1 : Nat) : Int) from by omega]
    exact int_normalize_of_range (by omega) (by omega)
  have h3 : IntKind.int.normalize ((n : Int) - ((n / 2 + 1 : Nat) : Int))
      = ((n - (n / 2 + 1) : Nat) : Int) := by
    rw [show ((n : Int) - ((n / 2 + 1 : Nat) : Int))
        = ((n - (n / 2 + 1) : Nat) : Int) from by omega]
    exact int_normalize_of_range (by omega) (by omega)
  go_walk
  rw [ciPosStmt_eq]
  go_walk
  rw [hd, h1, h2, h3]
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int ((n - (n / 2 + 1) : Nat) : Int) .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk ((n - (n / 2 + 1) : Nat) : Int)
      rw [int_normalize_of_range (by omega) (by omega)] at h
      exact h))
  -- `return Index(srt[pos])`
  go_walk
  rw [ciResStmt_eq]
  go_walk
  -- `srt[pos]` — the positional read at a symbolic index
  have hposlt : n - (n / 2 + 1) < srt.length := by
    have h := List.getElem?_eq_some_iff.1 hget
    obtain ⟨hlt, -⟩ := h
    exact hlt
  have hsrtlen : srt.length = n := by
    have h := hperm.length_eq
    simp at h
    omega
  have htakelen : (intVals .uint64 (srt.take (n - (n / 2 + 1)))).length
      = n - (n / 2 + 1) := by
    simp [intVals]
    omega
  have hsplit : intVals .uint64 srt ++ List.replicate trail (u64 0)
      = intVals .uint64 (srt.take (n - (n / 2 + 1)))
          ++ (GoValue.int res .uint64
              :: (intVals .uint64 (srt.drop (n - (n / 2 + 1) + 1))
                  ++ List.replicate trail (u64 0))) := by
    rw [intVals, intVals, intVals,
      list_map_split (fun v => GoValue.int v .uint64) srt _ hposlt,
      show srt[n - (n / 2 + 1)]'hposlt = res from by
        obtain ⟨hlt', he⟩ := List.getElem?_eq_some_iff.1 hget
        exact he]
    simp
  go_walk_step (wp_strict_apply_read (a := sta)
    (cell := intArrayCell cap .uint64
      (intVals .uint64 srt ++ List.replicate trail (u64 0)))
    (out := .int res .uint64)
    (v := .int ((n - (n / 2 + 1) : Nat) : Int) .int)
    (done := [.slice ⟨some (.base sta), 0, n, cap⟩])
    (happly := fun σ _ht hlk => by
      have hidx : sliceIndexLoc (⟨some (.base sta), 0, n, cap⟩ : SliceValue)
          ((n - (n / 2 + 1) : Nat) : Int)
          = .ok (.index (.base sta) ((n - (n / 2 + 1) : Nat) : Int)) :=
        sliceIndexLoc_prefix (by omega) (by omega)
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, applyStrictOp, valueAsInt, Bind.bind, Except.bind,
        pure, Except.pure, hidx, loadLoc, hlk, intArrayCell]
      rw [hsplit, arrayGet_middle' (x := GoValue.int res .uint64) htakelen.symm]))
  -- `Index(...)` — the named-type conversion, then the result store
  have hnormres : IntKind.uint64.normalize res = res := by
    refine hnorm res ?_
    obtain ⟨hlt', he⟩ := List.getElem?_eq_some_iff.1 hget
    exact he ▸ List.getElem_mem hlt'
  go_walk_step (wp_strict_apply_pin (out := .int res .uint64)
    (v := .int res .uint64) (done := [])
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, convertValueToTy, convertValueToTyFuel,
        typeResolutionFuel, resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.typeEnv_Index, Bind.bind, Except.bind, hnormres]))
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int res .uint64⟩)
    (fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        hnormres]))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- **THE `CommittedIndex` BODY WALK AT AN ARBITRARY NONEMPTY CONFIG** —
the real `main.MajorityConfig.CommittedIndex` of the pinned etcd-io/raft
lowering, on an arbitrary voter list `ks₀` and an arbitrary PARTIAL acked
map `ack`. Every statement of `majority.go`'s algorithm is walked: the
`len`, the empty-config test, the two scratch declarations, BOTH branches
of the fit test, the voter range (one generic iteration + the
permutation invariant, the reporting and the silent voter), the sort at a
symbolic length, and the `pos` readout.

`srt` is ANY sorted permutation of the acked-or-zero multiset and `res`
its element at `n - (n/2+1)`: the caller supplies the mathematical
identification (for the `∀`-config theorem, the reference's `sortAsc`). -/
theorem wp_committedIndex_body_all {ca cba la lba ra : Addr}
    {cty lty : Option Ty} {ks₀ srt : List Int} {ack : Int → Option Int}
    {aentries : Array (GoValue × GoValue)} {res : Int} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hne : ks₀ ≠ []) (hsmall : ks₀.length < 2 ^ 63)
    (hnormk : ∀ q ∈ ks₀, IntKind.uint64.normalize q = q)
    (hnormv : ∀ q ∈ ks₀, ∀ v : Int, ack q = some v →
      IntKind.uint64.normalize v = v)
    (hlook : ∀ q ∈ ks₀, ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int ((ack q).getD 0) .uint64, (ack q).isSome))
    (hperm : (ks₀.map (fun q => (ack q).getD 0)).Perm srt)
    (hsorted : srt.Pairwise (· ≤ ·))
    (hnormsrt : ∀ v ∈ srt, IntKind.uint64.normalize v = v)
    (hget : srt[ks₀.length - (ks₀.length / 2 + 1)]? = some res) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int res .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec committedIndexImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  have hlen : 0 < ks₀.length := List.length_pos_iff.mpr hne
  have hsize : (Int.ofNat (cfgSnapshot ks₀).size) = (ks₀.length : Int) := by
    rw [cfgSnapshot_size]
    rfl
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [committedIndexImpl_body_eq]
  go_walk with [committedIndexStmts_toList]
  -- `n := len(c)`
  go_walk_step (wp_ci_len (cba := cba) (cty := cty)
    (entries := cfgSnapshot ks₀)
    (by rw [cfgSnapshot_size, Int.ofNat_eq_natCast]
        exact int_normalize_of_range (by omega) (by omega)) rfl) as [na]
  go_walk with [hsize]
  -- `if n == 0 { return math.MaxUint64 }`, not taken
  go_walk_step (wp_ci_emptyIf (na := na) (n := (ks₀.length : Int)) rfl
    (fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]
      omega))
  go_walk
  go_walk_step wp_ci_stkDecl as [sta]
  go_walk
  go_walk_step wp_ci_srtDecl as [sra]
  go_walk
  -- `if len(stk) >= n { … } else { … }` — BOTH branches, existential scratch
  go_walk_step (wp_ci_fitIf_all (na := na) (sta := sta) (sra := sra)
    (n := ks₀.length) rfl rfl rfl) as [ba, cap, trail, Hpure, Hn, Hsr, Hst]
  icases Hpure with %hcap
  go_walk 1
  -- the voter loop
  go_walk_step (wp_ci_loop_all (na := na) (ca := ca) (cba := cba) (la := la)
    (lba := lba) (sra := sra) (sta := ba) (cty := cty) (lty := lty)
    (ks₀ := ks₀) (ack := ack) (aentries := aentries) (trail := trail)
    (cap := cap) hprog hmeths htypes hcap hsmall hnormk hnormv hlook
    rfl rfl rfl rfl)
    as [filled, zeros, Hloop, Hn2, Hc2, Hcb2, Hl2, Hlb2, Hsr2, Hst2]
  icases Hloop with %hloop
  obtain ⟨hfperm, hzf⟩ := hloop
  -- the acked-or-zero multiset: the zeros are the voters that never reported
  have hpermv : (List.replicate zeros (0 : Int) ++ filled).Perm srt := by
    have h1 : (List.replicate zeros (0 : Int) ++ filled).Perm
        (List.replicate zeros (0 : Int) ++ (ks₀.map ack).reduceOption) :=
      List.Perm.append_left _ hfperm
    have hz : zeros = (ks₀.map ack).length - ((ks₀.map ack).reduceOption).length := by
      have hl := hfperm.length_eq
      simp only [List.length_map]
      omega
    have h2 := perm_replicate_reduceOption (0 : Int) (ks₀.map ack)
    rw [← hz] at h2
    refine (h1.trans h2).trans ?_
    rw [List.map_map]
    exact hperm
  go_walk 1
  -- the sort, `pos` and the readout
  go_walk_step (wp_ci_tail_all (na := na) (sra := sra) (sta := ba) (ra := ra)
    (filled := filled) (srt := srt) (zeros := zeros) (trail := trail)
    (cap := cap) (n := ks₀.length) (res := res) htypes hzf hcap hlen hsmall
    hpermv hsorted hnormsrt hget rfl rfl rfl)

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- **The `CommittedIndex` body at the EMPTY config** — `n == 0`, so
`majority.go` returns `math.MaxUint64` and nothing else in the body runs.
This is the joint-quorum identity element, and `IsCommittedIndex`'s first
disjunct; the `∀`-config statement quantifies over `c` with no
nonemptiness hypothesis, so this branch is part of the theorem. -/
theorem wp_committedIndex_body_empty {ca cba la lba ra : Addr}
    {cty lty : Option Ty} {aentries : Array (GoValue × GoValue)} {k}
    (_hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (_hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot [])⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩),
                   .int 18446744073709551615 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec committedIndexImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [committedIndexImpl_body_eq]
  go_walk with [committedIndexStmts_toList]
  go_walk_step (wp_ci_len (cba := cba) (cty := cty)
    (entries := cfgSnapshot []) (by decide) rfl) as [na]
  go_walk
  rw [ciEmptyIf_eq]
  go_walk with [show Int.ofNat (cfgSnapshot ([] : List Int)).size = 0 from rfl]
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (v := .int 0 .int) (done := [.int 0 .int])
    (happly := fun σ => by
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, applyStrictOp, valueEq, valueEqFuel,
        typeResolutionFuel, Bind.bind, Except.bind, pure, Except.pure]
      rfl))
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩),
                 .int 18446744073709551615 .uint64⟩)
    (fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 18446744073709551615
          = 18446744073709551615 from by decide]))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris

/-! ## The ENCODING BRIDGE

`EncodesConfig`/`EncodesAcked` (`Specs/AutomationTargets.lean`) say what a
heap map SNAPSHOT has to look like to MEAN a `(c, acked)` pair. The walk
consumes `cfgSnapshot ks₀` and a lookup answer per voter; these lemmas
are the translation. -/

/-- `uint64` normalization on the representable range. -/
theorem uint64_normalize_of_lt {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) :
    IntKind.uint64.normalize v = v := by
  have hmod : v % (2 : Int) ^ 64 = v := Int.emod_eq_of_lt h0 (by omega)
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, hmod, if_false,
    Bool.false_eq_true]

/-- The voter id an entry carries. -/
def keyOf (p : GoValue × GoValue) : Int :=
  match p.1 with
  | .int w _ => w
  | _ => 0

/-- **The config snapshot IS a `cfgSnapshot`.** An `EncodesConfig`
snapshot is literally the machine's picture of the voter list it carries
— and that list is a permutation of `c`, which is where the `Nodup`
hypothesis is used (a snapshot could otherwise repeat a key). -/
theorem encodesConfig_cfgSnapshot {ce : Array (GoValue × GoValue)} {c : List Nat}
    (hnd : c.Nodup) (h : EncodesConfig ce c) :
    ∃ ks₀ : List Int, ce = cfgSnapshot ks₀
      ∧ ks₀.Perm (c.map (fun v : Nat => (v : Int)))
      ∧ ∀ q ∈ ks₀, 0 ≤ q ∧ q < 2 ^ 64 := by
  obtain ⟨hin, hcov, hsize⟩ := h
  refine ⟨ce.toList.map keyOf, ?_, ?_, ?_⟩
  · -- every entry is `voterEntry` of its key
    have hmap : (ce.toList.map keyOf).map voterEntry = ce.toList := by
      rw [List.map_map]
      have heach : ∀ p ∈ ce.toList, (voterEntry ∘ keyOf) p = id p := by
        intro p hp
        obtain ⟨v, -, hk, hv, -⟩ := hin p (by simpa using hp)
        obtain ⟨k₁, k₂⟩ := p
        simp only at hk hv
        subst hk
        subst hv
        rfl
      rw [List.map_congr_left heach, List.map_id]
    rw [cfgSnapshot, hmap, Array.toArray_toList]
  · -- the ids are `c`'s, in some order
    refine (List.Subperm.perm_of_length_le ?_ ?_).symm
    · refine List.subperm_of_subset ?_ ?_
      · exact List.Pairwise.map (fun v : Nat => (v : Int))
          (fun a b hab hcon => hab (by exact_mod_cast hcon)) hnd
      · intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, hp, hpk⟩ := hcov v hv
        refine List.mem_map.2 ⟨p, by simpa using hp, ?_⟩
        obtain ⟨k₁, k₂⟩ := p
        simp only at hpk
        subst hpk
        rfl
    · simp only [List.length_map, Array.length_toList]
      omega
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    obtain ⟨v, hlt, hk, -, -⟩ := hin p (by simpa using hp)
    obtain ⟨k₁, k₂⟩ := p
    simp only at hk
    subst hk
    refine ⟨by simp [keyOf], ?_⟩
    show keyOf ((GoValue.int (v : Int) .uint64), k₂) < 2 ^ 64
    simp only [keyOf]
    exact_mod_cast hlt

/-- The machine-side acked function an `EncodesAcked` snapshot denotes. -/
def ackOf (acked : Nat → Option Nat) (q : Int) : Option Int :=
  (acked q.toNat).map (fun i : Nat => (i : Int))

/-- **The `AckedIndexer` lookup, from the encoding.** For every voter id
the snapshot answers exactly Go's comma-ok pair for `acked` — the value
and `true` when the voter has reported, the `Index` zero and `false` when
it has not. -/
theorem encodesAcked_lookup {ae : Array (GoValue × GoValue)}
    {acked : Nat → Option Nat} (h : EncodesAcked ae acked)
    {lba : Addr} {lty : Option Ty} {q : Int} (hq0 : 0 ≤ q) (hq : q < 2 ^ 64)
    (σ : ExecState) (htypes : σ.types = quorumLowered.typeDefs.toList)
    (hl : Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData ae⟩) :
    mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
        (.defined ⟨"main.Index"⟩)
      = .ok (.int ((ackOf acked q).getD 0) .uint64, (ackOf acked q).isSome) := by
  obtain ⟨hin, hcov⟩ := h
  have hkeys : ∀ p ∈ ae.toList, ∃ w : Int, p.1 = .int w .uint64 := by
    intro p hp
    obtain ⟨v, i, -, hpe, -⟩ := hin p (by simpa using hp)
    exact ⟨(v : Int), by rw [hpe]⟩
  cases hack : acked q.toNat with
  | none =>
    have hmiss : ∀ p ∈ ae.toList, ∃ w : Int, p.1 = .int w .uint64 ∧ w ≠ q := by
      intro p hp
      obtain ⟨v, i, -, hpe, hav⟩ := hin p (by simpa using hp)
      refine ⟨(v : Int), by rw [hpe], ?_⟩
      intro hcon
      have hqv : q.toNat = v := by omega
      rw [hqv, hav] at hack
      cases hack
    have hdef : defaultValue σ (.defined ⟨"main.Index"⟩) = .ok (.int 0 .uint64) := by
      rw [execState_pin_eq (T := quorumLowered.typeDefs.toList) htypes
        (rfl (a := σ.functions)) (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index]
    rw [mapLookupValue_miss (kind := .uint64) hl hdef hmiss]
    simp [ackOf, hack]
  | some i =>
    have hqq : ((q.toNat : Nat) : Int) = q := by omega
    have hmem0 := hcov q.toNat i hack
    have hfun : ∀ p ∈ ae.toList, p.1 = .int q .uint64 →
        p.2 = .int (i : Int) .uint64 := by
      intro p hp hpk
      obtain ⟨v, j, -, hpe, hav⟩ := hin p (by simpa using hp)
      rw [hpe] at hpk
      have hv : (v : Int) = q := by
        injection hpk with h1 _
      have hqv : q.toNat = v := by omega
      rw [hqv, hav] at hack
      injection hack with hji
      rw [hpe, hji]
    have hmem : ∃ p ∈ ae.toList, p.1 = .int q .uint64 := by
      refine ⟨(.int ((q.toNat : Nat) : Int) .uint64, .int (i : Int) .uint64),
        by simpa using hmem0, ?_⟩
      show GoValue.int ((q.toNat : Nat) : Int) .uint64 = .int q .uint64
      rw [hqq]
    rw [mapLookupValue_hit (kind := .uint64) hl hkeys hfun hmem]
    simp [ackOf, hack]

end GoLean.Quorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum GoLean.Iris

/-- **The `CommittedIndex` CALLSITE at an arbitrary config** — the
method called on a heap-carried receiver and a heap-carried
`AckedIndexer`, from the caller's environment, with the answer delivered
into the caller's `uint64` cell by the machine's own frame-exit protocol.
`hcase` is the two-branch answer: the empty config returns
`math.MaxUint64`, a nonempty one the `(n/2+1)`-th largest acked-or-zero
index. -/
theorem wp_committedIndexCall_all {ca cba la lba ta : Addr}
    {cty lty : Option Ty} {ks₀ srt : List Int} {ack : Int → Option Int}
    {aentries : Array (GoValue × GoValue)} {res : Int} {w : GoValue} {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hsmall : ks₀.length < 2 ^ 63)
    (hnormk : ∀ q ∈ ks₀, IntKind.uint64.normalize q = q)
    (hnormv : ∀ q ∈ ks₀, ∀ v : Int, ack q = some v →
      IntKind.uint64.normalize v = v)
    (hlook : ∀ q ∈ ks₀, ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int ((ack q).getD 0) .uint64, (ack q).isSome))
    (hcase : (ks₀ = [] ∧ res = 18446744073709551615)
      ∨ (ks₀ ≠ [] ∧ (ks₀.map (fun q => (ack q).getD 0)).Perm srt
          ∧ srt.Pairwise (· ≤ ·)
          ∧ (∀ v ∈ srt, IntKind.uint64.normalize v = v)
          ∧ srt[ks₀.length - (ks₀.length / 2 + 1)]? = some res))
    (hres : LocalEnv.lookup env "$callres" = some (.base ta))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int .uint64), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int res .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
              #[.var "c", .var "l"]) env k) @ s ; E {{ Φ }} := by
  have hresnorm : IntKind.uint64.normalize res = res := by
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, -, hn, hg⟩
    · decide
    · refine hn res ?_
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hg
      exact he ▸ List.getElem_mem hlt
  iintro ⟨Hc, Hcb, Hl, Hlb, Ht, Hcont⟩
  go_walk
  go_walk_step (wp_call_enter₂₁ (func := QuorumPin.committedIndexImpl)
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
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])) as [a₀, a₁, a₂]
  -- the body, in whichever of the two shapes the config has
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hne, hperm, hsorted, hnormsrt, hget⟩
  · go_walk_step (wp_committedIndex_body_empty (ca := a₀) (cba := cba)
      (la := a₁) (lba := lba) (ra := a₂) (cty := cty) (lty := lty)
      (aentries := aentries) hprog hmeths htypes)
    go_walk_step (wp_frame_return₁ (ta := ta) (ra := a₂)
      (rcell := ⟨some (.defined ⟨"main.Index"⟩),
                 .int 18446744073709551615 .uint64⟩)
      (tcell := ⟨some (.int .uint64), w⟩)
      (tcell' := ⟨some (.int .uint64), .int 18446744073709551615 .uint64⟩)
      (hstore := fun σ _ht hlk => by
        have h := storeLoc_int_any (mkind := .uint64) hlk 18446744073709551615
        rw [show IntKind.uint64.normalize 18446744073709551615
          = 18446744073709551615 from by decide] at h
        exact h))
    go_walk_finish Hcont
  · go_walk_step (wp_committedIndex_body_all (ca := a₀) (cba := cba)
      (la := a₁) (lba := lba) (ra := a₂) (cty := cty) (lty := lty)
      (ks₀ := ks₀) (srt := srt) (ack := ack) (aentries := aentries) (res := res)
      hprog hmeths htypes hne hsmall hnormk hnormv hlook hperm hsorted
      hnormsrt hget)
    go_walk_step (wp_frame_return₁ (ta := ta) (ra := a₂)
      (rcell := ⟨some (.defined ⟨"main.Index"⟩), .int res .uint64⟩)
      (tcell := ⟨some (.int .uint64), w⟩)
      (tcell' := ⟨some (.int .uint64), .int res .uint64⟩)
      (hstore := fun σ _ht hlk => by
        have h := storeLoc_int_any (mkind := .uint64) hlk res
        rw [hresnorm] at h
        exact h))
    go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris

/-! ## The MATH bridge: the machine's sorted window is the reference's -/

/-- Every acked value an `EncodesAcked` snapshot can deliver is a
representable `uint64` — the snapshot carries the entry, and the
snapshot's entries are bounded. -/
theorem encodesAcked_lt {ae : Array (GoValue × GoValue)}
    {acked : Nat → Option Nat} (h : EncodesAcked ae acked) :
    ∀ v i : Nat, acked v = some i → i < 2 ^ 64 := by
  obtain ⟨hin, hcov⟩ := h
  intro v i hvi
  obtain ⟨v', i', hlt, hpe, -⟩ := hin _ (hcov v i hvi)
  have : i' = i := by
    injection hpe with h1 h2
    injection h2 with h2 _
    omega
  omega

/-- The sorted acked-or-zero window, at the machine's element type: the
reference's `sortAsc` image. -/
def sortedAcked (c : List Nat) (acked : Nat → Option Nat) : List Int :=
  (sortAsc (c.map (ackedOrZero acked))).map (fun v : Nat => (v : Int))

theorem sortedAcked_sorted (c : List Nat) (acked : Nat → Option Nat) :
    (sortedAcked c acked).Pairwise (· ≤ ·) := by
  rw [sortedAcked, List.pairwise_map]
  exact (sortAsc_sorted _).imp (by intro a b hab; exact_mod_cast hab)

theorem sortedAcked_length (c : List Nat) (acked : Nat → Option Nat) :
    (sortedAcked c acked).length = c.length := by
  simp [sortedAcked]

/-- The window's elements are representable, so they ride through the
machine's `uint64` normalization unchanged. -/
theorem sortedAcked_norm {ae : Array (GoValue × GoValue)} {c : List Nat}
    {acked : Nat → Option Nat} (h : EncodesAcked ae acked) :
    ∀ v ∈ sortedAcked c acked, IntKind.uint64.normalize v = v := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
  have hxm : x ∈ c.map (ackedOrZero acked) := (sortAsc_perm _).mem_iff.mp hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hxm
  have hlt : ackedOrZero acked u < 2 ^ 64 := by
    rw [ackedOrZero]
    cases hau : acked u with
    | none => simp
    | some i =>
      simp only [Option.getD_some]
      exact encodesAcked_lt h u i hau
  exact uint64_normalize_of_lt (by omega) (by exact_mod_cast hlt)

/-- **The machine's fill multiset IS the reference's**: the acked-or-zero
values of the snapshot's voters, permuted into the reference's sorted
order. -/
theorem sortedAcked_perm {ks₀ : List Int} {c : List Nat}
    {acked : Nat → Option Nat}
    (hks : ks₀.Perm (c.map (fun v : Nat => (v : Int)))) :
    (ks₀.map (fun q => (ackOf acked q).getD 0)).Perm (sortedAcked c acked) := by
  refine ((hks.map _).trans ?_)
  rw [List.map_map, sortedAcked]
  have hfun : (c.map ((fun q => (ackOf acked q).getD 0)
      ∘ (fun v : Nat => (v : Int))))
      = (c.map (ackedOrZero acked)).map (fun v : Nat => (v : Int)) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro v hv
    simp only [Function.comp_apply, ackOf, ackedOrZero, Int.toNat_natCast]
    cases acked v <;> simp
  rw [hfun]
  exact ((sortAsc_perm (c.map (ackedOrZero acked))).symm.map _)

/-- ... and the element the readout picks is the reference's answer. -/
theorem sortedAcked_get {c : List Nat} {acked : Nat → Option Nat}
    (hne : c ≠ []) :
    (sortedAcked c acked)[c.length - (c.length / 2 + 1)]?
      = some ((committedIndexRef c acked : Nat) : Int) := by
  have hlen : 0 < c.length := List.length_pos_iff.mpr hne
  have hlt : c.length - (c.length / 2 + 1) < (sortAsc (c.map (ackedOrZero acked))).length := by
    simp only [sortAsc_length, List.length_map]
    omega
  rw [sortedAcked, List.getElem?_map, List.getElem?_eq_getElem hlt]
  refine congrArg some (congrArg _ ?_)
  cases c with
  | nil => exact absurd rfl hne
  | cons a t =>
    rw [committedIndexRef]
    · rw [List.getElem_eq_getD 0]
      simp only [quorumSize]
    · simp

end GoLean.Quorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum GoLean.Iris

/-! ## THE ∀-CONFIG THEOREM

`committedIndexAllConfigs_statement` (`Specs/AutomationTargets.lean`,
phase 0 of this arc) is a `def … : Prop` written before the machinery;
this is its discharge. -/

/-- **THE ∀-CONFIG THEOREM.** For EVERY voter list `c`, EVERY acked map
`acked`, and every heap snapshot pair encoding them, the pinned lowering
of the real etcd-io/raft `main.MajorityConfig.CommittedIndex` — called on
that receiver and that `AckedIndexer` through the caller's environment —
delivers a value satisfying the declarative quorum spec
`IsCommittedIndex`, at `GoSpec` strength (triple + progress, any
admissible heap, any frame).

The per-program obligation is the WP walk `wp_committedIndexCall_all`,
whose voter range goes through `Laws/Range.wp_map_iter_inv` (one generic
iteration and a permutation invariant, not the `n!` iteration orders),
whose fit test covers BOTH branches, and whose `slices.Sort` is computed
at a symbolic length by induction over the machine's own loops. The
answer is identified with the reference `committedIndexRef` by
sorted-permutation uniqueness, and the reference meets the declarative
spec by `QuorumRefSpec.committedIndexRef_meets_spec_of_any`. -/
theorem committedIndexAllConfigs : committedIndexAllConfigs_statement := by
  intro c acked ce ae cty lty ca cba la lba ra w hnd hsmall hce hae _hnodup
  obtain ⟨ks₀, rfl, hks, hrange⟩ := encodesConfig_cfgSnapshot hnd hce
  have hkslen : ks₀.length = c.length := by
    have h := hks.length_eq
    simpa using h
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed, configPre]
  iintro ⟨Hr, Hc, Hcb, Hl, Hlb⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_committedIndexCall_all
    (ca := ⟨ca⟩) (cba := ⟨cba⟩) (la := ⟨la⟩) (lba := ⟨lba⟩) (ta := ⟨ra⟩)
    (cty := cty) (lty := lty) (ks₀ := ks₀) (srt := sortedAcked c acked)
    (ack := ackOf acked) (aentries := ae)
    (res := if c = [] then 18446744073709551615
            else ((committedIndexRef c acked : Nat) : Int))
    (w := w) hprog hmeths htypes (by omega)
    (fun q hq => by
      obtain ⟨h0, h1⟩ := hrange q hq
      exact uint64_normalize_of_lt h0 h1)
    (fun q hq v hv => by
      obtain ⟨h0, h1⟩ := hrange q hq
      simp only [ackOf, Option.map_eq_some_iff] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact uint64_normalize_of_lt (by omega)
        (by exact_mod_cast encodesAcked_lt hae _ i hi))
    (fun q hq σ ht hlk => by
      obtain ⟨h0, h1⟩ := hrange q hq
      exact encodesAcked_lookup hae h0 h1 σ (ht.trans htypes) hlk)
    (by
      by_cases hc : c = []
      · left
        refine ⟨?_, by rw [if_pos hc]⟩
        have : ks₀.length = 0 := by rw [hkslen, hc]; rfl
        exact List.length_eq_zero_iff.mp this
      · right
        refine ⟨?_, ?_, sortedAcked_sorted c acked, sortedAcked_norm hae, ?_⟩
        · intro hcon
          exact hc (by
            have : c.length = 0 := by rw [← hkslen, hcon]; rfl
            exact List.length_eq_zero_iff.mp this)
        · exact sortedAcked_perm hks
        · rw [if_neg hc, hkslen]
          exact sortedAcked_get hc)
    rfl rfl rfl)
  isplitl [Hc]
  · iexact Hc
  isplitl [Hcb]
  · iexact Hcb
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlb]
  · iexact Hlb
  isplitl [Hr]
  · iexact Hr
  iintro Hout
  iapply (wp_value' (v := ()))
  iexists (if c = [] then (18446744073709551615 : Int)
           else ((committedIndexRef c acked : Nat) : Int))
  isplitl [Hout]
  · iexact Hout
  · ipureintro
    by_cases hc : c = []
    · refine ⟨uint64Max, by rw [if_pos hc]; rfl, ?_⟩
      rw [hc]
      exact Or.inl ⟨rfl, rfl⟩
    · refine ⟨committedIndexRef c acked, by rw [if_neg hc], ?_⟩
      exact committedIndexRef_meets_spec_of_any c acked

/-! ### The first-order readout, and the negative twin

The ∀-config theorem is a separation-logic statement about a method
called with heap-carried inputs; the corpus-facing claim is first-order
("this run leaves 6 at this address"). The pair below reads the triple
out at the 3-voter encoding — a genuine INSTANCE of the ∀-config
theorem, not a re-proof — and refutes `12` from it. Both are
run-CONDITIONED, for the reason recorded once for the whole family
(`quorumOneKnownNotEleven`): a `GoTriple` says nothing about a program
that fails to terminate, so the unconditional `¬ GoSpec` form demands
EXHIBITING a terminating run (a kernel evaluation of the interpreter over
the pinned program), which stays owed. -/

/- `allOut`/`allOutEnv` (the ∀-config readout's seeded state) moved to
`Specs/Statements.lean` — the Iris-free statement layer (comparator-judge
sprint, 2026-08-02): the readout THEOREM statements reference them. -/

theorem encodesAcked_three : EncodesAcked threeAckedEntries ackedThreeAll := by
  constructor
  · intro p hp
    have hp' : p = ((GoValue.int 1 .uint64), (GoValue.int 12 .uint64))
        ∨ p = ((GoValue.int 2 .uint64), (GoValue.int 5 .uint64))
        ∨ p = ((GoValue.int 3 .uint64), (GoValue.int 6 .uint64)) := by
      simpa [threeAckedEntries] using hp
    rcases hp' with rfl | rfl | rfl
    · exact ⟨1, 12, by omega, rfl, rfl⟩
    · exact ⟨2, 5, by omega, rfl, rfl⟩
    · exact ⟨3, 6, by omega, rfl, rfl⟩
  · intro v i hvi
    have hv : (v = 1 ∧ i = 12) ∨ (v = 2 ∧ i = 5) ∨ (v = 3 ∧ i = 6) := by
      by_cases h1 : v = 1
      · subst h1; left; exact ⟨rfl, by simpa [ackedThreeAll] using hvi.symm⟩
      · by_cases h2 : v = 2
        · subst h2; right; left
          exact ⟨rfl, by simpa [ackedThreeAll] using hvi.symm⟩
        · by_cases h3 : v = 3
          · subst h3; right; right
            exact ⟨rfl, by simpa [ackedThreeAll] using hvi.symm⟩
          · simp [ackedThreeAll, h1, h2, h3] at hvi
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact Array.mem_def.mpr (by simp [threeAckedEntries])

/-- **The first-order readout of the ∀-CONFIG theorem**, at the 3-voter
encoding: every terminating run of `$callres = c.CommittedIndex(l)` from
the seeded five-cell state leaves `uint64(6)` at base address 0. An
INSTANCE of `committedIndexAllConfigs` — nothing about the walk is
re-proven here — which is also its non-vacuity witness: an admissible
initial state for the `∀`-config precondition exists. -/
theorem committedIndexAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) := by
  have htriple := (committedIndexAllConfigs [1, 2, 3] ackedThreeAll
    threeConfigEntries threeAckedEntries none none 1 2 3 4 0
    (.int 0 .uint64) (by decide) (by decide) encodesConfig_three
    encodesAcked_three (by decide)).1
  have hres := htriple allOut 5 (heapletOf allOut) (∅ : Heaplet)
    { disj := fun k => .inr (by
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
      sat_pre := by
        show sat (heapletOf allOut) (.sep (.pointsTo 0 _) (configPre 1 2 3 4 none none _ _))
        simp only [configPre]
        refine sat_sep_insert ?_ (sat_sep_insert ?_ (sat_sep_insert ?_
          (sat_sep_insert ?_ rfl)))
        · rfl
        · rfl
        · rfl
        · rfl
      wf := by decide +kernel }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨r, hr, hspec⟩ := hp2
  obtain ⟨hnr, hrsat⟩ := hr
  have hr6 : r = 6 := by
    have := (GoLean.Quorum.isCommittedIndex_iff [1, 2, 3] ackedThreeAll r).1 hrsat
    rw [this]
    rfl
  subst hr6
  subst hnr
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 6 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have hfin := hsub 0 ⟨some (.int .uint64), .int 6 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hfin
  exact loadLoc_base_of_lookup hfin

/-- **The ∀-config negative twin** — no terminating run leaves `12`, the
LARGEST acked index (the answer a "returns something a voter acked" bug
would give). Two lines from the readout, exactly as
`quorumThreeAllNotTwelve` is from `quorumThreeAllReturnsSix`. -/
theorem committedIndexAllNotTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) := by
  intro h12
  have h6 := committedIndexAllReturnsSix fuel ch σf ch' hrun
  have hcon := h6.symm.trans h12
  injection hcon with hval
  injection hval with hn _
  exact absurd hn (by decide)

/-- **The refutation, at the level the ∀-config statement speaks**: the
postcondition it delivers pins the answer UNIQUELY, so no wrong value can
satisfy it at ANY config — the `∀`-quantified form of the negative twin,
and the reason the concrete twin above is a corollary rather than a
separate obligation. (`isCommittedIndex_iff` is the characterization
mechanized in `Specs/QuorumRefSpec.lean`.) -/
theorem committedIndexAll_refutes_wrong (c : List Nat)
    (acked : Nat → Option Nat) (r : Nat) (hne : r ≠ committedIndexRef c acked) :
    ¬ GoLean.Quorum.IsCommittedIndex c acked r :=
  fun h => hne ((GoLean.Quorum.isCommittedIndex_iff c acked r).1 h)

end GoLean.Surface
