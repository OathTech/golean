import GoLeanProofs.Specs.Raft.SpanS23Walk3

/-!
# The apply walk, part 4 (A4d-SM2): the byIndex block

The comma-ok slot lookup, the S2 check (short-circuit guard, the
fire branch's five `utoa` units + the 13-part concat + `viol`), and
the first-insert — the walk's three exit-unified subcases, assembled
in `s23_byidx_seg` with the model readouts (`s2Hit`'s decision and
the append-if-absent) literally in the machine state.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE
  stepFn_rhs_apply)
open GoLean.RaftSeam.DriverNet (applyStrictOp_fieldGet)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. Small model helpers -/

theorem bget?_mem {kvs : List (Int × SlotA)} {w : Int} {s : SlotA}
    (h : bget? kvs w = some s) : (w, s) ∈ kvs := by
  induction kvs with
  | nil => cases h
  | cons p rest ih =>
    obtain ⟨k, s'⟩ := p
    rw [show bget? ((k, s') :: rest) w
      = (if k = w then some s' else bget? rest w) from rfl] at h
    by_cases hk : k = w
    · rw [if_pos hk] at h
      cases h
      subst hk
      exact List.mem_cons_self ..
    · rw [if_neg hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ## 2. The comma-ok lookup segment (26 steps) -/

section Lookup

variable {env6 : LocalEnv} {KK : Cont} {na₀ tw bm : Nat}
  {nodesV netV liveV pendV drvV hlV : GoValue} {lm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {bkvs : List (Int × SlotA)} {ixN : Nat}

/-- The env after `s`/`ok` are declared. -/
abbrev envSO (env6 : LocalEnv) (na : Nat) : LocalEnv :=
  LocalEnv.declare
    (LocalEnv.declare (([] : Scope) :: env6) "s" (.base ⟨na⟩))
    "ok" (.base ⟨na + 1⟩)

/-- **The comma-ok slot lookup** (26 steps): `s, ok :=
t.byIndex[idx]` — `s` holds the first-match slot (the slot ZERO on a
miss), `ok` the scan flag, landing on the `if ok` dispatch. -/
theorem s23_byidx_lookup_seg
    (henvT : LocalEnv.lookup env6 "t" = some (.base ⟨na₀⟩))
    (henvI : LocalEnv.lookup env6 "idx" = some (.base ⟨na₀ + 3⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (htP : Heap.lookup σ.heap (.base ⟨na₀⟩) = some (tParA tw))
    (hIc : Heap.lookup σ.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm
          (.map ⟨some (.base ⟨bm⟩)⟩) cc cm w pendV drvV sq tr hlV))
    (hBm : Heap.lookup σ.heap (.base ⟨bm⟩)
      = some ⟨none, .mapData (toEntriesB bkvs)⟩)
    (hix : ixN < 2 ^ 64)
    (hsl : ∀ p ∈ bkvs, p.2.1 < 2 ^ 64 ∧ p.2.2.2 < 2 ^ 64) :
    stepFnIter 26 σ
        (.exec byIdxBlock env6 (.seq [] env6 KK)) ch
      = .ok (.exec (.ifThenElse (.var "ok")
            (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)]))
          (envSO env6 σ.nextAddr)
          (.seq [] (envSO env6 σ.nextAddr) (.seq [] env6 KK)),
        { σ with heap := Heap.set (Heap.set (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), .struct tidS (slotFs 0 GoString.empty 0)⟩) (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool false⟩) (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), slotV ((bget? bkvs (ixN : Int)).getD zeroSlot)⟩) (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool (bIdxOf? bkvs (ixN : Int)).isSome⟩, nextAddr := σ.nextAddr + 2 }, ch) := by
  have htypes : σ.types = twinTypes := hag.1
  -- L1: block+pop, splice+pop (4)
  let env2 : LocalEnv := ([] : Scope) :: env6
  let ifStmt : Stmt := .ifThenElse (.var "ok")
    (.block #[] #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
    (.block #[] #[.mapAssign byIndexE (.var "idx")
      (.structLit (.defined tidS) #[.var "trm", .var "data", idE])
      (.int .uint64) (.defined tidS)])
  have hL1 : stepFnIter 2 σ
      (.exec byIdxBlock env6 (.seq [] env6 KK)) ch
      = .ok (.exec (.seqn
          #[.initialization { id := "s", typ := .defined tidS },
            .initialization { id := "ok", typ := .bool },
            .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
              (.int .uint64) (.defined tidS)]) env2
          (.seq [ifStmt] env2 (.seq [] env6 KK)), σ, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  have hL2 : stepFnIter 2 σ (.exec (.seqn
      #[.initialization { id := "s", typ := .defined tidS },
        .initialization { id := "ok", typ := .bool },
        .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
          (.int .uint64) (.defined tidS)]) env2
      (.seq [ifStmt] env2 (.seq [] env6 KK))) ch
      = .ok (.exec (.initialization { id := "s", typ := .defined tidS })
          env2
          (.seq [.initialization { id := "ok", typ := .bool },
            .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
              (.int .uint64) (.defined tidS), ifStmt] env2
            (.seq [] env6 KK)), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.initialization { id := "s", typ := .defined tidS },
        .initialization { id := "ok", typ := .bool },
        .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
          (.int .uint64) (.defined tidS)]) rfl
  -- L3-L6: the two inits + pops (4)
  let env2a : LocalEnv :=
    LocalEnv.declare env2 "s" (.base ⟨σ.nextAddr⟩)
  let σS : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), .struct tidS (slotFs 0 GoString.empty 0)⟩, nextAddr := σ.nextAddr + 1 }
  have hL3 : stepFnIter 1 σ
      (.exec (.initialization { id := "s", typ := .defined tidS })
        env2
        (.seq [.initialization { id := "ok", typ := .bool },
          .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
            (.int .uint64) (.defined tidS), ifStmt] env2
          (.seq [] env6 KK))) ch
      = .ok (.next (.seq [.initialization { id := "ok", typ := .bool },
          .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
            (.int .uint64) (.defined tidS), ifStmt] env2a
          (.seq [] env6 KK)), σS, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_slot htypes))
  have hL4 : stepFnIter 1 σS (.next (.seq
      [.initialization { id := "ok", typ := .bool },
        .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
          (.int .uint64) (.defined tidS), ifStmt] env2a
      (.seq [] env6 KK))) ch
      = .ok (.exec (.initialization { id := "ok", typ := .bool })
          env2a
          (.seq [.mapLookup (.var "s") (.var "ok") byIndexE
            (.var "idx") (.int .uint64) (.defined tidS), ifStmt]
            env2a (.seq [] env6 KK)), σS, ch) :=
    stepFnIter_one stepFn_seq_pop
  let σO : ExecState := { σS with heap := Heap.set σS.heap (.base ⟨σS.nextAddr⟩) ⟨some .bool, .bool false⟩, nextAddr := σS.nextAddr + 1 }
  have hL5 : stepFnIter 1 σS
      (.exec (.initialization { id := "ok", typ := .bool }) env2a
        (.seq [.mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
          (.int .uint64) (.defined tidS), ifStmt] env2a
          (.seq [] env6 KK))) ch
      = .ok (.next (.seq [.mapLookup (.var "s") (.var "ok") byIndexE
          (.var "idx") (.int .uint64) (.defined tidS), ifStmt]
          (envSO env6 σ.nextAddr) (.seq [] env6 KK)), σO, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_bool))
  have hL6 : stepFnIter 1 σO (.next (.seq
      [.mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
        (.int .uint64) (.defined tidS), ifStmt]
      (envSO env6 σ.nextAddr) (.seq [] env6 KK))) ch
      = .ok (.exec (.mapLookup (.var "s") (.var "ok") byIndexE
          (.var "idx") (.int .uint64) (.defined tidS))
          (envSO env6 σ.nextAddr)
          (.seq [ifStmt] (envSO env6 σ.nextAddr) (.seq [] env6 KK)),
        σO, ch) :=
    stepFnIter_one stepFn_seq_pop
  -- L7-L11: mapLookup open + the two refs + the rhs entry (5)
  let KR : Cont := .rhsK (.mapLookup (.int .uint64) (.defined tidS))
    [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
      .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
    [] [.var "idx"] (.seqn #[]) (envSO env6 σ.nextAddr)
    (.seq [ifStmt] (envSO env6 σ.nextAddr) (.seq [] env6 KK))
  have hL7 : stepFnIter 5 σO
      (.exec (.mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
        (.int .uint64) (.defined tidS)) (envSO env6 σ.nextAddr)
        (.seq [ifStmt] (envSO env6 σ.nextAddr) (.seq [] env6 KK))) ch
      = .ok (.evalE byIndexE (envSO env6 σ.nextAddr) KR, σO, ch) := by
    with_unfolding_all rfl
  -- L12: the byIndex read (5)
  have henvTso : LocalEnv.lookup (envSO env6 σ.nextAddr) "t"
      = some (.base ⟨na₀⟩) := by
    show LocalEnv.lookup ([("ok", Loc.base ⟨σ.nextAddr + 1⟩),
      ("s", Loc.base ⟨σ.nextAddr⟩)] :: env6) "t" = _
    rw [env_lookup_skip rfl]
    exact henvT
  have htPO : Heap.lookup σO.heap (.base ⟨na₀⟩)
      = some (tParA tw) := by
    have hna : na₀ < σ.nextAddr := by
      rcases Nat.lt_or_ge na₀ σ.nextAddr with h | h
      · exact h
      · rw [hfr na₀ h] at htP; cases htP
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨na₀⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ na₀),
      lookup_set_other (by omega : σ.nextAddr ≠ na₀)]
    exact htP
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hTwO : Heap.lookup σO.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm
          (.map ⟨some (.base ⟨bm⟩)⟩) cc cm w pendV drvV sq tr hlV)
      := by
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ tw),
      lookup_set_other (by omega : σ.nextAddr ≠ tw)]
    exact hTw
  have hL12 : stepFnIter 5 σO
      (.evalE byIndexE (envSO env6 σ.nextAddr) KR) ch
      = .ok (.retV (.map ⟨some (.base ⟨bm⟩)⟩) KR, σO, ch) :=
    read_field_seg (henv := henvTso) (hp := htPO) (hw := hTwO)
      (hf := rfl)

  -- L13: the idx read (2)
  have henvIso : LocalEnv.lookup (envSO env6 σ.nextAddr) "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    show LocalEnv.lookup ([("ok", Loc.base ⟨σ.nextAddr + 1⟩),
      ("s", Loc.base ⟨σ.nextAddr⟩)] :: env6) "idx" = _
    rw [env_lookup_skip rfl]
    exact henvI
  have hIcO : Heap.lookup σO.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩ := by
    have hna : na₀ + 3 < σ.nextAddr := by
      rcases Nat.lt_or_ge (na₀ + 3) σ.nextAddr with h | h
      · exact h
      · rw [hfr (na₀ + 3) h] at hIc; cases hIc
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨na₀ + 3⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ na₀ + 3),
      lookup_set_other (by omega : σ.nextAddr ≠ na₀ + 3)]
    exact hIc
  have hL13a : stepFnIter 1 σO
      (.retV (.map ⟨some (.base ⟨bm⟩)⟩) KR) ch
      = .ok (.evalE (.var "idx") (envSO env6 σ.nextAddr)
          (.rhsK (.mapLookup (.int .uint64) (.defined tidS))
            [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
              .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
            [.map ⟨some (.base ⟨bm⟩)⟩] [] (.seqn #[])
            (envSO env6 σ.nextAddr)
            (.seq [ifStmt] (envSO env6 σ.nextAddr)
              (.seq [] env6 KK))), σO, ch) := by
    with_unfolding_all rfl
  have hL13b : stepFnIter 1 σO
      (.evalE (.var "idx") (envSO env6 σ.nextAddr)
        (.rhsK (.mapLookup (.int .uint64) (.defined tidS))
          [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
            .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
          [.map ⟨some (.base ⟨bm⟩)⟩] [] (.seqn #[])
          (envSO env6 σ.nextAddr)
          (.seq [ifStmt] (envSO env6 σ.nextAddr)
            (.seq [] env6 KK)))) ch
      = .ok (.retV (.int (ixN : Int) .uint64)
          (.rhsK (.mapLookup (.int .uint64) (.defined tidS))
            [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
              .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
            [.map ⟨some (.base ⟨bm⟩)⟩] [] (.seqn #[])
            (envSO env6 σ.nextAddr)
            (.seq [ifStmt] (envSO env6 σ.nextAddr)
              (.seq [] env6 KK))), σO, ch) :=
    stepFnIter_one (stepFn_var (henv := henvIso) (hlook := hIcO))
  -- L14: the comma-ok apply (1)
  have hBmO : Heap.lookup σO.heap (.base ⟨bm⟩)
      = some ⟨none, .mapData (toEntriesB bkvs)⟩ := by
    have hna : bm < σ.nextAddr := by
      rcases Nat.lt_or_ge bm σ.nextAddr with h | h
      · exact h
      · rw [hfr bm h] at hBm; cases hBm
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨bm⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ bm),
      lookup_set_other (by omega : σ.nextAddr ≠ bm)]
    exact hBm
  have hL14 : stepFnIter 1 σO (.retV (.int (ixN : Int) .uint64)
      (.rhsK (.mapLookup (.int .uint64) (.defined tidS))
        [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
          .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
        [.map ⟨some (.base ⟨bm⟩)⟩] [] (.seqn #[])
        (envSO env6 σ.nextAddr)
        (.seq [ifStmt] (envSO env6 σ.nextAddr)
          (.seq [] env6 KK)))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
            .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
          [slotV ((bget? bkvs (ixN : Int)).getD zeroSlot),
            .bool (bIdxOf? bkvs (ixN : Int)).isSome] (.seqn #[])
          (envSO env6 σ.nextAddr)
          (.seq [ifStmt] (envSO env6 σ.nextAddr)
            (.seq [] env6 KK))), σO, ch) :=
    stepFnIter_one (stepFn_rhs_apply
      (h := applyRhsOp_mapLookup_toEntriesB htypes hBmO hix))
  -- L15/16: the two stores (2)
  have hnormS : normalizeValueForTy σO (.defined tidS)
      (slotV ((bget? bkvs (ixN : Int)).getD zeroSlot))
      = .ok (slotV ((bget? bkvs (ixN : Int)).getD zeroSlot)) := by
    cases hb : bget? bkvs (ixN : Int) with
    | none =>
      show normalizeValueForTy σO (.defined tidS)
          (.struct tidS (slotFs ((0 : Nat) : Int) GoString.empty
            ((0 : Nat) : Int)))
        = .ok (.struct tidS (slotFs ((0 : Nat) : Int) GoString.empty
            ((0 : Nat) : Int)))
      exact normalize_slotFs (σ := σO) (t := ((0 : Nat) : Int))
        (d := GoString.empty) (n := ((0 : Nat) : Int)) htypes
        (by omega) (by omega) (by omega) (by omega)
    | some sl =>
      have hm : sl.1 < 2 ^ 64 ∧ sl.2.2 < 2 ^ 64 :=
        hsl _ (bget?_mem hb)
      show normalizeValueForTy σO (.defined tidS)
          (.struct tidS (slotFs (sl.1 : Int) sl.2.1 (sl.2.2 : Int)))
        = .ok (.struct tidS (slotFs (sl.1 : Int) sl.2.1
            (sl.2.2 : Int)))
      exact normalize_slotFs (σ := σO) (t := (sl.1 : Int)) (d := sl.2.1)
        (n := (sl.2.2 : Int)) htypes
        (by omega) (by omega) (by omega) (by omega)
  let σP : ExecState := { σO with heap := Heap.set σO.heap (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), slotV ((bget? bkvs (ixN : Int)).getD zeroSlot)⟩ }
  have hsCellO : Heap.lookup σO.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.defined tidS),
          .struct tidS (slotFs 0 GoString.empty 0)⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hL15 : stepFnIter 1 σO (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
        .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
      [slotV ((bget? bkvs (ixN : Int)).getD zeroSlot),
        .bool (bIdxOf? bkvs (ixN : Int)).isSome] (.seqn #[])
      (envSO env6 σ.nextAddr)
      (.seq [ifStmt] (envSO env6 σ.nextAddr)
        (.seq [] env6 KK)))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
          [.bool (bIdxOf? bkvs (ixN : Int)).isSome] (.seqn #[])
          (envSO env6 σ.nextAddr)
          (.seq [ifStmt] (envSO env6 σ.nextAddr)
            (.seq [] env6 KK))), σP, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .defined tidS)
        (old := .struct tidS (slotFs 0 GoString.empty 0))
        (hlook := hsCellO) (hnorm := hnormS)))
  let σQ : ExecState := { σP with heap := Heap.set σP.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool (bIdxOf? bkvs (ixN : Int)).isSome⟩ }
  have hokCellP : Heap.lookup σP.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some .bool, .bool false⟩ := by
    show Heap.lookup (Heap.set σO.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ σ.nextAddr + 1)]
    exact lookup_set_self
  have hL16 : stepFnIter 1 σP (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
      [.bool (bIdxOf? bkvs (ixN : Int)).isSome] (.seqn #[])
      (envSO env6 σ.nextAddr)
      (.seq [ifStmt] (envSO env6 σ.nextAddr)
        (.seq [] env6 KK)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[])
          (envSO env6 σ.nextAddr)
          (.seq [ifStmt] (envSO env6 σ.nextAddr)
            (.seq [] env6 KK))), σQ, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .bool) (old := .bool false)
        (hlook := hokCellP)
        (hnorm := GoLean.SliceWalk.normalize_bool)))
  -- L17: drain (3)
  have hL17 : stepFnIter 3 σQ (.next (.storeK [] [] (.seqn #[])
      (envSO env6 σ.nextAddr)
      (.seq [ifStmt] (envSO env6 σ.nextAddr)
        (.seq [] env6 KK)))) ch
      = .ok (.exec ifStmt (envSO env6 σ.nextAddr)
          (.seq [] (envSO env6 σ.nextAddr) (.seq [] env6 KK)),
        σQ, ch) := by
    have s1 : stepFnIter 1 σQ (.next (.storeK [] [] (.seqn #[])
        (envSO env6 σ.nextAddr)
        (.seq [ifStmt] (envSO env6 σ.nextAddr)
          (.seq [] env6 KK)))) ch
        = .ok (.exec (.seqn #[]) (envSO env6 σ.nextAddr)
            (.seq [ifStmt] (envSO env6 σ.nextAddr)
              (.seq [] env6 KK)), σQ, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain s1 (stepFnIter_splice_pop (ss := #[]) rfl)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hL1 hL2) hL3) hL4) hL5) hL6) hL7) hL12)
        hL13a) hL13b) hL14) hL15)
    (stepFnIter_chain hL16 hL17)

end Lookup

/-! ## 3. The miss/insert subcase (30 steps, ends `.next Kc`) -/

section Miss

variable {env6 : LocalEnv} {envC : LocalEnv} {Kc : Cont}
  {na₀ tw nw bm dc : Nat}
  {nodesV netV liveV pendV drvV hlV rnV stV : GoValue} {lm gm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {bkvs : List (Int × SlotA)} {ixN tmN idvN : Nat}
  {tmvN cmvN stvN apl ltm : Nat} {dv : GoString}

/-- **The first-insert** (30 steps): `ok` is false, so the walk
builds the slot literal and appends it — ending `.next Kc` through
the frame. -/
theorem s23_byidx_miss_seg
    (henvT : LocalEnv.lookup env6 "t" = some (.base ⟨na₀⟩))
    (henvN : LocalEnv.lookup env6 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI : LocalEnv.lookup env6 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR : LocalEnv.lookup env6 "trm" = some (.base ⟨na₀ + 6⟩))
    (henvD : LocalEnv.lookup env6 "data" = some (.base ⟨dc⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hokC : Heap.lookup σ.heap (.base ⟨σ.nextAddr - 1⟩)
      = some ⟨some .bool, .bool false⟩)
    (hna2 : 2 ≤ σ.nextAddr)
    (htP : Heap.lookup σ.heap (.base ⟨na₀⟩) = some (tParA tw))
    (hnP : Heap.lookup σ.heap (.base ⟨na₀ + 1⟩) = some (ndParA nw))
    (hIc : Heap.lookup σ.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (hTc : Heap.lookup σ.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (hDc : Heap.lookup σ.heap (.base ⟨dc⟩) = some (sCell dv))
    (hNd : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm))
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm
          (.map ⟨some (.base ⟨bm⟩)⟩) cc cm w pendV drvV sq tr hlV))
    (hBm : Heap.lookup σ.heap (.base ⟨bm⟩)
      = some ⟨none, .mapData (toEntriesB bkvs)⟩)
    (hmiss : bIdxOf? bkvs (ixN : Int) = none)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64) (hidv : idvN < 2 ^ 64) :
    stepFnIter 30 σ
        (.exec (.ifThenElse (.var "ok")
            (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)]))
          (LocalEnv.declare (LocalEnv.declare (([] : Scope) :: env6)
            "s" (.base ⟨σ.nextAddr - 2⟩)) "ok"
            (.base ⟨σ.nextAddr - 1⟩))
          (.seq [] (LocalEnv.declare (LocalEnv.declare
            (([] : Scope) :: env6) "s" (.base ⟨σ.nextAddr - 2⟩))
            "ok" (.base ⟨σ.nextAddr - 1⟩))
            (.seq [] env6 (FKa envC Kc)))) ch
      = .ok (.next Kc,
        { σ with heap := Heap.set σ.heap (.base ⟨bm⟩) ⟨none, .mapData (toEntriesB (bkvs ++ [((ixN : Int), (tmN, dv, idvN))]))⟩ }, ch) := by
  have htypes : σ.types = twinTypes := hag.1
  let envO : LocalEnv := LocalEnv.declare (LocalEnv.declare
    (([] : Scope) :: env6) "s" (.base ⟨σ.nextAddr - 2⟩)) "ok"
    (.base ⟨σ.nextAddr - 1⟩)
  -- the ok read + dispatch (3)
  have hM1 : stepFnIter 1 σ
      (.exec (.ifThenElse (.var "ok")
          (.block #[]
            #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
          (.block #[]
            #[.mapAssign byIndexE (.var "idx")
                (.structLit (.defined tidS)
                  #[.var "trm", .var "data", idE])
                (.int .uint64) (.defined tidS)])) envO
        (.seq [] envO (.seq [] env6 (FKa envC Kc)))) ch
      = .ok (.evalE (.var "ok") envO
          (.ifK (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)]) envO
            (.seq [] envO (.seq [] env6 (FKa envC Kc)))), σ, ch) := by
    with_unfolding_all rfl
  have hM2 : stepFnIter 1 σ (.evalE (.var "ok") envO
      (.ifK (.block #[]
          #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
        (.block #[]
          #[.mapAssign byIndexE (.var "idx")
              (.structLit (.defined tidS)
                #[.var "trm", .var "data", idE])
              (.int .uint64) (.defined tidS)]) envO
        (.seq [] envO (.seq [] env6 (FKa envC Kc))))) ch
      = .ok (.retV (.bool false)
          (.ifK (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)]) envO
            (.seq [] envO (.seq [] env6 (FKa envC Kc)))), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := rfl) (hlook := hokC))
  have hM3 : stepFnIter 3 σ (.retV (.bool false)
      (.ifK (.block #[]
          #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
        (.block #[]
          #[.mapAssign byIndexE (.var "idx")
              (.structLit (.defined tidS)
                #[.var "trm", .var "data", idE])
              (.int .uint64) (.defined tidS)]) envO
        (.seq [] envO (.seq [] env6 (FKa envC Kc))))) ch
      = .ok (.exec (.mapAssign byIndexE (.var "idx")
          (.structLit (.defined tidS)
            #[.var "trm", .var "data", idE])
          (.int .uint64) (.defined tidS))
          (([] : Scope) :: envO)
          (.seq [] (([] : Scope) :: envO)
            (.seq [] envO (.seq [] env6 (FKa envC Kc)))), σ, ch) := by
    with_unfolding_all rfl
  -- the mapAssign (5 + 2 + 1 + 2 + 2 + 5 + 1 + 1)
  let envB2 : LocalEnv := ([] : Scope) :: envO
  have henvTB : LocalEnv.lookup envB2 "t" = some (.base ⟨na₀⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨σ.nextAddr - 1⟩),
          ("s", Loc.base ⟨σ.nextAddr - 2⟩)] :: env6) "t" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvT
  have henvIB : LocalEnv.lookup envB2 "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨σ.nextAddr - 1⟩),
          ("s", Loc.base ⟨σ.nextAddr - 2⟩)] :: env6) "idx" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvI
  have henvRB : LocalEnv.lookup envB2 "trm"
      = some (.base ⟨na₀ + 6⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨σ.nextAddr - 1⟩),
          ("s", Loc.base ⟨σ.nextAddr - 2⟩)] :: env6) "trm" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvR
  have henvDB : LocalEnv.lookup envB2 "data"
      = some (.base ⟨dc⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨σ.nextAddr - 1⟩),
          ("s", Loc.base ⟨σ.nextAddr - 2⟩)] :: env6) "data" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvD
  have henvNB : LocalEnv.lookup envB2 "nd"
      = some (.base ⟨na₀ + 1⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨σ.nextAddr - 1⟩),
          ("s", Loc.base ⟨σ.nextAddr - 2⟩)] :: env6) "nd" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvN
  let KMA : Cont := .stmtOpK
    (.mapAssign (.int .uint64) (.defined tidS)) 0 []
    [.var "idx", .structLit (.defined tidS)
      #[.var "trm", .var "data", idE]] envB2
    (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc))))
  have hM4 : stepFnIter 1 σ
      (.exec (.mapAssign byIndexE (.var "idx")
        (.structLit (.defined tidS)
          #[.var "trm", .var "data", idE])
        (.int .uint64) (.defined tidS)) envB2
        (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc)))))
        ch
      = .ok (.evalE byIndexE envB2 KMA, σ, ch) := by
    with_unfolding_all rfl
  have hM5 : stepFnIter 5 σ (.evalE byIndexE envB2 KMA) ch
      = .ok (.retV (.map ⟨some (.base ⟨bm⟩)⟩) KMA, σ, ch) :=
    read_field_seg (henv := henvTB) (hp := htP) (hw := hTw)
      (hf := rfl)
  have hM6 : stepFnIter 1 σ
      (.retV (.map ⟨some (.base ⟨bm⟩)⟩) KMA) ch
      = .ok (.evalE (.var "idx") envB2
          (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
            [.map ⟨some (.base ⟨bm⟩)⟩]
            [.structLit (.defined tidS)
              #[.var "trm", .var "data", idE]] envB2
            (.seq [] envB2
              (.seq [] envO (.seq [] env6 (FKa envC Kc))))),
        σ, ch) := by
    with_unfolding_all rfl
  have hM7 : stepFnIter 1 σ (.evalE (.var "idx") envB2
      (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
        [.map ⟨some (.base ⟨bm⟩)⟩]
        [.structLit (.defined tidS)
          #[.var "trm", .var "data", idE]] envB2
        (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc))))))
      ch
      = .ok (.retV (.int (ixN : Int) .uint64)
          (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
            [.map ⟨some (.base ⟨bm⟩)⟩]
            [.structLit (.defined tidS)
              #[.var "trm", .var "data", idE]] envB2
            (.seq [] envB2
              (.seq [] envO (.seq [] env6 (FKa envC Kc))))),
        σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvIB) (hlook := hIc))
  -- the structLit (1 open + 2 + 2 + 5 + 1 apply)
  let KSL : Cont := .strictK
    (.structLit (.defined tidS)) [] [] envB2
    (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
      [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩] [] envB2
      (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc)))))
  have hM8 : stepFnIter 2 σ (.retV (.int (ixN : Int) .uint64)
      (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
        [.map ⟨some (.base ⟨bm⟩)⟩]
        [.structLit (.defined tidS)
          #[.var "trm", .var "data", idE]] envB2
        (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc))))))
      ch
      = .ok (.evalE (.var "trm") envB2
          (.strictK (.structLit (.defined tidS)) []
            [.var "data", idE] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) := by
    with_unfolding_all rfl
  have hM9 : stepFnIter 1 σ (.evalE (.var "trm") envB2
      (.strictK (.structLit (.defined tidS)) []
        [.var "data", idE] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.retV (.int (tmN : Int) .uint64)
          (.strictK (.structLit (.defined tidS)) []
            [.var "data", idE] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvRB) (hlook := hTc))
  have hM10 : stepFnIter 1 σ (.retV (.int (tmN : Int) .uint64)
      (.strictK (.structLit (.defined tidS)) []
        [.var "data", idE] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.evalE (.var "data") envB2
          (.strictK (.structLit (.defined tidS))
            [.int (tmN : Int) .uint64] [idE] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) := by
    with_unfolding_all rfl
  have hM11 : stepFnIter 1 σ (.evalE (.var "data") envB2
      (.strictK (.structLit (.defined tidS))
        [.int (tmN : Int) .uint64] [idE] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.retV (.string dv)
          (.strictK (.structLit (.defined tidS))
            [.int (tmN : Int) .uint64] [idE] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvDB) (hlook := hDc))
  have hM12 : stepFnIter 1 σ (.retV (.string dv)
      (.strictK (.structLit (.defined tidS))
        [.int (tmN : Int) .uint64] [idE] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.evalE idE envB2
          (.strictK (.structLit (.defined tidS))
            [.string dv, .int (tmN : Int) .uint64] [] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) := by
    with_unfolding_all rfl
  have hM13 : stepFnIter 5 σ (.evalE idE envB2
      (.strictK (.structLit (.defined tidS))
        [.string dv, .int (tmN : Int) .uint64] [] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.retV (.int (idvN : Int) .uint64)
          (.strictK (.structLit (.defined tidS))
            [.string dv, .int (tmN : Int) .uint64] [] envB2
            (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
              [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
              [] envB2
              (.seq [] envB2
                (.seq [] envO (.seq [] env6 (FKa envC Kc)))))),
        σ, ch) :=
    read_field_seg (henv := henvNB) (hp := hnP) (hw := hNd)
      (hf := nodeFs_id)
  have hM14 : stepFnIter 1 σ (.retV (.int (idvN : Int) .uint64)
      (.strictK (.structLit (.defined tidS))
        [.string dv, .int (tmN : Int) .uint64] [] envB2
        (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
          [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
          [] envB2
          (.seq [] envB2
            (.seq [] envO (.seq [] env6 (FKa envC Kc))))))) ch
      = .ok (.retV (slotV (tmN, dv, idvN))
          (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
            [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
            [] envB2
            (.seq [] envB2
              (.seq [] envO (.seq [] env6 (FKa envC Kc))))),
        σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int (idvN : Int) .uint64,
        GoValue.string dv, GoValue.int (tmN : Int) .uint64])
      = [GoValue.int (tmN : Int) .uint64, GoValue.string dv,
          GoValue.int (idvN : Int) .uint64] from rfl]
    show (do
      return ((← buildStructValue σ (.defined tidS)
        #[.int (tmN : Int) .uint64, .string dv,
          .int (idvN : Int) .uint64]), σ)) = _
    rw [buildStructValue_slot htypes (by omega) (by omega) (by omega)
      (by omega)]
    rfl
  have hM15 : stepFnIter 1 σ (.retV (slotV (tmN, dv, idvN))
      (.stmtOpK (.mapAssign (.int .uint64) (.defined tidS)) 0
        [.int (ixN : Int) .uint64, .map ⟨some (.base ⟨bm⟩)⟩]
        [] envB2
        (.seq [] envB2 (.seq [] envO (.seq [] env6 (FKa envC Kc))))))
      ch
      = .ok (.next (.seq [] envB2
          (.seq [] envO (.seq [] env6 (FKa envC Kc)))),
        { σ with heap := Heap.set σ.heap (.base ⟨bm⟩) ⟨none, .mapData (toEntriesB (bkvs ++ [((ixN : Int), (tmN, dv, idvN))]))⟩ }, ch) := by
    refine stepFnIter_one (stepFn_stmtOp_apply (h := ?_))
    show applyStmtOp σ ch (.mapAssign (.int .uint64) (.defined tidS))
      0 [.map ⟨some (.base ⟨bm⟩)⟩, .int (ixN : Int) .uint64,
        slotV (tmN, dv, idvN)] = _
    simp only [applyStmtOp, applyStmtOpCore, Bind.bind, Except.bind,
      pure, Except.pure]
    rw [mapAssignValue_toEntriesB_insert (s := (tmN, dv, idvN))
      htypes hBm hmiss hix (by omega) (by omega)]
  -- the exits (4)
  have hM16 : stepFnIter 4
      { σ with heap := Heap.set σ.heap (.base ⟨bm⟩) ⟨none, .mapData (toEntriesB (bkvs ++ [((ixN : Int), (tmN, dv, idvN))]))⟩ }
      (.next (.seq [] envB2
        (.seq [] envO (.seq [] env6 (FKa envC Kc))))) ch
      = .ok (.next Kc,
        { σ with heap := Heap.set σ.heap (.base ⟨bm⟩) ⟨none, .mapData (toEntriesB (bkvs ++ [((ixN : Int), (tmN, dv, idvN))]))⟩ }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            hM1 hM2) hM3) hM4) hM5) hM6) hM7) hM8) hM9) hM10) hM11)
      hM12) hM13) hM14) hM15) hM16

end Miss

/-! ## 4. The generic left-spine concat evaluator

The S2 viol argument is a 14-leaf left-nested `+` spine; spelling its
walk leaf-by-leaf (the `concat6_eval` route) would be enormous, so
the spine is evaluated ONCE by structural induction over a leaf
descriptor list. (Promotion note: `concat6_eval` is this engine's
hand-rolled 6-leaf instance — fold it in on the next consolidation
slice.) -/

/-- One spine leaf: its expression, delivered string, step count. -/
structure CLeaf where
  e : Expr
  v : GoString
  k : Nat

/-- The left-nested spine over an accumulator expression. -/
def spineE (l : Expr) : List CLeaf → Expr
  | [] => l
  | lf :: rest => spineE (.add l lf.e) rest

/-- The pending-leaf continuation tower. -/
def nestK (env : LocalEnv) (K : Cont) : List CLeaf → Cont
  | [] => K
  | lf :: rest => .strictK .add [] [lf.e] env (nestK env K rest)

/-- The consume-phase step count. -/
def spineSteps : List CLeaf → Nat
  | [] => 0
  | lf :: rest => 1 + lf.k + 1 + spineSteps rest

/-- The folded string. -/
def spineFold (a : GoString) : List CLeaf → GoString
  | [] => a
  | lf :: rest => spineFold (GoString.append a lf.v) rest

/-- Descent: the machine unwinds the spine to the head, building the
tower. -/
theorem spine_desc {env : LocalEnv} {K : Cont} (σ : ExecState)
    (ch : Choices) :
    ∀ (leaves : List CLeaf) (l : Expr),
    stepFnIter leaves.length σ (.evalE (spineE l leaves) env K) ch
      = .ok (.evalE l env (nestK env K leaves), σ, ch)
  | [], l => by
    show stepFnIter 0 σ _ ch = _
    rfl
  | lf :: rest, l => by
    show stepFnIter (rest.length + 1) σ
      (.evalE (spineE (.add l lf.e) rest) env K) ch = _
    have h1 := spine_desc (env := env) (K := K) σ ch rest
      (.add l lf.e)
    have h2 : stepFnIter 1 σ
        (.evalE (.add l lf.e) env (nestK env K rest)) ch
        = .ok (.evalE l env
            (.strictK .add [] [lf.e] env (nestK env K rest)),
          σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain h1 h2

/-- Consume: each pending leaf evaluates and appends. -/
theorem spine_consume {env : LocalEnv} {K : Cont} (σ : ExecState)
    (ch : Choices) :
    ∀ (leaves : List CLeaf),
    (∀ lf ∈ leaves, ∀ K' : Cont,
      stepFnIter lf.k σ (.evalE lf.e env K') ch
        = .ok (.retV (.string lf.v) K', σ, ch)) →
    ∀ (a : GoString),
    stepFnIter (spineSteps leaves) σ
        (.retV (.string a) (nestK env K leaves)) ch
      = .ok (.retV (.string (spineFold a leaves)) K, σ, ch)
  | [], _, a => by
    show stepFnIter 0 σ _ ch = _
    rfl
  | lf :: rest, hleaves, a => by
    show stepFnIter (1 + lf.k + 1 + spineSteps rest) σ
      (.retV (.string a)
        (.strictK .add [] [lf.e] env (nestK env K rest))) ch = _
    have h1 : stepFnIter 1 σ (.retV (.string a)
        (.strictK .add [] [lf.e] env (nestK env K rest))) ch
        = .ok (.evalE lf.e env
            (.strictK .add [.string a] [] env (nestK env K rest)),
          σ, ch) := by
      with_unfolding_all rfl
    have h2 := hleaves lf (List.mem_cons_self ..)
      (.strictK .add [.string a] [] env (nestK env K rest))
    have h3 : stepFnIter 1 σ (.retV (.string lf.v)
        (.strictK .add [.string a] [] env (nestK env K rest))) ch
        = .ok (.retV (.string (GoString.append a lf.v))
            (nestK env K rest), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string lf.v, GoValue.string a])
        = [GoValue.string a, GoValue.string lf.v] from rfl]
      exact applyStrictOp_add_string
    have h4 := spine_consume (env := env) (K := K) σ ch rest
      (fun lf' hl' => hleaves lf' (List.mem_cons_of_mem _ hl'))
      (GoString.append a lf.v)
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      h1 h2) h3) h4

/-- **The spine evaluator**: descend + head + consume. The head leaf
is the first descriptor; the whole spine costs
`leaves.length + head.k + spineSteps rest`. -/
theorem spine_eval {env : LocalEnv} {K : Cont} (σ : ExecState)
    (ch : Choices) (hd : CLeaf) (rest : List CLeaf)
    (hhd : ∀ K' : Cont,
      stepFnIter hd.k σ (.evalE hd.e env K') ch
        = .ok (.retV (.string hd.v) K', σ, ch))
    (hleaves : ∀ lf ∈ rest, ∀ K' : Cont,
      stepFnIter lf.k σ (.evalE lf.e env K') ch
        = .ok (.retV (.string lf.v) K', σ, ch)) :
    stepFnIter (rest.length + hd.k + spineSteps rest) σ
        (.evalE (spineE hd.e rest) env K) ch
      = .ok (.retV (.string (spineFold hd.v rest)) K, σ, ch) :=
  stepFnIter_chain (stepFnIter_chain
    (spine_desc σ ch rest hd.e)
    (hhd (nestK env K rest)))
    (spine_consume σ ch rest hleaves hd.v)

/-! ## 5. The S2 fire branch -/

/-- The S2 viol argument (the 13-add tree, named). -/
def s2ArgE : Expr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add
    (.stringLit (gs [83, 50, 32, 97, 103, 114, 101, 101, 109,
      101, 110, 116, 58, 32, 105, 110, 100, 101, 120, 32]))
    (.var "$c2309"))
    (.stringLit (gs [32, 105, 115, 32, 40, 116, 101, 114, 109,
      61])))
    (.var "$c2310"))
    (.stringLit (gs [44])))
    (.fieldGet (.var "s") tidS "data"))
    (.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
      32])))
    (.var "$c2311"))
    (.stringLit (gs [32, 98, 117, 116, 32, 40, 116, 101, 114,
      109, 61])))
    (.var "$c2312"))
    (.stringLit (gs [44])))
    (.var "data"))
    (.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
      32])))
    (.var "$c2313")

/-- A field read on a struct-valued VARIABLE (3 steps): the S2
branch's `s.term`/`s.node`/`s.data` reads. -/
theorem fieldOnVar_seg {σ : ExecState} {env : LocalEnv} {K : Cont}
    {ch : Choices} {x : String} {a : Nat} {dty : Option Ty}
    {sj : SlotA} {f : String} {v : GoValue}
    (henv : LocalEnv.lookup env x = some (.base ⟨a⟩))
    (hlook : Heap.lookup σ.heap (.base ⟨a⟩) = some ⟨dty, slotV sj⟩)
    (hf : StructFields.lookup
      (slotFs (sj.1 : Int) sj.2.1 (sj.2.2 : Int)) f = some v) :
    stepFnIter 3 σ (.evalE (.fieldGet (.var x) tidS f) env K) ch
      = .ok (.retV v K, σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.evalE (.fieldGet (.var x) tidS f) env K) ch
      = .ok (.evalE (.var x) env
          (.strictK (.fieldGet tidS f) [] [] env K), σ, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 σ (.evalE (.var x) env
      (.strictK (.fieldGet tidS f) [] [] env K)) ch
      = .ok (.retV (slotV sj)
          (.strictK (.fieldGet tidS f) [] [] env K), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henv) (hlook := hlook))
  have h3 : stepFnIter 1 σ (.retV (slotV sj)
      (.strictK (.fieldGet tidS f) [] [] env K)) ch
      = .ok (.retV v K, σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [slotV sj]) = [slotV sj] from rfl]
    exact GoLean.RaftSeam.DriverNet.applyStrictOp_fieldGet hf
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- `s2Branch`, viewed with the named argument. -/
theorem s2Branch_view : s2Branch = .block #[]
    #[utoaUnit "$c2309" (.var "idx"),
      utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term"),
      utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] := rfl

section S2Fire

variable {env0 : LocalEnv} {K : Cont} {na₀ tw nw sc dc : Nat}
  {nodesV netV liveV byV pendV drvV hlV rnV stV : GoValue}
  {lm gm : Nat} {cc cm w sq : Int} {tr : GoString}
  {tmvN cmvN stvN apl ltm : Nat}
  {ixN tmN idvN tj nj : Nat} {dj dv : GoString}

/-- The S2 branch's cell pack: the branch pack + the `s` local and
the `data` cell. -/
def S2Cells (na₀ tw nw sc dc : Nat) (twc ndc icell tcell : HeapCell)
    (sj : SlotA) (dv : GoString) (σ' : ExecState) : Prop :=
  BrCells na₀ tw nw twc ndc icell tcell σ'
    ∧ Heap.lookup σ'.heap (.base ⟨sc⟩)
        = some ⟨some (.defined tidS), slotV sj⟩
    ∧ Heap.lookup σ'.heap (.base ⟨dc⟩) = some (sCell dv)

/-- **The S2 fire-branch walk**: five `utoaUnit_walk` rides, the
14-leaf spine, `viol_call_span` — `violations` incremented EXACTLY,
the trace existential. -/
theorem s2Branch_walk
    (henvT0 : LocalEnv.lookup env0 "t" = some (.base ⟨na₀⟩))
    (henvN0 : LocalEnv.lookup env0 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI0 : LocalEnv.lookup env0 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR0 : LocalEnv.lookup env0 "trm" = some (.base ⟨na₀ + 6⟩))
    (henvS0 : LocalEnv.lookup env0 "s" = some (.base ⟨sc⟩))
    (henvD0 : LocalEnv.lookup env0 "data" = some (.base ⟨dc⟩))
    (σB : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σB)
    (hfr : ∀ x, σB.nextAddr ≤ x →
      Heap.lookup σB.heap (.base ⟨x⟩) = none)
    (hBr : S2Cells na₀ tw nw sc dc
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
      ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
      ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
      (tj, dj, nj) dv σB)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64) (hidv : idvN < 2 ^ 64)
    (htj : tj < 2 ^ 64) (hnj : nj < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 8100, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σB (.exec s2Branch env0 K) ch
        = .ok (.next K, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc cm (w + 1)
              pendV drvV sq tr' hlV)
      ∧ (∀ x, x < σB.nextAddr → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σB.heap (.base ⟨x⟩))
      ∧ σB.nextAddr + 17 ≤ σ'.nextAddr
      ∧ σ'.nextAddr ≤ σB.nextAddr + 27
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  obtain ⟨⟨htP, hnP, hTw, hNd, hIc, hTc⟩, hSc, hDc⟩ := hBr
  -- bounds
  have htPna : na₀ < σB.nextAddr := by
    rcases Nat.lt_or_ge na₀ σB.nextAddr with h | h
    · exact h
    · rw [hfr na₀ h] at htP; cases htP
  have hnPna : na₀ + 1 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 1) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 1) h] at hnP; cases hnP
  have htwna : tw < σB.nextAddr := by
    rcases Nat.lt_or_ge tw σB.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnwna : nw < σB.nextAddr := by
    rcases Nat.lt_or_ge nw σB.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNd; cases hNd
  have hicna : na₀ + 3 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 3) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 3) h] at hIc; cases hIc
  have htcna : na₀ + 6 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 6) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 6) h] at hTc; cases hTc
  have hscna : sc < σB.nextAddr := by
    rcases Nat.lt_or_ge sc σB.nextAddr with h | h
    · exact h
    · rw [hfr sc h] at hSc; cases hSc
  have hdcna : dc < σB.nextAddr := by
    rcases Nat.lt_or_ge dc σB.nextAddr with h | h
    · exact h
    · rw [hfr dc h] at hDc; cases hDc
  -- the pack transport through a frame clause
  have thread : ∀ {σ1 σ2 : ExecState},
      (∀ x, x < σ1.nextAddr →
        Heap.lookup σ2.heap (.base ⟨x⟩)
          = Heap.lookup σ1.heap (.base ⟨x⟩)) →
      σB.nextAddr ≤ σ1.nextAddr →
      S2Cells na₀ tw nw sc dc
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr
          hlV)
        (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
        ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
        ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
        (tj, dj, nj) dv σ1 →
      S2Cells na₀ tw nw sc dc
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr
          hlV)
        (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
        ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
        ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
        (tj, dj, nj) dv σ2 := by
    rintro σ1 σ2 hf hle ⟨⟨j1, j2, j3, j4, j5, j6⟩, j7, j8⟩
    exact ⟨⟨by rw [hf na₀ (by omega)]; exact j1,
      by rw [hf (na₀ + 1) (by omega)]; exact j2,
      by rw [hf tw (by omega)]; exact j3,
      by rw [hf nw (by omega)]; exact j4,
      by rw [hf (na₀ + 3) (by omega)]; exact j5,
      by rw [hf (na₀ + 6) (by omega)]; exact j6⟩,
      by rw [hf sc (by omega)]; exact j7,
      by rw [hf dc (by omega)]; exact j8⟩
  -- transport into a fresh-cell init state
  have threadF : ∀ {σ1 : ExecState} {cell : HeapCell},
      σB.nextAddr ≤ σ1.nextAddr →
      S2Cells na₀ tw nw sc dc
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr
          hlV)
        (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
        ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
        ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
        (tj, dj, nj) dv σ1 →
      S2Cells na₀ tw nw sc dc
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr
          hlV)
        (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
        ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
        ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
        (tj, dj, nj) dv
        { σ1 with heap := Heap.set σ1.heap (.base ⟨σ1.nextAddr⟩) cell, nextAddr := σ1.nextAddr + 1 } := by
    intro σ1 cell hle hp
    refine thread ?_ (by omega) hp
    intro x hx
    show Heap.lookup (Heap.set σ1.heap (.base ⟨σ1.nextAddr⟩) _)
      (.base ⟨x⟩) = _
    have hx1 : x < σ1.nextAddr + 1 := by omega
    rw [lookup_set_other (by omega : σ1.nextAddr ≠ x)]
  -- B0: block + pop (2)
  let env2 : LocalEnv := ([] : Scope) :: env0
  have hB0 : stepFnIter 2 σB (.exec s2Branch env0 K) ch
      = .ok (.exec (utoaUnit "$c2309" (.var "idx")) env2
          (.seq [utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term"),
      utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] env2 K), σB, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- ===== UNIT 1 ($c2309) =====
  have hPF1 := threadF (σ1 := σB)
    (cell := sCell (gs [])) (by omega) ⟨⟨htP, hnP, hTw, hNd, hIc, hTc⟩, hSc, hDc⟩
  have hU1 := utoaUnit_walk (envQ := env2)
    (rest := [utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term"),
      utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]])
    (K := K) (c := "$c2309") (argE := (.var "idx")) (ka := 1) (av := ixN)
    σB ch hag hfr hix
    (env_lookup_head (scope_lookup_head ..))
    (by
      have hp := hPF1
      refine stepFnIter_one (stepFn_var (henv := ?_)
        (hlook := hp.1.2.2.2.2.1))
      show LocalEnv.lookup ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "idx" = _
      rw [env_lookup_skip rfl]
      exact henvI0)
  obtain ⟨m1, hb1, s1x, σU1, hrun1, hcell1, hna1lo,
    hna1hi, hfrm1, hfrs1, hag1⟩ := hU1
  have hPk1 := thread (σ1 := σB) (σ2 := σU1)
    (fun x hx => hfrm1 x hx) (by omega) ⟨⟨htP, hnP, hTw, hNd, hIc, hTc⟩, hSc, hDc⟩
  -- drain to unit 2 (2)
  have hD1 : stepFnIter 2 σU1
      (.exec (.seqn #[]) ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
        (.seq [utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term"),
      utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K)) ch
      = .ok (.exec (utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term")) ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
          (.seq [utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K),
        σU1, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 2 ($c2310) =====
  have hPF2 := threadF (σ1 := σU1)
    (cell := sCell (gs [])) (by omega) hPk1
  have hU2 := utoaUnit_walk (envQ := ([("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0))
    (rest := [utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]])
    (K := K) (c := "$c2310") (argE := (.fieldGet (.var "s") tidS "term")) (ka := 3) (av := tj)
    σU1 ch hag1 hfrs1 htj
    (env_lookup_head (scope_lookup_head ..))
    (by
      have hp := hPF2
      exact fieldOnVar_seg
        (henv := by
          show LocalEnv.lookup
            ([("$c2310", Loc.base ⟨σU1.nextAddr⟩),
              ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "s" = _
          rw [env_lookup_skip rfl]
          exact henvS0)
        (hlook := hp.2.1) (hf := rfl))
  obtain ⟨m2, hb2, s2x, σU2, hrun2, hcell2, hna2lo,
    hna2hi, hfrm2, hfrs2, hag2⟩ := hU2
  have hPk2 := thread (σ1 := σU1) (σ2 := σU2)
    (fun x hx => hfrm2 x hx) (by omega) hPk1
  -- drain to unit 3 (2)
  have hD2 : stepFnIter 2 σU2
      (.exec (.seqn #[]) ([("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
        (.seq [utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K)) ch
      = .ok (.exec (utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node")) ([("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
          (.seq [utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K),
        σU2, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 3 ($c2311) =====
  have hPF3 := threadF (σ1 := σU2)
    (cell := sCell (gs [])) (by omega) hPk2
  have hU3 := utoaUnit_walk (envQ := ([("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0))
    (rest := [utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]])
    (K := K) (c := "$c2311") (argE := (.fieldGet (.var "s") tidS "node")) (ka := 3) (av := nj)
    σU2 ch hag2 hfrs2 hnj
    (env_lookup_head (scope_lookup_head ..))
    (by
      have hp := hPF3
      exact fieldOnVar_seg
        (henv := by
          show LocalEnv.lookup
            ([("$c2311", Loc.base ⟨σU2.nextAddr⟩),
              ("$c2310", Loc.base ⟨σU1.nextAddr⟩),
              ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "s" = _
          rw [env_lookup_skip rfl]
          exact henvS0)
        (hlook := hp.2.1) (hf := rfl))
  obtain ⟨m3, hb3, s3x, σU3, hrun3, hcell3, hna3lo,
    hna3hi, hfrm3, hfrs3, hag3⟩ := hU3
  have hPk3 := thread (σ1 := σU2) (σ2 := σU3)
    (fun x hx => hfrm3 x hx) (by omega) hPk2
  -- drain to unit 4 (2)
  have hD3 : stepFnIter 2 σU3
      (.exec (.seqn #[]) ([("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
        (.seq [utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K)) ch
      = .ok (.exec (utoaUnit "$c2312" (.var "trm")) ([("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
          (.seq [utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K),
        σU3, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 4 ($c2312) =====
  have hPF4 := threadF (σ1 := σU3)
    (cell := sCell (gs [])) (by omega) hPk3
  have hU4 := utoaUnit_walk (envQ := ([("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0))
    (rest := [utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]])
    (K := K) (c := "$c2312") (argE := (.var "trm")) (ka := 1) (av := tmN)
    σU3 ch hag3 hfrs3 htm
    (env_lookup_head (scope_lookup_head ..))
    (by
      have hp := hPF4
      refine stepFnIter_one (stepFn_var (henv := ?_)
        (hlook := hp.1.2.2.2.2.2))
      show LocalEnv.lookup ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "trm" = _
      rw [env_lookup_skip rfl]
      exact henvR0)
  obtain ⟨m4, hb4, s4x, σU4, hrun4, hcell4, hna4lo,
    hna4hi, hfrm4, hfrs4, hag4⟩ := hU4
  have hPk4 := thread (σ1 := σU3) (σ2 := σU4)
    (fun x hx => hfrm4 x hx) (by omega) hPk3
  -- drain to unit 5 (2)
  have hD4 : stepFnIter 2 σU4
      (.exec (.seqn #[]) ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
        (.seq [utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K)) ch
      = .ok (.exec (utoaUnit "$c2313" idE) ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0)
          (.seq [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]] ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) K),
        σU4, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 5 ($c2313) =====
  have hPF5 := threadF (σ1 := σU4)
    (cell := sCell (gs [])) (by omega) hPk4
  have hU5 := utoaUnit_walk (envQ := ([("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0))
    (rest := [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]])
    (K := K) (c := "$c2313") (argE := idE) (ka := 5) (av := idvN)
    σU4 ch hag4 hfrs4 hidv
    (env_lookup_head (scope_lookup_head ..))
    (by
      have hp := hPF5
      exact read_field_seg
        (henv := show LocalEnv.lookup ([("$c2313", Loc.base ⟨σU4.nextAddr⟩), ("$c2312", Loc.base ⟨σU3.nextAddr⟩), ("$c2311", Loc.base ⟨σU2.nextAddr⟩), ("$c2310", Loc.base ⟨σU1.nextAddr⟩), ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "nd"
            = some (.base ⟨na₀ + 1⟩) from by
          rw [env_lookup_skip rfl]
          exact henvN0)
        (hp := hp.1.2.1) (hw := hp.1.2.2.2.1) (hf := nodeFs_id))
  obtain ⟨m5, hb5, s5x, σU5, hrun5, hcell5, hna5lo,
    hna5hi, hfrm5, hfrs5, hag5⟩ := hU5
  have hPk5 := thread (σ1 := σU4) (σ2 := σU5)
    (fun x hx => hfrm5 x hx) (by omega) hPk4
  -- drain to the viol call (2)
  let env2e : LocalEnv := [("$c2313", Loc.base ⟨σU4.nextAddr⟩),
        ("$c2312", Loc.base ⟨σU3.nextAddr⟩),
        ("$c2311", Loc.base ⟨σU2.nextAddr⟩),
        ("$c2310", Loc.base ⟨σU1.nextAddr⟩),
        ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0
  have hD5 : stepFnIter 2 σU5
      (.exec (.seqn #[]) env2e
        (.seq [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE]]
          env2e K)) ch
      = .ok (.exec (.call #[] ⟨"main.twin.viol"⟩
          #[.var "t", s2ArgE]) env2e (.seq [] env2e K), σU5, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- the string cells at σU5
  have hcell1U5 : Heap.lookup σU5.heap (.base ⟨σB.nextAddr⟩)
      = some (sCell s1x) := by
    rw [hfrm5 σB.nextAddr (by omega), hfrm4 σB.nextAddr (by omega),
      hfrm3 σB.nextAddr (by omega), hfrm2 σB.nextAddr (by omega)]
    exact hcell1
  have hcell2U5 : Heap.lookup σU5.heap (.base ⟨σU1.nextAddr⟩)
      = some (sCell s2x) := by
    rw [hfrm5 σU1.nextAddr (by omega), hfrm4 σU1.nextAddr (by omega),
      hfrm3 σU1.nextAddr (by omega)]
    exact hcell2
  have hcell3U5 : Heap.lookup σU5.heap (.base ⟨σU2.nextAddr⟩)
      = some (sCell s3x) := by
    rw [hfrm5 σU2.nextAddr (by omega), hfrm4 σU2.nextAddr (by omega)]
    exact hcell3
  have hcell4U5 : Heap.lookup σU5.heap (.base ⟨σU3.nextAddr⟩)
      = some (sCell s4x) := by
    rw [hfrm5 σU3.nextAddr (by omega)]
    exact hcell4
  -- V1: plan + t + advance (3)
  have hV1 : stepFnIter 1 σU5
      (.exec (.call #[] ⟨"main.twin.viol"⟩ #[.var "t", s2ArgE])
        env2e (.seq [] env2e K)) ch
      = .ok (.evalE (.var "t") env2e
          (.callArgsK ⟨"main.twin.viol"⟩ [] [] [s2ArgE] env2e
            (.seq [] env2e K)), σU5, ch) := by
    with_unfolding_all rfl
  have hV2 : stepFnIter 1 σU5 (.evalE (.var "t") env2e
      (.callArgsK ⟨"main.twin.viol"⟩ [] [] [s2ArgE] env2e
        (.seq [] env2e K))) ch
      = .ok (.retV (.addr (.base ⟨tw⟩))
          (.callArgsK ⟨"main.twin.viol"⟩ [] [] [s2ArgE] env2e
            (.seq [] env2e K)), σU5, ch) :=
    stepFnIter_one (stepFn_var
      (henv := by
        show LocalEnv.lookup ([("$c2313", Loc.base ⟨σU4.nextAddr⟩),
        ("$c2312", Loc.base ⟨σU3.nextAddr⟩),
        ("$c2311", Loc.base ⟨σU2.nextAddr⟩),
        ("$c2310", Loc.base ⟨σU1.nextAddr⟩),
        ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "t" = _
        rw [env_lookup_skip rfl]
        exact henvT0)
      (hlook := hPk5.1.1))
  have hV3 : stepFnIter 1 σU5 (.retV (.addr (.base ⟨tw⟩))
      (.callArgsK ⟨"main.twin.viol"⟩ [] [] [s2ArgE] env2e
        (.seq [] env2e K))) ch
      = .ok (.evalE s2ArgE env2e
          (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
            [] env2e (.seq [] env2e K)), σU5, ch) := by
    with_unfolding_all rfl
  -- V4: the spine
  let s2Rest : List CLeaf :=
    [⟨.var "$c2309", s1x, 1⟩,
     ⟨.stringLit (gs [32, 105, 115, 32, 40, 116, 101, 114, 109,
       61]), gs [32, 105, 115, 32, 40, 116, 101, 114, 109, 61], 1⟩,
     ⟨.var "$c2310", s2x, 1⟩,
     ⟨.stringLit (gs [44]), gs [44], 1⟩,
     ⟨.fieldGet (.var "s") tidS "data", dj, 3⟩,
     ⟨.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
       32]), gs [41, 32, 111, 110, 32, 110, 111, 100, 101, 32], 1⟩,
     ⟨.var "$c2311", s3x, 1⟩,
     ⟨.stringLit (gs [32, 98, 117, 116, 32, 40, 116, 101, 114, 109,
       61]), gs [32, 98, 117, 116, 32, 40, 116, 101, 114, 109, 61],
       1⟩,
     ⟨.var "$c2312", s4x, 1⟩,
     ⟨.stringLit (gs [44]), gs [44], 1⟩,
     ⟨.var "data", dv, 1⟩,
     ⟨.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
       32]), gs [41, 32, 111, 110, 32, 110, 111, 100, 101, 32], 1⟩,
     ⟨.var "$c2313", s5x, 1⟩]
  have hV4 : stepFnIter (s2Rest.length + 1 + spineSteps s2Rest) σU5
      (.evalE s2ArgE env2e
        (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
          [] env2e (.seq [] env2e K))) ch
      = .ok (.retV (.string (spineFold
          (gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101, 110,
            116, 58, 32, 105, 110, 100, 101, 120, 32]) s2Rest))
          (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
            [] env2e (.seq [] env2e K)), σU5, ch) := by
    have h0 := spine_eval (env := env2e)
      (K := .callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
        [] env2e (.seq [] env2e K)) σU5 ch
      ⟨.stringLit (gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101,
        110, 116, 58, 32, 105, 110, 100, 101, 120, 32]),
        gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101, 110, 116,
          58, 32, 105, 110, 100, 101, 120, 32], 1⟩
      s2Rest
      (fun K' => by with_unfolding_all rfl)
      ?leaves
    case leaves =>
      intro lf hlf K'
      simp only [s2Rest, List.mem_cons, List.not_mem_nil,
        or_false] at hlf
      rcases hlf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl
      · exact stepFnIter_one (stepFn_var (henv := rfl)
          (hlook := hcell1U5))
      · with_unfolding_all rfl
      · exact stepFnIter_one (stepFn_var (henv := rfl)
          (hlook := hcell2U5))
      · with_unfolding_all rfl
      · exact fieldOnVar_seg
          (henv := by
            show LocalEnv.lookup ([("$c2313", Loc.base ⟨σU4.nextAddr⟩),
        ("$c2312", Loc.base ⟨σU3.nextAddr⟩),
        ("$c2311", Loc.base ⟨σU2.nextAddr⟩),
        ("$c2310", Loc.base ⟨σU1.nextAddr⟩),
        ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "s" = _
            rw [env_lookup_skip rfl]
            exact henvS0)
          (hlook := hPk5.2.1) (hf := rfl)
      · with_unfolding_all rfl
      · exact stepFnIter_one (stepFn_var (henv := rfl)
          (hlook := hcell3U5))
      · with_unfolding_all rfl
      · exact stepFnIter_one (stepFn_var (henv := rfl)
          (hlook := hcell4U5))
      · with_unfolding_all rfl
      · exact stepFnIter_one (stepFn_var
          (henv := by
            show LocalEnv.lookup ([("$c2313", Loc.base ⟨σU4.nextAddr⟩),
        ("$c2312", Loc.base ⟨σU3.nextAddr⟩),
        ("$c2311", Loc.base ⟨σU2.nextAddr⟩),
        ("$c2310", Loc.base ⟨σU1.nextAddr⟩),
        ("$c2309", Loc.base ⟨σB.nextAddr⟩)] :: env0) "data" = _
            rw [env_lookup_skip rfl]
            exact henvD0)
          (hlook := hPk5.2.2))
      · with_unfolding_all rfl
      · exact stepFnIter_one (stepFn_var (henv := rfl)
          (hlook := hcell5))
    exact h0
  -- V5: the viol span (42)
  have hV5 := viol_call_span (envC := env2e)
    (Kc := .seq [] env2e K) (tw := tw)
    (nodesV := nodesV) (netV := netV) (liveV := liveV) (lm := lm)
    (byV := byV) (c := cc) (cm := cm) (w := w) (pendV := pendV)
    (drvV := drvV) (sq := sq) (tr := tr) (hlV := hlV)
    σU5 ch
    (spineFold (gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101,
      110, 116, 58, 32, 105, 110, 100, 101, 120, 32]) s2Rest)
    hag5 hPk5.1.2.2.1 hfrs5 hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
  -- V6: the seq-nil pop (1)
  let σV : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    σU5.heap (.base ⟨σU5.nextAddr⟩) (tParCell tw))
    (.base ⟨σU5.nextAddr + 1⟩) (sCell (spineFold
      (gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101, 110, 116,
        58, 32, 105, 110, 100, 101, 120, 32]) s2Rest)))
    (.base ⟨tw⟩)
    (twCell nodesV netV liveV lm byV cc cm (w + 1) pendV drvV
      sq (GoString.append tr (GoString.append (gs [32, 33])
        (spineFold (gs [83, 50, 32, 97, 103, 114, 101, 101, 109,
          101, 110, 116, 58, 32, 105, 110, 100, 101, 120, 32])
          s2Rest))) hlV))
    (σU5.nextAddr + 2)
  have hV6 : stepFnIter 1 σV (.next (.seq [] env2e K)) ch
      = .ok (.next K, σV, ch) := by
    with_unfolding_all rfl
  -- assemble
  refine ⟨2 + m1 + 2 + m2 + 2 + m3 + 2 + m4 + 2 + m5 + 2 + 1 + 1
      + 1 + (s2Rest.length + 1 + spineSteps s2Rest) + 42 + 1,
    by
      have h1 : spineSteps s2Rest = 41 := rfl
      have h2 : s2Rest.length = 13 := rfl
      omega,
    σV,
    GoString.append tr (GoString.append (gs [32, 33])
      (spineFold (gs [83, 50, 32, 97, 103, 114, 101, 101, 109, 101,
        110, 116, 58, 32, 105, 110, 100, 101, 120, 32]) s2Rest)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain hB0 hrun1) hD1) hrun2) hD2) hrun3)
              hD3) hrun4) hD4) hrun5) hD5) hV1) hV2) hV3) hV4) hV5)
      hV6
  · show Heap.lookup σV.heap (.base ⟨tw⟩) = _
    exact lookup_set_self
  · intro x hx hxtw
    show Heap.lookup (Heap.set (Heap.set (Heap.set σU5.heap
      (.base ⟨σU5.nextAddr⟩) _) (.base ⟨σU5.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) _) (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxtw he.symm),
      lookup_set_other (by omega : σU5.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σU5.nextAddr ≠ x),
      hfrm5 x (by omega), hfrm4 x (by omega), hfrm3 x (by omega),
      hfrm2 x (by omega), hfrm1 x (by omega)]
  · show σB.nextAddr + 17 ≤ σU5.nextAddr + 2
    omega
  · show σU5.nextAddr + 2 ≤ σB.nextAddr + 27
    omega
  · intro x hx
    have hx2 : σU5.nextAddr + 2 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set σU5.heap
      (.base ⟨σU5.nextAddr⟩) _) (.base ⟨σU5.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) _) (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : tw ≠ x),
      lookup_set_other (by omega : σU5.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σU5.nextAddr ≠ x)]
    exact hfrs5 x (by omega)
  · exact ⟨rfl, rfl, rfl, rfl⟩

end S2Fire

end GoLean.RaftSeam.SpanS23
