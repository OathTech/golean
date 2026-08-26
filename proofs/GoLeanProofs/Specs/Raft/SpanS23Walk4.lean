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

end GoLean.RaftSeam.SpanS23
