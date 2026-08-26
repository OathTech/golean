import GoLeanProofs.Specs.Raft.SpanS1

/-!
# The S1 record span WALK (A4d-SM1 item 3, part 2)

The machine walk consuming `SpanS1`'s vocabulary/projection layer:
the 47-step prefix (`claims++` + the comma-ok lookup), the 20-step
record segment, and the headline `s1_span_computes` (docstring there).
Split from `SpanS1.lean` so the kernel pins compile once.
-/

namespace GoLean.RaftSeam.SpanS1

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk (envB flagCell flagSet stepFn_ref normalize_bool
  lookup_pushScope)
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.NativeSpec (S1St lookupTerm s1Fires s1Step s1Run)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)
open GoLean.MapMem (toEntries idxOf? cnt setk)

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## 5. The span prefix: `claims++` + the comma-ok lookup
(47 steps, both branches share it) -/

/-- The uint64 default (any state). -/
theorem defaultValue_u64 {σ : ExecState} :
    defaultValue σ (.int .uint64) = .ok (.int 0 .uint64) := by
  with_unfolding_all rfl

section Walk

variable {envS : LocalEnv} {K : Cont} {lt ln tw nw lm : Nat}
  {dtyT dtyN dtyNw : Option Ty}
  {nodesV netV liveV byV pendV drvV hlV : GoValue}
  {cm sq : Int} {tr : GoString}
  {fsN : Array (String × GoValue)}
  {kvs : List (Int × Nat)} {cN wN tm idv : Nat}

/-- The scope stack after the two declarations. -/
def envP (envS : LocalEnv) (na : Nat) : LocalEnv :=
  [("ok", .base ⟨na + 1⟩), ("prev", .base ⟨na⟩)] :: envS

/-- The state after the prefix: `claims` bumped, the `prev`/`ok`
cells allocated and written with the lookup's result. -/
def prefixSt (tw na : Nat)
    (nodesV netV liveV : GoValue) (lm : Nat) (byV : GoValue)
    (c cm w : Int) (pendV drvV : GoValue) (sq : Int) (tr : GoString)
    (hlV : GoValue) (kvs : List (Int × Nat)) (tm : Nat)
    (σ : ExecState) : ExecState :=
  { σ with
      heap := Heap.set (Heap.set (Heap.set (Heap.set (Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV (c + 1) cm w pendV drvV sq tr hlV)) (.base ⟨na⟩) ⟨some (.int .uint64), .int 0 .uint64⟩) (.base ⟨na + 1⟩) ⟨some .bool, .bool false⟩) (.base ⟨na⟩) ⟨some (.int .uint64), .int (cnt kvs (tm : Int) : Int) .uint64⟩) (.base ⟨na + 1⟩) ⟨some .bool, .bool (idxOf? kvs (tm : Int)).isSome⟩,
      nextAddr := na + 2 }

/-- **The prefix walk** (47 steps): `t.claims++`, then
`prev, ok := t.leaderOf[nd.term]`, landing on the violation check. -/
theorem s1_prefix
    (henvT : LocalEnv.lookup envS "t" = some (.base ⟨lt⟩))
    (henvN : LocalEnv.lookup envS "nd" = some (.base ⟨ln⟩))
    (σ : ExecState) (ch : Choices)
    (ht : Heap.lookup σ.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩)
    (hn : Heap.lookup σ.heap (.base ⟨ln⟩)
      = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV (cN : Int) cm (wN : Int)
          pendV drvV sq tr hlV))
    (hNw : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some ⟨dtyNw, .struct tidN fsN⟩)
    (hterm : StructFields.lookup fsN "term"
      = some (.int (tm : Int) .uint64))
    (hlm : Heap.lookup σ.heap (.base ⟨lm⟩)
      = some ⟨none, .mapData (toEntries kvs)⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hag : bfTB.Agrees σ)
    (hd1 : lt ≠ tw) (hd2 : ln ≠ tw) (hd3 : nw ≠ tw) (hd4 : lm ≠ tw)
    (hvals : ∀ p ∈ kvs, p.2 < 2 ^ 64)
    (hc1 : (cN : Int) + 1 < 2 ^ 63) (hm0 : -(2 ^ 63) ≤ cm)
    (hm1 : cm < 2 ^ 63) (hw1 : (wN : Int) < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63)
    (htm : tm < 2 ^ 64) :
    stepFnIter 47 σ (.exec s1Block envS K) ch
      = .ok (.exec fireIf (envP envS σ.nextAddr)
          (.seq [recordAssign] (envP envS σ.nextAddr) K),
        prefixSt tw σ.nextAddr nodesV netV liveV lm byV (cN : Int) cm
          (wN : Int) pendV drvV sq tr hlV kvs tm σ, ch) := by
  -- frontier bounds for the touched cells
  have hltna : lt < σ.nextAddr := by
    rcases Nat.lt_or_ge lt σ.nextAddr with h | h
    · exact h
    · rw [hfr lt h] at ht; cases ht
  have hlnna : ln < σ.nextAddr := by
    rcases Nat.lt_or_ge ln σ.nextAddr with h | h
    · exact h
    · rw [hfr ln h] at hn; cases hn
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnwna : nw < σ.nextAddr := by
    rcases Nat.lt_or_ge nw σ.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNw; cases hNw
  have hlmna : lm < σ.nextAddr := by
    rcases Nat.lt_or_ge lm σ.nextAddr with h | h
    · exact h
    · rw [hfr lm h] at hlm; cases hlm
  -- P1: block + pop (2 steps)
  have hP1 : stepFnIter 2 σ (.exec s1Block envS K) ch
      = .ok (.exec claimsInc ([] :: envS)
          (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K),
        σ, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- P2: the claims increment (15 steps)
  let KC : Cont := .tgtOpK (.chain [.field ⟨"main.twin"⟩ "claims"])
    [] [] [] [] .vals
    [.add (.fieldGet (.deref (.var "t") tyTwinD) tidT "claims")
      (.intLit 1 .int)] []
    (.seqn #[]) ([] :: envS)
    (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K)
  have hP2a : stepFnIter 1 σ (.exec claimsInc ([] :: envS)
      (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K)) ch
      = .ok (.evalE (.var "t") ([] :: envS) KC, σ, ch) := by
    with_unfolding_all rfl
  have hP2b : stepFnIter 1 σ (.evalE (.var "t") ([] :: envS) KC) ch
      = .ok (.retV (.addr (.base ⟨tw⟩)) KC, σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envS "t").trans henvT) (hlook := ht))
  let KC2 : Cont := .strictK .add [] [.intLit 1 .int] ([] :: envS)
    (.rhsK .vals
      [.chain (.addr (.base ⟨tw⟩)) [] [.field ⟨"main.twin"⟩ "claims"]]
      [] [] (.seqn #[]) ([] :: envS)
      (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K))
  have hP2c : stepFnIter 2 σ (.retV (.addr (.base ⟨tw⟩)) KC) ch
      = .ok (.evalE (.fieldGet (.deref (.var "t") tyTwinD) tidT
          "claims") ([] :: envS) KC2, σ, ch) := by
    with_unfolding_all rfl
  have hP2d : stepFnIter 5 σ (.evalE (.fieldGet (.deref (.var "t")
      tyTwinD) tidT "claims") ([] :: envS) KC2) ch
      = .ok (.retV (.int (cN : Int) .int) KC2, σ, ch) :=
    read_field_seg
      (henv := (lookup_pushScope envS "t").trans henvT)
      (hp := ht) (hw := hTw) (hf := twinFs_claims)
  have hP2e : stepFnIter 2 σ (.retV (.int (cN : Int) .int) KC2) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .add [.int (cN : Int) .int] [] ([] :: envS)
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field ⟨"main.twin"⟩ "claims"]]
              [] [] (.seqn #[]) ([] :: envS)
              (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS)
                K))), σ, ch) := by
    with_unfolding_all rfl
  have hP2f : stepFnIter 1 σ (.retV (.int 1 .int)
      (.strictK .add [.int (cN : Int) .int] [] ([] :: envS)
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "claims"]]
          [] [] (.seqn #[]) ([] :: envS)
          (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS)
            K)))) ch
      = .ok (.retV (.int ((cN : Int) + 1) .int)
          (.rhsK .vals
            [.chain (.addr (.base ⟨tw⟩)) []
              [.field ⟨"main.twin"⟩ "claims"]]
            [] [] (.seqn #[]) ([] :: envS)
            (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K)),
        σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 1 .int,
        GoValue.int (cN : Int) .int])
      = [GoValue.int (cN : Int) .int, GoValue.int 1 .int] from rfl]
    exact GoLean.SliceWalk.applyStrictOp_add_int (by omega) (by omega)
  have hP2g : stepFnIter 1 σ (.retV (.int ((cN : Int) + 1) .int)
      (.rhsK .vals
        [.chain (.addr (.base ⟨tw⟩)) []
          [.field ⟨"main.twin"⟩ "claims"]]
        [] [] (.seqn #[]) ([] :: envS)
        (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "claims"]]
          [.int ((cN : Int) + 1) .int] (.seqn #[]) ([] :: envS)
          (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K)),
        σ, ch) := by
    with_unfolding_all rfl
  let σA : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm (wN : Int) pendV drvV sq tr hlV) }
  have hP2h : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "claims"]]
      [.int ((cN : Int) + 1) .int] (.seqn #[]) ([] :: envS)
      (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: envS)
          (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K)),
        σA, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_twin_claims (σ := σ) hag.1
        hTw (by omega) hc1 hm0 hm1 (by omega) hw1 hq0 hq1))
  -- P3: drain + splice/pop to prevOkSeqn (3 steps)
  have hP3 : stepFnIter 3 σA (.next (.storeK [] [] (.seqn #[])
      ([] :: envS)
      (.seq [prevOkSeqn, fireIf, recordAssign] ([] :: envS) K))) ch
      = .ok (.exec prevOkSeqn ([] :: envS)
          (.seq [fireIf, recordAssign] ([] :: envS) K), σA, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_splice_pop (ss := #[]) rfl)
  -- P4: prevOkSeqn (28 steps)
  -- P4a: splice/pop (2)
  have hP4a : stepFnIter 2 σA (.exec prevOkSeqn ([] :: envS)
      (.seq [fireIf, recordAssign] ([] :: envS) K)) ch
      = .ok (.exec (.initialization { id := "prev", typ := .int .uint64 })
          ([] :: envS)
          (.seq [.initialization { id := "ok", typ := .bool },
            .mapLookup (.var "prev") (.var "ok") lofE termE
              (.int .uint64) (.int .uint64), fireIf, recordAssign]
            ([] :: envS) K), σA, ch) :=
    stepFnIter_splice_pop
      (ss := #[.initialization { id := "prev", typ := .int .uint64 },
        .initialization { id := "ok", typ := .bool },
        .mapLookup (.var "prev") (.var "ok") lofE termE
          (.int .uint64) (.int .uint64)]) rfl
  -- P4b: the prev allocation (σA.nextAddr = σ.nextAddr)
  have hP4b : stepFnIter 1 σA
      (.exec (.initialization { id := "prev", typ := .int .uint64 })
        ([] :: envS)
        (.seq [.initialization { id := "ok", typ := .bool },
          .mapLookup (.var "prev") (.var "ok") lofE termE
            (.int .uint64) (.int .uint64), fireIf, recordAssign]
          ([] :: envS) K)) ch
      = .ok (.next (.seq [.initialization { id := "ok", typ := .bool },
            .mapLookup (.var "prev") (.var "ok") lofE termE
              (.int .uint64) (.int .uint64), fireIf, recordAssign]
          ([("prev", .base ⟨σ.nextAddr⟩)] :: envS) K),
        { σA with heap := Heap.set σA.heap (.base ⟨σ.nextAddr⟩) ⟨some (.int .uint64), .int 0 .uint64⟩, nextAddr := σ.nextAddr + 1 }, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_u64))
  let σA1 : ExecState := { σA with heap := Heap.set σA.heap (.base ⟨σ.nextAddr⟩) ⟨some (.int .uint64), .int 0 .uint64⟩, nextAddr := σ.nextAddr + 1 }
  -- P4c: pop + the ok allocation (2)
  have hP4c : stepFnIter 2 σA1 (.next (.seq
      [.initialization { id := "ok", typ := .bool },
        .mapLookup (.var "prev") (.var "ok") lofE termE
          (.int .uint64) (.int .uint64), fireIf, recordAssign]
      ([("prev", .base ⟨σ.nextAddr⟩)] :: envS) K)) ch
      = .ok (.next (.seq [.mapLookup (.var "prev") (.var "ok") lofE
            termE (.int .uint64) (.int .uint64), fireIf, recordAssign]
          (envP envS σ.nextAddr) K),
        { σA1 with heap := Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool false⟩, nextAddr := σ.nextAddr + 2 }, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_seq_pop)
      (stepFnIter_one (stepFn_init_seq (hdef := defaultValue_bool)))
  let σA2 : ExecState := { σA1 with heap := Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool false⟩, nextAddr := σ.nextAddr + 2 }
  -- cell reads at σA2
  have htA2 : Heap.lookup σA2.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩ := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨lt⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lt)]
    show Heap.lookup (Heap.set σA.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨lt⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ lt)]
    show Heap.lookup (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨lt⟩) = _
    rw [lookup_set_other (fun he => hd1 he.symm)]
    exact ht
  have hnA2 : Heap.lookup σA2.heap (.base ⟨ln⟩)
      = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨ln⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ln)]
    show Heap.lookup (Heap.set σA.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨ln⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ ln)]
    show Heap.lookup (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨ln⟩) = _
    rw [lookup_set_other (fun he => hd2 he.symm)]
    exact hn
  have hTwA2 : Heap.lookup σA2.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm
          (wN : Int) pendV drvV sq tr hlV) := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ tw)]
    show Heap.lookup (Heap.set σA.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨tw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ tw)]
    exact lookup_set_self
  have hNwA2 : Heap.lookup σA2.heap (.base ⟨nw⟩)
      = some ⟨dtyNw, .struct tidN fsN⟩ := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨nw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ nw)]
    show Heap.lookup (Heap.set σA.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨nw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ nw)]
    show Heap.lookup (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨nw⟩) = _
    rw [lookup_set_other (fun he => hd3 he.symm)]
    exact hNw
  have hlmA2 : Heap.lookup σA2.heap (.base ⟨lm⟩)
      = some ⟨none, .mapData (toEntries kvs)⟩ := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨lm⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lm)]
    show Heap.lookup (Heap.set σA.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨lm⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ lm)]
    show Heap.lookup (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨lm⟩) = _
    rw [lookup_set_other (fun he => hd4 he.symm)]
    exact hlm
  -- env lookups through the declaration scope (definitional skips)
  have henvT' : LocalEnv.lookup (envP envS σ.nextAddr) "t"
      = some (.base ⟨lt⟩) := henvT
  have henvN' : LocalEnv.lookup (envP envS σ.nextAddr) "nd"
      = some (.base ⟨ln⟩) := henvN
  -- P4d-P4i: pop + the mapLookup entry + the two target refs (6)
  let KML : Cont := .seq [fireIf, recordAssign]
    (envP envS σ.nextAddr) K
  let KRH : Cont := .rhsK (.mapLookup (.int .uint64) (.int .uint64))
    [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
     .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
    [] [termE] (.seqn #[]) (envP envS σ.nextAddr) KML
  have hP4d : stepFnIter 6 σA2 (.next (.seq
      [.mapLookup (.var "prev") (.var "ok") lofE termE
        (.int .uint64) (.int .uint64), fireIf, recordAssign]
      (envP envS σ.nextAddr) K)) ch
      = .ok (.evalE lofE (envP envS σ.nextAddr) KRH, σA2, ch) := by
    with_unfolding_all rfl
  -- P4j: the map read (5)
  have hP4j : stepFnIter 5 σA2
      (.evalE lofE (envP envS σ.nextAddr) KRH) ch
      = .ok (.retV (.map ⟨some (.base ⟨lm⟩)⟩) KRH, σA2, ch) :=
    read_field_seg (henv := henvT') (hp := htA2) (hw := hTwA2)
      (hf := twinFs_leaderOf)
  -- P4k: → the term read (1 + 5)
  let KRH2 : Cont := .rhsK (.mapLookup (.int .uint64) (.int .uint64))
    [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
     .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
    [.map ⟨some (.base ⟨lm⟩)⟩] [] (.seqn #[])
    (envP envS σ.nextAddr) KML
  have hP4k : stepFnIter 1 σA2
      (.retV (.map ⟨some (.base ⟨lm⟩)⟩) KRH) ch
      = .ok (.evalE termE (envP envS σ.nextAddr) KRH2, σA2, ch) := by
    with_unfolding_all rfl
  have hP4l : stepFnIter 5 σA2
      (.evalE termE (envP envS σ.nextAddr) KRH2) ch
      = .ok (.retV (.int (tm : Int) .uint64) KRH2, σA2, ch) :=
    read_field_seg (henv := henvN') (hp := hnA2) (hw := hNwA2)
      (hf := hterm)
  -- P4m: the lookup applies (1)
  have hP4m : stepFnIter 1 σA2
      (.retV (.int (tm : Int) .uint64) KRH2) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
           .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
          [.int (cnt kvs (tm : Int) : Int) .uint64,
           .bool (idxOf? kvs (tm : Int)).isSome]
          (.seqn #[]) (envP envS σ.nextAddr) KML), σA2, ch) :=
    stepFnIter_one (stepFn_rhs_apply
      (h := applyRhsOp_mapLookup_toEntries (hlook := hlmA2) htm))
  -- P4n: the prev store (1)
  have hprevA2 : Heap.lookup σA2.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.int .uint64), .int 0 .uint64⟩ := by
    show Heap.lookup (Heap.set σA1.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  let σA3 : ExecState := { σA2 with heap := Heap.set σA2.heap (.base ⟨σ.nextAddr⟩) ⟨some (.int .uint64), .int (cnt kvs (tm : Int) : Int) .uint64⟩ }
  have hP4n : stepFnIter 1 σA2 (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr⟩)) [] [],
       .chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
      [.int (cnt kvs (tm : Int) : Int) .uint64,
       .bool (idxOf? kvs (tm : Int)).isSome]
      (.seqn #[]) (envP envS σ.nextAddr) KML)) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
          [.bool (idxOf? kvs (tm : Int)).isSome]
          (.seqn #[]) (envP envS σ.nextAddr) KML), σA3, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .int .uint64) (old := .int 0 .uint64)
        (hlook := hprevA2)
        (hnorm := normalize_int_u64 (cnt_lt hvals (tm : Int)))))
  -- P4o: the ok store (1)
  have hokA3 : Heap.lookup σA3.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some .bool, .bool false⟩ := by
    show Heap.lookup (Heap.set σA2.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ σ.nextAddr + 1)]
    exact lookup_set_self
  have hP4o : stepFnIter 1 σA3 (.next (.storeK
      [.chain (.addr (.base ⟨σ.nextAddr + 1⟩)) [] []]
      [.bool (idxOf? kvs (tm : Int)).isSome]
      (.seqn #[]) (envP envS σ.nextAddr) KML)) ch
      = .ok (.next (.storeK [] [] (.seqn #[])
          (envP envS σ.nextAddr) KML),
        prefixSt tw σ.nextAddr nodesV netV liveV lm byV (cN : Int) cm
          (wN : Int) pendV drvV sq tr hlV kvs tm σ, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .bool) (old := .bool false)
        (hlook := hokA3) (hnorm := normalize_bool)))
  -- P4p: drain + splice/pop to fireIf (3)
  have hP4p : stepFnIter 3
      (prefixSt tw σ.nextAddr nodesV netV liveV lm byV (cN : Int) cm
        (wN : Int) pendV drvV sq tr hlV kvs tm σ)
      (.next (.storeK [] [] (.seqn #[]) (envP envS σ.nextAddr)
        KML)) ch
      = .ok (.exec fireIf (envP envS σ.nextAddr)
          (.seq [recordAssign] (envP envS σ.nextAddr) K),
        prefixSt tw σ.nextAddr nodesV netV liveV lm byV (cN : Int) cm
          (wN : Int) pendV drvV sq tr hlV kvs tm σ, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_splice_pop (ss := #[]) rfl)
  exact stepFnIter_chain hP1 (stepFnIter_chain hP2a
    (stepFnIter_chain hP2b (stepFnIter_chain hP2c
      (stepFnIter_chain hP2d (stepFnIter_chain hP2e
        (stepFnIter_chain hP2f (stepFnIter_chain hP2g
          (stepFnIter_chain hP2h (stepFnIter_chain hP3
            (stepFnIter_chain hP4a (stepFnIter_chain hP4b
              (stepFnIter_chain hP4c (stepFnIter_chain hP4d
                (stepFnIter_chain hP4j (stepFnIter_chain hP4k
                  (stepFnIter_chain hP4l (stepFnIter_chain hP4m
                    (stepFnIter_chain hP4n (stepFnIter_chain hP4o
                      hP4p)))))))))))))))))))

/-! ## 6. The record segment (`t.leaderOf[nd.term] = nd.id`,
20 steps — both branches share it) -/

/-- **The record walk**: the overwrite-insert, ending the whole span
(`.next K`). Stated at any state whose checker cells carry the
expected shapes (the branches instantiate it after their own
writes). -/
theorem s1_record_seg {envP' : LocalEnv} {K : Cont}
    {lt ln tw nw lm : Nat} {dtyT dtyN dtyNw : Option Ty}
    {nodesV netV liveV byV pendV drvV hlV : GoValue}
    {c cm w : Int} {sq : Int} {tr : GoString}
    {fsN : Array (String × GoValue)}
    {kvs' : List (Int × Nat)} {tm idv : Nat}
    (henvT : LocalEnv.lookup envP' "t" = some (.base ⟨lt⟩))
    (henvN : LocalEnv.lookup envP' "nd" = some (.base ⟨ln⟩))
    (σR : ExecState) (ch : Choices)
    (ht : Heap.lookup σR.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩)
    (hn : Heap.lookup σR.heap (.base ⟨ln⟩)
      = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩)
    (hTw : Heap.lookup σR.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    (hNw : Heap.lookup σR.heap (.base ⟨nw⟩)
      = some ⟨dtyNw, .struct tidN fsN⟩)
    (hterm : StructFields.lookup fsN "term"
      = some (.int (tm : Int) .uint64))
    (hid : StructFields.lookup fsN "id"
      = some (.int (idv : Int) .uint64))
    (hlm : Heap.lookup σR.heap (.base ⟨lm⟩)
      = some ⟨none, .mapData (toEntries kvs')⟩)
    (htm : tm < 2 ^ 64) (hidv : idv < 2 ^ 64) :
    stepFnIter 20 σR
        (.exec recordAssign envP' (.seq [] envP' K)) ch
      = .ok (.next K,
        { σR with heap := Heap.set σR.heap (.base ⟨lm⟩) ⟨none, .mapData (toEntries (setk kvs' (tm : Int) idv))⟩ }, ch) := by
  let KS1 : Cont := .stmtOpK (.mapAssign (.int .uint64) (.int .uint64))
    0 [] [termE, idE] envP' (.seq [] envP' K)
  have hR1 : stepFnIter 1 σR
      (.exec recordAssign envP' (.seq [] envP' K)) ch
      = .ok (.evalE lofE envP' KS1, σR, ch) := by
    with_unfolding_all rfl
  have hR2 : stepFnIter 5 σR (.evalE lofE envP' KS1) ch
      = .ok (.retV (.map ⟨some (.base ⟨lm⟩)⟩) KS1, σR, ch) :=
    read_field_seg (henv := henvT) (hp := ht) (hw := hTw)
      (hf := twinFs_leaderOf)
  let KS2 : Cont := .stmtOpK (.mapAssign (.int .uint64) (.int .uint64))
    0 [.map ⟨some (.base ⟨lm⟩)⟩] [idE] envP' (.seq [] envP' K)
  have hR3 : stepFnIter 1 σR (.retV (.map ⟨some (.base ⟨lm⟩)⟩) KS1) ch
      = .ok (.evalE termE envP' KS2, σR, ch) := by
    with_unfolding_all rfl
  have hR4 : stepFnIter 5 σR (.evalE termE envP' KS2) ch
      = .ok (.retV (.int (tm : Int) .uint64) KS2, σR, ch) :=
    read_field_seg (henv := henvN) (hp := hn) (hw := hNw)
      (hf := hterm)
  let KS3 : Cont := .stmtOpK (.mapAssign (.int .uint64) (.int .uint64))
    0 [.int (tm : Int) .uint64, .map ⟨some (.base ⟨lm⟩)⟩] [] envP'
    (.seq [] envP' K)
  have hR5 : stepFnIter 1 σR (.retV (.int (tm : Int) .uint64) KS2) ch
      = .ok (.evalE idE envP' KS3, σR, ch) := by
    with_unfolding_all rfl
  have hR6 : stepFnIter 5 σR (.evalE idE envP' KS3) ch
      = .ok (.retV (.int (idv : Int) .uint64) KS3, σR, ch) :=
    read_field_seg (henv := henvN) (hp := hn) (hw := hNw) (hf := hid)
  have happly : applyStmtOp σR ch
      (.mapAssign (.int .uint64) (.int .uint64)) 0
      (([GoValue.int (idv : Int) .uint64] ++
        [GoValue.int (tm : Int) .uint64,
         GoValue.map ⟨some (.base ⟨lm⟩)⟩]).reverse)
      = .ok ({ σR with heap := Heap.set σR.heap (.base ⟨lm⟩) ⟨none, .mapData (toEntries (setk kvs' (tm : Int) idv))⟩ }, ch) := by
    show applyStmtOp σR ch _ 0
      [GoValue.map ⟨some (.base ⟨lm⟩)⟩, GoValue.int (tm : Int) .uint64,
       GoValue.int (idv : Int) .uint64] = _
    simp only [applyStmtOp, applyStmtOpCore, Bind.bind, Except.bind,
      pure, Except.pure]
    rw [GoLean.MapMem.mapAssignValue_toEntries (hlook := hlm)
      (GoLean.SliceMem.unorm_nat_of_lt htm)
      (GoLean.SliceMem.unorm_nat_of_lt hidv)]
  have hR7 : stepFnIter 1 σR (.retV (.int (idv : Int) .uint64) KS3) ch
      = .ok (.next (.seq [] envP' K),
        { σR with heap := Heap.set σR.heap (.base ⟨lm⟩) ⟨none, .mapData (toEntries (setk kvs' (tm : Int) idv))⟩ }, ch) :=
    stepFnIter_one (stepFn_stmtOp_apply (h := happly))
  have hR8 : stepFnIter 1
      { σR with heap := Heap.set σR.heap (.base ⟨lm⟩) ⟨none, .mapData (toEntries (setk kvs' (tm : Int) idv))⟩ }
      (.next (.seq [] envP' K)) ch
      = .ok (.next K,
        { σR with heap := Heap.set σR.heap (.base ⟨lm⟩) ⟨none, .mapData (toEntries (setk kvs' (tm : Int) idv))⟩ }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain hR1 (stepFnIter_chain hR2
    (stepFnIter_chain hR3 (stepFnIter_chain hR4 (stepFnIter_chain hR5
      (stepFnIter_chain hR6 (stepFnIter_chain hR7 hR8))))))

/-! ## 7. The headline: `s1_span_computes` -/

/-- The model-side half: the machine's overwrite-insert projects to a
lookup-equal `s1Step` (pure data-refinement commutation). -/
theorem s1_abs_step {kvs : List (Int × Nat)} (hwf : KeysWf kvs)
    {cN wN tm idv : Nat} (htm : tm < 2 ^ 64) :
    LookupEq
      ⟨projLOf (setk kvs (tm : Int) idv), cN + 1,
        wN + (if s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv) then 1 else 0)⟩
      (s1Step ⟨projLOf kvs, cN, wN⟩ (tm, idv)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro t
  show lookupTerm (projLOf (setk kvs (tm : Int) idv)) t
    = lookupTerm ((tm, idv) :: projLOf kvs) t
  exact lookupTerm_projLOf_setk hwf htm t

/-- **THE S1 SPAN-COMPUTES-MODEL THEOREM** (the I4 interface's
interpreter half for S1, in the banked weak form): the interpreter
walking the S1 record span from ANY symbolic checker state performs
exactly `s1Step` on the abstract projection — claims `+1` EXACTLY,
violations `+ (if s1Fires … then 1 else 0)` EXACTLY (the MODEL
predicate literally in the machine-state readout), the claim map
updated to `setk` (lookup-equal to `s1Step`'s cons by `s1_abs_step`),
the trace existential, everything else framed. -/
theorem s1_span_computes
    (henvT : LocalEnv.lookup envS "t" = some (.base ⟨lt⟩))
    (henvN : LocalEnv.lookup envS "nd" = some (.base ⟨ln⟩))
    (σ : ExecState) (ch : Choices)
    (ht : Heap.lookup σ.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩)
    (hn : Heap.lookup σ.heap (.base ⟨ln⟩)
      = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV (cN : Int) cm (wN : Int)
          pendV drvV sq tr hlV))
    (hNw : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some ⟨dtyNw, .struct tidN fsN⟩)
    (hterm : StructFields.lookup fsN "term"
      = some (.int (tm : Int) .uint64))
    (hid : StructFields.lookup fsN "id"
      = some (.int (idv : Int) .uint64))
    (hlm : Heap.lookup σ.heap (.base ⟨lm⟩)
      = some ⟨none, .mapData (toEntries kvs)⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hag : bfTB.Agrees σ)
    (hd1 : lt ≠ tw) (hd2 : ln ≠ tw) (hd3 : nw ≠ tw) (hd4 : lm ≠ tw)
    (_hd5 : nw ≠ lm)
    (hkwf : KeysWf kvs)
    (hvals : ∀ p ∈ kvs, p.2 < 2 ^ 64)
    (hc1 : (cN : Int) + 1 < 2 ^ 63) (hm0 : -(2 ^ 63) ≤ cm)
    (hm1 : cm < 2 ^ 63) (hw1 : (wN : Int) + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63)
    (htm : tm < 2 ^ 64) (hidv : idv < 2 ^ 64) :
    ∃ m ≤ 5200, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ (.exec s1Block envS K) ch
        = .ok (.next K, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV
              ((cN + 1 : Nat) : Int) cm
              ((wN + (if s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv)
                  then 1 else 0) : Nat) : Int)
              pendV drvV sq tr' hlV)
      ∧ Heap.lookup σ'.heap (.base ⟨lm⟩)
          = some ⟨none, .mapData (toEntries (setk kvs (tm : Int) idv))⟩
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw → x ≠ lm →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr + 2 ≤ σ'.nextAddr
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  -- the machine guard value and its model reading
  have hfire := s1Fires_projLOf (cN := cN) (wN := wN) hkwf htm hidv
    hvals
  -- frontier bounds
  have hltna : lt < σ.nextAddr := by
    rcases Nat.lt_or_ge lt σ.nextAddr with h | h
    · exact h
    · rw [hfr lt h] at ht; cases ht
  have hlnna : ln < σ.nextAddr := by
    rcases Nat.lt_or_ge ln σ.nextAddr with h | h
    · exact h
    · rw [hfr ln h] at hn; cases hn
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnwna : nw < σ.nextAddr := by
    rcases Nat.lt_or_ge nw σ.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNw; cases hNw
  have hlmna : lm < σ.nextAddr := by
    rcases Nat.lt_or_ge lm σ.nextAddr with h | h
    · exact h
    · rw [hfr lm h] at hlm; cases hlm
  -- the prefix
  have hpre := s1_prefix (K := K) henvT henvN σ ch ht hn hTw hNw hterm
    hlm hfr hag hd1 hd2 hd3 hd4 hvals hc1 hm0 hm1 (by omega) hq0 hq1
    htm
  let σB : ExecState := prefixSt tw σ.nextAddr nodesV netV liveV lm
    byV (cN : Int) cm (wN : Int) pendV drvV sq tr hlV kvs tm σ
  -- cell facts at σB (heap = the 5-set nest, frontier + 2)
  have hσBna : σB.nextAddr = σ.nextAddr + 2 := rfl
  have hlkB : ∀ x : Nat, x ≠ tw → x < σ.nextAddr →
      Heap.lookup σB.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hxt hxna
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (fun he => hxt he.symm)]
  have htB : Heap.lookup σB.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩ := by
    rw [hlkB lt hd1 hltna]; exact ht
  have hnB : Heap.lookup σB.heap (.base ⟨ln⟩)
      = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
    rw [hlkB ln hd2 hlnna]; exact hn
  have hNwB : Heap.lookup σB.heap (.base ⟨nw⟩)
      = some ⟨dtyNw, .struct tidN fsN⟩ := by
    rw [hlkB nw hd3 hnwna]; exact hNw
  have hlmB : Heap.lookup σB.heap (.base ⟨lm⟩)
      = some ⟨none, .mapData (toEntries kvs)⟩ := by
    rw [hlkB lm hd4 hlmna]; exact hlm
  have hTwB : Heap.lookup σB.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm
          (wN : Int) pendV drvV sq tr hlV) := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨tw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ tw),
      lookup_set_other (by omega : σ.nextAddr ≠ tw),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ tw),
      lookup_set_other (by omega : σ.nextAddr ≠ tw)]
    exact lookup_set_self
  have hokB : Heap.lookup σB.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some .bool, .bool (idxOf? kvs (tm : Int)).isSome⟩ :=
    lookup_set_self
  have hprevB : Heap.lookup σB.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.int .uint64),
          .int (cnt kvs (tm : Int) : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hfrB : ∀ x, σB.nextAddr ≤ x →
      Heap.lookup σB.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx2 : σ.nextAddr + 2 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set σ.heap (.base ⟨tw⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : tw ≠ x)]
    exact hfr x (by omega)
  have hagB : bfTB.Agrees σB := hag
  -- the guard entry: 3 steps to the ok read value
  have hG1 : stepFnIter 3 σB (.exec fireIf (envP envS σ.nextAddr)
      (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
      = .ok (.retV (.bool (idxOf? kvs (tm : Int)).isSome)
          (.andK (.neqCmp (.int .uint64) (.var "prev") idE)
            (envP envS σ.nextAddr)
            (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
              (.seq [recordAssign] (envP envS σ.nextAddr) K))),
        σB, ch) := by
    have g1 : stepFnIter 2 σB (.exec fireIf (envP envS σ.nextAddr)
        (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
        = .ok (.evalE (.var "ok") (envP envS σ.nextAddr)
            (.andK (.neqCmp (.int .uint64) (.var "prev") idE)
              (envP envS σ.nextAddr)
              (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
                (.seq [recordAssign] (envP envS σ.nextAddr) K))),
          σB, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain g1 (stepFnIter_one
      (stepFn_var (henv := rfl) (hlook := hokB)))
  -- the shared clean-tail (else branch → record): given the walk to
  -- `retV (.bool false)` at the ifK, finish and conclude
  have hcleanTail : ∀ mG : Nat, mG ≤ 20 →
      stepFnIter mG σB (.exec fireIf (envP envS σ.nextAddr)
        (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
      = .ok (.retV (.bool false)
          (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
            (.seq [recordAssign] (envP envS σ.nextAddr) K)),
        σB, ch) →
      s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv) = false →
      ∃ m ≤ 5200, ∃ σ' : ExecState, ∃ tr' : GoString,
        stepFnIter m σ (.exec s1Block envS K) ch
          = .ok (.next K, σ', ch)
        ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
            = some (twCell nodesV netV liveV lm byV
                ((cN + 1 : Nat) : Int) cm
                ((wN + (if s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv)
                    then 1 else 0) : Nat) : Int)
                pendV drvV sq tr' hlV)
        ∧ Heap.lookup σ'.heap (.base ⟨lm⟩)
            = some ⟨none, .mapData (toEntries (setk kvs (tm : Int) idv))⟩
        ∧ (∀ x, x < σ.nextAddr → x ≠ tw → x ≠ lm →
            Heap.lookup σ'.heap (.base ⟨x⟩)
              = Heap.lookup σ.heap (.base ⟨x⟩))
        ∧ σ.nextAddr + 2 ≤ σ'.nextAddr
        ∧ (∀ x, σ'.nextAddr ≤ x →
            Heap.lookup σ'.heap (.base ⟨x⟩) = none)
        ∧ bfTB.Agrees σ' := by
    intro mG hmG hguard hfireF
    -- ifK false → else → splice/pop (3 steps)
    have hif : stepFnIter 3 σB (.retV (.bool false)
        (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
          (.seq [recordAssign] (envP envS σ.nextAddr) K))) ch
        = .ok (.exec recordAssign (envP envS σ.nextAddr)
            (.seq [] (envP envS σ.nextAddr) K), σB, ch) := by
      have i1 : stepFnIter 1 σB (.retV (.bool false)
          (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
            (.seq [recordAssign] (envP envS σ.nextAddr) K))) ch
          = .ok (.exec (.seqn #[]) (envP envS σ.nextAddr)
              (.seq [recordAssign] (envP envS σ.nextAddr) K),
            σB, ch) := by
        with_unfolding_all rfl
      exact stepFnIter_chain i1 (stepFnIter_splice_pop (ss := #[]) rfl)
    -- the record segment at σB
    have hrec := s1_record_seg (envP' := envP envS σ.nextAddr)
      (K := K) henvT henvN σB ch htB hnB hTwB
      hNwB hterm hid hlmB htm hidv
    have hall := stepFnIter_chain hpre (stepFnIter_chain hguard
      (stepFnIter_chain hif hrec))
    refine ⟨_, ?_, _, tr, hall, ?_, ?_, ?_, ?_, ?_, hagB⟩
    · omega
    · -- the twin cell readout
      rw [hfireF]
      show Heap.lookup (Heap.set σB.heap (.base ⟨lm⟩) _)
        (.base ⟨tw⟩) = _
      rw [lookup_set_other hd4,
        show ((cN + 1 : Nat) : Int) = (cN : Int) + 1 from by omega,
        show ((wN + (if false then 1 else 0) : Nat) : Int)
          = (wN : Int) from by simp]
      exact hTwB
    · exact lookup_set_self
    · intro x hxna hxt hxl
      show Heap.lookup (Heap.set σB.heap (.base ⟨lm⟩) _)
        (.base ⟨x⟩) = _
      rw [lookup_set_other (fun he => hxl he.symm)]
      exact hlkB x hxt hxna
    · show σ.nextAddr + 2 ≤ σB.nextAddr
      exact Nat.le_of_eq hσBna.symm
    · intro x hx
      have hx' : σB.nextAddr ≤ x := hx
      show Heap.lookup (Heap.set σB.heap (.base ⟨lm⟩) _)
        (.base ⟨x⟩) = none
      rw [lookup_set_other (by omega : lm ≠ x)]
      exact hfrB x hx'
  -- case split on the machine guard
  cases hok : (idxOf? kvs (tm : Int)).isSome with
  | false =>
    -- BRANCH A: `ok` is false — the short-circuit skip
    have hfireF : s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv) = false := by
      rw [← hfire, hok]
      rfl
    have hguard : stepFnIter (3 + 1) σB
        (.exec fireIf (envP envS σ.nextAddr)
          (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
        = .ok (.retV (.bool false)
            (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
              (.seq [recordAssign] (envP envS σ.nextAddr) K)),
          σB, ch) := by
      have g2 : stepFnIter 1 σB
          (.retV (.bool (idxOf? kvs (tm : Int)).isSome)
            (.andK (.neqCmp (.int .uint64) (.var "prev") idE)
              (envP envS σ.nextAddr)
              (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
                (.seq [recordAssign] (envP envS σ.nextAddr) K)))) ch
          = .ok (.retV (.bool false)
              (.ifK violBranch (.seqn #[]) (envP envS σ.nextAddr)
                (.seq [recordAssign] (envP envS σ.nextAddr) K)),
            σB, ch) := by
        rw [hok]
        with_unfolding_all rfl
      exact stepFnIter_chain hG1 g2
    exact hcleanTail (3 + 1) (by omega) hguard hfireF
  | true =>
    -- the guard-true walk: 14 steps to the neq verdict at the ifK
    let KIF : Cont := .ifK violBranch (.seqn #[])
      (envP envS σ.nextAddr)
      (.seq [recordAssign] (envP envS σ.nextAddr) K)
    have hguardT : stepFnIter (3 + 11) σB
        (.exec fireIf (envP envS σ.nextAddr)
          (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
        = .ok (.retV (.bool
            (!((cnt kvs (tm : Int) : Int) == (idv : Int)))) KIF,
          σB, ch) := by
      have g2 : stepFnIter 2 σB
          (.retV (.bool (idxOf? kvs (tm : Int)).isSome)
            (.andK (.neqCmp (.int .uint64) (.var "prev") idE)
              (envP envS σ.nextAddr) KIF)) ch
          = .ok (.evalE (.var "prev") (envP envS σ.nextAddr)
              (.strictK (.neqCmp (.int .uint64)) [] [idE]
                (envP envS σ.nextAddr) (.boolK KIF)), σB, ch) := by
        rw [hok]
        with_unfolding_all rfl
      have g4 : stepFnIter 1 σB (.evalE (.var "prev")
          (envP envS σ.nextAddr)
          (.strictK (.neqCmp (.int .uint64)) [] [idE]
            (envP envS σ.nextAddr) (.boolK KIF))) ch
          = .ok (.retV (.int (cnt kvs (tm : Int) : Int) .uint64)
              (.strictK (.neqCmp (.int .uint64)) [] [idE]
                (envP envS σ.nextAddr) (.boolK KIF)), σB, ch) :=
        stepFnIter_one (stepFn_var (henv := rfl) (hlook := hprevB))
      have g5 : stepFnIter 1 σB
          (.retV (.int (cnt kvs (tm : Int) : Int) .uint64)
            (.strictK (.neqCmp (.int .uint64)) [] [idE]
              (envP envS σ.nextAddr) (.boolK KIF))) ch
          = .ok (.evalE idE (envP envS σ.nextAddr)
              (.strictK (.neqCmp (.int .uint64))
                [.int (cnt kvs (tm : Int) : Int) .uint64] []
                (envP envS σ.nextAddr) (.boolK KIF)), σB, ch) := by
        with_unfolding_all rfl
      have g6 : stepFnIter 5 σB (.evalE idE (envP envS σ.nextAddr)
          (.strictK (.neqCmp (.int .uint64))
            [.int (cnt kvs (tm : Int) : Int) .uint64] []
            (envP envS σ.nextAddr) (.boolK KIF))) ch
          = .ok (.retV (.int (idv : Int) .uint64)
              (.strictK (.neqCmp (.int .uint64))
                [.int (cnt kvs (tm : Int) : Int) .uint64] []
                (envP envS σ.nextAddr) (.boolK KIF)), σB, ch) :=
        read_field_seg (henv := henvN) (hp := hnB) (hw := hNwB)
          (hf := hid)
      have g7 : stepFnIter 1 σB (.retV (.int (idv : Int) .uint64)
          (.strictK (.neqCmp (.int .uint64))
            [.int (cnt kvs (tm : Int) : Int) .uint64] []
            (envP envS σ.nextAddr) (.boolK KIF))) ch
          = .ok (.retV (.bool
              (!((cnt kvs (tm : Int) : Int) == (idv : Int))))
              (.boolK KIF), σB, ch) := by
        refine stepFnIter_one (stepFn_strict_apply (h := ?_))
        rw [show (List.reverse [GoValue.int (idv : Int) .uint64,
            GoValue.int (cnt kvs (tm : Int) : Int) .uint64])
          = [GoValue.int (cnt kvs (tm : Int) : Int) .uint64,
             GoValue.int (idv : Int) .uint64] from rfl]
        exact GoLean.SliceMem.applyStrictOp_neqCmp_int
      have g8 : stepFnIter 1 σB (.retV (.bool
          (!((cnt kvs (tm : Int) : Int) == (idv : Int))))
          (.boolK KIF)) ch
          = .ok (.retV (.bool
              (!((cnt kvs (tm : Int) : Int) == (idv : Int)))) KIF,
            σB, ch) := by
        with_unfolding_all rfl
      exact stepFnIter_chain hG1 (stepFnIter_chain g2
        (stepFnIter_chain g4 (stepFnIter_chain g5
          (stepFnIter_chain g6 (stepFnIter_chain g7 g8)))))
    cases hne : ((cnt kvs (tm : Int) : Int) == (idv : Int)) with
    | true =>
      -- BRANCH B: same claimant — no fire
      have hfireF : s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv)
          = false := by
        rw [← hfire, hok, hne]
        rfl
      have hguard : stepFnIter (3 + 11) σB
          (.exec fireIf (envP envS σ.nextAddr)
            (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
          = .ok (.retV (.bool false) KIF, σB, ch) := by
        rw [← show (!((cnt kvs (tm : Int) : Int) == (idv : Int)))
          = false from by rw [hne]; rfl]
        exact hguardT
      exact hcleanTail (3 + 11) (by omega) hguard hfireF
    | false =>
      -- BRANCH C: THE FIRE — three `utoa` calls, the concat, the
      -- `viol` call, then the record
      have hfireT : s1Fires ⟨projLOf kvs, cN, wN⟩ (tm, idv)
          = true := by
        rw [← hfire, hok, hne]
        rfl
      have hguard : stepFnIter (3 + 11) σB
          (.exec fireIf (envP envS σ.nextAddr)
            (.seq [recordAssign] (envP envS σ.nextAddr) K)) ch
          = .ok (.retV (.bool true) KIF, σB, ch) := by
        rw [← show (!((cnt kvs (tm : Int) : Int) == (idv : Int)))
          = true from by rw [hne]; rfl]
        exact hguardT
      -- ifK true → violBranch, block+pop (3 steps)
      let KRec2 : Cont := .seq [recordAssign] (envP envS σ.nextAddr) K
      let envQ0 : LocalEnv := [] :: envP envS σ.nextAddr
      have hifT : stepFnIter 3 σB (.retV (.bool true) KIF) ch
          = .ok (.exec (.seqn #[.initialization
                { id := "$c2291", typ := .string },
              .call #[.var "$c2291"] ⟨"utoa"⟩ #[termE]]) envQ0
              (.seq [.seqn #[.initialization
                  { id := "$c2292", typ := .string },
                .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
                .seqn #[.initialization
                  { id := "$c2293", typ := .string },
                .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
                .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
                envQ0 KRec2), σB, ch) := by
        have i1 : stepFnIter 1 σB (.retV (.bool true) KIF) ch
            = .ok (.exec violBranch (envP envS σ.nextAddr) KRec2,
              σB, ch) := by
          with_unfolding_all rfl
        exact stepFnIter_chain i1
          (stepFnIter_chain (stepFnIter_one stepFn_block)
            (stepFnIter_one stepFn_seq_pop))
      -- ===== CALL UNIT 1 ($c2291 := utoa(nd.term)) =====
      -- splice/pop + init + pop + call entry (5 steps)
      let envQ1 : LocalEnv :=
        [("$c2291", .base ⟨σB.nextAddr⟩)] :: envP envS σ.nextAddr
      let KU1seq : Cont := .seq
        [.seqn #[.initialization { id := "$c2292", typ := .string },
          .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
         .seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
         .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
        envQ1 KRec2
      let σF1 : ExecState := { σB with heap := Heap.set σB.heap (.base ⟨σB.nextAddr⟩) (sCell (gs [])), nextAddr := σB.nextAddr + 1 }
      have hU1a : stepFnIter 5 σB (.exec (.seqn #[.initialization
            { id := "$c2291", typ := .string },
          .call #[.var "$c2291"] ⟨"utoa"⟩ #[termE]]) envQ0
          (.seq [.seqn #[.initialization
              { id := "$c2292", typ := .string },
            .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
            .seqn #[.initialization
              { id := "$c2293", typ := .string },
            .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
            .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
            envQ0 KRec2)) ch
          = .ok (.evalE termE envQ1
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2291"])] []
                [] envQ1 KU1seq), σF1, ch) := by
        have u1 : stepFnIter 2 σB (.exec (.seqn #[.initialization
              { id := "$c2291", typ := .string },
            .call #[.var "$c2291"] ⟨"utoa"⟩ #[termE]]) envQ0
            (.seq [.seqn #[.initialization
                { id := "$c2292", typ := .string },
              .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
              .seqn #[.initialization
                { id := "$c2293", typ := .string },
              .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
              envQ0 KRec2)) ch
            = .ok (.exec (.initialization
                { id := "$c2291", typ := .string }) envQ0
                (.seq [.call #[.var "$c2291"] ⟨"utoa"⟩ #[termE],
                  .seqn #[.initialization
                    { id := "$c2292", typ := .string },
                  .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
                  .seqn #[.initialization
                    { id := "$c2293", typ := .string },
                  .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
                  envQ0 KRec2), σB, ch) :=
          stepFnIter_splice_pop (ss := #[.initialization
            { id := "$c2291", typ := .string },
            .call #[.var "$c2291"] ⟨"utoa"⟩ #[termE]]) rfl
        have u2 : stepFnIter 1 σB (.exec (.initialization
            { id := "$c2291", typ := .string }) envQ0
            (.seq [.call #[.var "$c2291"] ⟨"utoa"⟩ #[termE],
              .seqn #[.initialization
                { id := "$c2292", typ := .string },
              .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
              .seqn #[.initialization
                { id := "$c2293", typ := .string },
              .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
              envQ0 KRec2)) ch
            = .ok (.next (.seq [.call #[.var "$c2291"] ⟨"utoa"⟩
                #[termE],
              .seqn #[.initialization
                { id := "$c2292", typ := .string },
              .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
              .seqn #[.initialization
                { id := "$c2293", typ := .string },
              .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
              envQ1 KRec2), σF1, ch) :=
          stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
        have u3 : stepFnIter 2 σF1 (.next (.seq
            [.call #[.var "$c2291"] ⟨"utoa"⟩ #[termE],
              .seqn #[.initialization
                { id := "$c2292", typ := .string },
              .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]],
              .seqn #[.initialization
                { id := "$c2293", typ := .string },
              .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
            envQ1 KRec2)) ch
            = .ok (.evalE termE envQ1
                (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2291"])]
                  [] [] envQ1 KU1seq), σF1, ch) := by
          with_unfolding_all rfl
        exact stepFnIter_chain u1 (stepFnIter_chain u2 u3)
      -- the term read at σF1 (5)
      have hnF1 : Heap.lookup σF1.heap (.base ⟨ln⟩)
          = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
        show Heap.lookup (Heap.set σB.heap (.base ⟨σB.nextAddr⟩) _)
          (.base ⟨ln⟩) = _
        rw [lookup_set_other (show σB.nextAddr ≠ ln by
          rw [hσBna]; omega)]
        exact hnB
      have hNwF1 : Heap.lookup σF1.heap (.base ⟨nw⟩)
          = some ⟨dtyNw, .struct tidN fsN⟩ := by
        show Heap.lookup (Heap.set σB.heap (.base ⟨σB.nextAddr⟩) _)
          (.base ⟨nw⟩) = _
        rw [lookup_set_other (show σB.nextAddr ≠ nw by
          rw [hσBna]; omega)]
        exact hNwB
      have hU1b : stepFnIter 5 σF1 (.evalE termE envQ1
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2291"])] [] []
            envQ1 KU1seq)) ch
          = .ok (.retV (.int (tm : Int) .uint64)
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2291"])] []
                [] envQ1 KU1seq), σF1, ch) :=
        read_field_seg (henv := henvN) (hp := hnF1) (hw := hNwF1)
          (hf := hterm)
      -- the utoa call (≤ 74·20 + 87)
      have hU1c := utoa_call_span (envC := envQ1) (tgt := "$c2291")
        (ltc := σB.nextAddr) (Kc := KU1seq) rfl htm σF1 ch (gs [])
        hagB lookup_set_self
        (by
          intro x hx
          have hx1 : σB.nextAddr + 1 ≤ x := hx
          show Heap.lookup (Heap.set σB.heap (.base ⟨σB.nextAddr⟩) _)
            (.base ⟨x⟩) = none
          rw [lookup_set_other (by omega : σB.nextAddr ≠ x)]
          exact hfrB x (by omega))
      obtain ⟨mU1, hmU1, str1, σU1, hrun1, hres1, hna1, hfrm1, hfrs1,
        hag1⟩ := hU1c
      have hna1' : σF1.nextAddr + 2 ≤ σU1.nextAddr
          ∧ σU1.nextAddr ≤ σF1.nextAddr + 4 := by
        rw [hna1]
        split <;> omega
      have hF1na : σF1.nextAddr = σ.nextAddr + 3 := by
        show σB.nextAddr + 1 = _
        omega
      -- the cell chase at σU1 (everything below σ.nextAddr + 2,
      -- except the c1 target, is σB's)
      have hchase1 : ∀ x : Nat, x < σ.nextAddr + 2 →
          Heap.lookup σU1.heap (.base ⟨x⟩)
            = Heap.lookup σB.heap (.base ⟨x⟩) := by
        intro x hx
        rw [hfrm1 x (by omega) (by omega)]
        show Heap.lookup (Heap.set σB.heap (.base ⟨σB.nextAddr⟩) _)
          (.base ⟨x⟩) = _
        rw [lookup_set_other (by omega : σB.nextAddr ≠ x)]
      -- ===== CALL UNIT 2 ($c2292 := utoa(prev)) =====
      let envQ2 : LocalEnv :=
        [("$c2292", .base ⟨σU1.nextAddr⟩),
         ("$c2291", .base ⟨σB.nextAddr⟩)] :: envP envS σ.nextAddr
      let KU2seq : Cont := .seq
        [.seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
         .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]]
        envQ2 KRec2
      let σF2 : ExecState := { σU1 with heap := Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) (sCell (gs [])), nextAddr := σU1.nextAddr + 1 }
      have hU2a : stepFnIter 7 σU1
          (.exec (.seqn #[]) envQ1 KU1seq) ch
          = .ok (.evalE (.var "prev") envQ2
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2292"])] []
                [] envQ2 KU2seq), σF2, ch) := by
        have u1 : stepFnIter 2 σU1
            (.exec (.seqn #[]) envQ1 KU1seq) ch
            = .ok (.exec (.seqn #[.initialization
                  { id := "$c2292", typ := .string },
                .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]]) envQ1
                (.seq [.seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ1 KRec2), σU1, ch) :=
          stepFnIter_splice_pop (ss := #[]) rfl
        have u2 : stepFnIter 2 σU1 (.exec (.seqn #[.initialization
              { id := "$c2292", typ := .string },
            .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]]) envQ1
            (.seq [.seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ1 KRec2)) ch
            = .ok (.exec (.initialization
                { id := "$c2292", typ := .string }) envQ1
                (.seq [.call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"],
                  .seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ1 KRec2), σU1, ch) :=
          stepFnIter_splice_pop (ss := #[.initialization
            { id := "$c2292", typ := .string },
            .call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"]]) rfl
        have u3 : stepFnIter 1 σU1 (.exec (.initialization
            { id := "$c2292", typ := .string }) envQ1
            (.seq [.call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"],
              .seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ1 KRec2)) ch
            = .ok (.next (.seq
                [.call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"],
                  .seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2), σF2, ch) :=
          stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
        have u4 : stepFnIter 2 σF2 (.next (.seq
            [.call #[.var "$c2292"] ⟨"utoa"⟩ #[.var "prev"],
              .seqn #[.initialization { id := "$c2293", typ := .string },
          .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2)) ch
            = .ok (.evalE (.var "prev") envQ2
                (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2292"])]
                  [] [] envQ2 KU2seq), σF2, ch) := by
          with_unfolding_all rfl
        exact stepFnIter_chain u1 (stepFnIter_chain u2
          (stepFnIter_chain u3 u4))
      -- the prev read at σF2
      have hprevF2 : Heap.lookup σF2.heap (.base ⟨σ.nextAddr⟩)
          = some ⟨some (.int .uint64),
              .int (cnt kvs (tm : Int) : Int) .uint64⟩ := by
        show Heap.lookup (Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) _)
          (.base ⟨σ.nextAddr⟩) = _
        rw [lookup_set_other (show σU1.nextAddr ≠ σ.nextAddr by
          rw [hF1na] at hna1'; omega),
          hchase1 σ.nextAddr (by omega)]
        exact hprevB
      have hU2b : stepFnIter 1 σF2 (.evalE (.var "prev") envQ2
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2292"])] [] []
            envQ2 KU2seq)) ch
          = .ok (.retV (.int (cnt kvs (tm : Int) : Int) .uint64)
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2292"])] []
                [] envQ2 KU2seq), σF2, ch) :=
        stepFnIter_one (stepFn_var (henv := rfl) (hlook := hprevF2))
      -- the utoa call 2
      have hU2c := utoa_call_span (envC := envQ2) (tgt := "$c2292")
        (ltc := σU1.nextAddr) (Kc := KU2seq) rfl
        (cnt_lt hvals (tm : Int)) σF2 ch (gs [])
        hag1 lookup_set_self
        (by
          intro x hx
          have hx1 : σU1.nextAddr + 1 ≤ x := hx
          show Heap.lookup (Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) _)
            (.base ⟨x⟩) = none
          rw [lookup_set_other (by omega : σU1.nextAddr ≠ x)]
          exact hfrs1 x (by omega))
      obtain ⟨mU2, hmU2, str2, σU2, hrun2, hres2, hna2, hfrm2, hfrs2,
        hag2⟩ := hU2c
      have hna2' : σF2.nextAddr + 2 ≤ σU2.nextAddr
          ∧ σU2.nextAddr ≤ σF2.nextAddr + 4 := by
        rw [hna2]
        split <;> omega
      have hF2na : σU1.nextAddr + 1 = σF2.nextAddr := rfl
      have hchase2 : ∀ x : Nat, x < σ.nextAddr + 2 →
          Heap.lookup σU2.heap (.base ⟨x⟩)
            = Heap.lookup σB.heap (.base ⟨x⟩) := by
        intro x hx
        have hxlt : x < σU1.nextAddr := by
          rw [hF1na] at hna1'
          omega
        rw [hfrm2 x (by omega) (by omega)]
        show Heap.lookup (Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) _)
          (.base ⟨x⟩) = _
        rw [lookup_set_other (by omega : σU1.nextAddr ≠ x),
          hchase1 x (by omega)]
      -- the c1 cell at σU2
      have hc1U2 : Heap.lookup σU2.heap (.base ⟨σB.nextAddr⟩)
          = some (sCell str1) := by
        have hb : σB.nextAddr < σU1.nextAddr := by
          rw [hF1na] at hna1'
          rw [hσBna]
          omega
        rw [hfrm2 σB.nextAddr (by omega) (by omega)]
        show Heap.lookup (Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) _)
          (.base ⟨σB.nextAddr⟩) = _
        rw [lookup_set_other (by omega : σU1.nextAddr ≠ σB.nextAddr)]
        exact hres1
      -- ===== CALL UNIT 3 ($c2293 := utoa(nd.id)) =====
      let envQ3 : LocalEnv :=
        [("$c2293", .base ⟨σU2.nextAddr⟩),
         ("$c2292", .base ⟨σU1.nextAddr⟩),
         ("$c2291", .base ⟨σB.nextAddr⟩)] :: envP envS σ.nextAddr
      let KU3seq : Cont := .seq
        [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ3 KRec2
      let σF3 : ExecState := { σU2 with heap := Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) (sCell (gs [])), nextAddr := σU2.nextAddr + 1 }
      have hU3a : stepFnIter 7 σU2
          (.exec (.seqn #[]) envQ2 KU2seq) ch
          = .ok (.evalE idE envQ3
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2293"])] []
                [] envQ3 KU3seq), σF3, ch) := by
        have u1 : stepFnIter 2 σU2
            (.exec (.seqn #[]) envQ2 KU2seq) ch
            = .ok (.exec (.seqn #[.initialization
                  { id := "$c2293", typ := .string },
                .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]]) envQ2
                (.seq [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2),
              σU2, ch) :=
          stepFnIter_splice_pop (ss := #[]) rfl
        have u2 : stepFnIter 2 σU2 (.exec (.seqn #[.initialization
              { id := "$c2293", typ := .string },
            .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]]) envQ2
            (.seq [.call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2)) ch
            = .ok (.exec (.initialization
                { id := "$c2293", typ := .string }) envQ2
                (.seq [.call #[.var "$c2293"] ⟨"utoa"⟩ #[idE],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2), σU2, ch) :=
          stepFnIter_splice_pop (ss := #[.initialization
            { id := "$c2293", typ := .string },
            .call #[.var "$c2293"] ⟨"utoa"⟩ #[idE]]) rfl
        have u3 : stepFnIter 1 σU2 (.exec (.initialization
            { id := "$c2293", typ := .string }) envQ2
            (.seq [.call #[.var "$c2293"] ⟨"utoa"⟩ #[idE],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ2 KRec2)) ch
            = .ok (.next (.seq
                [.call #[.var "$c2293"] ⟨"utoa"⟩ #[idE],
                  .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ3 KRec2), σF3, ch) :=
          stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
        have u4 : stepFnIter 2 σF3 (.next (.seq
            [.call #[.var "$c2293"] ⟨"utoa"⟩ #[idE],
              .call #[] ⟨"main.twin.viol"⟩ #[.var "t", violStrE]] envQ3 KRec2)) ch
            = .ok (.evalE idE envQ3
                (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2293"])]
                  [] [] envQ3 KU3seq), σF3, ch) := by
          with_unfolding_all rfl
        exact stepFnIter_chain u1 (stepFnIter_chain u2
          (stepFnIter_chain u3 u4))
      -- the id read at σF3
      have hnF3 : Heap.lookup σF3.heap (.base ⟨ln⟩)
          = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
        show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          (.base ⟨ln⟩) = _
        rw [lookup_set_other (show σU2.nextAddr ≠ ln by
          rw [hF1na] at hna1'
          rw [← hF2na] at hna2'
          omega),
          hchase2 ln (by omega)]
        exact hnB
      have hNwF3 : Heap.lookup σF3.heap (.base ⟨nw⟩)
          = some ⟨dtyNw, .struct tidN fsN⟩ := by
        show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          (.base ⟨nw⟩) = _
        rw [lookup_set_other (show σU2.nextAddr ≠ nw by
          rw [hF1na] at hna1'
          rw [← hF2na] at hna2'
          omega),
          hchase2 nw (by omega)]
        exact hNwB
      have hU3b : stepFnIter 5 σF3 (.evalE idE envQ3
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2293"])] [] []
            envQ3 KU3seq)) ch
          = .ok (.retV (.int (idv : Int) .uint64)
              (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref "$c2293"])] []
                [] envQ3 KU3seq), σF3, ch) :=
        read_field_seg (henv := henvN) (hp := hnF3) (hw := hNwF3)
          (hf := hid)
      -- the utoa call 3
      have hU3c := utoa_call_span (envC := envQ3) (tgt := "$c2293")
        (ltc := σU2.nextAddr) (Kc := KU3seq) rfl hidv σF3 ch (gs [])
        hag2 lookup_set_self
        (by
          intro x hx
          have hx1 : σU2.nextAddr + 1 ≤ x := hx
          show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
            (.base ⟨x⟩) = none
          rw [lookup_set_other (by omega : σU2.nextAddr ≠ x)]
          exact hfrs2 x (by omega))
      obtain ⟨mU3, hmU3, str3, σU3, hrun3, hres3, hna3, hfrm3, hfrs3,
        hag3⟩ := hU3c
      have hna3' : σF3.nextAddr + 2 ≤ σU3.nextAddr
          ∧ σU3.nextAddr ≤ σF3.nextAddr + 4 := by
        rw [hna3]
        split <;> omega
      have hF3na : σU2.nextAddr + 1 = σF3.nextAddr := rfl
      have hchase3 : ∀ x : Nat, x < σ.nextAddr + 2 →
          Heap.lookup σU3.heap (.base ⟨x⟩)
            = Heap.lookup σB.heap (.base ⟨x⟩) := by
        intro x hx
        have hxlt : x < σU2.nextAddr := by
          rw [hF1na] at hna1'
          rw [← hF2na] at hna2'
          omega
        rw [hfrm3 x (by omega) (by omega)]
        show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          (.base ⟨x⟩) = _
        rw [lookup_set_other (by omega : σU2.nextAddr ≠ x),
          hchase2 x (by omega)]
      -- the c1/c2 cells at σU3
      have hbounds : σB.nextAddr < σU1.nextAddr
          ∧ σU1.nextAddr < σU2.nextAddr
          ∧ σU2.nextAddr < σU3.nextAddr := by
        rw [hF1na] at hna1'
        rw [← hF2na] at hna2'
        rw [← hF3na] at hna3'
        rw [hσBna]
        omega
      have hc1U3 : Heap.lookup σU3.heap (.base ⟨σB.nextAddr⟩)
          = some (sCell str1) := by
        rw [hfrm3 σB.nextAddr (by omega) (by omega)]
        show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          (.base ⟨σB.nextAddr⟩) = _
        rw [lookup_set_other (by omega : σU2.nextAddr ≠ σB.nextAddr)]
        exact hc1U2
      have hc2U3 : Heap.lookup σU3.heap (.base ⟨σU1.nextAddr⟩)
          = some (sCell str2) := by
        rw [hfrm3 σU1.nextAddr (by omega) (by omega)]
        show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          (.base ⟨σU1.nextAddr⟩) = _
        rw [lookup_set_other (by omega : σU2.nextAddr ≠ σU1.nextAddr)]
        exact hres2
      -- the base cells at σU3
      have htU3 : Heap.lookup σU3.heap (.base ⟨lt⟩)
          = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩ := by
        rw [hchase3 lt (by omega)]
        exact htB
      have hnU3 : Heap.lookup σU3.heap (.base ⟨ln⟩)
          = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
        rw [hchase3 ln (by omega)]
        exact hnB
      have hTwU3 : Heap.lookup σU3.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm
              (wN : Int) pendV drvV sq tr hlV) := by
        rw [hchase3 tw (by omega)]
        exact hTwB
      have hNwU3 : Heap.lookup σU3.heap (.base ⟨nw⟩)
          = some ⟨dtyNw, .struct tidN fsN⟩ := by
        rw [hchase3 nw (by omega)]
        exact hNwB
      have hlmU3 : Heap.lookup σU3.heap (.base ⟨lm⟩)
          = some ⟨none, .mapData (toEntries kvs)⟩ := by
        rw [hchase3 lm (by omega)]
        exact hlmB
      -- ===== THE VIOL CALL =====
      let KVseq : Cont := .seq [] envQ3 KRec2
      -- entry + the t read (V0: 2, V1: 1, V2: 1)
      have hV0 : stepFnIter 3 σU3
          (.exec (.seqn #[]) envQ3 KU3seq) ch
          = .ok (.evalE (.var "t") envQ3
              (.callArgsK ⟨"main.twin.viol"⟩ [] [] [violStrE] envQ3
                KVseq), σU3, ch) := by
        have v1 : stepFnIter 2 σU3
            (.exec (.seqn #[]) envQ3 KU3seq) ch
            = .ok (.exec (.call #[] ⟨"main.twin.viol"⟩
                #[.var "t", violStrE]) envQ3 KVseq, σU3, ch) :=
          stepFnIter_splice_pop (ss := #[]) rfl
        have v2 : stepFnIter 1 σU3 (.exec (.call #[]
            ⟨"main.twin.viol"⟩ #[.var "t", violStrE]) envQ3 KVseq) ch
            = .ok (.evalE (.var "t") envQ3
                (.callArgsK ⟨"main.twin.viol"⟩ [] [] [violStrE] envQ3
                  KVseq), σU3, ch) := by
          with_unfolding_all rfl
        exact stepFnIter_chain v1 v2
      have hV2 : stepFnIter 1 σU3 (.evalE (.var "t") envQ3
          (.callArgsK ⟨"main.twin.viol"⟩ [] [] [violStrE] envQ3
            KVseq)) ch
          = .ok (.retV (.addr (.base ⟨tw⟩))
              (.callArgsK ⟨"main.twin.viol"⟩ [] [] [violStrE] envQ3
                KVseq), σU3, ch) :=
        stepFnIter_one (stepFn_var (henv := henvT) (hlook := htU3))
      -- the concat towers
      let TA : Cont := .callArgsK ⟨"main.twin.viol"⟩ []
        [.addr (.base ⟨tw⟩)] [] envQ3 KVseq
      let W1 : Cont := .strictK .add [] [.var "$c2293"] envQ3 TA
      let W2 : Cont := .strictK .add []
        [.stringLit (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32])] envQ3 W1
      let W3 : Cont := .strictK .add [] [.var "$c2292"] envQ3 W2
      let W4 : Cont := .strictK .add []
        [.stringLit (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32])] envQ3 W3
      -- V3: dispatch to the c1 read (8 steps)
      have hV3 : stepFnIter 8 σU3 (.retV (.addr (.base ⟨tw⟩))
          (.callArgsK ⟨"main.twin.viol"⟩ [] [] [violStrE] envQ3
            KVseq)) ch
          = .ok (.evalE (.var "$c2291") envQ3
              (.strictK .add [.string (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32])] []
                envQ3 W4), σU3, ch) := by
        with_unfolding_all rfl
      -- V4: the c1 read
      have hV4 : stepFnIter 1 σU3 (.evalE (.var "$c2291") envQ3
          (.strictK .add [.string (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32])] []
            envQ3 W4)) ch
          = .ok (.retV (.string str1)
              (.strictK .add [.string (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32])] []
                envQ3 W4), σU3, ch) :=
        stepFnIter_one (stepFn_var (henv := rfl) (hlook := hc1U3))
      -- V5: fold + dispatch to the c2 read (5 steps)
      have hV5 : stepFnIter 5 σU3 (.retV (.string str1)
          (.strictK .add [.string (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32])] []
            envQ3 W4)) ch
          = .ok (.evalE (.var "$c2292") envQ3
              (.strictK .add [.string (GoString.append
                (GoString.append (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1)
                (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))] [] envQ3 W2), σU3, ch) := by
        with_unfolding_all rfl
      -- V6: the c2 read
      have hV6 : stepFnIter 1 σU3 (.evalE (.var "$c2292") envQ3
          (.strictK .add [.string (GoString.append
            (GoString.append (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1)
            (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))] [] envQ3 W2)) ch
          = .ok (.retV (.string str2)
              (.strictK .add [.string (GoString.append
                (GoString.append (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1)
                (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))] [] envQ3 W2), σU3, ch) :=
        stepFnIter_one (stepFn_var (henv := rfl) (hlook := hc2U3))
      -- V7: fold + dispatch to the c3 read (5 steps)
      have hV7 : stepFnIter 5 σU3 (.retV (.string str2)
          (.strictK .add [.string (GoString.append
            (GoString.append (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1)
            (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))] [] envQ3 W2)) ch
          = .ok (.evalE (.var "$c2293") envQ3
              (.strictK .add [.string (GoString.append
                (GoString.append (GoString.append (GoString.append
                  (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1) (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))
                  str2) (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32]))] [] envQ3 TA),
            σU3, ch) := by
        with_unfolding_all rfl
      -- V8: the c3 read
      have hV8 : stepFnIter 1 σU3 (.evalE (.var "$c2293") envQ3
          (.strictK .add [.string (GoString.append
            (GoString.append (GoString.append (GoString.append
              (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1) (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))
              str2) (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32]))] [] envQ3 TA)) ch
          = .ok (.retV (.string str3)
              (.strictK .add [.string (GoString.append
                (GoString.append (GoString.append (GoString.append
                  (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1) (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))
                  str2) (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32]))] [] envQ3 TA),
            σU3, ch) :=
        stepFnIter_one (stepFn_var (henv := rfl) (hlook := hres3))
      -- V9: the final fold (1 step)
      let SV : GoString := GoString.append (GoString.append
        (GoString.append (GoString.append (GoString.append
          (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1) (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32])) str2)
        (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32])) str3
      have hV9 : stepFnIter 1 σU3 (.retV (.string str3)
          (.strictK .add [.string (GoString.append
            (GoString.append (GoString.append (GoString.append
              (gs [83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32]) str1) (gs [32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104, 32, 110, 111, 100, 101, 32]))
              str2) (gs [32, 97, 110, 100, 32, 110, 111, 100, 101, 32]))] [] envQ3 TA)) ch
          = .ok (.retV (.string SV) TA, σU3, ch) := by
        with_unfolding_all rfl
      -- V10: the viol call span (42 steps)
      have hV10 := viol_call_span (envC := envQ3) (Kc := KVseq)
        (tw := tw) σU3 ch SV hag3 hTwU3 hfrs3
        (by omega) hc1 hm0 hm1 (by omega) hw1 hq0 hq1
      let trV : GoString := GoString.append tr
        (GoString.append (gs [32, 33]) SV)
      let σV : ExecState := twinSt (Heap.set (Heap.set (Heap.set
        σU3.heap (.base ⟨σU3.nextAddr⟩) (tParCell tw))
        (.base ⟨σU3.nextAddr + 1⟩) (sCell SV)) (.base ⟨tw⟩)
        (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm
          ((wN : Int) + 1) pendV drvV sq trV hlV))
        (σU3.nextAddr + 2)
      -- V11: block exit to the record (2 steps)
      have hV11 : stepFnIter 2 σV (.next KVseq) ch
          = .ok (.exec recordAssign (envP envS σ.nextAddr)
              (.seq [] (envP envS σ.nextAddr) K), σV, ch) := by
        with_unfolding_all rfl
      -- the record premises at σV
      have hltV : lt < σU3.nextAddr := by omega
      have htV : Heap.lookup σV.heap (.base ⟨lt⟩)
          = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩ := by
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨lt⟩) = _
        rw [lookup_set_other (fun he => hd1 he.symm),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ lt),
          lookup_set_other (by omega : σU3.nextAddr ≠ lt)]
        exact htU3
      have hnV : Heap.lookup σV.heap (.base ⟨ln⟩)
          = some ⟨dtyN, .addr (.base ⟨nw⟩)⟩ := by
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨ln⟩) = _
        rw [lookup_set_other (fun he => hd2 he.symm),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ ln),
          lookup_set_other (by omega : σU3.nextAddr ≠ ln)]
        exact hnU3
      have hNwV : Heap.lookup σV.heap (.base ⟨nw⟩)
          = some ⟨dtyNw, .struct tidN fsN⟩ := by
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨nw⟩) = _
        rw [lookup_set_other (fun he => hd3 he.symm),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ nw),
          lookup_set_other (by omega : σU3.nextAddr ≠ nw)]
        exact hNwU3
      have hlmV : Heap.lookup σV.heap (.base ⟨lm⟩)
          = some ⟨none, .mapData (toEntries kvs)⟩ := by
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨lm⟩) = _
        rw [lookup_set_other (fun he => hd4 he.symm),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ lm),
          lookup_set_other (by omega : σU3.nextAddr ≠ lm)]
        exact hlmU3
      have hTwV : Heap.lookup σV.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV ((cN : Int) + 1) cm
              ((wN : Int) + 1) pendV drvV sq trV hlV) :=
        lookup_set_self
      -- V12: the record segment (20 steps)
      have hV12 := s1_record_seg (envP' := envP envS σ.nextAddr)
        (K := K) henvT henvN σV ch htV hnV hTwV hNwV hterm hid hlmV
        htm hidv
      -- ===== ASSEMBLE =====
      have hall := stepFnIter_chain hpre (stepFnIter_chain hguard (stepFnIter_chain hifT (stepFnIter_chain hU1a (stepFnIter_chain hU1b (stepFnIter_chain hrun1 (stepFnIter_chain hU2a (stepFnIter_chain hU2b (stepFnIter_chain hrun2 (stepFnIter_chain hU3a (stepFnIter_chain hU3b (stepFnIter_chain hrun3 (stepFnIter_chain hV0 (stepFnIter_chain hV2 (stepFnIter_chain hV3 (stepFnIter_chain hV4 (stepFnIter_chain hV5 (stepFnIter_chain hV6 (stepFnIter_chain hV7 (stepFnIter_chain hV8 (stepFnIter_chain hV9 (stepFnIter_chain hV10 (stepFnIter_chain hV11 (hV12)))))))))))))))))))))))
      refine ⟨_, ?_, _, trV, hall, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- the bound
        have hb1 : mU1 ≤ 74 * 20 + 87 := by
          have := dig10_le20 htm
          omega
        have hb2 : mU2 ≤ 74 * 20 + 87 := by
          have := dig10_le20 (cnt_lt hvals (tm : Int))
          omega
        have hb3 : mU3 ≤ 74 * 20 + 87 := by
          have := dig10_le20 hidv
          omega
        omega
      · -- the twin cell readout
        rw [hfireT]
        show Heap.lookup (Heap.set σV.heap (.base ⟨lm⟩) _)
          (.base ⟨tw⟩) = _
        rw [lookup_set_other hd4,
          show ((cN + 1 : Nat) : Int) = (cN : Int) + 1 from by omega,
          show ((wN + (if true then 1 else 0) : Nat) : Int)
            = (wN : Int) + 1 from by simp]
        exact hTwV
      · exact lookup_set_self
      · -- the frame
        intro x hxna hxt hxl
        show Heap.lookup (Heap.set σV.heap (.base ⟨lm⟩) _)
          (.base ⟨x⟩) = _
        rw [lookup_set_other (fun he => hxl he.symm)]
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨x⟩) = _
        rw [lookup_set_other (fun he => hxt he.symm),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ x),
          lookup_set_other (by omega : σU3.nextAddr ≠ x),
          hchase3 x (by omega)]
        exact hlkB x hxt hxna
      · -- the frontier
        show σ.nextAddr + 2 ≤ σV.nextAddr
        show σ.nextAddr + 2 ≤ σU3.nextAddr + 2
        omega
      · -- freshness
        intro x hx
        have hx' : σU3.nextAddr + 2 ≤ x := hx
        show Heap.lookup (Heap.set σV.heap (.base ⟨lm⟩) _)
          (.base ⟨x⟩) = none
        rw [lookup_set_other (by omega : lm ≠ x)]
        show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
          (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
          (.base ⟨tw⟩) _) (.base ⟨x⟩) = none
        rw [lookup_set_other (by omega : tw ≠ x),
          lookup_set_other (by omega : σU3.nextAddr + 1 ≠ x),
          lookup_set_other (by omega : σU3.nextAddr ≠ x)]
        exact hfrs3 x (by omega)
      · -- Agrees
        exact ⟨rfl, rfl, rfl, rfl⟩

end Walk

end GoLean.RaftSeam.SpanS1
