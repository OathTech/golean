import GoLeanProofs.Examples.WordFreq.Range

/-!
# WordFreq — HarnessR

The queried read (`counts[query]`), the `$res0`/`$res1` stores, the two
frame exits back to the harness, the harness's own 4-tuple return, the
end-to-end run, and the target theorem `wordfreq_total`.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-! ## The exit-phase front (every mutable result cell symbolic) -/

/-- The 31-cell front with the result cells symbolic: `r3/r4` the
harness string results, `r5/r6` its numeric results, `r15/r16` the
harness's `hits`/`best`, `r19/r20` the subject's `$res0`/`$res1`. At
all-defaults this IS `wHeapCount` (definitional identity `xF_id`). -/
def xFront (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int)
    (b k cap : Nat) (iv0 sv2 : Int) (r3 r4 : GoString)
    (r5 r6 r15 r16 r19 r20 : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv), (.base ⟨2⟩, su64 qv),
   (.base ⟨3⟩, sstr r3), (.base ⟨4⟩, sstr r4),
   (.base ⟨5⟩, su64 r5), (.base ⟨6⟩, su64 r6), (.base ⟨7⟩, sstr (gs l)),
   (.base ⟨8⟩, su64 bnv), (.base ⟨9⟩, su64 bsv),
   (.base ⟨10⟩, sstr (gs l)), (.base ⟨11⟩, sstr (gs l)),
   (.base ⟨12⟩, su64 biv), (.base ⟨13⟩, sbool false),
   (.base ⟨14⟩, sstr (gs q)), (.base ⟨15⟩, su64 r15),
   (.base ⟨16⟩, su64 r16), (.base ⟨17⟩, sstr (gs l)),
   (.base ⟨18⟩, sstr (gs q)), (.base ⟨19⟩, su64 r19),
   (.base ⟨20⟩, su64 r20), (.base ⟨21⟩, slsCell b 0 k cap),
   (.base ⟨22⟩, sstr (gs l)), (.base ⟨23⟩, slsCell b 0 k cap),
   (.base ⟨24⟩, slsCell 25 0 0 0), (.base ⟨25⟩, strArrCell [] 0),
   (.base ⟨26⟩, slsCell b 0 k cap), (.base ⟨27⟩, sint iv0),
   (.base ⟨28⟩, sint sv2), (.base ⟨29⟩, sbool false),
   (.base ⟨30⟩, sbool false)]

/-- At the defaults the exit front IS the count front. -/
theorem xF_id (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int)
    (b k cap : Nat) (iv0 sv2 : Int) :
    wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      = xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 GoString.empty
          GoString.empty 0 0 0 0 0 0 := rfl

/-- The exit-phase state: the symbolic-result front over the count
debris (`D`, the five prologue cells at `a`, the loop/range debris
`tail`). -/
abbrev xSt (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (r3 r4 : GoString)
    (r5 r6 r15 r16 r19 r20 : Int) (D : Heap) (a : Nat)
    (kvs : List (List UInt8 × Nat)) (civ : Int) (tail : Heap)
    (na : Nat) : ExecState :=
  wSt σ (xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
    r15 r16 r19 r20 ++ D
    ++ [(.base ⟨a⟩, mhW (a + 1)), (.base ⟨a + 1⟩, mdW kvs),
        (.base ⟨a + 2⟩, mhW (a + 1)), (.base ⟨a + 3⟩, sint civ),
        (.base ⟨a + 4⟩, sbool false)]
    ++ tail) na

/-- No exit-front address reaches 31. -/
theorem lookup_xFront_none (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (r3 r4 : GoString)
    (r5 r6 r15 r16 r19 r20 : Int) {x : Nat} (hx : 31 ≤ x) :
    Heap.lookup (xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4
      r5 r6 r15 r16 r19 r20) (.base ⟨x⟩) = none := by
  simp only [xFront, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    base_beq_false (by omega : (20 : Nat) ≠ x),
    base_beq_false (by omega : (21 : Nat) ≠ x),
    base_beq_false (by omega : (22 : Nat) ≠ x),
    base_beq_false (by omega : (23 : Nat) ≠ x),
    base_beq_false (by omega : (24 : Nat) ≠ x),
    base_beq_false (by omega : (25 : Nat) ≠ x),
    base_beq_false (by omega : (26 : Nat) ≠ x),
    base_beq_false (by omega : (27 : Nat) ≠ x),
    base_beq_false (by omega : (28 : Nat) ≠ x),
    base_beq_false (by omega : (29 : Nat) ≠ x),
    base_beq_false (by omega : (30 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-! ## The exit phase: the queried read, the result stores, the two
frame exits, the harness return -/

/-- `$res1 = best` (subject). -/
abbrev wfAsgnRes1 : Stmt := .assign (.var "$res1") (.var "best")

section ExitPhase

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (r3 r4 : GoString)
  (r5 r6 r15 r16 r19 r20 : Int) (D : Heap) (a : Nat)
  (kvs : List (List UInt8 × Nat)) (civ : Int) (tail : Heap) (na : Nat)
  (ch : Choices)

/-- Exit A (13 steps): the result seam → `$res0 := counts[query]`
lands (the queried READ — an absent key answers 0). -/
theorem wfx_A (nb : Nat) (ha : 31 ≤ a) (hD : DeadFrom D a) :
    stepFnIter 13
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (rKRes a nb)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
            (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16
            (IntKind.normalize .uint64 ((cntW kvs q : Nat) : Int)) r20
            D a kvs civ tail na, ch) := by
  have hWDx : DeadFrom
      (xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 ++ D) a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_xFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3
          r4 r5 r6 r15 r16 r19 r20 (by omega))]
      exact hD x hx
  -- eA1+eA2: pop + splice
  have h1 : stepFnIter 1
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (rKRes a nb)) ch
      = .ok (.exec wfResSeqn (rEnv a nb)
            (.seq [] (rEnv a nb) wfFrameK),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
      r15 r16 r19 r20 D a kvs civ tail na)
    (ss := #[.assign (.var "$res0")
        (.mapGet (.var "counts") (.var "query") tStr tU64),
      wfAsgnRes1, .returnStmt])
    (env := rEnv a nb) (rest := []) (k := wfFrameK) (ch := ch))
  -- eA3 (5 steps, rfl): to the `counts` read point
  have h3 : stepFnIter 5
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.seq ((#[.assign (.var "$res0")
          (.mapGet (.var "counts") (.var "query") tStr tU64),
        wfAsgnRes1, .returnStmt] : Array Stmt).toList ++ [])
        (rEnv a nb) wfFrameK)) ch
      = .ok (.evalE (.var "counts") (rEnv a nb)
            (.strictK (.mapGet tStr tU64) [] [.var "query"] (rEnv a nb)
              (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
                (.seqn #[]) (rEnv a nb)
                (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb)
                  wfFrameK))),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  -- eA4: the `counts` read
  have h4 : stepFnIter 1
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.evalE (.var "counts") (rEnv a nb)
        (.strictK (.mapGet tStr tU64) [] [.var "query"] (rEnv a nb)
          (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
            (.seqn #[]) (rEnv a nb)
            (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))))
        ch
      = .ok (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
            (.strictK (.mapGet tStr tU64) [] [.var "query"] (rEnv a nb)
              (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
                (.seqn #[]) (rEnv a nb)
                (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb)
                  wfFrameK))),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 2⟩)
      (c := mhW (a + 1)) rfl ?_)
    exact lookup_five hWDx (by omega : (2 : Nat) < 5)
  -- eA5 (2 steps, rfl): the `query` read delivers `gs q`
  have h5 : stepFnIter 2
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
        (.strictK (.mapGet tStr tU64) [] [.var "query"] (rEnv a nb)
          (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
            (.seqn #[]) (rEnv a nb)
            (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))))
        ch
      = .ok (.retV (.string (gs q))
            (.strictK (.mapGet tStr tU64)
              [.map ⟨some (Loc.base ⟨a + 1⟩)⟩] [] (rEnv a nb)
              (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
                (.seqn #[]) (rEnv a nb)
                (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb)
                  wfFrameK))),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  -- eA6: the map READ at the query key
  have hlkD : Heap.lookup
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na).heap
      (.base ⟨a + 1⟩) = some ⟨none, .mapData (toEntriesW kvs)⟩ :=
    lookup_five hWDx (by omega : (1 : Nat) < 5)
  have h6 := stepFnIter_one (stepFn_strict_apply
    (done := [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]) (env := rEnv a nb)
    (k := .rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
      (.seqn #[]) (rEnv a nb)
      (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))
    (ch := ch)
    (applyStrictOp_mapGetW (a := ⟨a + 1⟩) (kvs := kvs) (w := q)
      (dty := none) hlkD))
  -- eA7 (2 steps, rfl): the store into `$res0` (cell 19)
  have h7 : stepFnIter 2
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.retV (.int ((cntW kvs q : Nat) : Int) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨19⟩)) [] []] [] []
          (.seqn #[]) (rEnv a nb)
          (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
            (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16
            (IntKind.normalize .uint64 ((cntW kvs q : Nat) : Int)) r20
            D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
      h4) h5) h6) h7

/-- Exit B (9 steps): `$res1 := best` — the `best` cell (at `nb` in
the debris) read and stored into cell 20. -/
theorem wfx_B (nb : Nat) (bv : Int) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (hnb : a + 5 ≤ nb)
    (hbest : Heap.lookup tail (.base ⟨nb⟩) = some (su64 bv)) :
    stepFnIter 9
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
        (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
            (.seq [.returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 (IntKind.normalize .uint64 bv) D a kvs civ tail
            na, ch) := by
  have hWDx : DeadFrom
      (xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 ++ D) a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_xFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3
          r4 r5 r6 r15 r16 r19 r20 (by omega))]
      exact hD x hx
  -- eB1+eB2: drain + splice
  have h1 : stepFnIter 1
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
        (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.exec (.seqn #[]) (rEnv a nb)
            (.seq [wfAsgnRes1, .returnStmt] (rEnv a nb) wfFrameK),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
      r15 r16 r19 r20 D a kvs civ tail na)
    (ss := #[]) (env := rEnv a nb)
    (rest := [wfAsgnRes1, .returnStmt]) (k := wfFrameK) (ch := ch))
  -- eB3 (4 steps, rfl): to the `best` read
  have h3 : stepFnIter 4
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wfAsgnRes1, .returnStmt]) (rEnv a nb) wfFrameK)) ch
      = .ok (.evalE (.var "best") (rEnv a nb)
            (.rhsK .vals [.chain (.addr (.base ⟨20⟩)) [] []] [] []
              (.seqn #[]) (rEnv a nb)
              (.seq [.returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  -- eB4: the `best` read
  have h4 : stepFnIter 1
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.evalE (.var "best") (rEnv a nb)
        (.rhsK .vals [.chain (.addr (.base ⟨20⟩)) [] []] [] []
          (.seqn #[]) (rEnv a nb)
          (.seq [.returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.retV (.int bv .uint64)
            (.rhsK .vals [.chain (.addr (.base ⟨20⟩)) [] []] [] []
              (.seqn #[]) (rEnv a nb)
              (.seq [.returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨nb⟩) (c := su64 bv)
      rfl ?_)
    show Heap.lookup
      ((xFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
          r16 r19 r20 ++ D
        ++ [(.base ⟨a⟩, mhW (a + 1)), (.base ⟨a + 1⟩, mdW kvs),
            (.base ⟨a + 2⟩, mhW (a + 1)), (.base ⟨a + 3⟩, sint civ),
            (.base ⟨a + 4⟩, sbool false)]) ++ tail)
      (.base ⟨nb⟩) = some (su64 bv)
    rw [lookup_append_right (by
      rw [lookup_append_right (hWDx nb (by omega)),
        lookup_cons_ne (base_beq_false (by omega : a ≠ nb)),
        lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ nb)),
        lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ nb)),
        lookup_cons_ne (base_beq_false (by omega : a + 3 ≠ nb)),
        lookup_cons_ne (base_beq_false (by omega : a + 4 ≠ nb))]
      rfl)]
    exact hbest
  -- eB5 (2 steps, rfl): the store into `$res1` (cell 20)
  have h5 : stepFnIter 2
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.retV (.int bv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨20⟩)) [] []] [] []
          (.seqn #[]) (rEnv a nb)
          (.seq [.returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
            (.seq [.returnStmt] (rEnv a nb) wfFrameK)),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 (IntKind.normalize .uint64 bv) D a kvs civ tail
            na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- Exit C (56 steps): the subject returns, the frame writes
`hits`/`best` back, the harness's four result stores and its own
return — the driver terminal. Every touched cell is front-concrete. -/
theorem wfx_C (nb : Nat) :
    stepFnIter 56
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
        (.seq [.returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.next .stop,
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 (gs l) (gs q)
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r19))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r20))
            (IntKind.normalize .uint64 r19)
            (IntKind.normalize .uint64 r20) r19 r20 D a kvs civ tail
            na, ch) := by
  -- eC1: drain
  have h1 : stepFnIter 1
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.storeK [] [] (.seqn #[]) (rEnv a nb)
        (.seq [.returnStmt] (rEnv a nb) wfFrameK))) ch
      = .ok (.exec (.seqn #[]) (rEnv a nb)
            (.seq [.returnStmt] (rEnv a nb) wfFrameK),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            r15 r16 r19 r20 D a kvs civ tail na, ch) := by
    with_unfolding_all rfl
  -- eC2: splice
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
      r15 r16 r19 r20 D a kvs civ tail na)
    (ss := #[]) (env := rEnv a nb) (rest := [.returnStmt])
    (k := wfFrameK) (ch := ch))
  -- eC3a (10 steps, rfl): the subject's return, the frame's
  -- `hits`/`best` write-back
  have h3 : stepFnIter 10
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6 r15
        r16 r19 r20 D a kvs civ tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt])
        (rEnv a nb) wfFrameK)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) hEnv3 hAfterWf),
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
            (IntKind.normalize .uint64 r19)
            (IntKind.normalize .uint64 r20) r19 r20 D a kvs civ tail
            na, ch) := by
    with_unfolding_all rfl
  -- eC3b (44 steps, rfl): the harness's four result stores and its
  -- return
  have h4 : stepFnIter 44
      (xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 r3 r4 r5 r6
        (IntKind.normalize .uint64 r19) (IntKind.normalize .uint64 r20)
        r19 r20 D a kvs civ tail na)
      (.next (.storeK [] [] (.seqn #[]) hEnv3 hAfterWf)) ch
      = .ok (.next .stop,
          xSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 (gs l) (gs q)
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r19))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r20))
            (IntKind.normalize .uint64 r19)
            (IntKind.normalize .uint64 r20) r19 r20 D a kvs civ tail
            na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
    h4

end ExitPhase

/-! ## The end-to-end run and the target theorem -/

/-- **The branch-uniform fuel BOUND** (affine `a·n + b`): the sum of
the phase bounds — build→scan `703·n + 402`, count `84·n + 85`, range
head 16, range loop `24·m + 1` charged at `m = n` (the distinct-word
count never exceeds the word count), exit 78. Dominates the measured
minimal fuels (`582/1145/2007/2575/…` at `n = 0/1/2/3/…`; bisected via
the native frontend, seed/qsel-independent at fixed `n`). -/
def wfFuel (n : Nat) : Nat := 811 * n + 582

/-- **The end-to-end machine run**: within `wfFuel n` steps from the
post-prelude seed, the machine reaches the driver terminal with the
four results in cells 3–6. -/
theorem wf_run (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) (ch : Choices) :
    ∃ k : Nat, k ≤ wfFuel n ∧
    ∃ (ch' : Choices) (b cap : Nat) (D tail : Heap) (a na : Nat)
      (kvs : List (List UInt8 × Nat)) (iv0 sv2 civ : Int),
      stepFnIter k
        (wSt sProg (wHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
          ((qsel : Nat) : Int)) 7) sHC0 ch
      = .ok (.next .stop,
          xSt sProg ((n : Nat) : Int) ((seed : Nat) : Int)
            ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
            (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
            iv0 sv2
            (gs (textFamily n seed)) (gs (qWord qsel))
            ((multiplicity (qWord qsel) (letterWords n seed) : Nat) : Int)
            ((maxMultiplicity (letterWords n seed) : Nat) : Int)
            ((multiplicity (qWord qsel) (letterWords n seed) : Nat) : Int)
            ((maxMultiplicity (letterWords n seed) : Nat) : Int)
            ((multiplicity (qWord qsel) (letterWords n seed) : Nat) : Int)
            ((maxMultiplicity (letterWords n seed) : Nat) : Int)
            D a kvs civ tail na, ch') := by
  let fs := letterWords n seed
  have hfsl : fs.length = n := letterWords_length n seed
  -- 1. build → scan
  obtain ⟨k₁, hk₁, b, cap, D, a, ch₁, sv2, hbuild, hinv⟩ :=
    build_scan_chain n seed qsel hn hseed hqsel ch
  obtain ⟨ha31, hD, hba, hcaplen, hbOr⟩ := hinv
  -- 2. the count phase
  have hcap' : fs.length ≤ cap := hcaplen
  obtain ⟨tail₁, na₁, htail₁, hna₁, hcount⟩ :=
    cn_phase sProg ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
      (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b cap fs
      ((wPos n : Nat) : Int) sv2 D a ha31 hD hbOr hcap'
      (by rw [hfsl]; exact hn) ch₁
  rw [hfsl] at hcount
  -- 3. the range head
  have hkvnorm : ∀ p ∈ countsFoldW fs,
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
    intro p hp
    have := countsFoldW_val_le fs hp
    exact unorm_nat_of_lt (by rw [hfsl] at this; omega)
  have hrhead := rg_head sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
    ((wPos n : Nat) : Int) sv2 D a (countsFoldW fs)
    ((n : Nat) : Int) tail₁ na₁ ch₁ ha31 hD htail₁ hna₁ hkvnorm
  -- 4. the range loop
  have hvals : ∀ p ∈ countsFoldW fs, p.2 ≤ n := by
    intro p hp
    have := countsFoldW_val_le fs hp
    omega
  obtain ⟨k₄, ch₄, tail₂, na₂, hk₄, hna₂, hbestlk, htail₂, hrloop⟩ :=
    rg_loop sProg ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
      (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
      ((wPos n : Nat) : Int) sv2 D a (countsFoldW fs)
      ((n : Nat) : Int) n (by omega) ha31 hD
      hkvnorm (countsFoldW_nodup_keys fs)
      (countsFoldW fs).length (countsFoldW fs) rfl #[] 0 na₁
      (tail₁ ++ [(Loc.base ⟨na₁⟩, su64 0)]) (na₁ + 1) ch₁
      ⟨[], by simp [toKeysW], by
        symm
        apply List.filter_eq_self.mpr
        intro z _
        simp⟩
      hvals (by omega) hna₁ (by omega) (by omega)
      (by
        rw [lookup_append_right (htail₁ na₁ (Nat.le_refl _))]
        exact lookup_singleton_self)
      (DeadFrom.push htail₁)
  rw [show (max 0 (maxOf ((countsFoldW fs).map Prod.snd)))
      = maxOf ((countsFoldW fs).map Prod.snd) from by omega] at hbestlk
  -- 5. the exit phase (`cnSt` at the count front IS `xSt` at the
  -- default result cells)
  have hxA := wfx_A sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
    ((wPos n : Nat) : Int) sv2 GoString.empty GoString.empty 0 0 0 0 0 0
    D a (countsFoldW fs) ((n : Nat) : Int) tail₂ na₂ ch₄ na₁
    ha31 hD
  have hhits : cntW (countsFoldW fs) (qWord qsel)
      = multiplicity (qWord qsel) fs := cnt_countsFoldW fs (qWord qsel)
  have hhits64 : multiplicity (qWord qsel) fs < 2 ^ 64 := by
    have h1 : (fs.filter (· = qWord qsel)).length ≤ fs.length :=
      List.length_filter_le _ _
    simp only [multiplicity]
    omega
  rw [hhits, unorm_nat_of_lt hhits64] at hxA
  have hbest : maxOf ((countsFoldW fs).map Prod.snd)
      = maxMultiplicity fs := maxOf_countsFoldW fs
  rw [hbest] at hbestlk
  have hbest64 : maxMultiplicity fs < 2 ^ 64 := by
    have := maxMult_le (ws := fs) (B := fs.length)
      (fun v hv => by
        simp only [multiplicity]
        exact List.length_filter_le _ _)
    omega
  have hxB := wfx_B sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
    ((wPos n : Nat) : Int) sv2 GoString.empty GoString.empty 0 0 0 0
    ((multiplicity (qWord qsel) fs : Nat) : Int) 0
    D a (countsFoldW fs) ((n : Nat) : Int) tail₂ na₂ ch₄ na₁
    ((maxMultiplicity fs : Nat) : Int) ha31 hD hna₁ hbestlk
  rw [unorm_nat_of_lt hbest64] at hxB
  have hxC := wfx_C sProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
    (textFamily n seed) (qWord qsel) ((n : Nat) : Int) b n cap
    ((wPos n : Nat) : Int) sv2 GoString.empty GoString.empty 0 0 0 0
    ((multiplicity (qWord qsel) fs : Nat) : Int)
    ((maxMultiplicity fs : Nat) : Int)
    D a (countsFoldW fs) ((n : Nat) : Int) tail₂ na₂ ch₄ na₁
  rw [unorm_nat_of_lt hhits64, unorm_nat_of_lt hbest64,
    unorm_nat_of_lt hhits64, unorm_nat_of_lt hbest64] at hxC
  -- 6. the chain
  have hchain := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hbuild
      hcount) hrhead) hrloop) hxA) hxB) hxC
  have hmle : (countsFoldW fs).length ≤ n := by
    have := countsFoldW_length_le fs
    omega
  refine ⟨k₁ + (84 * n + 85) + 16 + k₄ + 13 + 9 + 56, by
      have : 24 * (countsFoldW fs).length + 1 ≤ 24 * n + 1 := by
        omega
      simp only [wfFuel]
      omega,
    ch₄, b, cap, D, tail₂, a, na₂, countsFoldW fs,
    ((wPos n : Nat) : Int), sv2, ((n : Nat) : Int), hchain⟩

/-- **The target theorem** (the lane owner's root wraps it verbatim):
for every `n < 2^60`, `seed < 2^64`, `qsel < 2^64`, past the affine
fuel bound `wfFuel n` and at EVERY nondeterminism-choice stream, the
harness completes normally and returns the built text, the queried
word, its multiplicity among the text's words, and the maximum
multiplicity any word attains. -/
theorem wordfreq_total (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) :
    ∀ fuel : Nat, wfFuel n ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
          wordfreqLowered.funcs wordfreqHarnessRFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
            .int (qsel : Int) .uint64]
          wordfreqLowered.methods ch
        = .ok { values := #[.string (gs (textFamily n seed)),
                            .string (gs (qWord qsel)),
                            .int (multiplicity (qWord qsel)
                              (wordsOf (textFamily n seed)) : Nat) .uint64,
                            .int (maxMultiplicity
                              (wordsOf (textFamily n seed)) : Nat) .uint64] } := by
  intro fuel hfuel ch
  obtain ⟨k, hk, ch', b, cap, D, tail, a, na, kvs, iv0, sv2, civ,
    hrun⟩ := wf_run n seed qsel hn hseed hqsel ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [w_entry_eq,
    unorm_of_range (v := (n : Int)) (by omega) (by
      have : (n : Int) < 2 ^ 60 := by exact_mod_cast hn
      omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by
      exact_mod_cast hseed),
    unorm_of_range (v := (qsel : Int)) (by omega) (by
      exact_mod_cast hqsel)]
  rw [show sHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int)
      = wSt sProg (wHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
        ((qsel : Nat) : Int)) 7 from rfl]
  rw [hfold, runConfig_next_stop]
  show (Except.ok { values := #[_, _, _, _] } : Except GoError Result)
    = _
  rw [← wordsOf_textFamily n seed]

end GoLean.Examples.WordFreq
