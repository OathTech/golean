import GoLeanProofs.Examples.WordFreq.Scan2

/-!
# WordFreq — scan phase, part 3

The un-parked close arm (W3's parked composite, landed via the
recorded repair: the 22-link prefix split into three chain theorems of
≤ 8 links, and the substring `(l.drop s).take (i - s)` abstracted as
an OPAQUE parameter `f : List UInt8` pinned by `hf`, so chained state
terms stay small), then the iteration composites, the scan loop, the
exit segment, `scan_phase`, and the build→scan chain.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-! ## The separator CLOSE arm, un-parked (repair: split chains +
opaque substring) -/

section CloseArm

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (D : Heap)
  (na : Nat) (ch : Choices)

/-- Close-arm chain A: `w > 0` true, into the append block, the `$c16`
declaration lands. 17 steps (6 links). -/
theorem sc_close_chainA (iv sv2 cv : Int)
    (hna : 31 ≤ na) (hD : DeadFrom D na) :
    stepFnIter 17
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec scIfW (scEnvBC na) (scKPost1 na)) ch
      = .ok (.next (.seq
            [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF]
            (scEnvS16 na) (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, slsNil)]) (na + 3), ch) := by
  have h0 := ck_armDesc
    (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    na ch
  have h1 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (x := "w") (env := scEnvBC na) (a := ⟨na⟩)
    (k := .strictK .greaterCmp [] [.intLit 0 .int] (scEnvBC na)
      (scKArm na)) (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      iv sv2 true false hna (lookup_c1of2 hD)))
  have h2 := ck_close1 σ nv sv qv bnv bsv l q biv b cap fs
    iv sv2
    (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2) na
    ch
  have h3 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (ss := #[.initialization { id := "$c16", typ := tSlS }, scMkSl16,
      scAsgnAddr16])
    (env := scEnvA2 na) (rest := [scStC17, scStOut, scStInFF])
    (k := scKClose na) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
    (t := .initialization { id := "$c16", typ := tSlS })
    (rest := [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF])
    (env := scEnvA2 na) (k := scKClose na) (ch := ch))
  have h5 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
      (.exec (.initialization { id := "$c16", typ := tSlS })
        (scEnvA2 na)
        (.seq [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF]
          (scEnvA2 na) (scKClose na))) ch
      = .ok (.next (.seq
            [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF]
            (scEnvS16 na) (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, slsNil)]) (na + 3), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]) (na + 2))
      (p := { id := "$c16", typ := tSlS })
      (rest := [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF])
      (env := scEnvA2 na) (k := scKClose na) (ch := ch)
      (v := .slice ⟨none, 0, 0, 0⟩)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    rw [show Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            iv sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)]))
        (.base ⟨na + 2⟩) ⟨some tSlS, .slice ⟨none, 0, 0, 0⟩⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            iv sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, slsNil)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          iv sv2 true false _ (by omega),
        set_fresh (DeadFrom.push2 hD (na + 2) (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h0 h1) h2) h3) h4) h5

/-- Close-arm chain B: the `$c16` make/fill — `make([]string, 1, 1)`,
`$c16[0] = s[start:i]` — to the drained store queue. The substring is
delivered concretely by the slice op and immediately abstracted to the
OPAQUE `f` via `hf`. 23 steps (8 links). -/
theorem sc_close_chainB (s i : Nat) (cv : Int) (f : List UInt8)
    (hf : (l.drop s).take (i - s) = f)
    (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hsle : s ≤ i) (hile : i ≤ l.length) :
    stepFnIter 23
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, slsNil)]) (na + 3))
      (.next (.seq [scMkSl16, scAsgnAddr16, scStC17, scStOut, scStInFF]
        (scEnvS16 na) (scKClose na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvS16 na)
            (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na)
              (scKClose na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            ((s : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
            (na + 4), ch) := by
  have h6 := ck_mkSl
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((s : Nat) : Int) true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, slsNil)]) (na + 3))
    [scAsgnAddr16, scStC17, scStOut, scStInFF] (scKClose na) ch na
  have h7 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, slsNil)]) (na + 3))
      (.retV (.int 1 .int)
        (.stmtOpK (.makeSlice tStr true) 1
          [.int 1 .int, .addr (.base ⟨na + 2⟩)] [] (scEnvS16 na)
          (.seq [scAsgnAddr16, scStC17, scStOut, scStInFF]
            (scEnvS16 na) (scKClose na)))) ch
      = .ok (.next (.seq [scAsgnAddr16, scStC17, scStOut, scStInFF]
            (scEnvS16 na) (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            ((s : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
            (na + 4), ch) := by
    refine stepFnIter_one (stepFn_stmtOp_apply ?_)
    have h := applyStmtOp_makeSlice_str11
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, slsNil)]) (na + 3))
      (t := na + 2) (ch := ch)
      (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) ((s : Nat) : Int) true false (by omega)
        (lookup_c3of3 hD))
      (show na + 2 ≠ na + 3 by omega)
    rw [show Heap.set
        (Heap.set
          (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
              ((i : Nat) : Int) ((s : Nat) : Int) true false
            ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
                (.base ⟨na + 2⟩, slsNil)]))
          (.base ⟨na + 3⟩)
          ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)
        (.base ⟨na + 2⟩) ⟨some tSlS, slsVal (na + 3) 0 1 1⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) ((s : Nat) : Int) true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr),
                  .array #[.string GoString.empty]⟩)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          ((i : Nat) : Int) ((s : Nat) : Int) true false _ (by omega),
        set_fresh (DeadFrom.push3 hD (na + 3) (Nat.le_refl _))]
      rw [show (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, slsNil)])
          ++ [(.base ⟨na + 3⟩,
              (⟨some (.array 1 tStr),
                .array #[.string GoString.empty]⟩ : HeapCell))]
          = D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, slsNil),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr),
                  .array #[.string GoString.empty]⟩)] from by
        simp [List.append_assoc]]
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          ((i : Nat) : Int) ((s : Nat) : Int) true false _ (by omega),
        set_c3of4 hD]] at h
    exact h
  have h8 := ck_c16a
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((s : Nat) : Int) true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
      (na + 4))
    [scStC17, scStOut, scStInFF] (scKClose na) ch na
  have h9 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((s : Nat) : Int) true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
      (na + 4))
    (x := "$c16") (env := scEnvS16 na) (a := ⟨na + 2⟩)
    (k := .tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals
      [.slice (.var "s") (.var "start") (.var "i") none] []
      (.seqn #[]) (scEnvS16 na)
      (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na) (scKClose na)))
    (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) ((s : Nat) : Int) true false (by omega)
      (lookup_c3of4 hD)))
  have h10 := ck_c16b σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((s : Nat) : Int) true
    (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
      (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
      (.base ⟨na + 3⟩,
        ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
    (na + 4) na [scStC17, scStOut, scStInFF] (scKClose na) ch
  have h11 := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((s : Nat) : Int) .int, .string (gs l)])
    (env := scEnvS16 na)
    (k := .rhsK .vals
      [.chain (slsVal (na + 3) 0 1 1) [.int 0 .int] [.index]] [] []
      (.seqn #[]) (scEnvS16 na)
      (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na) (scKClose na)))
    (ch := ch)
    (applyStrictOp_slice_string
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
        (na + 4))
      (l := l) (lo := s) (hi := i) (ik := .int) (ik' := .int) hsle hile))
  rw [hf] at h11
  have h12 := sc_ckF
    (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      ((s : Nat) : Int) true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
      (na + 4))
    (.string (gs f))
    (.chain (slsVal (na + 3) 0 1 1) [.int 0 .int] [.index])
    (scEnvS16 na)
    (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na) (scKClose na)) ch
  have h13 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
        (na + 4))
      (.next (.storeK
        [.chain (slsVal (na + 3) 0 1 1) [.int 0 .int] [.index]]
        [.string (gs f)] (.seqn #[])
        (scEnvS16 na)
        (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na)
          (scKClose na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (scEnvS16 na)
            (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na)
              (scKClose na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            ((s : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr),
                  .array #[.string (gs f)]⟩)])
            (na + 4), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_c16
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)])
        (na + 4))
      (e := na + 3) (v0 := GoString.empty)
      (w := gs f)
      (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) ((s : Nat) : Int) true false (by omega)
        (lookup_c4of4 hD))
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) ((s : Nat) : Int) true false _ (by omega),
      set_c4of4 hD] at h
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h6 h7) h8) h9) h10) h11) h12) h13

/-- Close-arm chain C: `$c17` declared, `append(out, $c16...)` argument
reads, to the append apply point. Fully opaque in the substring `f`.
13 steps (8 links). -/
theorem sc_close_chainC (iv sv2 cv : Int) (f : List UInt8)
    (hna : 31 ≤ na) (hD : DeadFrom D na) :
    stepFnIter 13
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
        (na + 4))
      (.next (.storeK [] [] (.seqn #[]) (scEnvS16 na)
        (.seq [scStC17, scStOut, scStInFF] (scEnvS16 na)
          (scKClose na)))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
            (.stmtOpK (.appendSlice tStr) 1
              [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
                .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
              (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) (na + 5), ch) := by
  have h14 := stepFnIter_one (stepFn_storeK_nil
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
      (na + 4))
    (body := .seqn #[]) (env := scEnvS16 na)
    (k := .seq [scStC17, scStOut, scStInFF] (scEnvS16 na)
      (scKClose na)) (ch := ch))
  have h15 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
      (na + 4))
    (ss := #[]) (env := scEnvS16 na)
    (rest := [scStC17, scStOut, scStInFF]) (k := scKClose na)
    (ch := ch))
  have h16 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
      (na + 4))
    (t := scStC17) (rest := [scStOut, scStInFF]) (env := scEnvS16 na)
    (k := scKClose na) (ch := ch))
  have h17 := stepFnIter_one (stepFn_seqn_splice
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
      (na + 4))
    (ss := #[.initialization { id := "$c17", typ := tSlS }, scApp17])
    (env := scEnvS16 na) (rest := [scStOut, scStInFF])
    (k := scKClose na) (ch := ch))
  have h18 := stepFnIter_one (stepFn_seq_pop
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
      (na + 4))
    (t := .initialization { id := "$c17", typ := tSlS })
    (rest := [scApp17, scStOut, scStInFF]) (env := scEnvS16 na)
    (k := scKClose na) (ch := ch))
  have h19 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
        (na + 4))
      (.exec (.initialization { id := "$c17", typ := tSlS })
        (scEnvS16 na)
        (.seq [scApp17, scStOut, scStInFF] (scEnvS16 na)
          (scKClose na))) ch
      = .ok (.next (.seq [scApp17, scStOut, scStInFF] (scEnvS17 na)
            (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) (na + 5), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)])
        (na + 4))
      (p := { id := "$c17", typ := tSlS })
      (rest := [scApp17, scStOut, scStInFF]) (env := scEnvS16 na)
      (k := scKClose na) (ch := ch)
      (v := .slice ⟨none, 0, 0, 0⟩)
      (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
    rw [show Heap.set
        (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            iv sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)]))
        (.base ⟨na + 4⟩) ⟨some tSlS, .slice ⟨none, 0, 0, 0⟩⟩
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            iv sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) from by
      rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
          iv sv2 true false _ (by omega),
        set_fresh (DeadFrom.push4 hD (na + 4) (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  have h20 := ck_c17a σ nv sv qv bnv bsv l q biv b cap fs
    iv sv2 true
    (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
      (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
      (.base ⟨na + 3⟩,
        ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
      (.base ⟨na + 4⟩, slsNil)])
    (na + 5) na [scStOut, scStInFF] (scKClose na) ch
  have h21 := stepFnIter_one (stepFn_var
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (.base ⟨na + 4⟩, slsNil)]) (na + 5))
    (x := "$c16") (env := scEnvS17 na) (a := ⟨na + 2⟩)
    (k := .stmtOpK (.appendSlice tStr) 1
      [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
        .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
      (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)))
    (ch := ch) rfl
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      iv sv2 true false (by omega)
      (lookup_c3of5 hD)))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h14 h15) h16) h17) h18) h19) h20) h21

/-- The close arm's shared prefix, composed: `w > 0` true, `inField`
true, the `$c16` make/fill, the `$c17` declaration, to the append
apply point — with the field substring OPAQUE (`hf` pins it). 53
steps. -/
theorem sc_arm_close_pre (s i : Nat) (cv : Int) (f : List UInt8)
    (hf : (l.drop s).take (i - s) = f)
    (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hsle : s ≤ i) (hile : i ≤ l.length) :
    stepFnIter 53
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
        ((s : Nat) : Int) true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)])
        (na + 2))
      (.exec scIfW (scEnvBC na) (scKPost1 na)) ch
      = .ok (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
            (.stmtOpK (.appendSlice tStr) 1
              [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
                .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
              (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na))),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            ((s : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) (na + 5), ch) :=
  stepFnIter_chain (stepFnIter_chain
    (sc_close_chainA σ nv sv qv bnv bsv l q biv b cap fs D na ch
      ((i : Nat) : Int) ((s : Nat) : Int) cv hna hD)
    (sc_close_chainB σ nv sv qv bnv bsv l q biv b cap fs D na ch
      s i cv f hf hna hD hsle hile))
    (sc_close_chainC σ nv sv qv bnv bsv l q biv b cap fs D na ch
      ((i : Nat) : Int) ((s : Nat) : Int) cv f hna hD)

/-- The IN-PLACE append branch (`|fs| < cap`): from the append apply
point, the element lands in the `out` backing, the tail runs. 41
steps. -/
theorem sc_close_inplace (i : Nat) (sv2 cv : Int) (f : List UInt8)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hblt : b < na) (hb31 : 31 ≤ b)
    (hDb : Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
    (hlt : fs.length < cap) (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 41
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5))
      (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice tStr) 1
          [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
            .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
          (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)))) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap (fs ++ [f])
            ((i + 1 : Nat) : Int) sv2 false false
            ((Heap.set D (.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
              ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
                (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
                (.base ⟨na + 3⟩,
                  ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
                (.base ⟨na + 4⟩,
                  ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)])
            (na + 5), ch) := by
  have happly := applyStmtOp_append_str_inplace
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
      sv2 true false
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (.base ⟨na + 4⟩, slsNil)]) (na + 5))
    (t := na + 4) (b := b) (e := na + 3) (fs := fs) (cap := cap)
    (f := f) (ch := ch)
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 true false hb31
      (lookup_append_left hDb))
    (lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 true false (by omega)
      (lookup_c4of5 hD))
    (by
      rw [Machine.Heap.lookup_set_ne
        (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
          : (Loc.base ⟨b⟩ : Loc) ≠ .base ⟨na + 4⟩)]
      exact lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false (by omega)
        (lookup_c5of5 hD))
    hlt
  have h22 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5))
      (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice tStr) 1
          [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
            .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
          (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)))) ch
      = .ok (.next (.seq [scStOut, scStInFF] (scEnvS17 na)
            (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            sv2 true false
            ((Heap.set D (.base ⟨b⟩)
                (strArrCell (fs ++ [f]) cap))
              ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
                (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
                (.base ⟨na + 3⟩,
                  ⟨some (.array 1 tStr),
                    .array #[.string (gs f)]⟩),
                (.base ⟨na + 4⟩,
                  ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)])
            (na + 5), ch) := by
    refine stepFnIter_one (stepFn_stmtOp_apply ?_)
    rw [show (scSt σ nv sv qv bnv bsv l q biv b cap fs
          ((i : Nat) : Int) sv2 true false
          (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
            (.base ⟨na + 3⟩,
              ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
            (.base ⟨na + 4⟩, slsNil)]) (na + 5)).heap
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) from rfl,
      set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false _ hb31,
      set_append_left hDb,
      set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false _ (by omega),
      set_c5of5 (DeadFrom.set hD hblt)] at happly
    exact happly
  have hl17 : Heap.lookup
      ((Heap.set D (.base ⟨b⟩)
          (strArrCell (fs ++ [f]) cap))
        ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩,
            ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)])
      (.base ⟨na + 4⟩)
      = some ⟨some tSlS,
          slsVal b 0 (fs ++ [f]).length cap⟩
      := by
    rw [show (fs ++ [f]).length
        = fs.length + 1 from by simp]
    exact lookup_c5of5 (DeadFrom.set hD hblt)
  have hlw : Heap.lookup
      ((Heap.set D (.base ⟨b⟩)
          (strArrCell (fs ++ [f]) cap))
        ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩,
            ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)])
      (.base ⟨na⟩) = some (sint 1) :=
    lookup_c1of5 (DeadFrom.set hD hblt)
  have htail := sc_closeTail σ nv sv qv bnv bsv l q biv b cap fs
    sv2
    ((Heap.set D (.base ⟨b⟩)
        (strArrCell (fs ++ [f]) cap))
      ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (.base ⟨na + 4⟩,
          ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)])
    (na + 5) na ch i b cap (fs ++ [f])
    (by omega) hl17 hlw hi63
  exact stepFnIter_chain h22 htail

/-- The SPILL append branch (`|fs| = cap`): from the append apply
point, ONE capacity choice is consumed, a fresh backing materializes
at `na + 5`, the tail runs. 41 steps. -/
theorem sc_close_spill (i : Nat) (sv2 cv : Int) (f : List UInt8)
    (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (heq : fs.length = cap) (hi63 : i + 1 < 2 ^ 63) :
    ∃ (newCap : Nat) (ch' : Choices), fs.length + 1 ≤ newCap ∧
    stepFnIter 41
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5))
      (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice tStr) 1
          [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
            .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
          (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)))) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv (na + 5) newCap (fs ++ [f])
            ((i + 1 : Nat) : Int) sv2 false false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩,
                ⟨some tSlS, slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
              (.base ⟨na + 5⟩,
                strArrCell (fs ++ [f]) newCap)])
            (na + 6), ch') := by
  have hbfull : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5)).heap
      (.base ⟨b⟩) = some (strArrCell fs cap) := by
    rcases hbOr with ⟨h31, hDb⟩ | ⟨hb25, hc0, hfs0⟩
    · exact lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false h31
        (lookup_append_left hDb)
    · subst hb25; subst hc0; subst hfs0
      exact lookup_scan25 nv sv qv bnv bsv l q biv 25 0 0
        ((i : Nat) : Int) sv2 true false _
  have hefull : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5)).heap
      (.base ⟨na + 3⟩)
      = some ⟨some (.array 1 tStr),
          .array #[.string (gs f)]⟩ :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 true false (by omega)
      (lookup_c4of5 hD)
  have htfull : Heap.lookup
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5)).heap
      (.base ⟨na + 4⟩) = some slsNil :=
    lookup_scanD nv sv qv bnv bsv l q biv b fs.length cap
      ((i : Nat) : Int) sv2 true false (by omega)
      (lookup_c5of5 hD)
  obtain ⟨newCap, ch', hbound, hstep⟩ :=
    sc_spillStep
      (scSt σ nv sv qv bnv bsv l q biv b cap fs
        ((i : Nat) : Int) sv2 true false
        (D ++ [(Loc.base ⟨na⟩, sint 1), (Loc.base ⟨na + 1⟩, su8 cv),
          (Loc.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (Loc.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (Loc.base ⟨na + 4⟩, slsNil)]) (na + 5))
      na b cap fs f (scEnvS17 na)
      (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)) ch
      rfl hbfull hefull htfull heq
  have h22 : stepFnIter 1
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        true false
        (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)]) (na + 5))
      (.retV (.slice ⟨some (.base ⟨na + 3⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice tStr) 1
          [.slice ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩,
            .addr (.base ⟨na + 4⟩)] [] (scEnvS17 na)
          (.seq [scStOut, scStInFF] (scEnvS17 na) (scKClose na)))) ch
      = .ok (.next (.seq [scStOut, scStInFF] (scEnvS17 na)
            (scKClose na)),
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
            sv2 true false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩,
                ⟨some tSlS,
                  slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
              (.base ⟨na + 5⟩,
                strArrCell (fs ++ [f]) newCap)])
            (na + 6), ch') := by
    rw [show (scSt σ nv sv qv bnv bsv l q biv b cap fs
          ((i : Nat) : Int) sv2 true false
          (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
            (.base ⟨na + 3⟩,
              ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
            (.base ⟨na + 4⟩, slsNil)]) (na + 5)).heap
        = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
            ((i : Nat) : Int) sv2 true false
          ++ (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
              (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
              (.base ⟨na + 3⟩,
                ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
              (.base ⟨na + 4⟩, slsNil)]) from rfl] at hstep
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false _
        (by omega : (31 : Nat) ≤ na + 5),
      set_fresh (DeadFrom.push5 hD (na + 5) (Nat.le_refl _))]
      at hstep
    rw [show (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
          (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (.base ⟨na + 4⟩, slsNil)])
        ++ [(.base ⟨na + 5⟩,
            strArrCell (fs ++ [f]) newCap)]
        = D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
            (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
            (.base ⟨na + 3⟩,
              ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
            (.base ⟨na + 4⟩, slsNil),
            (.base ⟨na + 5⟩,
              strArrCell (fs ++ [f]) newCap)] from by
      simp [List.append_assoc]] at hstep
    rw [set_scanD nv sv qv bnv bsv l q biv b fs.length cap
        ((i : Nat) : Int) sv2 true false _
        (by omega : (31 : Nat) ≤ na + 4),
      set_c5of6 hD, wSt_wSt] at hstep
    exact hstep
  have hl17 : Heap.lookup
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (.base ⟨na + 4⟩,
          ⟨some tSlS, slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
        (.base ⟨na + 5⟩,
          strArrCell (fs ++ [f]) newCap)])
      (.base ⟨na + 4⟩)
      = some ⟨some tSlS,
          slsVal (na + 5) 0 (fs ++ [f]).length
            newCap⟩ := by
    rw [show (fs ++ [f]).length
        = fs.length + 1 from by simp]
    exact lookup_c5of6 hD
  have hlw : Heap.lookup
      (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
        (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (.base ⟨na + 4⟩,
          ⟨some tSlS, slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
        (.base ⟨na + 5⟩,
          strArrCell (fs ++ [f]) newCap)])
      (.base ⟨na⟩) = some (sint 1) :=
    lookup_c1of6 hD
  have htail := sc_closeTail σ nv sv qv bnv bsv l q biv b cap fs
    sv2
    (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv),
      (.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
      (.base ⟨na + 3⟩,
        ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
      (.base ⟨na + 4⟩,
        ⟨some tSlS, slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
      (.base ⟨na + 5⟩,
        strArrCell (fs ++ [f]) newCap)])
    (na + 6) na ch' i (na + 5) newCap
    (fs ++ [f])
    (by omega) hl17 hlw hi63
  exact ⟨newCap, ch', hbound, stepFnIter_chain h22 htail⟩

/-- **The separator close arm** (`w = 1`, in field): the open field
`s[start:i]` (opaquely `f`, pinned by `hf`) is appended to `out` — in
place or through a choice-consuming spill — `inField` falls, `i`
advances. 94 steps; the exit carries the choice-dependent backing
existentially. -/
theorem sc_arm_close (s i : Nat) (cv : Int) (f : List UInt8)
    (hf : (l.drop s).take (i - s) = f)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hblt : b < na)
    (hcap : fs.length ≤ cap)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (hsle : s ≤ i) (hile : i ≤ l.length) (hi63 : i + 1 < 2 ^ 63) :
    ∃ (b' cap' : Nat) (D' : Heap) (na' : Nat) (ch' : Choices),
      stepFnIter 94
        (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
          ((s : Nat) : Int) true false
          (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 cv)])
          (na + 2))
        (.exec scIfW (scEnvBC na) (scKPost1 na)) ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv l q biv b' cap'
              (fs ++ [f]) ((i + 1 : Nat) : Int)
              ((s : Nat) : Int) false false D' na', ch')
      ∧ 31 ≤ b'
      ∧ Heap.lookup D' (.base ⟨b'⟩)
          = some (strArrCell (fs ++ [f]) cap')
      ∧ fs.length + 1 ≤ cap' ∧ DeadFrom D' na' ∧ b' < na'
      ∧ na + 2 ≤ na' := by
  have hpre := sc_arm_close_pre σ nv sv qv bnv bsv l q biv b cap fs D
    na ch s i cv f hf hna hD hsle hile
  rcases Nat.lt_or_ge fs.length cap with hlt | hge
  · -- IN PLACE
    have hb31 : 31 ≤ b := by
      rcases hbOr with ⟨h31, _⟩ | ⟨_, hc0, _⟩
      · exact h31
      · omega
    have hDb : Heap.lookup D (Loc.base ⟨b⟩) = some (strArrCell fs cap) := by
      rcases hbOr with ⟨_, hDb⟩ | ⟨_, hc0, _⟩
      · exact hDb
      · omega
    have hrest := sc_close_inplace σ nv sv qv bnv bsv l q biv b cap fs
      D na ch i ((s : Nat) : Int) cv f hna hD hblt hb31 hDb hlt hi63
    refine ⟨b, cap,
      (Heap.set D (Loc.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
        ++ [(Loc.base ⟨na⟩, sint 1), (Loc.base ⟨na + 1⟩, su8 cv),
          (Loc.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
          (Loc.base ⟨na + 3⟩,
            ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
          (Loc.base ⟨na + 4⟩,
            ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩)],
      na + 5, ch,
      stepFnIter_chain hpre hrest,
      hb31,
      lookup_append_left (lookup_set_self (h := D) (l := Loc.base ⟨b⟩)),
      by omega,
      DeadFrom.push5 (DeadFrom.set hD hblt),
      by omega, by omega⟩
  · -- SPILL
    have heq : fs.length = cap := by omega
    obtain ⟨newCap, ch', hbound, hrest⟩ := sc_close_spill σ nv sv qv
      bnv bsv l q biv b cap fs D na ch i ((s : Nat) : Int) cv f hna hD
      hbOr heq hi63
    refine ⟨na + 5, newCap,
      D ++ [(Loc.base ⟨na⟩, sint 1), (Loc.base ⟨na + 1⟩, su8 cv),
        (Loc.base ⟨na + 2⟩, ⟨some tSlS, slsVal (na + 3) 0 1 1⟩),
        (Loc.base ⟨na + 3⟩,
          ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩),
        (Loc.base ⟨na + 4⟩,
          ⟨some tSlS, slsVal (na + 5) 0 (fs.length + 1) newCap⟩),
        (Loc.base ⟨na + 5⟩,
          strArrCell (fs ++ [f]) newCap)],
      na + 6, ch',
      stepFnIter_chain hpre hrest,
      by omega,
      lookup_c6of6 hD,
      hbound,
      DeadFrom.push6 hD,
      by omega, by omega⟩

end CloseArm

/-! ## The per-byte iteration composites (dispatch + prefix + classify
+ arm, loop head to loop head) -/

/-- `==`-miss for a letter byte (97…99) against a classifier
constant. -/
theorem beqF_letter {v : Nat} (h1 : 97 ≤ v) (h2 : v ≤ 99) {w : Int}
    (hw : w < 97 ∨ 99 < w) : (((v : Nat) : Int) == w) = false :=
  beq_eq_false_iff_ne.mpr (by omega)

section Iter

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (sv2 : Int)
  (D : Heap) (na : Nat) (ch : Choices)

/-- **First-pass iteration** (byte 32 — the leading space — not in
field): flag write, skip arm. 123 steps. -/
theorem sc_iter0 (i : Nat) (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hi : i < l.length) (hbyte : l.getD i 0 = 32)
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 123
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false true D na) scHeadCfg ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int)
            sv2 false false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 32)])
            (na + 2), ch) := by
  have hA := sc_A0_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast hi)] at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i sv2 false
    D na ch hna hD hi
  rw [show (((l.getD i 0).toNat : Nat) : Int) = (32 : Int) from by
    rw [hbyte]; decide] at hP
  have hC := sc_cls_sep32 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch hna hD
  have hS := sc_arm_skip σ nv sv qv bnv bsv l q biv b cap fs sv2
    (D ++ [(Loc.base ⟨na⟩, sint 1), (Loc.base ⟨na + 1⟩, su8 32)])
    (na + 2) na ch i hna (lookup_c1of2 hD) hi63
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
    hS

/-- **Skip iteration** (byte 32, not in field, later pass): `i`
advances past a separator space. 116 steps. -/
theorem sc_iter_skip (i : Nat) (hna : 31 ≤ na) (hD : DeadFrom D na)
    (hi : i < l.length) (hbyte : l.getD i 0 = 32)
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 116
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false false D na) scHeadCfg ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int)
            sv2 false false
            (D ++ [(.base ⟨na⟩, sint 1), (.base ⟨na + 1⟩, su8 32)])
            (na + 2), ch) := by
  have hA := sc_A1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast hi)] at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i sv2 false
    D na ch hna hD hi
  rw [show (((l.getD i 0).toNat : Nat) : Int) = (32 : Int) from by
    rw [hbyte]; decide] at hP
  have hC := sc_cls_sep32 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch hna hD
  have hS := sc_arm_skip σ nv sv qv bnv bsv l q biv b cap fs sv2
    (D ++ [(Loc.base ⟨na⟩, sint 1), (Loc.base ⟨na + 1⟩, su8 32)])
    (na + 2) na ch i hna (lookup_c1of2 hD) hi63
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
    hS

/-- **Letter iteration, LONG variant** (`i + 2 < len`, letter byte,
not in field): the field opens, `c1`/`c2` debris. 275 steps. -/
theorem sc_iter_letter_long (i : Nat) (hna : 31 ≤ na)
    (hD : DeadFrom D na) (hi2 : i + 2 < l.length)
    (hlen : l.length < 2 ^ 62)
    (h97 : 97 ≤ (l.getD i 0).toNat) (h99 : (l.getD i 0).toNat ≤ 99)
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 275
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false false D na) scHeadCfg ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int)
            ((i : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 0),
              (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat)),
              (.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
              (.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
            (na + 4), ch) := by
  have hA := sc_A1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast (by omega : i < l.length))]
    at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i sv2 false
    D na ch hna hD (by omega)
  have hC := sc_cls_letter_long σ nv sv qv bnv bsv l q biv b cap fs sv2
    false D na ch i (((l.getD i 0).toNat : Nat) : Int) hna hD hi2 hlen
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inr (by omega)))
    (beqF_letter h97 h99 (Or.inr (by omega)))
    (beqF_letter h97 h99 (Or.inr (by omega)))
    (beqF_letter h97 h99 (Or.inr (by omega)))
  have hS := sc_arm_letter σ nv sv qv bnv bsv l q biv b cap fs sv2
    (D ++ [(Loc.base ⟨na⟩, sint 0),
      (Loc.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat)),
      (Loc.base ⟨na + 2⟩, su8 ((l.getD (i + 1) 0).toNat : Nat)),
      (Loc.base ⟨na + 3⟩, su8 ((l.getD (i + 2) 0).toNat : Nat))])
    (na + 4) na ch i hna (lookup_c1of4 hD) hi63
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
    hS

/-- **Letter iteration, SHORT variant** (`¬ i + 2 < len`): the field
opens, no probe debris. 183 steps. -/
theorem sc_iter_letter_short (i : Nat) (hna : 31 ≤ na)
    (hD : DeadFrom D na) (hi : i < l.length)
    (hi2 : ¬ (i + 2 < l.length)) (hlen : l.length < 2 ^ 62)
    (h97 : 97 ≤ (l.getD i 0).toNat) (h99 : (l.getD i 0).toNat ≤ 99)
    (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 183
      (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int) sv2
        false false D na) scHeadCfg ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv b cap fs ((i + 1 : Nat) : Int)
            ((i : Nat) : Int) true false
            (D ++ [(.base ⟨na⟩, sint 0),
              (.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))])
            (na + 2), ch) := by
  have hA := sc_A1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) sv2 false D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast hi)] at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i sv2 false
    D na ch hna hD hi
  have hC := sc_cls_letter_short σ nv sv qv bnv bsv l q biv b cap fs sv2
    false D na ch i (((l.getD i 0).toNat : Nat) : Int) hna hD hi hi2 hlen
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inl (by omega)))
    (beqF_letter h97 h99 (Or.inr (by omega)))
  have hS := sc_arm_letter σ nv sv qv bnv bsv l q biv b cap fs sv2
    (D ++ [(Loc.base ⟨na⟩, sint 0),
      (Loc.base ⟨na + 1⟩, su8 ((l.getD i 0).toNat : Nat))])
    (na + 2) na ch i hna (lookup_c1of2 hD) hi63
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
    hS

/-- **Close iteration (space)** (byte 32, IN field): the open field is
appended, in place or by spill. 180 steps. -/
theorem sc_iter_close32 (s i : Nat) (f : List UInt8)
    (hf : (l.drop s).take (i - s) = f)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hblt : b < na)
    (hcap : fs.length ≤ cap)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (hi : i < l.length) (hbyte : l.getD i 0 = 32)
    (hsle : s ≤ i) (hi63 : i + 1 < 2 ^ 63) :
    ∃ (b' cap' : Nat) (D' : Heap) (na' : Nat) (ch' : Choices),
      stepFnIter 180
        (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
          ((s : Nat) : Int) true false D na) scHeadCfg ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv l q biv b' cap' (fs ++ [f])
              ((i + 1 : Nat) : Int) ((s : Nat) : Int) false false D' na',
            ch')
      ∧ 31 ≤ b'
      ∧ Heap.lookup D' (.base ⟨b'⟩)
          = some (strArrCell (fs ++ [f]) cap')
      ∧ fs.length + 1 ≤ cap' ∧ DeadFrom D' na' ∧ b' < na'
      ∧ na + 2 ≤ na' := by
  have hA := sc_A1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((s : Nat) : Int) true D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast hi)] at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i
    ((s : Nat) : Int) true D na ch hna hD hi
  rw [show (((l.getD i 0).toNat : Nat) : Int) = (32 : Int) from by
    rw [hbyte]; decide] at hP
  have hC := sc_cls_sep32 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((s : Nat) : Int) true D na ch hna hD
  obtain ⟨b', cap', D', na', ch', hstep, hb31', hlook', hcap', hD',
    hblt', hna'⟩ :=
    sc_arm_close σ nv sv qv bnv bsv l q biv b cap fs D na ch s i 32 f
      hf hna hD hblt hcap hbOr hsle (by omega) hi63
  exact ⟨b', cap', D', na', ch',
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
      hstep,
    hb31', hlook', hcap', hD', hblt', hna'⟩

/-- **Close iteration (tab)** (byte 9, IN field). 186 steps. -/
theorem sc_iter_close9 (s i : Nat) (f : List UInt8)
    (hf : (l.drop s).take (i - s) = f)
    (hna : 31 ≤ na) (hD : DeadFrom D na) (hblt : b < na)
    (hcap : fs.length ≤ cap)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (hi : i < l.length) (hbyte : l.getD i 0 = 9)
    (hsle : s ≤ i) (hi63 : i + 1 < 2 ^ 63) :
    ∃ (b' cap' : Nat) (D' : Heap) (na' : Nat) (ch' : Choices),
      stepFnIter 186
        (scSt σ nv sv qv bnv bsv l q biv b cap fs ((i : Nat) : Int)
          ((s : Nat) : Int) true false D na) scHeadCfg ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv l q biv b' cap' (fs ++ [f])
              ((i + 1 : Nat) : Int) ((s : Nat) : Int) false false D' na',
            ch')
      ∧ 31 ≤ b'
      ∧ Heap.lookup D' (.base ⟨b'⟩)
          = some (strArrCell (fs ++ [f]) cap')
      ∧ fs.length + 1 ≤ cap' ∧ DeadFrom D' na' ∧ b' < na'
      ∧ na + 2 ≤ na' := by
  have hA := sc_A1_raw σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((s : Nat) : Int) true D na ch
  rw [show decide (((i : Nat) : Int) < ((l.length : Nat) : Int)) = true
    from decide_eq_true (by exact_mod_cast hi)] at hA
  have hP := sc_prefix σ nv sv qv bnv bsv l q biv b cap fs i
    ((s : Nat) : Int) true D na ch hna hD hi
  rw [show (((l.getD i 0).toNat : Nat) : Int) = (9 : Int) from by
    rw [hbyte]; decide] at hP
  have hC := sc_cls_sep9 σ nv sv qv bnv bsv l q biv b cap fs
    ((i : Nat) : Int) ((s : Nat) : Int) true D na ch hna hD
  obtain ⟨b', cap', D', na', ch', hstep, hb31', hlook', hcap', hD',
    hblt', hna'⟩ :=
    sc_arm_close σ nv sv qv bnv bsv l q biv b cap fs D na ch s i 9 f
      hf hna hD hblt hcap hbOr hsle (by omega) hi63
  exact ⟨b', cap', D', na', ch',
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hP) hC)
      hstep,
    hb31', hlook', hcap', hD', hblt', hna'⟩

end Iter

/-! ## The word composite and the scan loop (at the FAMILY text) -/

section Loop

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (q : List UInt8)
  (biv : Int)

/-- The scan loop's invariant on the backing region (the `out` slice
either still names the empty `$c15` backing at front cell 25 or a
debris-region backing holding exactly the words so far). -/
def ScanInv (seed j : Nat) (b cap : Nat) (D : Heap) (na : Nat) : Prop :=
  31 ≤ na ∧ DeadFrom D na ∧ b < na
  ∧ (letterWords j seed).length ≤ cap
  ∧ ((31 ≤ b ∧ Heap.lookup D (.base ⟨b⟩)
        = some (strArrCell (letterWords j seed) cap))
      ∨ (b = 25 ∧ cap = 0 ∧ letterWords j seed = []))

/-- **One word block** (letter, closing separator, and — for the
two-space separator — the trailing skip), loop head to loop head:
within 600 steps word `j` lands in the backing. -/
theorem sc_word (n seed : Nat) (hn : n < 2 ^ 60) (j : Nat) (hj : j < n)
    (sv2 : Int) (b cap : Nat) (D : Heap) (na : Nat) (ch : Choices)
    (hinv : ScanInv seed j b cap D na) :
    ∃ k : Nat, k ≤ 600 ∧
    ∃ (b' cap' : Nat) (D' : Heap) (na' : Nat) (ch' : Choices)
      (sv2' : Int),
      stepFnIter k
        (scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b cap
          (letterWords j seed) ((wPos j : Nat) : Int) sv2 false false
          D na) scHeadCfg ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b' cap'
              (letterWords (j + 1) seed) ((wPos (j + 1) : Nat) : Int)
              sv2' false false D' na', ch')
      ∧ ScanInv seed (j + 1) b' cap' D' na' ∧ na ≤ na' := by
  obtain ⟨hna, hD, hblt, hcap, hbOr⟩ := hinv
  have hlenP : (textFamily n seed).length = wPos n :=
    textFamily_length n seed
  have hwle : wPos n ≤ 3 * n + 1 := wPos_le n
  have hj1n : wPos (j + 1) ≤ wPos n := wPos_mono hj
  have hj2 : wPos j + 2 ≤ wPos (j + 1) := wPos_succ_ge j
  have hj3le : wPos (j + 1) ≤ wPos j + 3 := wPos_succ_le j
  have hlen62 : (textFamily n seed).length < 2 ^ 62 := by
    rw [hlenP]; omega
  have h97 : 97 ≤ ((textFamily n seed).getD (wPos j) 0).toNat := by
    rw [textFamily_getD_letter seed hj]; exact letterByte_ge seed j
  have h99 : ((textFamily n seed).getD (wPos j) 0).toNat ≤ 99 := by
    rw [textFamily_getD_letter seed hj]; exact letterByte_le seed j
  -- the letter iteration (long or short), packaged
  have hletter : ∃ kl : Nat, kl ≤ 275 ∧
      ∃ (D₁ : Heap) (na₁ : Nat),
      stepFnIter kl
        (scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b cap
          (letterWords j seed) ((wPos j : Nat) : Int) sv2 false false
          D na) scHeadCfg ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b cap
              (letterWords j seed) ((wPos j + 1 : Nat) : Int)
              ((wPos j : Nat) : Int) true false D₁ na₁, ch)
      ∧ 31 ≤ na₁ ∧ DeadFrom D₁ na₁ ∧ b < na₁ ∧ na ≤ na₁
      ∧ ((31 ≤ b ∧ Heap.lookup D₁ (.base ⟨b⟩)
            = some (strArrCell (letterWords j seed) cap))
          ∨ (b = 25 ∧ cap = 0 ∧ letterWords j seed = [])) := by
    rcases Nat.lt_or_ge (wPos j + 2) (textFamily n seed).length
      with hlong | hshort
    · refine ⟨275, by omega, _, _,
        sc_iter_letter_long σ nv sv qv bnv bsv (textFamily n seed) q
          biv b cap (letterWords j seed) sv2 D na ch (wPos j) hna hD
          hlong hlen62 h97 h99 (by omega),
        by omega, DeadFrom.push4 hD, by omega, by omega, ?_⟩
      rcases hbOr with ⟨hb31, hDb⟩ | hright
      · exact Or.inl ⟨hb31, lookup_append_left hDb⟩
      · exact Or.inr hright
    · refine ⟨183, by omega, _, _,
        sc_iter_letter_short σ nv sv qv bnv bsv (textFamily n seed) q
          biv b cap (letterWords j seed) sv2 D na ch (wPos j) hna hD
          (by omega) (by omega) hlen62 h97 h99 (by omega),
        by omega, DeadFrom.push2 hD, by omega, by omega, ?_⟩
      rcases hbOr with ⟨hb31, hDb⟩ | hright
      · exact Or.inl ⟨hb31, lookup_append_left hDb⟩
      · exact Or.inr hright
  obtain ⟨kl, hkl, D₁, na₁, hL, hna₁, hD₁, hblt₁, hnale₁, hbOr₁⟩ :=
    hletter
  -- the closing separator at `wPos j + 1`, by shape
  have hf : ((textFamily n seed).drop (wPos j)).take
      ((wPos j + 1) - wPos j) = [letterByte seed j] := by
    rw [show wPos j + 1 - wPos j = 1 from by omega]
    exact textFamily_slice_word seed hj
  have hiC : wPos j + 1 < (textFamily n seed).length := by
    rw [hlenP]; omega
  have hsep1 : (textFamily n seed).getD (wPos j + 1) 0
      = (sepBytes j).getD 0 0 := textFamily_getD_sep1 seed hj
  have hfsucc : letterWords j seed ++ [[letterByte seed j]]
      = letterWords (j + 1) seed := (letterWords_succ j seed).symm
  have hinv' : ∀ (b' cap' : Nat) (D' : Heap) (na' : Nat),
      31 ≤ b'
      → Heap.lookup D' (.base ⟨b'⟩)
          = some (strArrCell (letterWords j seed ++ [[letterByte seed j]])
              cap')
      → (letterWords j seed).length + 1 ≤ cap'
      → DeadFrom D' na' → b' < na' → na₁ + 2 ≤ na'
      → ScanInv seed (j + 1) b' cap' D' na' := by
    intro b' cap' D' na' hb31' hlook' hcap' hD' hblt' hna'
    refine ⟨by omega, hD', hblt', ?_, Or.inl ⟨hb31', ?_⟩⟩
    · rw [letterWords_length]
      have := letterWords_length j seed
      omega
    · rw [← hfsucc]; exact hlook'
  have h3cases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases h3cases with h3 | h3 | h3
  · -- "[32]": close32, and `wPos (j+1) = wPos j + 2`
    have hsl : (sepBytes j).length = 1 := by
      rw [sepBytes_length]; simp [h3]
    have hbyte : (textFamily n seed).getD (wPos j + 1) 0 = 32 := by
      rw [hsep1, show sepBytes j = [32] from by simp [sepBytes, h3]]
      rfl
    obtain ⟨b', cap', D', na', ch', hstep, hb31', hlook', hcap', hD',
      hblt', hna'⟩ :=
      sc_iter_close32 σ nv sv qv bnv bsv (textFamily n seed) q biv b
        cap (letterWords j seed) D₁ na₁ ch (wPos j) (wPos j + 1)
        [letterByte seed j] hf hna₁ hD₁ hblt₁ (by
          have := letterWords_length j seed; omega) hbOr₁ hiC hbyte
        (by omega) (by omega)
    rw [hfsucc,
      show wPos j + 1 + 1 = wPos (j + 1) from by
        simp only [wPos, hsl]] at hstep
    exact ⟨kl + 180, by omega, b', cap', D', na', ch',
      ((wPos j : Nat) : Int), stepFnIter_chain hL hstep,
      hinv' b' cap' D' na' hb31' hlook' hcap'
        hD' hblt' hna',
      by omega⟩
  · -- "[32, 32]": close32 then a skip, `wPos (j+1) = wPos j + 3`
    have hsl : (sepBytes j).length = 2 := by
      rw [sepBytes_length]; simp [h3]
    have hbyte : (textFamily n seed).getD (wPos j + 1) 0 = 32 := by
      rw [hsep1, show sepBytes j = [32, 32] from by simp [sepBytes, h3]]
      rfl
    have hw3 : wPos (j + 1) = wPos j + 3 := by
      simp only [wPos, hsl]
    obtain ⟨b', cap', D', na', ch', hstep, hb31', hlook', hcap', hD',
      hblt', hna'⟩ :=
      sc_iter_close32 σ nv sv qv bnv bsv (textFamily n seed) q biv b
        cap (letterWords j seed) D₁ na₁ ch (wPos j) (wPos j + 1)
        [letterByte seed j] hf hna₁ hD₁ hblt₁ (by
          have := letterWords_length j seed; omega) hbOr₁ hiC hbyte
        (by omega) (by omega)
    have hbyte2 : (textFamily n seed).getD (wPos j + 2) 0 = 32 :=
      textFamily_getD_sep2 seed hj h3
    have hiS : wPos j + 2 < (textFamily n seed).length := by
      rw [hlenP]; omega
    have hskip := sc_iter_skip σ nv sv qv bnv bsv (textFamily n seed)
      q biv b' cap' (letterWords (j + 1) seed)
      ((wPos j : Nat) : Int) D' na' ch' (wPos j + 2)
      (by omega) hD' hiS hbyte2 (by omega)
    rw [hfsucc,
      show wPos j + 1 + 1 = wPos j + 2 from by omega] at hstep
    rw [show wPos j + 2 + 1 = wPos (j + 1) from by omega] at hskip
    exact ⟨kl + 180 + 116, by omega, b', cap',
      D' ++ [(.base ⟨na'⟩, sint 1), (.base ⟨na' + 1⟩, su8 32)],
      na' + 2, ch', ((wPos j : Nat) : Int),
      stepFnIter_chain (stepFnIter_chain hL hstep) hskip,
      (by
        have hbase := hinv' b' cap' D' na' hb31' hlook' hcap' hD'
          hblt' hna'
        obtain ⟨h1, h2, h3', h4, h5⟩ := hbase
        refine ⟨by omega, DeadFrom.push2 h2, by omega, h4, ?_⟩
        rcases h5 with ⟨hb31'', hDb''⟩ | hright
        · exact Or.inl ⟨hb31'', lookup_append_left hDb''⟩
        · exact Or.inr hright),
      by omega⟩
  · -- "[9]": close9, `wPos (j+1) = wPos j + 2`
    have hsl : (sepBytes j).length = 1 := by
      rw [sepBytes_length]; simp [h3]
    have hbyte : (textFamily n seed).getD (wPos j + 1) 0 = 9 := by
      rw [hsep1, show sepBytes j = [9] from by simp [sepBytes, h3]]
      rfl
    obtain ⟨b', cap', D', na', ch', hstep, hb31', hlook', hcap', hD',
      hblt', hna'⟩ :=
      sc_iter_close9 σ nv sv qv bnv bsv (textFamily n seed) q biv b
        cap (letterWords j seed) D₁ na₁ ch (wPos j) (wPos j + 1)
        [letterByte seed j] hf hna₁ hD₁ hblt₁ (by
          have := letterWords_length j seed; omega) hbOr₁ hiC hbyte
        (by omega) (by omega)
    rw [hfsucc,
      show wPos j + 1 + 1 = wPos (j + 1) from by
        simp only [wPos, hsl]] at hstep
    exact ⟨kl + 186, by omega, b', cap', D', na', ch',
      ((wPos j : Nat) : Int), stepFnIter_chain hL hstep,
      hinv' b' cap' D' na' hb31' hlook' hcap'
        hD' hblt' hna',
      by omega⟩

/-- **The scan loop**: from the loop head at word `j`, within
`600·(n−j)` steps every remaining word lands. -/
theorem sc_loop (n seed : Nat) (hn : n < 2 ^ 60) :
    ∀ m j : Nat, m = n - j → j ≤ n →
    ∀ (sv2 : Int) (b cap : Nat) (D : Heap) (na : Nat) (ch : Choices),
    ScanInv seed j b cap D na →
    ∃ k : Nat, k ≤ 600 * m ∧
    ∃ (b' cap' : Nat) (D' : Heap) (na' : Nat) (ch' : Choices)
      (sv2' : Int),
      stepFnIter k
        (scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b cap
          (letterWords j seed) ((wPos j : Nat) : Int) sv2 false false
          D na) scHeadCfg ch
        = .ok (scHeadCfg,
            scSt σ nv sv qv bnv bsv (textFamily n seed) q biv b' cap'
              (letterWords n seed) ((wPos n : Nat) : Int) sv2' false
              false D' na', ch')
      ∧ ScanInv seed n b' cap' D' na' := by
  intro m
  induction m with
  | zero =>
      intro j hm hj sv2 b cap D na ch hinv
      have : j = n := by omega
      subst this
      exact ⟨0, by omega, b, cap, D, na, ch, sv2, rfl, hinv⟩
  | succ m ih =>
      intro j hm hj sv2 b cap D na ch hinv
      have hjlt : j < n := by omega
      obtain ⟨k₁, hk₁, b₁, cap₁, D₁, na₁, ch₁, sv₁, h₁, hinv₁, _⟩ :=
        sc_word σ nv sv qv bnv bsv q biv n seed hn j hjlt sv2 b cap D
          na ch hinv
      obtain ⟨k₂, hk₂, b₂, cap₂, D₂, na₂, ch₂, sv₂', h₂, hinv₂⟩ :=
        ih (j + 1) (by omega) (by omega) sv₁ b₁ cap₁ D₁ na₁ ch₁ hinv₁
      exact ⟨k₁ + k₂, by omega, b₂, cap₂, D₂, na₂, ch₂, sv₂',
        stepFnIter_chain h₁ h₂, hinv₂⟩

end Loop

/-! ## The exit segment and the count-phase seam -/

/-- The count-phase seam front (cells 0–30): the words handle
delivered into `words` (cell 21) and the shim result cell (23); the
scan cells stay behind as dead debris. -/
def wHeapCount (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int)
    (b k cap : Nat) (iv sv2 : Int) : Heap :=
  wHeapWF nv sv qv bnv bsv l q biv ++
    [(.base ⟨21⟩, slsCell b 0 k cap), (.base ⟨22⟩, sstr (gs l)),
     (.base ⟨23⟩, slsCell b 0 k cap),
     (.base ⟨24⟩, slsCell 25 0 0 0), (.base ⟨25⟩, strArrCell [] 0),
     (.base ⟨26⟩, slsCell b 0 k cap), (.base ⟨27⟩, sint iv),
     (.base ⟨28⟩, sint sv2), (.base ⟨29⟩, sbool false),
     (.base ⟨30⟩, sbool false)]

/-- **The exit segment**: test false → break out of the loop → the
tail `if` (not in field) → `$res0 = out` → return through the shim
frame into `words`. 29 steps, front-only. -/
theorem sc_exit_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b k cap : Nat) (iv sv2 : Int)
    (D : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29
      (wSt σ (wHeapScan nv sv qv bnv bsv l q biv b k cap iv sv2 false
        false ++ D) na)
      (.retV (.bool false) scCmpK) ch
      = .ok (.exec (.seqn #[]) wfEnvW wfAfterShim,
          wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv sv2
            ++ D) na, ch) := by
  with_unfolding_all rfl

/-! ## The scan phase, assembled -/

/-- **The scan phase**: from the shim-body entry at the FAMILY text,
within `600·n + 251` steps the fields slice holding EXACTLY
`letterWords n seed` is delivered into `words` and the machine parks
at the count-phase seam `.exec (.seqn #[]) wfEnvW wfAfterShim`. The
backing is choice-dependent: `ScanInv` locates the words either in the
debris region (`31 ≤ b`) or — for `n = 0` — at the empty front backing
(`b = 25`). -/
theorem scan_phase (σ : ExecState) (nv sv qv bnv bsv : Int)
    (q : List UInt8) (biv : Int) (n seed : Nat) (hn : n < 2 ^ 60)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 600 * n + 251 ∧
    ∃ (b cap : Nat) (D : Heap) (na : Nat) (ch' : Choices) (sv2 : Int),
      stepFnIter k
        (wSt σ (wHeapShim nv sv qv bnv bsv (textFamily n seed) q biv)
          24)
        (.exec goleanShimStringsFieldsFunc.body shimFrameEnv
          shimFrameK) ch
      = .ok (.exec (.seqn #[]) wfEnvW wfAfterShim,
          wSt σ (wHeapCount nv sv qv bnv bsv (textFamily n seed) q biv
            b n cap ((wPos n : Nat) : Int) sv2 ++ D) na, ch')
      ∧ ScanInv seed n b cap D na := by
  have hlenP : (textFamily n seed).length = wPos n :=
    textFamily_length n seed
  have hwle : wPos n ≤ 3 * n + 1 := wPos_le n
  have hwpos : 1 ≤ wPos n := wPos_pos n
  have hpro := sc_pro_raw σ nv sv qv bnv bsv (textFamily n seed) q biv
    ch
  have hD31 : DeadFrom ([] : Heap) 31 := fun x _ => rfl
  have hiter0 := sc_iter0 σ nv sv qv bnv bsv (textFamily n seed) q biv
    25 0 [] 0 [] 31 ch 0 (by omega) hD31 (by omega)
    (show (textFamily n seed).getD 0 0 = 32 from rfl) (by omega)
  obtain ⟨kL, hkL, b', cap', D', na', ch', sv2', hloop, hinvN⟩ :=
    sc_loop σ nv sv qv bnv bsv q biv n seed hn n 0 (by omega)
      (by omega) ((0 : Nat) : Int) 25 0
      ([] ++ [(.base ⟨31⟩, sint 1), (.base ⟨32⟩, su8 32)]) 33 ch
      ⟨by omega, DeadFrom.push2 hD31, by omega,
        by rw [letterWords_length]; omega, Or.inr ⟨rfl, rfl, rfl⟩⟩
  rw [show ((0 + 1 : Nat) : Int) = ((wPos 0 : Nat) : Int) from rfl]
    at hiter0
  have hA := sc_A1_raw σ nv sv qv bnv bsv (textFamily n seed) q biv b'
    cap' (letterWords n seed) ((wPos n : Nat) : Int) sv2' false D' na'
    ch'
  rw [show decide (((wPos n : Nat) : Int)
      < (((textFamily n seed).length : Nat) : Int)) = false from
    decide_eq_false (by rw [hlenP]; omega)] at hA
  have hexit := sc_exit_raw σ nv sv qv bnv bsv (textFamily n seed) q
    biv b' (letterWords n seed).length cap' ((wPos n : Nat) : Int)
    sv2' D' na' ch'
  have hchain := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hpro hiter0) hloop) hA) hexit
  rw [letterWords_length] at hchain
  exact ⟨79 + 123 + kL + 20 + 29, by omega, b', cap', D', na', ch',
    sv2', hchain, hinvN⟩

/-! ## The build → scan chain (at the pinned program) -/

/-- **Build → scan**: from the post-prelude machine seed, within
`703·n + 402` steps the family text is built, `wordFreq` and the shim
frames are entered, the scan delivers EXACTLY `letterWords n seed`
into `words`, and the machine parks at the count-phase seam. -/
theorem build_scan_chain (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) (ch : Choices) :
    ∃ k : Nat, k ≤ 703 * n + 402 ∧
    ∃ (b cap : Nat) (D : Heap) (na : Nat) (ch' : Choices) (sv2 : Int),
      stepFnIter k
        (wSt sProg (wHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
          ((qsel : Nat) : Int)) 7) sHC0 ch
      = .ok (.exec (.seqn #[]) wfEnvW wfAfterShim,
          wSt sProg (wHeapCount ((n : Nat) : Int) ((seed : Nat) : Int)
            ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
            (textFamily n seed) (qWord qsel) ((n : Nat) : Int)
            b n cap ((wPos n : Nat) : Int) sv2 ++ D) na, ch')
      ∧ ScanInv seed n b cap D na := by
  obtain ⟨kB, hkB, hbuild⟩ := build_phase n seed qsel (by omega) hseed
    hqsel ch
  have hcall := stepFnIter_one (ch := ch) (stepFn_call_enter
    (plans := wfShapes) (env := hEnv3) (k := hAfterWf)
    (vals := [.string (gs (textFamily n seed))])
    (v := .string (gs (qWord qsel)))
    (wf_enterFrame_fact ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
      (textFamily n seed) (qWord qsel) ((n : Nat) : Int)))
  have hwfpro := wf_pro_raw sProg ((n : Nat) : Int)
    ((seed : Nat) : Int) ((qsel : Nat) : Int) ((n : Nat) : Int)
    ((seed : Nat) : Int) (textFamily n seed) (qWord qsel)
    ((n : Nat) : Int) ch
  have hshim := stepFnIter_one (ch := ch) (stepFn_call_enter
    (plans := shimShapes) (env := wfEnvW) (k := wfAfterShim)
    (vals := []) (v := .string (gs (textFamily n seed)))
    (shim_enterFrame_fact ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
      (textFamily n seed) (qWord qsel) ((n : Nat) : Int)))
  obtain ⟨kS, hkS, b, cap, D, na, ch', sv2, hscan, hinv⟩ :=
    scan_phase sProg ((n : Nat) : Int) ((seed : Nat) : Int)
      ((qsel : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int)
      (qWord qsel) ((n : Nat) : Int) n seed hn ch
  exact ⟨kB + 1 + 8 + 1 + kS, by omega, b, cap, D, na, ch', sv2,
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hbuild hcall) hwfpro) hshim) hscan,
    hinv⟩

end GoLean.Examples.WordFreq