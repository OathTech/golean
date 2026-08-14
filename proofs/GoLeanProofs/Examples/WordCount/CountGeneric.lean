import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.Machine

/-!
# WordCount — CountGeneric

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

section CountGeneric

open GoLean.Surface GoLean.SliceMem

/-- The map-handle heap cell at data address `bMap`. -/
abbrev mhG (bMap : Nat) : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨bMap⟩)⟩⟩
/-- The nil-map cell (`$c1`'s default). -/
abbrev nilMapCell : HeapCell := ⟨some tMap, .map ⟨none⟩⟩
/-- The input-slice handle over backing address `bArr`. -/
abbrev wsHG (bArr L : Nat) : GoValue :=
  .slice ⟨some (.base ⟨bArr⟩), 0, L, L⟩

/-- **The placement-generic counting ITERATION** (53 steps): stated over
an abstract state family `S`, abstract placement environments/
continuations, and the per-segment transition FACTS as hypotheses —
each hypothesis type pins every intermediate state and configuration,
so no instantiation can send the unifier into the concrete front (the
storm-class fix, session note §1 fix 2). -/
theorem wcIter_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp postK : Cont)
    (env3g : LocalEnv) (u1Envg uEnvg : Nat → LocalEnv)
    -- the segment facts
    (hC1 : ∀ kvs iv dead na ch,
      stepFnIter 7 (S kvs iv false dead na) (.retV (.bool true) cmp) ch
        = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3g
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3g postK),
          S kvs iv false dead na, ch))
    (hInit1 : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := "$c1", typ := tMap }) env3g
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3g postK)) ch
        = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Envg na) postK),
          S kvs iv false (dead ++ [(.base ⟨na⟩, nilMapCell)]) (na + 1), ch))
    (hC2 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Envg na₀) postK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
              [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt1 : ∀ kvs iv dead na₀ na ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK)),
          S kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG bMap)]) na, ch))
    (hC3 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK))) ch
        = .ok (.exec (.initialization { id := "$c2", typ := tU64 })
              (u1Envg na₀)
              (.seq [.assign (.var "$c2")
                  (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
                (u1Envg na₀) postK),
          S kvs iv false dead na, ch))
    (hInit2 : ∀ kvs iv dead na₀ ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG bMap)]) (na₀ + 1))
          (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Envg na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1Envg na₀) postK)) ch
        = .ok (.next (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (uEnvg na₀) postK),
          S kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch))
    (hC4 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 8 (S kvs iv false dead na)
          (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnvg na₀) postK)) ch
        = .ok (.retV (.int iv .int)
              (.strictK .indexGet [wsHG bArr ws.length] [] (uEnvg na₀)
                (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                  (.seqn #[]) (uEnvg na₀)
                  (.seq [mapAsgnStmt] (uEnvg na₀) postK))),
          S kvs iv false dead na, ch))
    (hRead : ∀ kvs (i : Nat) dead na, i < ws.length →
      applyStrictOp (S kvs ((i : Nat) : Int) false dead na) .indexGet
          [wsHG bArr ws.length, .int ((i : Nat) : Int) .int]
        = .ok (.int (ws.getD i 0) .uint64,
            S kvs ((i : Nat) : Int) false dead na))
    (hC5 : ∀ kvs iv dead na₀ na (w : GoValue) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
            (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
              (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnStmt] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt2 : ∀ kvs iv dead na₀ na (w : Int) ch, 0 ≤ w → w < 2 ^ 64 →
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell 0)])
          na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnStmt] (uEnvg na₀) postK)),
          S kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch))
    (hC6 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 4 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c1") (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 []
                [.var "$c2",
                 .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                   (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hVar1 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var "$c1") (uEnvg na₀) k) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩) k,
            S kvs iv false
              (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hVar2 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var "$c2") (uEnvg na₀) k) ch
        = .ok (.retV (.int w .uint64) k,
            S kvs iv false
              (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hC7 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.stmtOpK (.mapAssign tU64 tU64) 0 []
              [.var "$c2",
               .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                 (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c2") (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
                [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                  (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC8 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int w .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c1") (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hC9 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvg na₀)
              (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                (.stmtOpK (.mapAssign tU64 tU64) 0
                  [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                  (uEnvg na₀) (.seq [] (uEnvg na₀) postK))))) ch
        = .ok (.evalE (.var "$c2") (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hMapGet : ∀ kvs iv dead na (w : Int), 0 ≤ w → w < 2 ^ 64 →
      applyStrictOp (S kvs iv false dead na) (.mapGet tU64 tU64)
          [.map ⟨some (.base ⟨bMap⟩)⟩, .int w .uint64]
        = .ok (.int (cnt kvs w : Int) .uint64, S kvs iv false dead na))
    (hC10 : ∀ kvs iv dead na₀ na (w cv : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int cv .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))) ch
        = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hMapAsgn : ∀ kvs iv dead na₀ na (w : Int) (v : Nat) ch,
      0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
      stepFn (S kvs iv false dead na)
          (.retV (.int ((v : Nat) : Int) .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0
              [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.next (.seq [] (uEnvg na₀) postK),
            S (setk kvs w v) iv false dead na, ch))
    (hC11 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.next (.seq [] (uEnvg na₀) postK)) ch
        = .ok (head, S kvs iv false dead na, ch))
    -- the iteration-level hypotheses
    (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat)
    (ch : Choices)
    (hi : i < ws.length)
    (hw0 : 0 ≤ ws.getD i 0) (hw64 : ws.getD i 0 < 2 ^ 64)
    (hcnt : cnt kvs (ws.getD i 0) + 1 < 2 ^ 64)
    (hna : base0 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53 (S kvs ((i : Nat) : Int) false dead na)
        (.retV (.bool true) cmp) ch
      = .ok (head,
          S (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1))
            ((i : Nat) : Int) false
            (dead ++ [(.base ⟨na⟩, mhG bMap),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have h1 := stepFnIter_chain (hC1 kvs ((i : Nat) : Int) dead na ch)
    (stepFnIter_one (hInit1 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h2 := stepFnIter_chain h1
    (hC2 kvs ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, nilMapCell)]) na
      (na + 1) ch)
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (hSt1 kvs ((i : Nat) : Int) dead na (na + 1) ch hna hdead))
  have h4 := stepFnIter_chain h3
    (hC3 kvs ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, mhG bMap)]) na (na + 1)
      ch)
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (hInit2 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h6 := stepFnIter_chain h5
    (hC4 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) ch)
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_strict_apply (done := [wsHG bArr ws.length])
      (hRead kvs i
        (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)])
        (na + 2) hi)))
  have h8 := stepFnIter_chain h7
    (hC5 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) (.int (ws.getD i 0) .uint64) ch)
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (hSt2 kvs ((i : Nat) : Int) dead na (na + 2) (ws.getD i 0) ch hw0 hw64
      hna hdead))
  have h10 := stepFnIter_chain h9
    (hC6 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  have h11 := stepFnIter_chain h10
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h12 := stepFnIter_chain h11
    (hC7 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h14 := stepFnIter_chain h13
    (hC8 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ch)
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h16 := stepFnIter_chain h15
    (hC9 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ch)
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h18 := stepFnIter_chain h17
    (stepFnIter_one (stepFn_strict_apply
      (done := [.map ⟨some (.base ⟨bMap⟩)⟩])
      (hMapGet kvs ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
        (na + 2) (ws.getD i 0) hw0 hw64)))
  have h19 := stepFnIter_chain h18
    (hC10 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ((cnt kvs (ws.getD i 0) : Nat) : Int) ch)
  have hcast : ((cnt kvs (ws.getD i 0) : Nat) : Int) + 1
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by omega
  have hnorm1 : IntKind.normalize .uint64 ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int)
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by
    refine GoLean.SliceMem.unorm_of_range (by omega) ?_
    exact_mod_cast hcnt
  rw [hcast, hnorm1] at h19
  have h20 := stepFnIter_chain h19
    (stepFnIter_one (hMapAsgn kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1) ch hw0 hw64 hcnt))
  have h21 := stepFnIter_chain h20
    (hC11 (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1)) ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  exact h21


/-- **The placement-generic counting LOOP + exit** (strong induction on
the remaining word count): from the exit-test delivery at word `i`, the
run reaches the range head (`mapIterK`) over the snapshot of the full
counts, with `best` zeroed at `na + 2·(L−i)`, within `84·(L−i) + 23`
steps. -/
theorem wcLoop_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp : Cont) (exitK : Cont)
    (env2g envR0g : LocalEnv) (envRBg : Nat → LocalEnv) (kRg : Nat → Cont)
    (hlen : ws.length < 2 ^ 63)
    (hIter : ∀ (i : Nat) (dead : Heap) (na : Nat) (ch : Choices),
      i < ws.length → base0 ≤ na → DeadFrom dead na →
      stepFnIter 53 (S (countsList (ws.take i)) ((i : Nat) : Int) false dead
          na) (.retV (.bool true) cmp) ch
        = .ok (head,
            S (countsList (ws.take (i + 1))) ((i : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch))
    (hA1 : ∀ kvs iv dead na ch,
      stepFnIter 29 (S kvs iv false dead na) head ch
        = .ok (.retV (wsHG bArr ws.length)
              (.strictK (.lengthOf (some (.slice tU64))) [] [] env2g
                (.strictK .lessCmp
                  [.int (IntKind.normalize .int
                    (IntKind.normalize .int (iv + 1))) .int]
                  [] env2g cmp)),
            S kvs (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
              false dead na, ch))
    (hX0 : ∀ kvs iv dead na ch,
      stepFnIter 9 (S kvs iv false dead na) (.retV (.bool false) cmp) ch
        = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0g
              (.seq [.assign (.var "best") (.intLit 0 .uint64),
                wcMapRangeStmt, retSeqn] envR0g exitK),
            S kvs iv false dead na, ch))
    (hInitBest : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := "best", typ := tU64 }) envR0g
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0g exitK)) ch
        = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] (envRBg na) exitK),
            S kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch))
    (hX0b : ∀ kvs iv dead B na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRBg B) exitK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
              [.int 0 .uint64] (.seqn #[]) (envRBg B)
              (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK)),
            S kvs iv false dead na, ch))
    (hStBest : ∀ kvs iv dead B na ch, base0 ≤ B → DeadFrom dead B →
      stepFn (S kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRBg B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (envRBg B)
              (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK)),
            S kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na, ch))
    (hX0c : ∀ kvs iv dead B na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (envRBg B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK))) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
              (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBg B)
                (kRg B)),
            S kvs iv false dead na, ch))
    (hSnap : ∀ kvs iv dead B na ch,
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int) = ((p.2 : Nat) : Int)) →
      stepFn (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBg B)
              (kRg B))) ch
        = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
              (toEntries kvs) (envRBg B) (kRg B)),
            S kvs iv false dead na, ch))
    (hNormKvs : ∀ p ∈ countsList ws,
      IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int) = ((p.2 : Nat) : Int)) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), base0 ≤ na → DeadFrom dead na →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ DeadFrom tail (na + 2 * n + 1)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (S (countsList (ws.take i)) ((i : Nat) : Int) false dead na)
          (.retV (.bool (decide (((i : Nat) : Int) < (ws.length : Int)))) cmp)
          ch
        = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
              (toEntries (countsList ws)) (envRBg (na + 2 * n))
              (kRg (na + 2 * n))),
            S (countsList ws) ((ws.length : Nat) : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi dead na hna hdead ch
    rcases Nat.lt_or_ge i ws.length with hlt | hge
    · -- iterate
      rw [show (decide (((i : Nat) : Int) < (ws.length : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hIt := hIter i dead na ch hlt hna hdead
      have hdead₂ : DeadFrom (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) :=
        DeadFrom.push2 hdead
      have hA1' := hA1 (countsList (ws.take (i + 1))) ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63),
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63)] at hA1'
      have hLen := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply (done := []) (env := env2g)
          (k := .strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] env2g
            cmp)
          (ch := ch)
          (GoLean.SliceMem.applyStrictOp_len_slice
            (σ := S (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (b := .base ⟨bArr⟩) (off := 0) (len := ws.length)
            (cap := ws.length) (elem := tU64) (Nat.le_refl _)))
      have hCmp := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply
          (done := [.int ((i + 1 : Nat) : Int) .int]) (env := env2g)
          (k := cmp) (ch := ch)
          (GoLean.SliceMem.applyStrictOp_lessCmp_int
            (σ := S (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (a := ((i + 1 : Nat) : Int)) (b := ((ws.length : Nat) : Int))
            (k := .int) (k' := .int)))
      obtain ⟨k, tail, hk, htail, hbest, hrun⟩ := ih (n - 1) (by omega)
        (i + 1) (by omega) (by omega)
        (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)
        (by omega) hdead₂ ch
      refine ⟨53 + 29 + 1 + 1 + k, tail, by omega, ?_, ?_, ?_⟩
      · intro x hx
        exact htail x (by omega)
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact hbest
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hIt hA1')
            hLen) hCmp) hrun
    · -- exit: i = ws.length
      have hiL : i = ws.length := by omega
      subst hiL
      have hn0 : n = 0 := by omega
      subst hn0
      rw [show (decide (((ws.length : Nat) : Int) < ((ws.length : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      have hX := hX0 (countsList (ws.take ws.length)) ((ws.length : Nat) : Int)
        dead na ch
      have hIB := hInitBest (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) dead na ch hna hdead
      have h1 := stepFnIter_chain hX (stepFnIter_one hIB)
      have hXb := hX0b (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
      have h2 := stepFnIter_chain h1 hXb
      have hSB := hStBest (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) dead na (na + 1) ch hna hdead
      have h3 := stepFnIter_chain h2 (stepFnIter_one hSB)
      have hXc := hX0c (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
      have h4 := stepFnIter_chain h3 hXc
      have hSn := hSnap (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
        (by rw [List.take_length]; exact hNormKvs)
      have h5 := stepFnIter_chain h4 (stepFnIter_one hSn)
      rw [List.take_length] at h5
      refine ⟨23, dead ++ [(.base ⟨na⟩, u64cell 0)], by omega, ?_, ?_, ?_⟩
      · simpa using DeadFrom.push (c := u64cell 0) hdead
      · rw [Nat.mul_zero, Nat.add_zero,
          GoLean.Surface.lookup_append_right (hdead na (Nat.le_refl na))]
        exact GoLean.Surface.lookup_singleton_self
      · simpa using h5


end CountGeneric

end GoLean.Examples.WordCount
