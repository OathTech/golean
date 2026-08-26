import GoLeanProofs.Specs.Raft.SpanS23Walk4

/-!
# The apply walk, part 5 (A4d-SM2): the byIndex block assembled

The three byIndex subcases (miss/insert, hit-agree, hit-fire)
exit-unified at `.next Kc` with the model readouts (`s2HitB`,
`bInsertIfAbsent`) EXACT — split from part 4 for iteration speed.
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
set_option maxHeartbeats 16000000

/-! ## 6. The byIndex block, assembled -/

/-- Append-if-absent (the machine's first-insert on the model). -/
def bInsertIfAbsent (kvs : List (Int × SlotA)) (w : Int)
    (sl : SlotA) : List (Int × SlotA) :=
  match bIdxOf? kvs w with
  | none => kvs ++ [(w, sl)]
  | some _ => kvs

/-- The S2 counter delta of the block (the model's `s2Hit` at the
projection, spelled on the machine's slot list). -/
def s2HitB (kvs : List (Int × SlotA)) (ixN tmN : Nat)
    (dv : GoString) : Nat :=
  match bget? kvs (ixN : Int) with
  | none => 0
  | some sj => if sj.1 ≠ tmN ∨ encGS sj.2.1 ≠ encGS dv then 1 else 0

section ByIdx

variable {env6 : LocalEnv} {envC : LocalEnv} {Kc : Cont}
  {na₀ tw nw bm dc : Nat}
  {nodesV netV liveV pendV drvV hlV rnV stV : GoValue} {lm gm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {bkvs : List (Int × SlotA)} {ixN tmN idvN : Nat}
  {tmvN cmvN stvN apl ltm : Nat} {dv : GoString}

/-- **The hit path** (`ok` true): the S2 guard (short-circuit), the
fire branch or the agree skip — exit-unified at `.next Kc`, the S2
readout EXACT on the found slot. Stated at the post-lookup state
(the `s`/`ok` cells sit just below the frontier). -/
theorem s23_byidx_hit_seg {env6 : LocalEnv} {envC : LocalEnv}
    {Kc : Cont} {na₀ tw nw dc sc : Nat}
    {nodesV netV liveV byV pendV drvV hlV rnV stV : GoValue}
    {lm gm : Nat} {cc cm w sq : Int} {tr : GoString}
    {ixN tmN idvN tj nj : Nat} {dj dv : GoString}
    {tmvN cmvN stvN apl ltm : Nat}
    (henvT : LocalEnv.lookup env6 "t" = some (.base ⟨na₀⟩))
    (henvN : LocalEnv.lookup env6 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI : LocalEnv.lookup env6 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR : LocalEnv.lookup env6 "trm" = some (.base ⟨na₀ + 6⟩))
    (henvD : LocalEnv.lookup env6 "data" = some (.base ⟨dc⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (htP : Heap.lookup σ.heap (.base ⟨na₀⟩) = some (tParA tw))
    (hnP : Heap.lookup σ.heap (.base ⟨na₀ + 1⟩) = some (ndParA nw))
    (hIc : Heap.lookup σ.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (hTcP : Heap.lookup σ.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (hDc : Heap.lookup σ.heap (.base ⟨dc⟩) = some (sCell dv))
    (hNd : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm))
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq
          tr hlV))
    (hsC : Heap.lookup σ.heap (.base ⟨sc⟩)
      = some ⟨some (.defined tidS), slotV (tj, dj, nj)⟩)
    (hokC : Heap.lookup σ.heap (.base ⟨sc + 1⟩)
      = some ⟨some .bool, .bool true⟩)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64) (hidv : idvN < 2 ^ 64)
    (htj : tj < 2 ^ 64) (hnj : nj < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 8170, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ
          (.exec (.ifThenElse (.var "ok")
              (.block #[]
                #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
              (.block #[]
                #[.mapAssign byIndexE (.var "idx")
                    (.structLit (.defined tidS)
                      #[.var "trm", .var "data", idE])
                    (.int .uint64) (.defined tidS)]))
            (envSO env6 (sc))
            (.seq [] (envSO env6 (sc))
              (.seq [] env6 (FKa envC Kc)))) ch
        = .ok (.next Kc, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc cm
              (w + ((if tj ≠ tmN ∨ encGS dj ≠ encGS dv
                then (1 : Nat) else 0) : Nat)) pendV drvV sq
              tr' hlV)
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr ≤ σ'.nextAddr
      ∧ σ'.nextAddr ≤ σ.nextAddr + 27
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  -- the ok read + dispatch + block (5)
  let envSO' : LocalEnv := envSO env6 (sc)
  let envB : LocalEnv := ([] : Scope) :: envSO'
  have hH1 : stepFnIter 2 σ
      (.exec (.ifThenElse (.var "ok")
          (.block #[]
            #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
          (.block #[]
            #[.mapAssign byIndexE (.var "idx")
                (.structLit (.defined tidS)
                  #[.var "trm", .var "data", idE])
                (.int .uint64) (.defined tidS)])) envSO'
        (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))) ch
      = .ok (.retV (.bool true)
          (.ifK (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)]) envSO'
            (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))),
        σ, ch) := by
    have g1 : stepFnIter 1 σ
        (.exec (.ifThenElse (.var "ok")
            (.block #[]
              #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
            (.block #[]
              #[.mapAssign byIndexE (.var "idx")
                  (.structLit (.defined tidS)
                    #[.var "trm", .var "data", idE])
                  (.int .uint64) (.defined tidS)])) envSO'
          (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))) ch
        = .ok (.evalE (.var "ok") envSO'
            (.ifK (.block #[]
                #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
              (.block #[]
                #[.mapAssign byIndexE (.var "idx")
                    (.structLit (.defined tidS)
                      #[.var "trm", .var "data", idE])
                    (.int .uint64) (.defined tidS)]) envSO'
              (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))),
          σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain g1 (stepFnIter_one (stepFn_var
      (henv := rfl) (hlook := hokC)))
  have hH2 : stepFnIter 3 σ (.retV (.bool true)
      (.ifK (.block #[]
          #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
        (.block #[]
          #[.mapAssign byIndexE (.var "idx")
              (.structLit (.defined tidS)
                #[.var "trm", .var "data", idE])
              (.int .uint64) (.defined tidS)]) envSO'
        (.seq [] envSO' (.seq [] env6 (FKa envC Kc))))) ch
      = .ok (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[]))
          envB
          (.seq [] envB
            (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))),
        σ, ch) := by
    with_unfolding_all rfl
  -- the guard to the first comparison's Bool (8)
  have henvSB : LocalEnv.lookup envB "s"
      = some (.base ⟨sc⟩) := rfl
  have henvRB : LocalEnv.lookup envB "trm"
      = some (.base ⟨na₀ + 6⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨sc + 1⟩),
          ("s", Loc.base ⟨sc⟩)] :: env6) "trm" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvR
  have henvDB : LocalEnv.lookup envB "data"
      = some (.base ⟨dc⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨sc + 1⟩),
          ("s", Loc.base ⟨sc⟩)] :: env6) "data" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvD
  let KIf2 : Cont := .seq [] envB
    (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))
  have hH3 : stepFnIter 3 σ
      (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[])) envB
        KIf2) ch
      = .ok (.evalE (.fieldGet (.var "s") tidS "term") envB
          (.strictK (.neqCmp (.int .uint64)) [] [.var "trm"] envB
            (.orK (.neqCmp .string
                (.fieldGet (.var "s") tidS "data") (.var "data"))
              envB
              (.ifK s2Branch (.seqn #[]) envB KIf2))), σ, ch) := by
    with_unfolding_all rfl
  have hH4 := fieldOnVar_seg (σ := σ) (env := envB)
    (K := .strictK (.neqCmp (.int .uint64)) [] [.var "trm"] envB
      (.orK (.neqCmp .string
          (.fieldGet (.var "s") tidS "data") (.var "data")) envB
        (.ifK s2Branch (.seqn #[]) envB KIf2)))
    (ch := ch) (sj := (tj, dj, nj))
    henvSB hsC (rfl :
      StructFields.lookup (slotFs ((tj : Nat) : Int) dj
        ((nj : Nat) : Int)) "term"
        = some (.int ((tj : Nat) : Int) .uint64))
  have hH5 : stepFnIter 2 σ
      (.retV (.int ((tj : Nat) : Int) .uint64)
        (.strictK (.neqCmp (.int .uint64)) [] [.var "trm"] envB
          (.orK (.neqCmp .string
              (.fieldGet (.var "s") tidS "data") (.var "data"))
            envB (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
      = .ok (.retV (.int (tmN : Int) .uint64)
          (.strictK (.neqCmp (.int .uint64))
            [.int ((tj : Nat) : Int) .uint64] [] envB
            (.orK (.neqCmp .string
                (.fieldGet (.var "s") tidS "data") (.var "data"))
              envB (.ifK s2Branch (.seqn #[]) envB KIf2))),
        σ, ch) := by
    have g1 : stepFnIter 1 σ
        (.retV (.int ((tj : Nat) : Int) .uint64)
          (.strictK (.neqCmp (.int .uint64)) [] [.var "trm"] envB
            (.orK (.neqCmp .string
                (.fieldGet (.var "s") tidS "data") (.var "data"))
              envB (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
        = .ok (.evalE (.var "trm") envB
            (.strictK (.neqCmp (.int .uint64))
              [.int ((tj : Nat) : Int) .uint64] [] envB
              (.orK (.neqCmp .string
                  (.fieldGet (.var "s") tidS "data") (.var "data"))
                envB (.ifK s2Branch (.seqn #[]) envB KIf2))),
          σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain g1 (stepFnIter_one (stepFn_var
      (henv := henvRB) (hlook := hTcP)))
  have hH6 : stepFnIter 1 σ (.retV (.int (tmN : Int) .uint64)
      (.strictK (.neqCmp (.int .uint64))
        [.int ((tj : Nat) : Int) .uint64] [] envB
        (.orK (.neqCmp .string
            (.fieldGet (.var "s") tidS "data") (.var "data"))
          envB (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
      = .ok (.retV (.bool (!(((tj : Nat) : Int) == (tmN : Int))))
          (.orK (.neqCmp .string
              (.fieldGet (.var "s") tidS "data") (.var "data"))
            envB (.ifK s2Branch (.seqn #[]) envB KIf2)), σ, ch)
      := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int (tmN : Int) .uint64,
        GoValue.int ((tj : Nat) : Int) .uint64])
      = [GoValue.int ((tj : Nat) : Int) .uint64,
          GoValue.int (tmN : Int) .uint64] from rfl]
    exact applyStrictOp_neqCmp_u64
  -- shared: the branch-entry S2 pack + walk applier
  have hPack : S2Cells na₀ tw nw (sc) dc
      (twCell nodesV netV liveV lm byV cc
        cm w pendV drvV sq tr hlV)
      (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
      ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
      ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
      (tj, dj, nj) dv σ :=
    ⟨⟨htP, hnP, hTw, hNd, hIc, hTcP⟩, hsC, hDc⟩
  have henvTB : LocalEnv.lookup envB "t" = some (.base ⟨na₀⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨sc + 1⟩),
          ("s", Loc.base ⟨sc⟩)] :: env6) "t" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvT
  have henvNB : LocalEnv.lookup envB "nd"
      = some (.base ⟨na₀ + 1⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨sc + 1⟩),
          ("s", Loc.base ⟨sc⟩)] :: env6) "nd" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvN
  have henvIB : LocalEnv.lookup envB "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    show LocalEnv.lookup (([] : Scope)
      :: [("ok", Loc.base ⟨sc + 1⟩),
          ("s", Loc.base ⟨sc⟩)] :: env6) "idx" = _
    rw [env_lookup_skip rfl, env_lookup_skip rfl]
    exact henvI
  -- the exit chunk from `.next KIf2`
  have hExit : stepFnIter 4 σ (.next KIf2) ch
    = .ok (.next Kc, σ, ch) := by
    with_unfolding_all rfl
  -- the FIRE closer (shared by the two disagreement paths)
  have hfire :
      ∀ (hguard : tj ≠ tmN ∨ encGS dj ≠ encGS dv)
        (mg : Nat)
        (hg : stepFnIter mg σ
          (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[])) envB
            KIf2) ch
          = .ok (.exec s2Branch envB KIf2, σ, ch)),
        mg ≤ 30 →
      ∃ m ≤ 8170, ∃ σ' : ExecState, ∃ tr' : GoString,
        stepFnIter m σ
            (.exec (.ifThenElse (.var "ok")
                (.block #[]
                  #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
                (.block #[]
                  #[.mapAssign byIndexE (.var "idx")
                      (.structLit (.defined tidS)
                        #[.var "trm", .var "data", idE])
                      (.int .uint64) (.defined tidS)])) envSO'
              (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))) ch
          = .ok (.next Kc, σ', ch)
        ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
            = some (twCell nodesV netV liveV lm byV cc cm
                (w + ((if tj ≠ tmN ∨ encGS dj ≠ encGS dv
                  then (1 : Nat) else 0) : Nat)) pendV drvV
                sq tr' hlV)
        ∧ (∀ x, x < σ.nextAddr → x ≠ tw →
            Heap.lookup σ'.heap (.base ⟨x⟩)
              = Heap.lookup σ.heap (.base ⟨x⟩))
        ∧ σ.nextAddr ≤ σ'.nextAddr
        ∧ σ'.nextAddr ≤ σ.nextAddr + 27
        ∧ (∀ x, σ'.nextAddr ≤ x →
            Heap.lookup σ'.heap (.base ⟨x⟩) = none)
        ∧ bfTB.Agrees σ' := by
    intro hguard mg hg hmg
    have hBW := s2Branch_walk (env0 := envB) (K := KIf2)
      henvTB henvNB henvIB henvRB henvSB henvDB σ ch
      hag hfr hPack hix htm hidv htj hnj
      hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
    obtain ⟨mB, hmB, σ', tr', hrunB, hTw', hfrm', hlo, hhi,
      hfrs', hag'⟩ := hBW
    have hExit' : stepFnIter 4 σ' (.next KIf2) ch
        = .ok (.next Kc, σ', ch) := by
      with_unfolding_all rfl
    refine ⟨5 + mg + mB + 4, by omega, σ', tr', ?_, ?_, ?_,
      by omega, by omega, hfrs', hag'⟩
    · have hpre : stepFnIter 5 σ
          (.exec (.ifThenElse (.var "ok")
              (.block #[]
                #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
              (.block #[]
                #[.mapAssign byIndexE (.var "idx")
                    (.structLit (.defined tidS)
                      #[.var "trm", .var "data", idE])
                    (.int .uint64) (.defined tidS)])) envSO'
            (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))) ch
          = .ok (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[]))
              envB KIf2, σ, ch) :=
        stepFnIter_chain hH1 hH2
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        hpre hg) hrunB) hExit'
    · rw [hTw']
      rw [show (if tj ≠ tmN ∨ encGS dj ≠ encGS dv
          then (1 : Nat) else 0) = 1 from by
        rw [if_pos hguard]]
      rw [show w + ((1 : Nat) : Int) = w + 1 from by omega]
    · intro x hx hxtw
      rw [hfrm' x (by omega) hxtw]
  -- === the guard outcome split ===
  by_cases htjm : tj = tmN
  · -- first comparison EQUAL: evaluate the data comparison
    have hb1 : (!(((tj : Nat) : Int) == (tmN : Int))) = false := by
      subst htjm
      simp
    have hH7 : stepFnIter 1 σ
        (.retV (.bool (!(((tj : Nat) : Int) == (tmN : Int))))
          (.orK (.neqCmp .string
              (.fieldGet (.var "s") tidS "data") (.var "data"))
            envB (.ifK s2Branch (.seqn #[]) envB KIf2))) ch
        = .ok (.evalE (.neqCmp .string
            (.fieldGet (.var "s") tidS "data") (.var "data")) envB
            (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)),
          σ, ch) := by
      rw [hb1]
      with_unfolding_all rfl
    have hH8 : stepFnIter 1 σ
        (.evalE (.neqCmp .string
          (.fieldGet (.var "s") tidS "data") (.var "data")) envB
          (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2))) ch
        = .ok (.evalE (.fieldGet (.var "s") tidS "data") envB
            (.strictK (.neqCmp .string) [] [.var "data"] envB
              (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2))),
          σ, ch) := by
      with_unfolding_all rfl
    have hH9 := fieldOnVar_seg (σ := σ) (env := envB)
      (K := .strictK (.neqCmp .string) [] [.var "data"] envB
        (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)))
      (ch := ch) (sj := (tj, dj, nj))
      henvSB hsC (rfl :
        StructFields.lookup (slotFs ((tj : Nat) : Int) dj
          ((nj : Nat) : Int)) "data" = some (.string dj))
    have hH10 : stepFnIter 2 σ (.retV (.string dj)
        (.strictK (.neqCmp .string) [] [.var "data"] envB
          (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
        = .ok (.retV (.string dv)
            (.strictK (.neqCmp .string) [.string dj] [] envB
              (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2))),
          σ, ch) := by
      have g1 : stepFnIter 1 σ (.retV (.string dj)
          (.strictK (.neqCmp .string) [] [.var "data"] envB
            (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
          = .ok (.evalE (.var "data") envB
              (.strictK (.neqCmp .string) [.string dj] [] envB
                (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2))),
            σ, ch)
          := by
        with_unfolding_all rfl
      exact stepFnIter_chain g1 (stepFnIter_one (stepFn_var
        (henv := henvDB) (hlook := hDc)))
    have hH11 : stepFnIter 1 σ (.retV (.string dv)
        (.strictK (.neqCmp .string) [.string dj] [] envB
          (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)))) ch
        = .ok (.retV (.bool (!(dj == dv)))
            (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2)),
          σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string dv,
          GoValue.string dj])
        = [GoValue.string dj, GoValue.string dv] from rfl]
      exact applyStrictOp_neqCmp_string
    have hH11b : stepFnIter 1 σ (.retV (.bool (!(dj == dv)))
        (.boolK (.ifK s2Branch (.seqn #[]) envB KIf2))) ch
        = .ok (.retV (.bool (!(dj == dv)))
            (.ifK s2Branch (.seqn #[]) envB KIf2), σ, ch) := by
      with_unfolding_all rfl
    by_cases hdjv : encGS dj = encGS dv
    · -- AGREE: no violation, exit
      have hdeq : dj = dv := encGS_inj hdjv
      have hb2 : (!(dj == dv)) = false := by
        rw [gsBeq_iff_eq.mpr hdeq]
        rfl
      have hH12 : stepFnIter 6 σ (.retV (.bool (!(dj == dv)))
          (.ifK s2Branch (.seqn #[]) envB KIf2)) ch
          = .ok (.next Kc, σ, ch) := by
        rw [hb2]
        have g1 : stepFnIter 1 σ (.retV (.bool false)
            (.ifK s2Branch (.seqn #[]) envB KIf2)) ch
            = .ok (.exec (.seqn #[]) envB KIf2, σ, ch) := by
          with_unfolding_all rfl
        have g2 : stepFnIter 1 σ
            (.exec (.seqn #[]) envB KIf2) ch
            = .ok (.next KIf2, σ, ch) :=
          stepFnIter_one stepFn_seqn_splice
        exact stepFnIter_chain (stepFnIter_chain g1 g2) hExit
      refine ⟨5 + 3 + 3 + 2 + 1 + 1 + 1 + 3 + 2 + 1 + 1 + 6,
        by omega, σ, tr, ?_, ?_, ?_, by omega, by omega,
        hfr, hag⟩
      · have hpre : stepFnIter 5 σ
            (.exec (.ifThenElse (.var "ok")
                (.block #[]
                  #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
                (.block #[]
                  #[.mapAssign byIndexE (.var "idx")
                      (.structLit (.defined tidS)
                        #[.var "trm", .var "data", idE])
                      (.int .uint64) (.defined tidS)])) envSO'
              (.seq [] envSO' (.seq [] env6 (FKa envC Kc)))) ch
            = .ok (.exec (.ifThenElse s2GuardE s2Branch
                (.seqn #[])) envB KIf2, σ, ch) :=
          stepFnIter_chain hH1 hH2
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain
                hpre hH3) hH4) hH5) hH6) hH7)
              hH8) hH9) hH10) hH11) hH11b) hH12
      · rw [hTw]
        rw [show (if tj ≠ tmN ∨ encGS dj ≠ encGS dv
            then (1 : Nat) else 0) = 0 from by
          rw [if_neg (fun hor => hor.elim (fun h => h htjm)
            (fun h => h hdjv))]]
        rw [show w + ((0 : Nat) : Int) = w from by omega]
      · intro x hx _
        rfl
    · -- DATA DISAGREES: fire
      have hdne : dj ≠ dv := fun he => hdjv (he ▸ rfl)
      have hb2 : (!(dj == dv)) = true := by
        have : (dj == dv) = false := by
          cases hb : (dj == dv)
          · rfl
          · exact absurd (gsBeq_iff_eq.mp hb) hdne
        rw [this]
        rfl
      have hg : stepFnIter
          (3 + 3 + 2 + 1 + 1 + 1 + 3 + 2 + 1 + 1 + 1)
          σ (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[]))
            envB KIf2) ch
          = .ok (.exec s2Branch envB KIf2, σ, ch) := by
        have hH12 : stepFnIter 1 σ
            (.retV (.bool (!(dj == dv)))
              (.ifK s2Branch (.seqn #[]) envB KIf2)) ch
            = .ok (.exec s2Branch envB KIf2, σ, ch) := by
          rw [hb2]
          with_unfolding_all rfl
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain hH3 hH4) hH5) hH6) hH7) hH8) hH9)
              hH10) hH11) hH11b) hH12
      exact hfire (Or.inr hdjv)
        (3 + 3 + 2 + 1 + 1 + 1 + 3 + 2 + 1 + 1 + 1) hg (by omega)
  · -- first comparison DIFFERS: short-circuit fire
    have hb1 : (!(((tj : Nat) : Int) == (tmN : Int))) = true := by
      have : (((tj : Nat) : Int) == ((tmN : Nat) : Int)) = false
          := by
        cases hb : (((tj : Nat) : Int) == ((tmN : Nat) : Int))
        · rfl
        · exfalso
          apply htjm
          have := beq_iff_eq.mp hb
          omega
      rw [this]
      rfl
    have hg : stepFnIter (3 + 3 + 2 + 1 + 1 + 1) σ
        (.exec (.ifThenElse s2GuardE s2Branch (.seqn #[])) envB
          KIf2) ch
        = .ok (.exec s2Branch envB KIf2, σ, ch) := by
      have hH7 : stepFnIter 1 σ
          (.retV (.bool (!(((tj : Nat) : Int) == (tmN : Int))))
            (.orK (.neqCmp .string
                (.fieldGet (.var "s") tidS "data") (.var "data"))
              envB (.ifK s2Branch (.seqn #[]) envB KIf2))) ch
          = .ok (.retV (.bool true)
              (.ifK s2Branch (.seqn #[]) envB KIf2), σ, ch) := by
        rw [hb1]
        with_unfolding_all rfl
      have hH8 : stepFnIter 1 σ (.retV (.bool true)
          (.ifK s2Branch (.seqn #[]) envB KIf2)) ch
          = .ok (.exec s2Branch envB KIf2, σ, ch) := by
        with_unfolding_all rfl
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain hH3 hH4) hH5) hH6)
        hH7) hH8
    exact hfire (Or.inl htjm) (3 + 3 + 2 + 1 + 1 + 1) hg
      (by omega)


/-- **The byIndex block** (`s, ok := t.byIndex[idx]` + the S2
check / first-insert), all three subcases exit-unified at `.next Kc`
with the model readouts EXACT. -/
theorem s23_byidx_seg
    (henvT : LocalEnv.lookup env6 "t" = some (.base ⟨na₀⟩))
    (henvN : LocalEnv.lookup env6 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI : LocalEnv.lookup env6 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR : LocalEnv.lookup env6 "trm" = some (.base ⟨na₀ + 6⟩))
    (henvD : LocalEnv.lookup env6 "data" = some (.base ⟨dc⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
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
    (hd1 : tw ≠ bm) (_hd2 : nw ≠ bm) (_hd3 : dc ≠ bm) (_hd4 : dc ≠ tw)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64) (hidv : idvN < 2 ^ 64)
    (hsl : ∀ p ∈ bkvs, p.2.1 < 2 ^ 64 ∧ p.2.2.2 < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 8200, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ
          (.exec byIdxBlock env6 (.seq [] env6 (FKa envC Kc))) ch
        = .ok (.next Kc, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm
              (.map ⟨some (.base ⟨bm⟩)⟩) cc cm
              (w + (s2HitB bkvs ixN tmN dv : Nat)) pendV drvV sq
              tr' hlV)
      ∧ Heap.lookup σ'.heap (.base ⟨bm⟩)
          = some ⟨none, .mapData (toEntriesB
              (bInsertIfAbsent bkvs (ixN : Int) (tmN, dv, idvN)))⟩
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw → x ≠ bm →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr + 2 ≤ σ'.nextAddr
      ∧ σ'.nextAddr ≤ σ.nextAddr + 29
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  have htypes : σ.types = twinTypes := hag.1
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hbmna : bm < σ.nextAddr := by
    rcases Nat.lt_or_ge bm σ.nextAddr with h | h
    · exact h
    · rw [hfr bm h] at hBm; cases hBm
  have hdcna : dc < σ.nextAddr := by
    rcases Nat.lt_or_ge dc σ.nextAddr with h | h
    · exact h
    · rw [hfr dc h] at hDc; cases hDc
  have hnwna : nw < σ.nextAddr := by
    rcases Nat.lt_or_ge nw σ.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNd; cases hNd
  have htPna : na₀ < σ.nextAddr := by
    rcases Nat.lt_or_ge na₀ σ.nextAddr with h | h
    · exact h
    · rw [hfr na₀ h] at htP; cases htP
  have hnPna : na₀ + 1 < σ.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 1) σ.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 1) h] at hnP; cases hnP
  have hicna : na₀ + 3 < σ.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 3) σ.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 3) h] at hIc; cases hIc
  have htcna : na₀ + 6 < σ.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 6) σ.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 6) h] at hTc; cases hTc
  -- the lookup segment (26)
  have hLk := s23_byidx_lookup_seg (env6 := env6)
    (KK := FKa envC Kc) henvT henvI σ ch hag hfr htP hIc hTw hBm
    hix hsl
  -- the post-lookup state
  let σQ : ExecState := { σ with heap := Heap.set (Heap.set (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), .struct tidS (slotFs 0 GoString.empty 0)⟩) (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool false⟩) (.base ⟨σ.nextAddr⟩) ⟨some (.defined tidS), slotV ((bget? bkvs (ixN : Int)).getD zeroSlot)⟩) (.base ⟨σ.nextAddr + 1⟩) ⟨some .bool, .bool (bIdxOf? bkvs (ixN : Int)).isSome⟩, nextAddr := σ.nextAddr + 2 }
  have hlkQ : ∀ x : Nat, x < σ.nextAddr →
      Heap.lookup σQ.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
  have hfrQ : ∀ x, σQ.nextAddr ≤ x →
      Heap.lookup σQ.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx2 : σ.nextAddr + 2 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  -- === CASE SPLIT on the scan ===
  cases hbi : bIdxOf? bkvs (ixN : Int) with
  | none =>
    -- MISS: insert
    have hbg : bget? bkvs (ixN : Int) = none := bIdxOf?_none_bget? hbi
    have hokQ : Heap.lookup σQ.heap (.base ⟨σQ.nextAddr - 1⟩)
        = some ⟨some .bool, .bool false⟩ := by
      show Heap.lookup σQ.heap (.base ⟨σ.nextAddr + 1⟩) = _
      show Heap.lookup (Heap.set _ (.base ⟨σ.nextAddr + 1⟩)
        ⟨some .bool, .bool (bIdxOf? bkvs (ixN : Int)).isSome⟩) _ = _
      rw [hbi]
      exact lookup_set_self
    have hM := s23_byidx_miss_seg (env6 := env6) (envC := envC)
      (Kc := Kc) henvT henvN henvI henvR henvD σQ ch
      (hag : bfTB.Agrees σQ) hfrQ hokQ
      (by show 2 ≤ σ.nextAddr + 2; omega)
      (by rw [hlkQ na₀ (by omega)]; exact htP)
      (by rw [hlkQ (na₀ + 1) (by omega)]; exact hnP)
      (by rw [hlkQ (na₀ + 3) (by omega)]; exact hIc)
      (by rw [hlkQ (na₀ + 6) (by omega)]; exact hTc)
      (by rw [hlkQ dc (by omega)]; exact hDc)
      (by rw [hlkQ nw (by omega)]; exact hNd)
      (by rw [hlkQ tw (by omega)]; exact hTw)
      (by rw [hlkQ bm (by omega)]; exact hBm)
      hbi hix htm hidv
    refine ⟨26 + 30, by omega,
      { σQ with heap := Heap.set σQ.heap (.base ⟨bm⟩) ⟨none, .mapData (toEntriesB (bkvs ++ [((ixN : Int), (tmN, dv, idvN))]))⟩ },
      tr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hag⟩
    · exact stepFnIter_chain hLk hM
    · show Heap.lookup (Heap.set σQ.heap (.base ⟨bm⟩) _)
        (.base ⟨tw⟩) = _
      rw [lookup_set_other (fun he => hd1 he.symm),
        hlkQ tw (by omega), hTw]
      show _ = some (twCell nodesV netV liveV lm
        (.map ⟨some (.base ⟨bm⟩)⟩) cc cm
        (w + (s2HitB bkvs ixN tmN dv : Nat)) pendV drvV sq tr hlV)
      rw [show s2HitB bkvs ixN tmN dv = 0 from by
        unfold s2HitB
        rw [hbg]]
      rw [show w + ((0 : Nat) : Int) = w from by omega]
    · show Heap.lookup (Heap.set σQ.heap (.base ⟨bm⟩) _)
        (.base ⟨bm⟩) = _
      rw [lookup_set_self,
        show bInsertIfAbsent bkvs (ixN : Int) (tmN, dv, idvN)
          = bkvs ++ [((ixN : Int), (tmN, dv, idvN))] from by
          unfold bInsertIfAbsent
          rw [hbi]]
    · intro x hx hxtw hxbm
      show Heap.lookup (Heap.set σQ.heap (.base ⟨bm⟩) _)
        (.base ⟨x⟩) = _
      rw [lookup_set_other (fun he => hxbm he.symm),
        hlkQ x (by omega)]
    · show σ.nextAddr + 2 ≤ σ.nextAddr + 2
      omega
    · show σ.nextAddr + 2 ≤ σ.nextAddr + 29
      omega
    · intro x hx
      have hx2 : σ.nextAddr + 2 ≤ x := hx
      show Heap.lookup (Heap.set σQ.heap (.base ⟨bm⟩) _)
        (.base ⟨x⟩) = none
      rw [lookup_set_other (by omega : bm ≠ x)]
      exact hfrQ x (by omega)
  | some j =>
    obtain ⟨sj, hbg, hmem⟩ := bIdxOf?_some_bget? hbi
    obtain ⟨tj, dj, nj⟩ := sj
    have hsjr := hsl _ (bget?_mem hbg)
    have hokQ : Heap.lookup σQ.heap (.base ⟨σ.nextAddr + 1⟩)
        = some ⟨some .bool, .bool true⟩ := by
      show Heap.lookup (Heap.set _ (.base ⟨σ.nextAddr + 1⟩)
        ⟨some .bool, .bool (bIdxOf? bkvs (ixN : Int)).isSome⟩) _ = _
      rw [hbi]
      exact lookup_set_self
    have hsQ : Heap.lookup σQ.heap (.base ⟨σ.nextAddr⟩)
        = some ⟨some (.defined tidS), slotV (tj, dj, nj)⟩ := by
      show Heap.lookup (Heap.set (Heap.set _ (.base ⟨σ.nextAddr⟩)
        ⟨some (.defined tidS),
          slotV ((bget? bkvs (ixN : Int)).getD zeroSlot)⟩)
        (.base ⟨σ.nextAddr + 1⟩) _) _ = _
      rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr),
        lookup_set_self, hbg]
      rfl
    have hHit := s23_byidx_hit_seg (env6 := env6) (envC := envC)
      (Kc := Kc) (na₀ := na₀) (tw := tw) (nw := nw)
      (dc := dc) (sc := σ.nextAddr)
      henvT henvN henvI henvR henvD σQ ch
      (hag : bfTB.Agrees σQ) hfrQ
      (by rw [hlkQ na₀ (by omega)]; exact htP)
      (by rw [hlkQ (na₀ + 1) (by omega)]; exact hnP)
      (by rw [hlkQ (na₀ + 3) (by omega)]; exact hIc)
      (by rw [hlkQ (na₀ + 6) (by omega)]; exact hTc)
      (by rw [hlkQ dc (by omega)]; exact hDc)
      (by rw [hlkQ nw (by omega)]; exact hNd)
      (by rw [hlkQ tw (by omega)]; exact hTw)
      hsQ hokQ
      hix htm hidv hsjr.1 hsjr.2
      hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
    obtain ⟨mH, hmH, σ', tr', hrunH, hTw', hfrm', hlo, hhi, hfrs',
      hag'⟩ := hHit
    have hQna : σQ.nextAddr = σ.nextAddr + 2 := rfl
    refine ⟨26 + mH, by omega, σ', tr', ?_, ?_, ?_, ?_, by omega,
      by omega, hfrs', hag'⟩
    · exact stepFnIter_chain hLk hrunH
    · rw [hTw']
      rw [show (if tj ≠ tmN ∨ encGS dj ≠ encGS dv then 1 else 0)
          = s2HitB bkvs ixN tmN dv from by
        unfold s2HitB
        rw [hbg]]
    · rw [hfrm' bm (by show bm < σ.nextAddr + 2; omega)
        (fun he => hd1 he.symm),
        hlkQ bm (by omega), hBm]
      rw [show bInsertIfAbsent bkvs (ixN : Int) (tmN, dv, idvN)
        = bkvs from by
        unfold bInsertIfAbsent
        rw [hbi]]
    · intro x hx hxtw hxbm
      rw [hfrm' x (by omega) hxtw, hlkQ x (by omega)]

end ByIdx

end GoLean.RaftSeam.SpanS23
