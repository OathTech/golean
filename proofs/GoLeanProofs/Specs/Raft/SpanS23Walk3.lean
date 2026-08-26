import GoLeanProofs.Specs.Raft.SpanS23Walk2

/-!
# The apply walk, part 3 (A4d-SM2): the main-path segments

The deterministic mid-body segments between the S3 guards and the
byIndex block: the two cursor stores, the `GetType` unit + the
anomaly guard's EntryNormal skip, the `GetData`/`len` pair with BOTH
exits (the empty-payload EARLY RETURN and the fall-through), the
`data` conversion, the `got` write, and `committed++`.

Each segment is stated in the guard-segment pack style: the run, the
changed cells' facts, frame respect below the entry frontier,
frontier bounds, freshness, `Agrees`.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE)
open GoLean.RaftSeam.SpanApplyGetters
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

section MainPath

variable {env0 : LocalEnv} {KK : Cont} {nxt : Stmt}
  {rest4 : List Stmt} {na₀ tw nw : Nat}
  {rnV stV : GoValue} {gm : Nat}
  {idvN tmvN cmvN stvN apl ltm ixN tmN : Nat}

/-- **The cursor stores** (22 steps): `nd.applied = idx;
nd.lastTrm = trm`, each a whole-node re-normalizing field store. -/
theorem s23_cursors_seg
    (henvN0 : LocalEnv.lookup env0 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI0 : LocalEnv.lookup env0 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR0 : LocalEnv.lookup env0 "trm" = some (.base ⟨na₀ + 6⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hnP : Heap.lookup σ.heap (.base ⟨na₀ + 1⟩) = some (ndParA nw))
    (hNd : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm))
    (hIc : Heap.lookup σ.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (hTc : Heap.lookup σ.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (hidv : idvN < 2 ^ 64) (htmv : tmvN < 2 ^ 64)
    (hcmv : cmvN < 2 ^ 64) (hstv : stvN < 2 ^ 64)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64)
    (_hapl : apl < 2 ^ 64) (hltm : ltm < 2 ^ 64) :
    stepFnIter 22 σ
        (.exec appliedAsn env0
          (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)) ch
      = .ok (.exec nxt env0 (.seq rest4 env0 KK),
        { σ with heap := Heap.set (Heap.set σ.heap (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN ltm gm)) (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN tmN gm) }, ch) := by
  have htypes : σ.types = twinTypes := hag.1
  -- applied store (2 + 7 = 9), landing on the drained storeK
  have hA1 : stepFnIter 2 σ
      (.exec appliedAsn env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)) ch
      = .ok (.exec (.assign (.addr (.fieldAddr (.var "nd") tidN
            "applied")) (.var "idx")) env0
          (.seq (lastTrmAsn :: nxt :: rest4) env0 KK), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.assign (.addr (.fieldAddr (.var "nd") tidN "applied"))
        (.var "idx")]) rfl
  have hA2 : stepFnIter 1 σ
      (.exec (.assign (.addr (.fieldAddr (.var "nd") tidN "applied"))
        (.var "idx")) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)) ch
      = .ok (.evalE (.var "nd") env0
          (.tgtOpK (.chain [.field tidN "applied"]) [] [] [] [] .vals
            [.var "idx"] [] (.seqn #[]) env0
            (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σ, ch) := by
    with_unfolding_all rfl
  have hA3 : stepFnIter 1 σ (.evalE (.var "nd") env0
      (.tgtOpK (.chain [.field tidN "applied"]) [] [] [] [] .vals
        [.var "idx"] [] (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.retV (.addr (.base ⟨nw⟩))
          (.tgtOpK (.chain [.field tidN "applied"]) [] [] [] [] .vals
            [.var "idx"] [] (.seqn #[]) env0
            (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvN0) (hlook := hnP))
  have hA4 : stepFnIter 1 σ (.retV (.addr (.base ⟨nw⟩))
      (.tgtOpK (.chain [.field tidN "applied"]) [] [] [] [] .vals
        [.var "idx"] [] (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.evalE (.var "idx") env0
          (.rhsK .vals
            [.chain (.addr (.base ⟨nw⟩)) []
              [.field tidN "applied"]] [] [] (.seqn #[]) env0
            (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σ, ch) := by
    with_unfolding_all rfl
  have hA5 : stepFnIter 1 σ (.evalE (.var "idx") env0
      (.rhsK .vals
        [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "applied"]]
        [] [] (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.retV (.int (ixN : Int) .uint64)
          (.rhsK .vals
            [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "applied"]]
            [] [] (.seqn #[]) env0
            (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henvI0) (hlook := hIc))
  have hA6 : stepFnIter 1 σ (.retV (.int (ixN : Int) .uint64)
      (.rhsK .vals
        [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "applied"]]
        [] [] (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "applied"]]
          [.int (ixN : Int) .uint64] (.seqn #[]) env0
          (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σ, ch) := by
    with_unfolding_all rfl
  let σA : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN ltm gm) }
  have hA7 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "applied"]]
      [.int (ixN : Int) .uint64] (.seqn #[]) env0
      (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env0
          (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)), σA, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_node_applied (σ := σ) htypes hNd
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
  have hA8 : stepFnIter 5 σA (.next (.storeK [] [] (.seqn #[]) env0
      (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
      = .ok (.exec (.assign (.addr (.fieldAddr (.var "nd") tidN
            "lastTrm")) (.var "trm")) env0
          (.seq (nxt :: rest4) env0 KK), σA, ch) := by
    have s1 : stepFnIter 1 σA (.next (.storeK [] [] (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK))) ch
        = .ok (.exec (.seqn #[]) env0
            (.seq (lastTrmAsn :: nxt :: rest4) env0 KK), σA, ch) :=
      stepFnIter_one stepFn_storeK_nil
    have s2 : stepFnIter 2 σA (.exec (.seqn #[]) env0
        (.seq (lastTrmAsn :: nxt :: rest4) env0 KK)) ch
        = .ok (.exec lastTrmAsn env0 (.seq (nxt :: rest4) env0 KK),
          σA, ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    have s3 : stepFnIter 2 σA
        (.exec lastTrmAsn env0 (.seq (nxt :: rest4) env0 KK)) ch
        = .ok (.exec (.assign (.addr (.fieldAddr (.var "nd") tidN
              "lastTrm")) (.var "trm")) env0
            (.seq (nxt :: rest4) env0 KK), σA, ch) :=
      stepFnIter_splice_pop
        (ss := #[.assign (.addr (.fieldAddr (.var "nd") tidN
          "lastTrm")) (.var "trm")]) rfl
    have := stepFnIter_chain (stepFnIter_chain s1 s2) s3
    exact this
  -- lastTrm store (7)
  have hnPA : Heap.lookup σA.heap (.base ⟨na₀ + 1⟩)
      = some (ndParA nw) := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨nw⟩) _) _ = _
    by_cases h : nw = na₀ + 1
    · rw [h] at hNd
      rw [hnP] at hNd
      cases hNd
    · rw [lookup_set_other h]
      exact hnP
  have hNdA : Heap.lookup σA.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN ixN ltm gm) :=
    lookup_set_self
  have hTcA : Heap.lookup σA.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨nw⟩) _) _ = _
    by_cases h : nw = na₀ + 6
    · rw [h] at hNd
      rw [hTc] at hNd
      cases hNd
    · rw [lookup_set_other h]
      exact hTc
  have hB2 : stepFnIter 1 σA
      (.exec (.assign (.addr (.fieldAddr (.var "nd") tidN "lastTrm"))
        (.var "trm")) env0 (.seq (nxt :: rest4) env0 KK)) ch
      = .ok (.evalE (.var "nd") env0
          (.tgtOpK (.chain [.field tidN "lastTrm"]) [] [] [] [] .vals
            [.var "trm"] [] (.seqn #[]) env0
            (.seq (nxt :: rest4) env0 KK)), σA, ch) := by
    with_unfolding_all rfl
  have hB3 : stepFnIter 1 σA (.evalE (.var "nd") env0
      (.tgtOpK (.chain [.field tidN "lastTrm"]) [] [] [] [] .vals
        [.var "trm"] [] (.seqn #[]) env0
        (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.retV (.addr (.base ⟨nw⟩))
          (.tgtOpK (.chain [.field tidN "lastTrm"]) [] [] [] [] .vals
            [.var "trm"] [] (.seqn #[]) env0
            (.seq (nxt :: rest4) env0 KK)), σA, ch) :=
    stepFnIter_one (stepFn_var (henv := henvN0) (hlook := hnPA))
  have hB4 : stepFnIter 1 σA (.retV (.addr (.base ⟨nw⟩))
      (.tgtOpK (.chain [.field tidN "lastTrm"]) [] [] [] [] .vals
        [.var "trm"] [] (.seqn #[]) env0
        (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.evalE (.var "trm") env0
          (.rhsK .vals
            [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
            [] [] (.seqn #[]) env0
            (.seq (nxt :: rest4) env0 KK)), σA, ch) := by
    with_unfolding_all rfl
  have hB5 : stepFnIter 1 σA (.evalE (.var "trm") env0
      (.rhsK .vals
        [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
        [] [] (.seqn #[]) env0 (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.retV (.int (tmN : Int) .uint64)
          (.rhsK .vals
            [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
            [] [] (.seqn #[]) env0
            (.seq (nxt :: rest4) env0 KK)), σA, ch) :=
    stepFnIter_one (stepFn_var (henv := henvR0) (hlook := hTcA))
  have hB6 : stepFnIter 1 σA (.retV (.int (tmN : Int) .uint64)
      (.rhsK .vals
        [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
        [] [] (.seqn #[]) env0 (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
          [.int (tmN : Int) .uint64] (.seqn #[]) env0
          (.seq (nxt :: rest4) env0 KK)), σA, ch) := by
    with_unfolding_all rfl
  let σB : ExecState := { σ with heap := Heap.set (Heap.set σ.heap (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN ltm gm)) (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN tmN gm) }
  have hB7 : stepFnIter 1 σA (.next (.storeK
      [.chain (.addr (.base ⟨nw⟩)) [] [.field tidN "lastTrm"]]
      [.int (tmN : Int) .uint64] (.seqn #[]) env0
      (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env0
          (.seq (nxt :: rest4) env0 KK)), σB, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_node_lastTrm (σ := σA) htypes hNdA
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
  have hB8 : stepFnIter 3 σB (.next (.storeK [] [] (.seqn #[]) env0
      (.seq (nxt :: rest4) env0 KK))) ch
      = .ok (.exec nxt env0 (.seq rest4 env0 KK), σB, ch) := by
    have s1 : stepFnIter 1 σB (.next (.storeK [] [] (.seqn #[]) env0
        (.seq (nxt :: rest4) env0 KK))) ch
        = .ok (.exec (.seqn #[]) env0 (.seq (nxt :: rest4) env0 KK),
          σB, ch) :=
      stepFnIter_one stepFn_storeK_nil
    have s2 : stepFnIter 2 σB (.exec (.seqn #[]) env0
        (.seq (nxt :: rest4) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest4 env0 KK), σB, ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    exact stepFnIter_chain s1 s2
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hA1 hA2) hA3) hA4) hA5) hA6) hA7) hA8)
      hB2) hB3) hB4) hB5) hB6) (stepFnIter_chain hB7 hB8)

/-- **A getter-unit prelude** (6 steps): splice/init/pop/plan +
the `e` argument read, landing on the delivered receiver at the
getter's `callArgsK`. -/
theorem getterUnit_prelude {env0 : LocalEnv} {KK : Cont}
    {rest : List Stmt} {na₀ ew : Nat}
    (c : String) (ty : Ty) (getter : String) {dv : GoValue}
    (hce : c ≠ "e")
    (henvE : LocalEnv.lookup env0 "e" = some (.base ⟨na₀ + 2⟩))
    (σ : ExecState) (ch : Choices)
    (hdef : defaultValue σ ty = .ok dv)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (heP : Heap.lookup σ.heap (.base ⟨na₀ + 2⟩) = some (eParA ew)) :
    stepFnIter 6 σ
        (.exec (getterUnit c ty getter) env0 (.seq rest env0 KK)) ch
      = .ok (.retV (.addr (.base ⟨ew⟩))
          (.callArgsK ⟨getter⟩ [(.chain [], [.ref c])] [] []
            (env0.declare c (.base ⟨σ.nextAddr⟩))
            (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK)),
        { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some ty, dv⟩, nextAddr := σ.nextAddr + 1 }, ch) := by
  have g1 : stepFnIter 2 σ
      (.exec (getterUnit c ty getter) env0 (.seq rest env0 KK)) ch
      = .ok (.exec (.initialization { id := c, typ := ty }) env0
          (.seq (.call #[.var c] ⟨getter⟩ #[.var "e"] :: rest)
            env0 KK), σ, ch) :=
    stepFnIter_splice_pop
      (ss := #[.initialization { id := c, typ := ty },
        .call #[.var c] ⟨getter⟩ #[.var "e"]]) rfl
  let σF : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some ty, dv⟩, nextAddr := σ.nextAddr + 1 }
  have g2 : stepFnIter 1 σ
      (.exec (.initialization { id := c, typ := ty }) env0
        (.seq (.call #[.var c] ⟨getter⟩ #[.var "e"] :: rest)
          env0 KK)) ch
      = .ok (.next (.seq (.call #[.var c] ⟨getter⟩ #[.var "e"]
            :: rest) (env0.declare c (.base ⟨σ.nextAddr⟩)) KK),
          σF, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := hdef))
  have g3 : stepFnIter 1 σF (.next (.seq
      (.call #[.var c] ⟨getter⟩ #[.var "e"] :: rest)
      (env0.declare c (.base ⟨σ.nextAddr⟩)) KK)) ch
      = .ok (.exec (.call #[.var c] ⟨getter⟩ #[.var "e"])
          (env0.declare c (.base ⟨σ.nextAddr⟩))
          (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK),
        σF, ch) :=
    stepFnIter_one stepFn_seq_pop
  have g4 : stepFnIter 1 σF (.exec (.call #[.var c] ⟨getter⟩
      #[.var "e"]) (env0.declare c (.base ⟨σ.nextAddr⟩))
      (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK)) ch
      = .ok (.evalE (.var "e") (env0.declare c (.base ⟨σ.nextAddr⟩))
          (.callArgsK ⟨getter⟩ [(.chain [], [.ref c])] [] []
            (env0.declare c (.base ⟨σ.nextAddr⟩))
            (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK)),
        σF, ch) := by
    with_unfolding_all rfl
  have henvE' : LocalEnv.lookup (env0.declare c (.base ⟨σ.nextAddr⟩))
      "e" = some (.base ⟨na₀ + 2⟩) := by
    cases env0 with
    | nil => cases henvE
    | cons sc outer =>
      show LocalEnv.lookup (((c, Loc.base ⟨σ.nextAddr⟩) :: sc)
        :: outer) "e" = _
      cases hs : Scope.lookup sc "e" with
      | some l =>
        rw [env_lookup_head (by rw [scope_lookup_ne hce]; exact hs)]
        have : LocalEnv.lookup (sc :: outer) "e" = some l := by
          simp [LocalEnv.lookup, hs]
        rw [this] at henvE
        exact henvE
      | none =>
        rw [env_lookup_skip (by rw [scope_lookup_ne hce]; exact hs)]
        have : LocalEnv.lookup (sc :: outer) "e"
            = LocalEnv.lookup outer "e" := by
          simp [LocalEnv.lookup, hs]
        rw [this] at henvE
        exact henvE
  have hePna : na₀ + 2 < σ.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 2) σ.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 2) h] at heP; cases heP
  have heF : Heap.lookup σF.heap (.base ⟨na₀ + 2⟩)
      = some (eParA ew) := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨na₀ + 2⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ na₀ + 2)]
    exact heP
  have g5 : stepFnIter 1 σF (.evalE (.var "e")
      (env0.declare c (.base ⟨σ.nextAddr⟩))
      (.callArgsK ⟨getter⟩ [(.chain [], [.ref c])] [] []
        (env0.declare c (.base ⟨σ.nextAddr⟩))
        (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK))) ch
      = .ok (.retV (.addr (.base ⟨ew⟩))
          (.callArgsK ⟨getter⟩ [(.chain [], [.ref c])] [] []
            (env0.declare c (.base ⟨σ.nextAddr⟩))
            (.seq rest (env0.declare c (.base ⟨σ.nextAddr⟩)) KK)),
        σF, ch) :=
    stepFnIter_one (stepFn_var (henv := henvE') (hlook := heF))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain g1 g2) g3) g4) g5

/-- Declared-name lookup (any env). -/
theorem lookup_declare_self (env : LocalEnv) (c : String) (l : Loc) :
    LocalEnv.lookup (env.declare c l) c = some l := by
  cases env <;> simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]

/-- Declare preserves other names (any env). -/
theorem lookup_declare_ne {c x : String} (h : c ≠ x)
    (env : LocalEnv) (l : Loc) :
    LocalEnv.lookup (env.declare c l) x = LocalEnv.lookup env x := by
  cases env with
  | nil =>
    simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup,
      beq_eq_false_iff_ne.mpr h]
  | cons sc outer =>
    show LocalEnv.lookup (((c, l) :: sc) :: outer) x = _
    cases hs : Scope.lookup sc x with
    | some l' =>
      rw [env_lookup_head (by rw [scope_lookup_ne h]; exact hs)]
      simp [LocalEnv.lookup, hs]
    | none =>
      rw [env_lookup_skip (by rw [scope_lookup_ne h]; exact hs)]
      simp [LocalEnv.lookup, hs]

section TypeSeg

variable {env0 : LocalEnv} {KK : Cont} {nxt : Stmt}
  {rest5 : List Stmt} {na₀ ew li lt2 lty : Nat}
  {dtyEw dtyTy : Option Ty} {fsE : Array (String × GoValue)}

/-- **The GetType unit + the EntryNormal skip** (66 steps): the type
value is delivered (premise: the entry is `EntryNormal`), the anomaly
guard reads it and falls through. -/
theorem s23_type_seg
    (henvE : LocalEnv.lookup env0 "e" = some (.base ⟨na₀ + 2⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (heP : Heap.lookup σ.heap (.base ⟨na₀ + 2⟩) = some (eParA ew))
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfTy : StructFields.lookup fsE "Type"
      = some (.addr (.base ⟨lty⟩)))
    (hTyc : Heap.lookup σ.heap (.base ⟨lty⟩)
      = some ⟨dtyTy, .int 0 .int32⟩) :
    stepFnIter 66 σ
        (.exec (getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
          "raftpb.Entry.GetType") env0
          (.seq (anomalyIfS :: nxt :: rest5) env0 KK)) ch
      = .ok (.exec nxt
          (env0.declare "$c2304" (.base ⟨σ.nextAddr⟩))
          (.seq rest5
            (env0.declare "$c2304" (.base ⟨σ.nextAddr⟩)) KK),
        twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
            (.base ⟨σ.nextAddr + 1⟩) (xCell ew))
            (.base ⟨σ.nextAddr + 2⟩)
              ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
          (σ.nextAddr + 3), ch) := by
  have htypes : σ.types = twinTypes := hag.1
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hltyna : lty < σ.nextAddr := by
    rcases Nat.lt_or_ge lty σ.nextAddr with h | h
    · exact h
    · rw [hfr lty h] at hTyc; cases hTyc
  -- the prelude (6)
  have hdefET : defaultValue σ (.defined ⟨"raftpb.EntryType"⟩)
      = .ok (.int 0 .int32) := by
    cases σ with
    | mk types functions methods methodSets heap nextAddr =>
      simp only at htypes
      subst htypes
      kernel_rfl
  have hP := getterUnit_prelude (env0 := env0) (KK := KK)
    (rest := anomalyIfS :: nxt :: rest5) (na₀ := na₀) (ew := ew)
    "$c2304" (.defined ⟨"raftpb.EntryType"⟩) "raftpb.Entry.GetType"
    (dv := .int 0 .int32) (by decide) henvE σ ch hdefET hfr heP
  let env3 : LocalEnv := env0.declare "$c2304" (.base ⟨σ.nextAddr⟩)
  let σF : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩, nextAddr := σ.nextAddr + 1 }
  -- the GetType span (49)
  have hEwF : Heap.lookup σF.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ ew)]
    exact hEw
  have hTycF : Heap.lookup σF.heap (.base ⟨lty⟩)
      = some ⟨dtyTy, .int 0 .int32⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨lty⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ lty)]
    exact hTyc
  have hfrF : ∀ x, σF.nextAddr ≤ x →
      Heap.lookup σF.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx1 : σ.nextAddr + 1 ≤ x := hx
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  have hSpan := getType_call_span (envC := env3) (tgt := "$c2304")
    (ltc := σ.nextAddr)
    (Kc := .seq (anomalyIfS :: nxt :: rest5) env3 KK)
    (lw := ew) (li := lty)
    (lookup_declare_self env0 "$c2304" (.base ⟨σ.nextAddr⟩))
    (v := 0) (by omega) (by omega) σF ch hag hEwF hfTy hTycF
    lookup_set_self hfrF (by omega) (by omega)
  let σT : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    σF.heap (.base ⟨σF.nextAddr⟩) (xCell ew))
    (.base ⟨σF.nextAddr + 1⟩)
      ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
    (.base ⟨σ.nextAddr⟩)
      ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
    (σF.nextAddr + 2)
  -- drain (2)
  have hDr : stepFnIter 2 σT
      (.exec (.seqn #[]) env3
        (.seq (anomalyIfS :: nxt :: rest5) env3 KK)) ch
      = .ok (.exec anomalyIfS env3 (.seq (nxt :: rest5) env3 KK),
        σT, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- the anomaly guard skip (9)
  have htcT : Heap.lookup σT.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩ :=
    lookup_set_self
  have hG1 : stepFnIter 2 σT
      (.exec anomalyIfS env3 (.seq (nxt :: rest5) env3 KK)) ch
      = .ok (.evalE (.var "$c2304") env3
          (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)) []
            [.intLit 0 .int32] env3
            (.ifK anomalyBranch (.seqn #[]) env3
              (.seq (nxt :: rest5) env3 KK))), σT, ch) := by
    with_unfolding_all rfl
  have hG2 : stepFnIter 1 σT (.evalE (.var "$c2304") env3
      (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)) []
        [.intLit 0 .int32] env3
        (.ifK anomalyBranch (.seqn #[]) env3
          (.seq (nxt :: rest5) env3 KK)))) ch
      = .ok (.retV (.int 0 .int32)
          (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)) []
            [.intLit 0 .int32] env3
            (.ifK anomalyBranch (.seqn #[]) env3
              (.seq (nxt :: rest5) env3 KK))), σT, ch) :=
    stepFnIter_one (stepFn_var
      (henv := lookup_declare_self env0 "$c2304" (.base ⟨σ.nextAddr⟩))
      (hlook := htcT))
  have hG3 : stepFnIter 2 σT (.retV (.int 0 .int32)
      (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)) []
        [.intLit 0 .int32] env3
        (.ifK anomalyBranch (.seqn #[]) env3
          (.seq (nxt :: rest5) env3 KK)))) ch
      = .ok (.retV (.int 0 .int32)
          (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩))
            [.int 0 .int32] [] env3
            (.ifK anomalyBranch (.seqn #[]) env3
              (.seq (nxt :: rest5) env3 KK))), σT, ch) := by
    with_unfolding_all rfl
  have hG4 : stepFnIter 1 σT (.retV (.int 0 .int32)
      (.strictK (.neqCmp (.defined ⟨"raftpb.EntryType"⟩))
        [.int 0 .int32] [] env3
        (.ifK anomalyBranch (.seqn #[]) env3
          (.seq (nxt :: rest5) env3 KK)))) ch
      = .ok (.retV (.bool false)
          (.ifK anomalyBranch (.seqn #[]) env3
            (.seq (nxt :: rest5) env3 KK)), σT, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .int32,
        GoValue.int 0 .int32])
      = [GoValue.int 0 .int32, GoValue.int 0 .int32] from rfl]
    have h0 := applyStrictOp_neqCmp_entryType (σ := σT)
      (htypes := rfl) (a := 0) (b := 0)
    rw [show (!((0 : Int) == (0 : Int))) = false from rfl] at h0
    exact h0
  have hG5 : stepFnIter 3 σT (.retV (.bool false)
      (.ifK anomalyBranch (.seqn #[]) env3
        (.seq (nxt :: rest5) env3 KK))) ch
      = .ok (.exec nxt env3 (.seq rest5 env3 KK), σT, ch) := by
    have d1 : stepFnIter 1 σT (.retV (.bool false)
        (.ifK anomalyBranch (.seqn #[]) env3
          (.seq (nxt :: rest5) env3 KK))) ch
        = .ok (.exec (.seqn #[]) env3
            (.seq (nxt :: rest5) env3 KK), σT, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d1 (stepFnIter_splice_pop (ss := #[]) rfl)
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hP hSpan) hDr) hG1) hG2) hG3) hG4) hG5
  exact hall

end TypeSeg

section LenSeg

variable {env0 : LocalEnv} {KK : Cont} {nxt : Stmt}
  {rest6 : List Stmt} {na₀ ew da : Nat}
  {dtyEw dtyD : Option Ty} {fsE : Array (String × GoValue)}
  {doff dlen dcap : Nat}

/-- The nil-slice default. -/
theorem defaultValue_sliceU8 {σ : ExecState} :
    defaultValue σ (.slice (.int .uint8))
      = .ok (.slice ⟨none, 0, 0, 0⟩) := by
  with_unfolding_all rfl

/-- **The GetData unit + the `len` guard, fall-through** (54 steps):
the payload is nonempty, so the guard reads a nonzero length and the
walk continues. -/
theorem s23_len_seg
    (henvE : LocalEnv.lookup env0 "e" = some (.base ⟨na₀ + 2⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (heP : Heap.lookup σ.heap (.base ⟨na₀ + 2⟩) = some (eParA ew))
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfD : StructFields.lookup fsE "Data"
      = some (.slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩))
    (hdc : dlen ≤ dcap) (hnz : dlen ≠ 0) :
    stepFnIter 54 σ
        (.exec (getterUnit "$c2307" (.slice (.int .uint8))
          "raftpb.Entry.GetData") env0
          (.seq (lenIfS :: nxt :: rest6) env0 KK)) ch
      = .ok (.exec nxt
          (env0.declare "$c2307" (.base ⟨σ.nextAddr⟩))
          (.seq rest6
            (env0.declare "$c2307" (.base ⟨σ.nextAddr⟩)) KK),
        twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
            (.base ⟨σ.nextAddr + 1⟩) (xCell ew))
            (.base ⟨σ.nextAddr + 2⟩)
              ⟨some (.slice (.int .uint8)),
                .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩⟩)
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.slice (.int .uint8)),
                .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩⟩)
          (σ.nextAddr + 3), ch) := by
  -- prelude (6)
  have hP := getterUnit_prelude (env0 := env0) (KK := KK)
    (rest := lenIfS :: nxt :: rest6) (na₀ := na₀) (ew := ew)
    "$c2307" (.slice (.int .uint8)) "raftpb.Entry.GetData"
    (dv := .slice ⟨none, 0, 0, 0⟩) (by decide) henvE σ ch
    defaultValue_sliceU8 hfr heP
  let env4 : LocalEnv := env0.declare "$c2307" (.base ⟨σ.nextAddr⟩)
  let σF : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩, nextAddr := σ.nextAddr + 1 }
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hEwF : Heap.lookup σF.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ ew)]
    exact hEw
  have hfrF : ∀ x, σF.nextAddr ≤ x →
      Heap.lookup σF.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx1 : σ.nextAddr + 1 ≤ x := hx
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  -- the GetData span (35)
  have hSpan := getData_call_span (envC := env4) (tgt := "$c2307")
    (ltc := σ.nextAddr)
    (Kc := .seq (lenIfS :: nxt :: rest6) env4 KK) (lw := ew)
    (lookup_declare_self env0 "$c2307" (.base ⟨σ.nextAddr⟩))
    (sv := .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩)
    σF ch hag hEwF hfD lookup_set_self hfrF (by omega)
  let σD : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    σF.heap (.base ⟨σF.nextAddr⟩) (xCell ew))
    (.base ⟨σF.nextAddr + 1⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩⟩)
    (.base ⟨σ.nextAddr⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩⟩)
    (σF.nextAddr + 2)
  -- drain (2)
  have hDr : stepFnIter 2 σD
      (.exec (.seqn #[]) env4 (.seq (lenIfS :: nxt :: rest6) env4 KK))
      ch
      = .ok (.exec lenIfS env4 (.seq (nxt :: rest6) env4 KK),
        σD, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- the len guard (11)
  have htcD : Heap.lookup σD.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.slice (.int .uint8)),
          .slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩⟩ :=
    lookup_set_self
  have hG1 : stepFnIter 3 σD
      (.exec lenIfS env4 (.seq (nxt :: rest6) env4 KK)) ch
      = .ok (.evalE (.var "$c2307") env4
          (.strictK (.lengthOf (some (.slice (.int .uint8)))) []
            [] env4
            (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
              (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
                (.seq (nxt :: rest6) env4 KK)))), σD, ch) := by
    with_unfolding_all rfl
  have hG2 : stepFnIter 1 σD (.evalE (.var "$c2307") env4
      (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] [] env4
        (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
          (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
            (.seq (nxt :: rest6) env4 KK))))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩)
          (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] []
            env4
            (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
              (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
                (.seq (nxt :: rest6) env4 KK)))), σD, ch) :=
    stepFnIter_one (stepFn_var
      (henv := lookup_declare_self env0 "$c2307" (.base ⟨σ.nextAddr⟩))
      (hlook := htcD))
  have hG3 : stepFnIter 1 σD
      (.retV (.slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩)
        (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] []
          env4
          (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 KK))))) ch
      = .ok (.retV (.int (dlen : Int) .int)
          (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 KK))), σD, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.slice
        ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩])
      = [GoValue.slice ⟨some (.base ⟨da⟩), doff, dlen, dcap⟩]
      from rfl]
    exact applyStrictOp_length_slice hdc
  have hG4 : stepFnIter 2 σD (.retV (.int (dlen : Int) .int)
      (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
        (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
          (.seq (nxt :: rest6) env4 KK)))) ch
      = .ok (.retV (.int 0 .int)
          (.strictK (.eqCmp (.int .int)) [.int (dlen : Int) .int] []
            env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 KK))), σD, ch) := by
    with_unfolding_all rfl
  have hG5 : stepFnIter 1 σD (.retV (.int 0 .int)
      (.strictK (.eqCmp (.int .int)) [.int (dlen : Int) .int] []
        env4
        (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
          (.seq (nxt :: rest6) env4 KK)))) ch
      = .ok (.retV (.bool false)
          (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
            (.seq (nxt :: rest6) env4 KK)), σD, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .int,
        GoValue.int (dlen : Int) .int])
      = [GoValue.int (dlen : Int) .int, GoValue.int 0 .int]
      from rfl]
    have h0 := applyStrictOp_eqCmp_int (σ := σD) (a := (dlen : Int))
      (b := 0)
    rw [show (((dlen : Int)) == (0 : Int)) = false from by
      rw [beq_eq_false_iff_ne]
      omega] at h0
    exact h0
  have hG6 : stepFnIter 3 σD (.retV (.bool false)
      (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
        (.seq (nxt :: rest6) env4 KK))) ch
      = .ok (.exec nxt env4 (.seq rest6 env4 KK), σD, ch) := by
    have d1 : stepFnIter 1 σD (.retV (.bool false)
        (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
          (.seq (nxt :: rest6) env4 KK))) ch
        = .ok (.exec (.seqn #[]) env4 (.seq (nxt :: rest6) env4 KK),
          σD, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d1 (stepFnIter_splice_pop (ss := #[]) rfl)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hP hSpan) hDr) hG1) hG2)
      hG3) hG4) hG5) hG6

/-- **The GetData unit + the `len` guard, EMPTY payload** (58 steps):
the guard reads length zero and the span EARLY-RETURNS through the
targetless frame — the machine's `.returning` cascade to the
caller's resumption. -/
theorem s23_len_ret {env0 : LocalEnv} {envC : LocalEnv} {Kc : Cont}
    {nxt : Stmt} {rest6 : List Stmt} {na₀ ew da : Nat}
    {dtyEw : Option Ty} {fsE : Array (String × GoValue)}
    {doff dcap : Nat}
    (henvE : LocalEnv.lookup env0 "e" = some (.base ⟨na₀ + 2⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (heP : Heap.lookup σ.heap (.base ⟨na₀ + 2⟩) = some (eParA ew))
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfD : StructFields.lookup fsE "Data"
      = some (.slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩)) :
    stepFnIter 58 σ
        (.exec (getterUnit "$c2307" (.slice (.int .uint8))
          "raftpb.Entry.GetData") env0
          (.seq (lenIfS :: nxt :: rest6) env0 (FKa envC Kc))) ch
      = .ok (.next Kc,
        twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
            (.base ⟨σ.nextAddr + 1⟩) (xCell ew))
            (.base ⟨σ.nextAddr + 2⟩)
              ⟨some (.slice (.int .uint8)),
                .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
            (.base ⟨σ.nextAddr⟩)
              ⟨some (.slice (.int .uint8)),
                .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
          (σ.nextAddr + 3), ch) := by
  have hP := getterUnit_prelude (env0 := env0)
    (KK := FKa envC Kc) (rest := lenIfS :: nxt :: rest6)
    (na₀ := na₀) (ew := ew)
    "$c2307" (.slice (.int .uint8)) "raftpb.Entry.GetData"
    (dv := .slice ⟨none, 0, 0, 0⟩) (by decide) henvE σ ch
    defaultValue_sliceU8 hfr heP
  let env4 : LocalEnv := env0.declare "$c2307" (.base ⟨σ.nextAddr⟩)
  let σF : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩, nextAddr := σ.nextAddr + 1 }
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hEwF : Heap.lookup σF.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ ew)]
    exact hEw
  have hfrF : ∀ x, σF.nextAddr ≤ x →
      Heap.lookup σF.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx1 : σ.nextAddr + 1 ≤ x := hx
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  have hSpan := getData_call_span (envC := env4) (tgt := "$c2307")
    (ltc := σ.nextAddr)
    (Kc := .seq (lenIfS :: nxt :: rest6) env4 (FKa envC Kc))
    (lw := ew)
    (lookup_declare_self env0 "$c2307" (.base ⟨σ.nextAddr⟩))
    (sv := .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩)
    σF ch hag hEwF hfD lookup_set_self hfrF (by omega)
  let σD : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    σF.heap (.base ⟨σF.nextAddr⟩) (xCell ew))
    (.base ⟨σF.nextAddr + 1⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
    (.base ⟨σ.nextAddr⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
    (σF.nextAddr + 2)
  have hDr : stepFnIter 2 σD
      (.exec (.seqn #[]) env4
        (.seq (lenIfS :: nxt :: rest6) env4 (FKa envC Kc))) ch
      = .ok (.exec lenIfS env4
          (.seq (nxt :: rest6) env4 (FKa envC Kc)), σD, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have htcD : Heap.lookup σD.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.slice (.int .uint8)),
          .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩ :=
    lookup_set_self
  -- the guard (8 steps to the bool)
  have hG1 : stepFnIter 3 σD
      (.exec lenIfS env4 (.seq (nxt :: rest6) env4 (FKa envC Kc))) ch
      = .ok (.evalE (.var "$c2307") env4
          (.strictK (.lengthOf (some (.slice (.int .uint8)))) []
            [] env4
            (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
              (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
                (.seq (nxt :: rest6) env4 (FKa envC Kc))))),
        σD, ch) := by
    with_unfolding_all rfl
  have hG2 : stepFnIter 1 σD (.evalE (.var "$c2307") env4
      (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] [] env4
        (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
          (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
            (.seq (nxt :: rest6) env4 (FKa envC Kc)))))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩)
          (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] []
            env4
            (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
              (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
                (.seq (nxt :: rest6) env4 (FKa envC Kc))))),
        σD, ch) :=
    stepFnIter_one (stepFn_var
      (henv := lookup_declare_self env0 "$c2307" (.base ⟨σ.nextAddr⟩))
      (hlook := htcD))
  have hG3 : stepFnIter 1 σD
      (.retV (.slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩)
        (.strictK (.lengthOf (some (.slice (.int .uint8)))) [] []
          env4
          (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 (FKa envC Kc)))))) ch
      = .ok (.retV (.int 0 .int)
          (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 (FKa envC Kc)))), σD, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.slice
        ⟨some (.base ⟨da⟩), doff, 0, dcap⟩])
      = [GoValue.slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩] from rfl]
    exact applyStrictOp_length_slice (by omega)
  have hG4 : stepFnIter 2 σD (.retV (.int 0 .int)
      (.strictK (.eqCmp (.int .int)) [] [.intLit 0 .int] env4
        (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
          (.seq (nxt :: rest6) env4 (FKa envC Kc))))) ch
      = .ok (.retV (.int 0 .int)
          (.strictK (.eqCmp (.int .int)) [.int 0 .int] [] env4
            (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
              (.seq (nxt :: rest6) env4 (FKa envC Kc)))), σD, ch) := by
    with_unfolding_all rfl
  have hG5 : stepFnIter 1 σD (.retV (.int 0 .int)
      (.strictK (.eqCmp (.int .int)) [.int 0 .int] [] env4
        (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
          (.seq (nxt :: rest6) env4 (FKa envC Kc))))) ch
      = .ok (.retV (.bool true)
          (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
            (.seq (nxt :: rest6) env4 (FKa envC Kc))), σD, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .int, GoValue.int 0 .int])
      = [GoValue.int 0 .int, GoValue.int 0 .int] from rfl]
    have h0 := applyStrictOp_eqCmp_int (σ := σD) (a := (0 : Int))
      (b := 0)
    rw [show (((0 : Int)) == (0 : Int)) = true from rfl] at h0
    exact h0
  -- the return path (7)
  have hR : stepFnIter 7 σD (.retV (.bool true)
      (.ifK (.block #[] #[.returnStmt]) (.seqn #[]) env4
        (.seq (nxt :: rest6) env4 (FKa envC Kc)))) ch
      = .ok (.next Kc, σD, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hP hSpan) hDr) hG1) hG2)
      hG3) hG4) hG5) hR

end LenSeg

section TailSeg

variable {env4 : LocalEnv} {KK : Cont} {na₀ ew da tw nw gm : Nat}
  {dtyEw dtyD : Option Ty} {fsE : Array (String × GoValue)}
  {doff dcap : Nat} {dbs : List UInt8} {darr : Array GoValue}
  {rnV stV : GoValue}
  {idvN tmvN cmvN stvN apl ltm : Nat}
  {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {gkvs : List (GoString × Bool)}

/-- `committed` on the spelled twin fields. -/
theorem twinFs_committed {nodesV netV liveV byV pendV drvV hlV :
    GoValue} {lm : Nat} {c cm w sq : Int} {tr : GoString} :
    StructFields.lookup (twinFs nodesV netV liveV lm byV c cm w pendV
      drvV sq tr hlV) "committed" = some (.int cm .int) := rfl

/-- **The data/got/committed tail** (87 steps): the second `GetData`,
`data := string(bytes)` (the window premises feed the conversion),
`got[data] = true`, `committed++` — landing on the byIndex block. -/
theorem s23_tail_seg
    (henvE : LocalEnv.lookup env4 "e" = some (.base ⟨na₀ + 2⟩))
    (henvN : LocalEnv.lookup env4 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvT : LocalEnv.lookup env4 "t" = some (.base ⟨na₀⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (heP : Heap.lookup σ.heap (.base ⟨na₀ + 2⟩) = some (eParA ew))
    (hnP : Heap.lookup σ.heap (.base ⟨na₀ + 1⟩) = some (ndParA nw))
    (htP : Heap.lookup σ.heap (.base ⟨na₀⟩) = some (tParA tw))
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfD : StructFields.lookup fsE "Data"
      = some (.slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩))
    (harr : Heap.lookup σ.heap (.base ⟨da⟩)
      = some ⟨dtyD, .array darr⟩)
    (hwin : ∀ i, (hi : i < dbs.length) →
      darr[doff + i]? = some (.int ((dbs[i].toNat : Int)) .uint8))
    (hdc : dbs.length ≤ dcap)
    (hNd : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm))
    (hGm : Heap.lookup σ.heap (.base ⟨gm⟩)
      = some ⟨none, .mapData (toEntriesS gkvs)⟩)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq
          tr hlV))
    (hd1 : tw ≠ gm) (_hd2 : nw ≠ gm) (_hd3 : tw ≠ nw)
    (_hd4 : da ≠ gm) (_hd5 : da ≠ tw)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm + 1 < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ σ' : ExecState,
      stepFnIter 87 σ
          (.exec (getterUnit "$c2308" (.slice (.int .uint8))
            "raftpb.Entry.GetData") env4
            (.seq [dataAsn, gotAsn, commitAsn, byIdxBlock] env4 KK))
          ch
        = .ok (.exec byIdxBlock
            ((env4.declare "$c2308"
              (.base ⟨σ.nextAddr⟩)).declare "data"
              (.base ⟨σ.nextAddr + 3⟩))
            (.seq []
              ((env4.declare "$c2308"
                (.base ⟨σ.nextAddr⟩)).declare "data"
                (.base ⟨σ.nextAddr + 3⟩)) KK), σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨gm⟩)
          = some ⟨none, .mapData (toEntriesS (setks gkvs ⟨⟨dbs⟩⟩
              true))⟩
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc (cm + 1) w
              pendV drvV sq tr hlV)
      ∧ Heap.lookup σ'.heap (.base ⟨σ.nextAddr + 3⟩)
          = some (sCell ⟨⟨dbs⟩⟩)
      ∧ (∀ x, x < σ.nextAddr → x ≠ gm → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ'.nextAddr = σ.nextAddr + 4
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  have htypes : σ.types = twinTypes := hag.1
  -- bounds
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hdana : da < σ.nextAddr := by
    rcases Nat.lt_or_ge da σ.nextAddr with h | h
    · exact h
    · rw [hfr da h] at harr; cases harr
  have hnwna : nw < σ.nextAddr := by
    rcases Nat.lt_or_ge nw σ.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNd; cases hNd
  have hgmna : gm < σ.nextAddr := by
    rcases Nat.lt_or_ge gm σ.nextAddr with h | h
    · exact h
    · rw [hfr gm h] at hGm; cases hGm
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnPna : na₀ + 1 < σ.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 1) σ.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 1) h] at hnP; cases hnP
  have htPna : na₀ < σ.nextAddr := by
    rcases Nat.lt_or_ge na₀ σ.nextAddr with h | h
    · exact h
    · rw [hfr na₀ h] at htP; cases htP
  -- ===== getData2 unit (6 + 35 + 2) =====
  have hP := getterUnit_prelude (env0 := env4) (KK := KK)
    (rest := [dataAsn, gotAsn, commitAsn, byIdxBlock])
    (na₀ := na₀) (ew := ew)
    "$c2308" (.slice (.int .uint8)) "raftpb.Entry.GetData"
    (dv := .slice ⟨none, 0, 0, 0⟩) (by decide) henvE σ ch
    defaultValue_sliceU8 hfr heP
  let env5 : LocalEnv := env4.declare "$c2308" (.base ⟨σ.nextAddr⟩)
  let σF : ExecState := { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩, nextAddr := σ.nextAddr + 1 }
  have hEwF : Heap.lookup σF.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ ew)]
    exact hEw
  have hfrF : ∀ x, σF.nextAddr ≤ x →
      Heap.lookup σF.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx1 : σ.nextAddr + 1 ≤ x := hx
    show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  have hSpan := getData_call_span (envC := env5) (tgt := "$c2308")
    (ltc := σ.nextAddr)
    (Kc := .seq [dataAsn, gotAsn, commitAsn, byIdxBlock] env5 KK)
    (lw := ew)
    (lookup_declare_self env4 "$c2308" (.base ⟨σ.nextAddr⟩))
    (sv := .slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩)
    σF ch hag hEwF hfD lookup_set_self hfrF (by omega)
  let σD : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    σF.heap (.base ⟨σF.nextAddr⟩) (xCell ew))
    (.base ⟨σF.nextAddr + 1⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩⟩)
    (.base ⟨σ.nextAddr⟩)
      ⟨some (.slice (.int .uint8)),
        .slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩⟩)
    (σF.nextAddr + 2)
  have hDr : stepFnIter 2 σD
      (.exec (.seqn #[]) env5
        (.seq [dataAsn, gotAsn, commitAsn, byIdxBlock] env5 KK)) ch
      = .ok (.exec dataAsn env5
          (.seq [gotAsn, commitAsn, byIdxBlock] env5 KK), σD, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- σD cell chases
  have hlkD : ∀ x : Nat, x < σ.nextAddr →
      Heap.lookup σD.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
  -- ===== dataAsn (15) =====
  have hA1 : stepFnIter 4 σD
      (.exec dataAsn env5
        (.seq [gotAsn, commitAsn, byIdxBlock] env5 KK)) ch
      = .ok (.exec (.assign (.var "data")
            (.stringFromByteSlice (.var "$c2308")))
          (env5.declare "data" (.base ⟨σD.nextAddr⟩))
          (.seq [gotAsn, commitAsn, byIdxBlock]
            (env5.declare "data" (.base ⟨σD.nextAddr⟩)) KK),
        { σD with heap := Heap.set σD.heap (.base ⟨σD.nextAddr⟩) (sCell (gs [])), nextAddr := σD.nextAddr + 1 }, ch) := by
    have a1 : stepFnIter 2 σD
        (.exec dataAsn env5
          (.seq [gotAsn, commitAsn, byIdxBlock] env5 KK)) ch
        = .ok (.exec (.initialization { id := "data", typ := .string })
            env5
            (.seq (.assign (.var "data")
                (.stringFromByteSlice (.var "$c2308"))
              :: gotAsn :: commitAsn :: [byIdxBlock]) env5 KK),
          σD, ch) :=
      stepFnIter_splice_pop
        (ss := #[.initialization { id := "data", typ := .string },
          .assign (.var "data")
            (.stringFromByteSlice (.var "$c2308"))]) rfl
    have a2 : stepFnIter 1 σD
        (.exec (.initialization { id := "data", typ := .string }) env5
          (.seq (.assign (.var "data")
              (.stringFromByteSlice (.var "$c2308"))
            :: gotAsn :: commitAsn :: [byIdxBlock]) env5 KK)) ch
        = .ok (.next (.seq (.assign (.var "data")
              (.stringFromByteSlice (.var "$c2308"))
            :: gotAsn :: commitAsn :: [byIdxBlock])
            (env5.declare "data" (.base ⟨σD.nextAddr⟩)) KK),
          { σD with heap := Heap.set σD.heap (.base ⟨σD.nextAddr⟩) (sCell (gs [])), nextAddr := σD.nextAddr + 1 }, ch) :=
      stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
    have a3 : stepFnIter 1
        { σD with heap := Heap.set σD.heap (.base ⟨σD.nextAddr⟩) (sCell (gs [])), nextAddr := σD.nextAddr + 1 }
        (.next (.seq (.assign (.var "data")
            (.stringFromByteSlice (.var "$c2308"))
          :: gotAsn :: commitAsn :: [byIdxBlock])
          (env5.declare "data" (.base ⟨σD.nextAddr⟩)) KK)) ch
        = .ok (.exec (.assign (.var "data")
              (.stringFromByteSlice (.var "$c2308")))
            (env5.declare "data" (.base ⟨σD.nextAddr⟩))
            (.seq [gotAsn, commitAsn, byIdxBlock]
              (env5.declare "data" (.base ⟨σD.nextAddr⟩)) KK),
          { σD with heap := Heap.set σD.heap (.base ⟨σD.nextAddr⟩) (sCell (gs [])), nextAddr := σD.nextAddr + 1 }, ch) :=
      stepFnIter_one stepFn_seq_pop
    exact stepFnIter_chain (stepFnIter_chain a1 a2) a3
  let env6 : LocalEnv := env5.declare "data" (.base ⟨σD.nextAddr⟩)
  let σE : ExecState := { σD with heap := Heap.set σD.heap (.base ⟨σD.nextAddr⟩) (sCell (gs [])), nextAddr := σD.nextAddr + 1 }
  have hσDna : σD.nextAddr = σ.nextAddr + 3 := rfl
  -- the c2308 slice cell at σE
  have hslE : Heap.lookup σE.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.slice (.int .uint8)),
          .slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩⟩ := by
    show Heap.lookup (Heap.set σD.heap (.base ⟨σD.nextAddr⟩) _)
      (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by rw [hσDna]; omega)]
    exact lookup_set_self
  have harrE : Heap.lookup σE.heap (.base ⟨da⟩)
      = some ⟨dtyD, .array darr⟩ := by
    show Heap.lookup (Heap.set σD.heap (.base ⟨σD.nextAddr⟩) _)
      (.base ⟨da⟩) = _
    rw [lookup_set_other (by rw [hσDna]; omega),
      hlkD da (by omega)]
    exact harr
  have hdataE : Heap.lookup σE.heap (.base ⟨σD.nextAddr⟩)
      = some (sCell (gs [])) := lookup_set_self
  -- the assign body (9)
  have hB1 : stepFnIter 1 σE
      (.exec (.assign (.var "data")
        (.stringFromByteSlice (.var "$c2308"))) env6
        (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)) ch
      = .ok (.evalE (.ref "data") env6
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.stringFromByteSlice (.var "$c2308")] [] (.seqn #[])
            env6 (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)),
        σE, ch) := by
    with_unfolding_all rfl
  have hB2 : stepFnIter 1 σE (.evalE (.ref "data") env6
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.stringFromByteSlice (.var "$c2308")] [] (.seqn #[]) env6
        (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.retV (.addr (.base ⟨σD.nextAddr⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.stringFromByteSlice (.var "$c2308")] [] (.seqn #[])
            env6 (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)),
        σE, ch) :=
    stepFnIter_one (GoLean.SliceWalk.stepFn_ref
      (lookup_declare_self env5 "data" (.base ⟨σD.nextAddr⟩)))
  have hB3 : stepFnIter 1 σE (.retV (.addr (.base ⟨σD.nextAddr⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.stringFromByteSlice (.var "$c2308")] [] (.seqn #[]) env6
        (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.evalE (.stringFromByteSlice (.var "$c2308")) env6
          (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
            [] [] (.seqn #[]) env6
            (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)),
        σE, ch) := by
    with_unfolding_all rfl
  have hB4 : stepFnIter 1 σE
      (.evalE (.stringFromByteSlice (.var "$c2308")) env6
        (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
          [] [] (.seqn #[]) env6
          (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.evalE (.var "$c2308") env6
          (.strictK .stringFromByteSlice [] [] env6
            (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
              [] [] (.seqn #[]) env6
              (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))),
        σE, ch) := by
    with_unfolding_all rfl
  have henv2308 : LocalEnv.lookup env6 "$c2308"
      = some (.base ⟨σ.nextAddr⟩) := by
    rw [lookup_declare_ne (by decide) env5 (.base ⟨σD.nextAddr⟩)]
    exact lookup_declare_self env4 "$c2308" (.base ⟨σ.nextAddr⟩)
  have hB5 : stepFnIter 1 σE (.evalE (.var "$c2308") env6
      (.strictK .stringFromByteSlice [] [] env6
        (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
          [] [] (.seqn #[]) env6
          (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨da⟩), doff, dbs.length,
            dcap⟩)
          (.strictK .stringFromByteSlice [] [] env6
            (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
              [] [] (.seqn #[]) env6
              (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))),
        σE, ch) :=
    stepFnIter_one (stepFn_var (henv := henv2308) (hlook := hslE))
  have hvisE : sliceVisibleValues σE
      ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩
      = .ok (bytesArr dbs) :=
    sliceVisibleValues_of_array harrE hwin hdc
  have hB6 : stepFnIter 1 σE
      (.retV (.slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩)
        (.strictK .stringFromByteSlice [] [] env6
          (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
            [] [] (.seqn #[]) env6
            (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)))) ch
      = .ok (.retV (.string ⟨⟨dbs⟩⟩)
          (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
            [] [] (.seqn #[]) env6
            (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)),
        σE, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.slice
        ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩])
      = [GoValue.slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩]
      from rfl]
    exact applyStrictOp_stringFromByteSlice hvisE
  have hB7 : stepFnIter 1 σE (.retV (.string ⟨⟨dbs⟩⟩)
      (.rhsK .vals [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
        [] [] (.seqn #[]) env6
        (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
          [.string ⟨⟨dbs⟩⟩] (.seqn #[]) env6
          (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)), σE, ch) := by
    with_unfolding_all rfl
  let σG : ExecState := { σE with heap := Heap.set σE.heap (.base ⟨σD.nextAddr⟩) (sCell ⟨⟨dbs⟩⟩) }
  have hB8 : stepFnIter 1 σE (.next (.storeK
      [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
      [.string ⟨⟨dbs⟩⟩] (.seqn #[]) env6
      (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env6
          (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)), σG, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .string) (old := .string (gs []))
        (hlook := hdataE) (hnorm := normalize_string)))
  have hB9 : stepFnIter 3 σG (.next (.storeK [] [] (.seqn #[]) env6
      (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.exec gotAsn env6
          (.seq [commitAsn, byIdxBlock] env6 KK), σG, ch) := by
    have s1 : stepFnIter 1 σG (.next (.storeK [] [] (.seqn #[]) env6
        (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
        = .ok (.exec (.seqn #[]) env6
            (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK), σG, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain s1 (stepFnIter_splice_pop (ss := #[]) rfl)
  -- σG chases (every new cell sits at ≥ σ.nextAddr)
  have hlkG : ∀ x : Nat, x < σ.nextAddr →
      Heap.lookup σG.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx
    show Heap.lookup (Heap.set (Heap.set σD.heap
      (.base ⟨σD.nextAddr⟩) _) (.base ⟨σD.nextAddr⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by rw [hσDna]; omega),
      lookup_set_other (by rw [hσDna]; omega),
      hlkD x (by omega)]
  have hnPG : Heap.lookup σG.heap (.base ⟨na₀ + 1⟩)
      = some (ndParA nw) := by
    rw [hlkG (na₀ + 1) (by omega)]; exact hnP
  have hNdG : Heap.lookup σG.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm) := by
    rw [hlkG nw (by omega)]; exact hNd
  have hGmG : Heap.lookup σG.heap (.base ⟨gm⟩)
      = some ⟨none, .mapData (toEntriesS gkvs)⟩ := by
    rw [hlkG gm (by omega)]; exact hGm
  have hdataG : Heap.lookup σG.heap (.base ⟨σD.nextAddr⟩)
      = some (sCell ⟨⟨dbs⟩⟩) := lookup_set_self
  have henvN6 : LocalEnv.lookup env6 "nd"
      = some (.base ⟨na₀ + 1⟩) := by
    rw [lookup_declare_ne (by decide) env5 (.base ⟨σD.nextAddr⟩),
      lookup_declare_ne (by decide) env4 (.base ⟨σ.nextAddr⟩)]
    exact henvN
  have henvD6 : LocalEnv.lookup env6 "data"
      = some (.base ⟨σD.nextAddr⟩) :=
    lookup_declare_self env5 "data" (.base ⟨σD.nextAddr⟩)
  have henvT6 : LocalEnv.lookup env6 "t" = some (.base ⟨na₀⟩) := by
    rw [lookup_declare_ne (by decide) env5 (.base ⟨σD.nextAddr⟩),
      lookup_declare_ne (by decide) env4 (.base ⟨σ.nextAddr⟩)]
    exact henvT
  -- ===== gotAsn (12) =====
  have hC1 : stepFnIter 1 σG
      (.exec gotAsn env6 (.seq [commitAsn, byIdxBlock] env6 KK)) ch
      = .ok (.evalE gotE env6
          (.stmtOpK (.mapAssign .string .bool) 0 []
            [.var "data", .boolLit true] env6
            (.seq [commitAsn, byIdxBlock] env6 KK)), σG, ch) := by
    with_unfolding_all rfl
  have hC2 : stepFnIter 5 σG (.evalE gotE env6
      (.stmtOpK (.mapAssign .string .bool) 0 []
        [.var "data", .boolLit true] env6
        (.seq [commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.retV (.map ⟨some (.base ⟨gm⟩)⟩)
          (.stmtOpK (.mapAssign .string .bool) 0 []
            [.var "data", .boolLit true] env6
            (.seq [commitAsn, byIdxBlock] env6 KK)), σG, ch) :=
    read_field_seg (henv := henvN6) (hp := hnPG) (hw := hNdG)
      (hf := nodeFs_got)
  have hC3 : stepFnIter 1 σG (.retV (.map ⟨some (.base ⟨gm⟩)⟩)
      (.stmtOpK (.mapAssign .string .bool) 0 []
        [.var "data", .boolLit true] env6
        (.seq [commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.evalE (.var "data") env6
          (.stmtOpK (.mapAssign .string .bool) 0
            [.map ⟨some (.base ⟨gm⟩)⟩] [.boolLit true] env6
            (.seq [commitAsn, byIdxBlock] env6 KK)), σG, ch) := by
    with_unfolding_all rfl
  have hC4 : stepFnIter 1 σG (.evalE (.var "data") env6
      (.stmtOpK (.mapAssign .string .bool) 0
        [.map ⟨some (.base ⟨gm⟩)⟩] [.boolLit true] env6
        (.seq [commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.retV (.string ⟨⟨dbs⟩⟩)
          (.stmtOpK (.mapAssign .string .bool) 0
            [.map ⟨some (.base ⟨gm⟩)⟩] [.boolLit true] env6
            (.seq [commitAsn, byIdxBlock] env6 KK)), σG, ch) :=
    stepFnIter_one (stepFn_var (henv := henvD6) (hlook := hdataG))
  have hC5 : stepFnIter 2 σG (.retV (.string ⟨⟨dbs⟩⟩)
      (.stmtOpK (.mapAssign .string .bool) 0
        [.map ⟨some (.base ⟨gm⟩)⟩] [.boolLit true] env6
        (.seq [commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.retV (.bool true)
          (.stmtOpK (.mapAssign .string .bool) 0
            [.string ⟨⟨dbs⟩⟩, .map ⟨some (.base ⟨gm⟩)⟩] [] env6
            (.seq [commitAsn, byIdxBlock] env6 KK)), σG, ch) := by
    with_unfolding_all rfl
  let σH : ExecState := { σG with heap := Heap.set σG.heap (.base ⟨gm⟩) ⟨none, .mapData (toEntriesS (setks gkvs ⟨⟨dbs⟩⟩ true))⟩ }
  have hC6 : stepFnIter 1 σG (.retV (.bool true)
      (.stmtOpK (.mapAssign .string .bool) 0
        [.string ⟨⟨dbs⟩⟩, .map ⟨some (.base ⟨gm⟩)⟩] [] env6
        (.seq [commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.next (.seq [commitAsn, byIdxBlock] env6 KK),
        σH, ch) := by
    refine stepFnIter_one (stepFn_stmtOp_apply (h := ?_))
    show applyStmtOp σG ch (.mapAssign .string .bool) 0
      [GoValue.map ⟨some (.base ⟨gm⟩)⟩, .string ⟨⟨dbs⟩⟩, .bool true]
      = _
    simp only [applyStmtOp, applyStmtOpCore, Bind.bind, Except.bind,
      pure, Except.pure]
    rw [mapAssignValue_toEntriesS (hlook := hGmG)]
  have hC7 : stepFnIter 1 σH
      (.next (.seq [commitAsn, byIdxBlock] env6 KK)) ch
      = .ok (.exec commitAsn env6 (.seq [byIdxBlock] env6 KK),
        σH, ch) :=
    stepFnIter_one stepFn_seq_pop
  -- ===== commitAsn (17) =====
  have htPH : Heap.lookup σH.heap (.base ⟨na₀⟩)
      = some (tParA tw) := by
    show Heap.lookup (Heap.set σG.heap (.base ⟨gm⟩) _)
      (.base ⟨na₀⟩) = _
    by_cases h : gm = na₀
    · rw [h] at hGm
      rw [htP] at hGm
      cases hGm
    · rw [lookup_set_other h, hlkG na₀ (by omega)]
      exact htP
  have hTwH : Heap.lookup σH.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq
          tr hlV) := by
    show Heap.lookup (Heap.set σG.heap (.base ⟨gm⟩) _)
      (.base ⟨tw⟩) = _
    rw [lookup_set_other (fun he => hd1 he.symm),
      hlkG tw (by omega)]
    exact hTw
  have hD1 : stepFnIter 1 σH
      (.exec commitAsn env6 (.seq [byIdxBlock] env6 KK)) ch
      = .ok (.evalE (.var "t") env6
          (.tgtOpK (.chain [.field tidT "committed"]) [] [] [] []
            .vals [.add committedE (.intLit 1 .int)] [] (.seqn #[])
            env6 (.seq [byIdxBlock] env6 KK)), σH, ch) := by
    with_unfolding_all rfl
  have hD2 : stepFnIter 1 σH (.evalE (.var "t") env6
      (.tgtOpK (.chain [.field tidT "committed"]) [] [] [] [] .vals
        [.add committedE (.intLit 1 .int)] [] (.seqn #[]) env6
        (.seq [byIdxBlock] env6 KK))) ch
      = .ok (.retV (.addr (.base ⟨tw⟩))
          (.tgtOpK (.chain [.field tidT "committed"]) [] [] [] []
            .vals [.add committedE (.intLit 1 .int)] [] (.seqn #[])
            env6 (.seq [byIdxBlock] env6 KK)), σH, ch) :=
    stepFnIter_one (stepFn_var (henv := henvT6) (hlook := htPH))
  have hD3 : stepFnIter 2 σH (.retV (.addr (.base ⟨tw⟩))
      (.tgtOpK (.chain [.field tidT "committed"]) [] [] [] [] .vals
        [.add committedE (.intLit 1 .int)] [] (.seqn #[]) env6
        (.seq [byIdxBlock] env6 KK))) ch
      = .ok (.evalE committedE env6
          (.strictK .add [] [.intLit 1 .int] env6
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field tidT "committed"]] [] [] (.seqn #[]) env6
              (.seq [byIdxBlock] env6 KK))), σH, ch) := by
    with_unfolding_all rfl
  have hD4 : stepFnIter 5 σH (.evalE committedE env6
      (.strictK .add [] [.intLit 1 .int] env6
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
          [] [] (.seqn #[]) env6
          (.seq [byIdxBlock] env6 KK)))) ch
      = .ok (.retV (.int cm .int)
          (.strictK .add [] [.intLit 1 .int] env6
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field tidT "committed"]] [] [] (.seqn #[]) env6
              (.seq [byIdxBlock] env6 KK))), σH, ch) :=
    read_field_seg (henv := henvT6) (hp := htPH) (hw := hTwH)
      (hf := twinFs_committed)
  have hD5 : stepFnIter 2 σH (.retV (.int cm .int)
      (.strictK .add [] [.intLit 1 .int] env6
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
          [] [] (.seqn #[]) env6 (.seq [byIdxBlock] env6 KK)))) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .add [.int cm .int] [] env6
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field tidT "committed"]] [] [] (.seqn #[]) env6
              (.seq [byIdxBlock] env6 KK))), σH, ch) := by
    with_unfolding_all rfl
  have hD6 : stepFnIter 1 σH (.retV (.int 1 .int)
      (.strictK .add [.int cm .int] [] env6
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
          [] [] (.seqn #[]) env6 (.seq [byIdxBlock] env6 KK)))) ch
      = .ok (.retV (.int (cm + 1) .int)
          (.rhsK .vals
            [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
            [] [] (.seqn #[]) env6 (.seq [byIdxBlock] env6 KK)),
        σH, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 1 .int, GoValue.int cm .int])
      = [GoValue.int cm .int, GoValue.int 1 .int] from rfl]
    exact GoLean.SliceWalk.applyStrictOp_add_int (by omega) (by omega)
  have hD7 : stepFnIter 1 σH (.retV (.int (cm + 1) .int)
      (.rhsK .vals
        [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
        [] [] (.seqn #[]) env6 (.seq [byIdxBlock] env6 KK))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
          [.int (cm + 1) .int] (.seqn #[]) env6
          (.seq [byIdxBlock] env6 KK)), σH, ch) := by
    with_unfolding_all rfl
  let σI : ExecState := { σH with heap := Heap.set σH.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV cc (cm + 1) w pendV drvV sq tr hlV) }
  have hD8 : stepFnIter 1 σH (.next (.storeK
      [.chain (.addr (.base ⟨tw⟩)) [] [.field tidT "committed"]]
      [.int (cm + 1) .int] (.seqn #[]) env6
      (.seq [byIdxBlock] env6 KK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env6
          (.seq [byIdxBlock] env6 KK)), σI, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_twin_committed (σ := σH) rfl hTwH
        hc0 hc1 (by omega) hm1 hw0 hw1 hq0 hq1))
  have hD9 : stepFnIter 3 σI (.next (.storeK [] [] (.seqn #[]) env6
      (.seq [byIdxBlock] env6 KK))) ch
      = .ok (.exec byIdxBlock env6 (.seq [] env6 KK), σI, ch) := by
    have s1 : stepFnIter 1 σI (.next (.storeK [] [] (.seqn #[]) env6
        (.seq [byIdxBlock] env6 KK))) ch
        = .ok (.exec (.seqn #[]) env6 (.seq [byIdxBlock] env6 KK),
          σI, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain s1 (stepFnIter_splice_pop (ss := #[]) rfl)
  -- assemble (6+35+2 + 4 + 9 + 3 + 12 + 17 = 87, staged)
  have hS1 : stepFnIter 43 σ
      (.exec (getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData") env4
        (.seq [dataAsn, gotAsn, commitAsn, byIdxBlock] env4 KK)) ch
      = .ok (.exec dataAsn env5
          (.seq [gotAsn, commitAsn, byIdxBlock] env5 KK), σD, ch) :=
    stepFnIter_chain (stepFnIter_chain hP hSpan) hDr
  have hS2 : stepFnIter 11 σD
      (.exec dataAsn env5
        (.seq [gotAsn, commitAsn, byIdxBlock] env5 KK)) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
          [.string ⟨⟨dbs⟩⟩] (.seqn #[]) env6
          (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK)), σE, ch) :=
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain hA1 hB1) hB2) hB3) hB4) hB5) hB6) hB7
  have hS3 : stepFnIter 4 σE (.next (.storeK
      [.chain (.addr (.base ⟨σD.nextAddr⟩)) [] []]
      [.string ⟨⟨dbs⟩⟩] (.seqn #[]) env6
      (.seq [gotAsn, commitAsn, byIdxBlock] env6 KK))) ch
      = .ok (.exec gotAsn env6
          (.seq [commitAsn, byIdxBlock] env6 KK), σG, ch) :=
    stepFnIter_chain hB8 hB9
  have hS4 : stepFnIter 12 σG
      (.exec gotAsn env6 (.seq [commitAsn, byIdxBlock] env6 KK)) ch
      = .ok (.exec commitAsn env6 (.seq [byIdxBlock] env6 KK),
        σH, ch) :=
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        hC1 hC2) hC3) hC4) hC5) hC6) hC7
  have hS5 : stepFnIter 17 σH
      (.exec commitAsn env6 (.seq [byIdxBlock] env6 KK)) ch
      = .ok (.exec byIdxBlock env6 (.seq [] env6 KK), σI, ch) :=
    stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain hD1 hD2) hD3) hD4) hD5)
        hD6) hD7) hD8) hD9
  refine ⟨σI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hS1 hS2) hS3) hS4) hS5
  · show Heap.lookup (Heap.set σH.heap (.base ⟨tw⟩) _)
      (.base ⟨gm⟩) = _
    rw [lookup_set_other hd1]
    exact lookup_set_self
  · exact lookup_set_self
  · show Heap.lookup (Heap.set σH.heap (.base ⟨tw⟩) _)
      (.base ⟨σ.nextAddr + 3⟩) = _
    rw [lookup_set_other (by omega : tw ≠ σ.nextAddr + 3)]
    show Heap.lookup (Heap.set σG.heap (.base ⟨gm⟩) _)
      (.base ⟨σ.nextAddr + 3⟩) = _
    rw [lookup_set_other (by omega : gm ≠ σ.nextAddr + 3)]
    exact hdataG
  · intro x hx hxgm hxtw
    show Heap.lookup (Heap.set σH.heap (.base ⟨tw⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxtw he.symm)]
    show Heap.lookup (Heap.set σG.heap (.base ⟨gm⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxgm he.symm),
      hlkG x (by omega)]
  · show σ.nextAddr + 1 + 2 + 1 = σ.nextAddr + 4
    omega
  · intro x hx
    have hx4 : σ.nextAddr + 4 ≤ x := by
      have : σ.nextAddr + 1 + 2 + 1 ≤ x := hx
      omega
    show Heap.lookup (Heap.set σH.heap (.base ⟨tw⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : tw ≠ x)]
    show Heap.lookup (Heap.set σG.heap (.base ⟨gm⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : gm ≠ x)]
    show Heap.lookup (Heap.set (Heap.set σD.heap
      (.base ⟨σD.nextAddr⟩) _) (.base ⟨σD.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by rw [hσDna]; omega),
      lookup_set_other (by rw [hσDna]; omega)]
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)

end TailSeg

end MainPath

end GoLean.RaftSeam.SpanS23
