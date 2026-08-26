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
    (hapl : apl < 2 ^ 64) (hltm : ltm < 2 ^ 64) :
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

end MainPath

end GoLean.RaftSeam.SpanS23
