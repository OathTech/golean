import GoLeanProofs.Sym.DriftApply

/-!
# THE MASTER STEP COMMUTATION WALK (WP arc slice 4, phase 2)

`stepFn'` vs `stepFn`, arm-for-arm over ANY sound interpretation — the
design's §6.2 layer 3, proven as ONE shared-code walk (log JC-4):

- at the CONCRETE interpretation it is **THE DRIFT THEOREM**
  (`stepFn'_concrete_agrees`, the charter's `:80-83` clause in the
  ruled OQ3 embedding-mediated spelling): any computing arm of
  `stepFn'` diverging from `stepFn` fails this module, hence the
  default build. This REPLACES phase 1's 16-shape spike gate
  (`spikeStep_sound`) with full-arm coverage.
- at the symbolic interpretation it is `stepFnS_sound` — the
  refinement theorem's per-step half; `Sym/Refine.lean` composes it
  through the window driver.

Statement shape: success-only (`stepFn' s c = .ok (c₁, s₁) →
stepFn (conc s) (conc c) ch = .ok (conc c₁, conc s₁, ch)`, ∀ σ ∀ ch
with `ch` unchanged): quit arms are refuted hypotheses and assert
nothing; the ~50 value/heap-touching arms ride the layer-2 helper
lemmas (`Sym/Drift{,Ops,Apply}.lean`); the ~60 pure-control arms close
by congruence (`cases h; rfl` through the structurally-compiled
`concC`/`concK`).
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

set_option maxHeartbeats 12800000 in
/-- THE MASTER WALK: one successful mirror step transports to the
machine, for every table-carrier `σ` and choice stream `ch` (unchanged
— the mirror consumes no choices; Q3 quits are what make this true by
construction). -/
theorem stepFn'_conc (hI : I.Sound) (σ : ExecState) (ch : Choices)
    {s : State D} {c : Config D} {c₁ : Config D} {s₁ : State D}
    (h : stepFn' s c = .ok (c₁, s₁)) :
    stepFn (concS I σ s) (concC I c) ch
      = .ok (concC I c₁, concS I σ s₁, ch) := by
  cases c with
  | panicked msg => simp [stepFn', quit] at h
  | panicking chain k => simp [stepFn', quit] at h
  | blockedSend a b c => simp [stepFn', quit] at h
  | blockedRecv a b c d e => simp [stepFn', quit] at h
  | blockedSelect a b c => simp [stepFn', quit] at h
  | spawned k => simp [stepFn', quit] at h
  | blockedSync a b c d => simp [stepFn', quit] at h
  | exec stmt env k =>
      cases stmt
      case seqn ss =>
        cases h
        simp only [concC, stepFn, seqCont_conc]
        rfl
      case block decls ss =>
        simp only [stepFn'] at h
        obtain ⟨⟨env', s2⟩, halloc, h2⟩ := bind_eq_ok.mp h
        have hov : c₁ = .next (.seq ss.toList env' k) ∧ s₁ = s2 := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h2
        rw [hov.1, hov.2]
        simp only [concC, concK, stepFn]
        refine bind_eq_ok.mpr
          ⟨(env', concS I σ s2), allocDecls_conc hI σ _ _ halloc, rfl⟩
      case initialization p =>
        cases k <;>
          first
            | (simp [stepFn', quit] at h; done)
            | skip
        case seq rest kenv k' =>
          simp only [stepFn'] at h
          by_cases henv : kenv = env
          · rw [if_pos henv] at h
            obtain ⟨v, hv, h2⟩ := bind_eq_ok.mp h
            rcases halloc : s.alloc v (some p.typ) with ⟨loc, s2⟩
            rw [halloc] at h2
            try simp only [] at h2
            have hov : c₁ = .next (.seq rest (env.declare p.id loc) k')
                ∧ s₁ = s2 := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2]
            simp only [concC, concK, stepFn]
            rw [if_pos henv]
            refine bind_eq_ok.mpr
              ⟨concV I v, default_conc hI _ hv, ?_⟩
            rw [alloc_conc, halloc]
            rfl
          · rw [if_neg henv] at h
            cases h
      case assign lhs rhs =>
        rcases hplan : targetPlan lhs with _ | ⟨sh, _ | ⟨e, ops⟩⟩ <;>
          (simp only [stepFn'] at h; rw [hplan] at h)
        · cases h
        · cases h
        · cases h
          simp only [concC, concK, stepFn]
          rw [hplan]
          rfl
      case ifThenElse c t e => cases h; rfl
      case «while» c b => cases h; rfl
      case returnStmt => cases h; rfl
      case breakStmt => cases h; rfl
      case continueStmt => cases h; rfl
      case label name => cases h; rfl
      case labeled name b => cases h; rfl
      case breakTo name => cases h; rfl
      case continueTo name => cases h; rfl
      case breakable b => cases h; rfl
      case deferCall callee args => cases h; rfl
      case panicStmt e => simp [stepFn', quit] at h
      case callValue targets callee args =>
        rcases hplan : targetsPlan targets.toList with _ | plans <;>
          (simp only [stepFn'] at h; rw [hplan] at h)
        · cases h
        · cases h
          simp only [concC, concK, stepFn]
          rw [hplan]
          rfl
      case call targets fid args =>
        rcases hplan : targetsPlan targets.toList with _ | plans <;>
          (simp only [stepFn'] at h; rw [hplan] at h)
        · cases h
        · rcases hargs : args.toList with _ | ⟨a, rest⟩ <;>
            rw [hargs] at h
          · cases h
          · cases h
            simp only [concC, concK, stepFn]
            rw [hplan, hargs]
            rfl
      case mapRange keyVar valVar mapExpr keyTy valTy body =>
        cases h
        rfl
      case chanSend a b c => simp [stepFn', quit] at h
      case closeChan a => simp [stepFn', quit] at h
      case chanRecv a b c => simp [stepFn', quit] at h
      case goStmt a b => simp [stepFn', quit] at h
      case selectStmt a b => simp [stepFn', quit] at h
      case unsupported feature => simp [stepFn', quit] at h
      case mapLookup t okT base index keyTy valueTy =>
        rcases hplan : targetsPlan [t, okT]
            with _ | (_ | ⟨⟨sh, _ | ⟨e, ops⟩⟩, rest⟩) <;>
          (simp only [stepFn'] at h; rw [hplan] at h) <;>
          try (cases h; done)
        cases h
        simp only [concC, concK, stepFn]
        rw [hplan]
        rfl
      case typeAssert t okT expr targetTy =>
        simp [stepFn', quit] at h
      case assignMany left right =>
        simp only [stepFn'] at h
        by_cases hsz : left.size = right.size
        · rw [if_pos hsz] at h
          rcases hplan : targetsPlan left.toList
              with _ | (_ | ⟨⟨sh, _ | ⟨e, ops⟩⟩, rest⟩) <;>
            rw [hplan] at h <;>
            try (cases h; done)
          cases h
          simp only [concC, concK, stepFn]
          rw [if_pos hsz, hplan]
          rfl
        · rw [if_neg hsz] at h
          cases h
      case syncStmt a b c => simp [stepFn', quit] at h
      -- the eleven wide statements ride ONE generic script over
      -- `stmtPlan`'s three outcomes
      all_goals (
        simp only [stepFn'] at h
        split at h
        · rename_i op nt e rest heq
          cases h
          simp only [concC, concK, stepFn]
          rw [heq]
          simp [pure, Except.pure]
        · rename_i op nt heq
          obtain ⟨s2, happ, h2⟩ := bind_eq_ok.mp h
          have hov : c₁ = .next k ∧ s₁ = s2 := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [concC, concK, stepFn]
          rw [heq]
          simp only []
          have := applyStmtOp_conc hI σ happ nt ch
          simp only [List.map_nil] at this
          rw [this]
          simp [pure, Except.pure, Bind.bind, Except.bind]
        · cases h)
  | evalE e env k =>
      cases e
      case var id =>
        rcases hlk : LocalEnv.lookup env id with _ | loc <;>
          (simp only [stepFn'] at h; rw [hlk] at h)
        · cases h
        · obtain ⟨v, hv, h2⟩ := bind_eq_ok.mp h
          have hov : c₁ = .retV v k ∧ s₁ = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [concC, concK, stepFn]
          rw [hlk]
          exact bind_eq_ok.mpr ⟨concV I v, loadLoc_conc σ hv, rfl⟩
      case intLit value kind =>
        cases h
        simp [stepFn, concC, concK, hI.litI, pure, Except.pure]
      case boolLit value =>
        cases h
        simp [stepFn, concC, concK, hI.litB, pure, Except.pure]
      case stringLit value =>
        cases h
        simp [stepFn, concC, concK, pure, Except.pure]
      case ref id =>
        rcases hlk : LocalEnv.lookup env id with _ | loc <;>
          (simp only [stepFn'] at h; rw [hlk] at h)
        · cases h
        · cases h
          simp only [concC, concK, stepFn]
          rw [hlk]
          simp [pure, Except.pure]
      case locLit l =>
        cases h
        simp [stepFn, concC, concK, pure, Except.pure]
      case and l r => cases h; rfl
      case or l r => cases h; rfl
      case recoverCall => simp [stepFn', quit] at h
      case unsupported feature => simp [stepFn', quit] at h
      -- the strict expression forms ride ONE generic script over
      -- `strictPlan`'s three outcomes
      all_goals (
        simp only [stepFn'] at h
        split at h
        · rename_i op e1 rest heq
          cases h
          simp only [concC, concK, stepFn]
          rw [heq]
          simp [pure, Except.pure]
        · rename_i op heq
          obtain ⟨⟨v, s2⟩, happ, h2⟩ := bind_eq_ok.mp h
          have hov : c₁ = .retV v k ∧ s₁ = s2 := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [concC, concK, stepFn]
          rw [heq]
          simp only []
          have := applyStrictOp_conc hI σ happ
          simp only [List.map_nil] at this
          rw [this]
          simp [pure, Except.pure, Bind.bind, Except.bind]
        · cases h)
  | retV v k =>
      cases k
      case stop => simp [stepFn', quit] at h
      case strictK op done pending env k' =>
        cases pending with
        | cons e rest => cases h; rfl
        | nil =>
            simp only [stepFn'] at h
            obtain ⟨⟨out, s2⟩, happ, h2⟩ := bind_eq_ok.mp h
            have hov : c₁ = .retV out k' ∧ s₁ = s2 := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2]
            simp only [concC, concK, stepFn]
            have := applyStrictOp_conc hI σ happ
            simp only [List.map_reverse, List.map_cons] at this
            rw [this]
            rfl
      case andK r env k' =>
        simp only [stepFn'] at h
        obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
        simp only [concC, concK, stepFn]
        rw [show valueAsBool (concV I v) = .ok b from asBoolAt_conc hI hb]
        simp only [ok_bind]
        cases b with
        | true =>
            rw [if_pos rfl] at h2
            have hov : c₁ = .evalE r env (.boolK k') ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_pos rfl]
            rfl
        | false =>
            rw [if_neg (by decide)] at h2
            have hov : c₁ = .retV (.bool (D.litB false)) k' ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_neg (by decide)]
            simp [concC, concK, hI.litB, pure, Except.pure]
      case orK r env k' =>
        simp only [stepFn'] at h
        obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
        simp only [concC, concK, stepFn]
        rw [show valueAsBool (concV I v) = .ok b from asBoolAt_conc hI hb]
        simp only [ok_bind]
        cases b with
        | true =>
            rw [if_pos rfl] at h2
            have hov : c₁ = .retV (.bool (D.litB true)) k' ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_pos rfl]
            simp [concC, concK, hI.litB, pure, Except.pure]
        | false =>
            rw [if_neg (by decide)] at h2
            have hov : c₁ = .evalE r env (.boolK k') ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_neg (by decide)]
            rfl
      case boolK k' =>
        simp only [stepFn'] at h
        obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
        have hov : c₁ = .retV (.bool (D.litB b)) k' ∧ s₁ = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h2
        rw [hov.1, hov.2]
        simp only [concC, concK, stepFn]
        rw [show valueAsBool (concV I v) = .ok b from asBoolAt_conc hI hb]
        simp [concC, concK, hI.litB, pure, Except.pure, ok_bind]
      case ifK t e env k' =>
        simp only [stepFn'] at h
        obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
        simp only [concC, concK, stepFn]
        rw [show valueAsBool (concV I v) = .ok b from asBoolAt_conc hI hb]
        simp only [ok_bind]
        cases b with
        | true =>
            rw [if_pos rfl] at h2
            have hov : c₁ = .exec t env k' ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_pos rfl]
            rfl
        | false =>
            rw [if_neg (by decide)] at h2
            have hov : c₁ = .exec e env k' ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_neg (by decide)]
            rfl
      case whileK cnd b env k' =>
        simp only [stepFn'] at h
        obtain ⟨bb, hb, h2⟩ := bind_eq_ok.mp h
        simp only [concC, concK, stepFn]
        rw [show valueAsBool (concV I v) = .ok bb from asBoolAt_conc hI hb]
        simp only [ok_bind]
        cases bb with
        | true =>
            rw [if_pos rfl] at h2
            have hov : c₁ = .exec b env (.loop cnd b env k') ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_pos rfl]
            rfl
        | false =>
            rw [if_neg (by decide)] at h2
            have hov : c₁ = .next k' ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2, if_neg (by decide)]
            rfl
      case callArgsK fid plans vals pending env k' =>
        cases pending with
        | cons a rest =>
            cases h
            simp [stepFn, concC, concK, pure, Except.pure]
        | nil => simp [stepFn', quit] at h
      case stmtOpK op nt done pending env k' =>
        cases pending with
        | cons e rest =>
            simp only [stepFn'] at h
            by_cases hnt : done.length < nt
            · rw [if_pos hnt] at h
              obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
              have hov : c₁ = .evalE e env
                  (.stmtOpK op nt (v :: done) rest env k') ∧ s₁ = s := by
                simpa [pure, Except.pure, eq_comm, and_comm] using h2
              rw [hov.1, hov.2]
              simp only [concC, concK, stepFn]
              rw [if_pos (by simpa using hnt)]
              rw [show valueAsLoc (concV I v) = .ok loc
                    from asLoc_conc hloc]
              rfl
            · rw [if_neg hnt] at h
              cases h
              simp only [concC, concK, stepFn]
              rw [if_neg (by simpa using hnt)]
              rfl
        | nil =>
            simp only [stepFn'] at h
            obtain ⟨s2, happ, h2⟩ := bind_eq_ok.mp h
            have hov : c₁ = .next k' ∧ s₁ = s2 := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2]
            simp only [concC, concK, stepFn]
            have := applyStmtOp_conc hI σ happ nt ch
            simp only [List.map_reverse, List.map_cons] at this
            rw [this]
            rfl
      case callValCalleeK plans args env k' =>
        cases args with
        | nil => cases v <;> simp [stepFn', quit] at h
        | cons a rest =>
            simp only [stepFn'] at h
            obtain ⟨ok, hok, h2⟩ := bind_eq_ok.mp h
            by_cases hb : ok = true
            · rw [if_pos hb] at h2
              have hov : c₁ = .evalE a env
                  (.callValArgsK v plans [] rest env k') ∧ s₁ = s := by
                simpa [pure, Except.pure, eq_comm, and_comm] using h2
              rw [hov.1, hov.2]
              simp only [concC, concK, stepFn]
              rw [show deferrableCallee (concV I v) = ok
                    from deferrable_conc hok, hb, if_pos rfl]
              rfl
            · rw [if_neg hb] at h2
              cases h2
      case callValArgsK cv plans vals pending env k' =>
        cases pending with
        | cons a rest =>
            cases h
            simp [stepFn, concC, concK, pure, Except.pure]
        | nil => cases cv <;> simp [stepFn', quit] at h
      case deferCalleeK args env k' =>
        simp only [stepFn'] at h
        obtain ⟨ok, hok, h2⟩ := bind_eq_ok.mp h
        by_cases hb : ok = true
        · rw [if_pos hb] at h2
          simp only [concC, concK, stepFn]
          rw [show deferrableCallee (concV I v) = ok
                from deferrable_conc hok, hb, if_pos rfl]
          cases args with
          | cons a rest =>
              have hov : c₁ = .evalE a env
                  (.deferArgsK v [] rest env k') ∧ s₁ = s := by
                simpa [pure, Except.pure, eq_comm, and_comm] using h2
              rw [hov.1, hov.2]
              rfl
          | nil =>
              rcases hpd : pushDefer' (v, ([] : List (Value D))) k'
                  with _ | k2 <;> rw [hpd] at h2
              · cases h2
              · have hov : c₁ = .next k2 ∧ s₁ = s := by
                  simpa [pure, Except.pure, eq_comm, and_comm] using h2
                rw [hov.1, hov.2]
                have := pushDefer_conc (I := I) v [] k'
                simp only [List.map_nil] at this
                rw [this, hpd]
                rfl
        · rw [if_neg hb] at h2
          cases h2
      case deferArgsK cv vals pending env k' =>
        cases pending with
        | cons a rest =>
            cases h
            simp [stepFn, concC, concK, pure, Except.pure]
        | nil =>
            simp only [stepFn'] at h
            rcases hpd : pushDefer' (cv, vals ++ [v]) k'
                with _ | k2 <;> rw [hpd] at h
            · cases h
            · have hov : c₁ = .next k2 ∧ s₁ = s := by
                simpa [pure, Except.pure, eq_comm, and_comm] using h
              rw [hov.1, hov.2]
              simp only [concC, concK, stepFn]
              have := pushDefer_conc (I := I) cv (vals ++ [v]) k'
              simp only [List.map_append, List.map_cons, List.map_nil]
                at this
              rw [this, hpd]
              rfl
      case mapRangeK keyVar valVar keyTy valTy body env k' =>
        simp only [stepFn'] at h
        obtain ⟨entries, hentries, h2⟩ := bind_eq_ok.mp h
        have hov : c₁ = .next (.mapIterK keyVar valVar keyTy valTy body
            entries env k') ∧ s₁ = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h2
        rw [hov.1, hov.2]
        simp only [concC, concK, stepFn]
        rw [show mapRangeSnapshotEntries (concS I σ s) keyTy valTy
              (concV I v) = .ok (concEntries I entries)
            from mapRangeSnapshotEntries_conc hI σ hentries]
        simp only [ok_bind]
        rfl
      case panicArgK k' => simp [stepFn', quit] at h
      case panicResumeK chain k' => simp [stepFn', quit] at h
      case chanStK a b c d e => simp [stepFn', quit] at h
      case selectOpsK a b c d e f => simp [stepFn', quit] at h
      case goCalleeK a b c => simp [stepFn', quit] at h
      case goArgsK a b c d e => simp [stepFn', quit] at h
      case syncStK a b c d e => simp [stepFn', quit] at h
      case tgtOpK sh ops pending refs targets rop rhs vals body env k' =>
        cases pending with
        | cons e rest => cases h; rfl
        | nil =>
            simp only [stepFn'] at h
            rcases hcomp : completeTargetRef' sh (v :: ops).reverse
                with _ | r <;> rw [hcomp] at h
            · cases h
            · have hcompm := completeRef_conc I sh (v :: ops).reverse
              rw [hcomp] at hcompm
              simp only [List.map_reverse, List.map_cons] at hcompm
              cases targets with
              | cons tp rest =>
                  obtain ⟨sh', ops'⟩ := tp
                  cases ops' with
                  | nil => cases h
                  | cons e' rest' =>
                      cases h
                      simp only [concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map, pure, Except.pure]
              | nil =>
                  cases rhs with
                  | cons e' rest' =>
                      cases h
                      simp only [concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map, pure, Except.pure]
                  | nil =>
                      cases h
                      simp only [concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map, pure, Except.pure]
      case rhsK rop refs done pending body env k' =>
        cases pending with
        | cons e rest => cases h; rfl
        | nil =>
            simp only [stepFn'] at h
            obtain ⟨vals2, happ, h2⟩ := bind_eq_ok.mp h
            have hov : c₁ = .next (.storeK refs vals2 body env k')
                ∧ s₁ = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h2
            rw [hov.1, hov.2]
            simp only [concC, concK, stepFn]
            have := applyRhsOp_conc hI σ happ
            simp only [List.map_reverse, List.map_cons] at this
            rw [this]
            rfl
      all_goals simp [stepFn', quit] at h
  | next k =>
      cases k
      case stop => simp [stepFn', quit] at h
      case seq rest env k' =>
        cases rest with
        | nil => cases h; rfl
        | cons t ts => cases h; rfl
      case loop c b env k' => cases h; rfl
      case frame targets tenv results defers k' w =>
        cases defers with
        | cons d ds =>
            obtain ⟨cv, cargs⟩ := d
            cases cv <;> simp [stepFn', quit] at h
        | nil =>
            cases targets with
            | nil =>
                cases results with
                | nil => cases h; rfl
                | cons rl rls => simp [stepFn', quit] at h
            | cons tp rest =>
                obtain ⟨sh, ops⟩ := tp
                cases ops with
                | nil => simp [stepFn', quit] at h
                | cons e ops' =>
                    simp only [stepFn'] at h
                    obtain ⟨vs, hvs, h2⟩ := bind_eq_ok.mp h
                    have hov : c₁ = .evalE e tenv (.tgtOpK sh [] ops' []
                        rest .vals [] vs (.seqn #[]) tenv k')
                        ∧ s₁ = s := by
                      simpa [pure, Except.pure, eq_comm, and_comm]
                        using h2
                    rw [hov.1, hov.2]
                    simp only [concC, concK, stepFn]
                    refine bind_eq_ok.mpr
                      ⟨vs.map (concV I), loadMany_conc σ hvs, rfl⟩
      case panicResumeK chain k' => simp [stepFn', quit] at h
      case breakableK k' => cases h; rfl
      case labelK name k' => cases h; rfl
      case mapIterK keyVar valVar keyTy valTy body remaining env k' =>
        simp only [stepFn'] at h
        by_cases hemp : remaining.isEmpty = true
        · rw [if_pos hemp] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [if_pos (by simpa [Array.isEmpty_iff] using hemp)]
          rfl
        · rw [if_neg hemp] at h
          cases h
      case storeK refs vals body env k' =>
        cases refs with
        | nil =>
            cases vals with
            | nil => cases h; rfl
            | cons a b => simp [stepFn', quit] at h
        | cons r rs =>
            cases vals with
            | nil => simp [stepFn', quit] at h
            | cons val vrest =>
                simp only [stepFn'] at h
                obtain ⟨s2, hstore, h2⟩ := bind_eq_ok.mp h
                have hov : c₁ = .next (.storeK rs vrest body env k')
                    ∧ s₁ = s2 := by
                  simpa [pure, Except.pure, eq_comm, and_comm] using h2
                rw [hov.1, hov.2]
                simp only [concC, concK, stepFn, List.map_cons]
                rw [storeTarget_conc hI σ hstore]
                rfl
      all_goals simp [stepFn', quit] at h
  | breaking k =>
      cases k <;>
        first
          | (simp [stepFn', quit] at h; done)
          | (cases h; rfl)
  | continuing k =>
      cases k <;>
        first
          | (simp [stepFn', quit] at h; done)
          | (cases h; rfl)
  | returning k =>
      cases k
      case seq rest env k' => cases h; rfl
      case breakableK k' => cases h; rfl
      case labelK name k' => cases h; rfl
      case loop c b env k' => cases h; rfl
      case mapIterK a b c d e f g k' => cases h; rfl
      case frame targets tenv results defers k' w =>
        cases defers with
        | cons d ds =>
            obtain ⟨cv, cargs⟩ := d
            cases cv <;> simp [stepFn', quit] at h
        | nil =>
            cases targets with
            | nil =>
                cases results with
                | nil => cases h; rfl
                | cons rl rls => simp [stepFn', quit] at h
            | cons tp rest =>
                obtain ⟨sh, ops⟩ := tp
                cases ops with
                | nil => simp [stepFn', quit] at h
                | cons e ops' =>
                    simp only [stepFn'] at h
                    obtain ⟨vs, hvs, h2⟩ := bind_eq_ok.mp h
                    have hov : c₁ = .evalE e tenv (.tgtOpK sh [] ops' []
                        rest .vals [] vs (.seqn #[]) tenv k')
                        ∧ s₁ = s := by
                      simpa [pure, Except.pure, eq_comm, and_comm]
                        using h2
                    rw [hov.1, hov.2]
                    simp only [concC, concK, stepFn]
                    refine bind_eq_ok.mpr
                      ⟨vs.map (concV I), loadMany_conc σ hvs, rfl⟩
      all_goals simp [stepFn', quit] at h
  | breakingTo L k =>
      cases k
      case seq rest env k' => cases h; rfl
      case loop c b env k' => cases h; rfl
      case breakableK k' => cases h; rfl
      case mapIterK a b c d e f g k' => cases h; rfl
      case labelK name k' =>
        simp only [stepFn'] at h
        by_cases hn : name = L
        · rw [if_pos hn] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [if_pos hn]
          rfl
        · rw [if_neg hn] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [if_neg hn]
          rfl
      all_goals simp [stepFn', quit] at h
  | continuingTo L k =>
      cases k
      case seq rest env k' => cases h; rfl
      case breakableK k' => cases h; rfl
      case labelK name k' =>
        simp only [stepFn'] at h
        by_cases hn : name = L
        · rw [if_pos hn] at h
          cases h
        · rw [if_neg hn] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [if_neg hn]
          rfl
      case loop c b env k' =>
        simp only [stepFn'] at h
        by_cases hl : contHeadLabel' k' = some L
        · rw [if_pos hl] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [contHeadLabel_conc, if_pos hl]
          rfl
        · rw [if_neg hl] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [contHeadLabel_conc, if_neg hl]
          rfl
      case mapIterK keyVar valVar keyTy valTy body remaining env k' =>
        simp only [stepFn'] at h
        by_cases hl : contHeadLabel' k' = some L
        · rw [if_pos hl] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [contHeadLabel_conc, if_pos hl]
          rfl
        · rw [if_neg hl] at h
          cases h
          simp only [concC, concK, stepFn]
          rw [contHeadLabel_conc, if_neg hl]
          rfl
      all_goals simp [stepFn', quit] at h

/-! ## The two gated instances -/

/-- **THE DRIFT THEOREM** (charter `:80-83`, the ruled OQ3
embedding-mediated spelling): at the concrete interpretation the
mirror agrees with `stepFn` on every successful step — mirror drift on
ANY computing arm fails this theorem, hence the default build. The
concrete `Sound` pack closes definitionally (`cInterp_sound`), so this
instance carries no semantic slack: the walk IS the comparison. -/
theorem stepFn'_concrete_agrees (σ : ExecState) (ch : Choices)
    {s : State cdom} {c : Config cdom} {c₁ : Config cdom}
    {s₁ : State cdom} (h : stepFn' s c = .ok (c₁, s₁)) :
    stepFn (concS cInterp σ s) (concC cInterp c) ch
      = .ok (concC cInterp c₁, concS cInterp σ s₁, ch) :=
  stepFn'_conc cInterp_sound σ ch h

/-- The symbolic instance: one successful EVALUATOR step transports to
the machine at every valuation — the refinement theorem's per-step
half (design §6.2 layer 3 at `symInterp`). -/
theorem stepFnS_sound (ρ : Valuation) (σ : ExecState) (ch : Choices)
    {S : SymState} {C C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnS S C = .ok (C₁, S₁)) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) :=
  stepFn'_conc (symInterp_sound ρ) σ ch h

end GoLean.Sym
