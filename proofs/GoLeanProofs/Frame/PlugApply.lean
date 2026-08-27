import GoLeanProofs.Frame.PlugOps

/-!
# The plug rule, part 3: builder commutations (design note §7)

The channel/sync/select applies and the receive-target entry BUILD
configurations that embed the caller `env`/continuation `k` without
ever inspecting them, so `plugC` commutes with each unconditionally —
no barrier hypothesis, no premises. (Contrast the §7 premise-carrying
helpers in `PlugOps`: recover and the delete-prunes are the two
machine features that DO inspect the context through a call
boundary.)

Proof style: enumerate the same case tree as the definition (the
state operations are IDENTICAL on both sides — same σ — so one
`cases hX :` per operation serves both), close every leaf with the
one uniform simp battery (`plg`).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {env' : LocalEnv} {k' : Cont}

/-- The pair-level plug map on apply results. -/
abbrev plugPair (env' : LocalEnv) (k' : Cont) :
    Config × ExecState → Config × ExecState :=
  fun r => (plugC env' k' r.1, r.2)

theorem enterRecvTargets_plug (s : ExecState) (targets : List Assignee)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k : Cont) :
    enterRecvTargets s targets vals body env (plugK env' k' k)
      = (enterRecvTargets s targets vals body env k).map (plugPair env' k') := by
  unfold enterRecvTargets
  repeat' split
  all_goals first | rfl | (subst_vars; simp_all [plugC, plugK, Except.map])

/-- The one leaf closer for the builder walks. -/
local macro "plg" : tactic =>
  `(tactic| first
      | rfl
      | simp_all [plugC, plugK, enterRecvTargets_plug, Except.map, bind,
          Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw])

theorem applyChanOp_plug (s : ExecState) (op : ChanStOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) :
    applyChanOp s op vs env (plugK env' k' k)
      = (applyChanOp s op vs env k).map (plugPair env' k') := by
  cases op with
  | send elem =>
      match vs with
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ :: _ => rfl
      | [chv, vv] =>
          simp only [applyChanOp]
          cases hch : valueAsChan chv
          case error => plg
          case ok ch =>
            cases hnv : normalizeValueForTy s elem vv
            case error => plg
            case ok v2 =>
              cases hcb : ch.base
              case none => plg
              case some loc =>
                cases hcc : chanCell s loc
                case error => plg
                case ok trip =>
                  obtain ⟨buf, cap, closed⟩ := trip
                  by_cases hcl : closed = true
                  · plg
                  · simp only [hch, hnv, hcb, hcc, bind, Except.bind,
                      if_neg hcl]
                    split
                    · cases hst : storeLoc s loc
                          (.chanData (buf.push v2) cap closed) <;> plg
                    · plg
  | close =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [chv] =>
          simp only [applyChanOp]
          cases hch : valueAsChan chv
          case error => plg
          case ok ch =>
            cases hcb : ch.base
            case none => plg
            case some loc =>
              cases hcc : chanCell s loc
              case error => plg
              case ok trip =>
                obtain ⟨buf, cap, closed⟩ := trip
                by_cases hcl : closed = true
                · plg
                · cases hst : storeLoc s loc (.chanData buf cap true) <;> plg
  | recv targets elem =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [chv] =>
          simp only [applyChanOp]
          cases hch : valueAsChan chv
          case error => plg
          case ok ch =>
            cases hcb : ch.base
            case none => plg
            case some loc =>
              cases hcc : chanCell s loc
              case error => plg
              case ok trip =>
                obtain ⟨buf, cap, closed⟩ := trip
                cases hv0 : buf[0]?
                case some v =>
                  cases hst : storeLoc s loc
                      (.chanData (buf.eraseIdx! 0) cap closed)
                  case error => plg
                  case ok s1 =>
                    cases targets with
                    | nil => plg
                    | cons a ts =>
                        cases henter : enterRecvTargets s1 (a :: ts)
                            (recvStores v true (a :: ts).length)
                            (.seqn #[]) env k <;> plg
                case none =>
                  by_cases hcl : closed = true
                  · cases hdv : defaultValue s elem
                    case error => plg
                    case ok zero =>
                      cases targets with
                      | nil => plg
                      | cons a ts =>
                          cases henter : enterRecvTargets s (a :: ts)
                              (recvStores zero false (a :: ts).length)
                              (.seqn #[]) env k <;> plg
                  · plg

theorem applySyncOp_plug (s : ExecState) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) :
    applySyncOp s op vs env (plugK env' k' k)
      = (applySyncOp s op vs env k).map (plugPair env' k') := by
  have hloc : ∀ (av : GoValue)
      (f g : Loc → Except GoError (Config × ExecState)),
      (∀ loc, f loc = (g loc).map (plugPair env' k')) →
      ((valueAsLoc av >>= f) = (valueAsLoc av >>= g).map (plugPair env' k')) := by
    intro av f g h
    cases hv : valueAsLoc av with
    | error e => simp [bind, Except.bind, Except.map]
    | ok loc => simp [bind, Except.bind, h loc]
  cases op with
  | lock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case mutex locked =>
              by_cases hl : locked = true
              · plg
              · cases hst : storeLoc s loc (.syncData (.mutex true)) <;> plg
            all_goals plg
  | unlock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case mutex locked =>
              by_cases hl : locked = true
              · cases hst : storeLoc s loc (.syncData (.mutex false)) <;> plg
              · plg
            all_goals plg
  | rlock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case rwmutex writer readers pendingW =>
              by_cases hg : (writer || pendingW > 0) = true
              · plg
              · cases hst : storeLoc s loc
                    (.syncData (.rwmutex writer (readers + 1) pendingW)) <;> plg
            all_goals plg
  | runlock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case rwmutex writer readers pendingW =>
              cases readers with
              | zero => plg
              | succ r =>
                  cases hst : storeLoc s loc
                      (.syncData (.rwmutex writer r pendingW)) <;> plg
            all_goals plg
  | wlock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case rwmutex writer readers pendingW =>
              simp only [hsc, bind, Except.bind]
              split
              · cases hst : storeLoc s loc
                    (.syncData (.rwmutex true 0 pendingW)) <;> plg
              · cases hst : storeLoc s loc
                    (.syncData (.rwmutex writer readers (pendingW + 1))) <;> plg
            all_goals plg
  | wunlock =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case rwmutex writer readers pendingW =>
              by_cases hw : writer = true
              · cases hst : storeLoc s loc
                    (.syncData (.rwmutex false readers pendingW)) <;> plg
              · plg
            all_goals plg
  | wgAdd =>
      match vs with
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ :: _ => rfl
      | [av, dv] =>
          simp only [applySyncOp]
          cases hv : valueAsLoc av
          case error => plg
          case ok loc =>
            cases hd : valueAsInt dv
            case error => plg
            case ok delta =>
              cases hsc : syncCell s loc
              case error => plg
              case ok cell =>
                cases cell
                case waitGroup counter waiters =>
                  cases hst : storeLoc s loc (.syncData (.waitGroup
                      ((counter + delta + 2147483648).emod 4294967296
                        - 2147483648)
                      (if ((counter + delta + 2147483648).emod 4294967296
                            - 2147483648) == 0 && waiters > 0 then 0
                        else waiters)))
                  case error => plg
                  case ok s2 =>
                    simp only [hv, hd, hsc, hst, bind, Except.bind]
                    split <;> plg
                all_goals plg
  | wgWait =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case waitGroup counter waiters =>
              by_cases hz : (counter == 0) = true
              · plg
              · cases hst : storeLoc s loc
                    (.syncData (.waitGroup counter (waiters + 1))) <;> plg
            all_goals plg
  | onceBegin targets =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case once started don =>
              by_cases hs1 : (!started) = true
              · cases hst : storeLoc s loc (.syncData (.once true false))
                case error => plg
                case ok s2 =>
                  cases henter : enterRecvTargets s2 targets [.bool true]
                      (.seqn #[]) env k <;> plg
              · by_cases hd2 : don = true
                · cases henter : enterRecvTargets s targets [.bool false]
                      (.seqn #[]) env k <;> plg
                · plg
            all_goals plg
  | onceComplete =>
      match vs with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [av] =>
          simp only [applySyncOp]
          refine hloc av _ _ (fun loc => ?_)
          cases hsc : syncCell s loc
          case error => plg
          case ok cell =>
            cases cell
            case once started don =>
              by_cases hs1 : started = true
              · cases hst : storeLoc s loc (.syncData (.once true true)) <;> plg
              · plg
            all_goals plg

theorem commitClause_plug (s : ExecState) (env : LocalEnv) (k : Cont)
    (cl : EvClause) :
    commitClause s env (plugK env' k' k) cl
      = (commitClause s env k cl).map (plugPair env' k') := by
  cases cl with
  | sendEv chv vv elem body =>
      simp only [commitClause]
      cases hch : valueAsChan chv
      case error => plg
      case ok ch =>
        cases hcb : ch.base
        case none => plg
        case some loc =>
          cases hcc : chanCell s loc
          case error => plg
          case ok trip =>
            obtain ⟨buf, cap, closed⟩ := trip
            by_cases hcl2 : closed = true
            · plg
            · simp only [hch, hcb, hcc, bind, Except.bind, if_neg hcl2]
              split
              · cases hnv : normalizeValueForTy s elem vv
                case error => plg
                case ok v2 =>
                  cases hst : storeLoc s loc
                      (.chanData (buf.push v2) cap closed) <;> plg
              · plg
  | recvEv chv targets elem body =>
      simp only [commitClause]
      cases hch : valueAsChan chv
      case error => plg
      case ok ch =>
        cases hcb : ch.base
        case none => plg
        case some loc =>
          cases hcc : chanCell s loc
          case error => plg
          case ok trip =>
            obtain ⟨buf, cap, closed⟩ := trip
            cases hv0 : buf[0]?
            case some v =>
              cases hst : storeLoc s loc
                  (.chanData (buf.eraseIdx! 0) cap closed)
              case error => plg
              case ok s1 =>
                cases targets with
                | nil => plg
                | cons a ts =>
                    cases henter : enterRecvTargets s1 (a :: ts)
                        (recvStores v true (a :: ts).length) body env k <;> plg
            case none =>
              by_cases hcl2 : closed = true
              · cases hdv : defaultValue s elem
                case error => plg
                case ok zero =>
                  cases targets with
                  | nil => plg
                  | cons a ts =>
                      cases henter : enterRecvTargets s (a :: ts)
                          (recvStores zero false (a :: ts).length) body env k <;>
                        plg
              · plg

/-! ## The select layer -/

/-- The outcome-level plug map. -/
def plugOutcome (env' : LocalEnv) (k' : Cont) : SelectOutcome → SelectOutcome
  | .done c σ cl? => .done (plugC env' k' c) σ cl?
  | .picks commits =>
      .picks (commits.map (fun p => (p.1,
        match p.2 with
        | .inl r => .inl (plugPair env' k' r)
        | .inr m => .inr m)))

private theorem mapM_commit_plug (s : ExecState) (env : LocalEnv) (k : Cont) :
    ∀ (ready : List EvClause),
      (ready.mapM (fun cl =>
        Machine.applySelectCore.match_3
          (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
          (commitClause s env (plugK env' k' k) cl)
          (fun r => Except.ok (cl, Sum.inl r))
          (fun msg => Except.ok (cl, Sum.inr msg))
          (fun e => Except.error e)))
      = (ready.mapM (fun cl =>
        Machine.applySelectCore.match_3
          (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
          (commitClause s env k cl)
          (fun r => Except.ok (cl, Sum.inl r))
          (fun msg => Except.ok (cl, Sum.inr msg))
          (fun e => Except.error e))).map
        (List.map (fun p => (p.1,
          match p.2 with
          | .inl r => .inl (plugPair env' k' r)
          | .inr m => .inr m)))
  | [] => rfl
  | cl :: rest => by
      simp only [List.mapM_cons]
      rw [commitClause_plug, mapM_commit_plug s env k rest]
      cases hcc : commitClause s env k cl with
      | error e =>
          cases e <;>
            cases hrest : rest.mapM (fun cl =>
              Machine.applySelectCore.match_3
                (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
                (commitClause s env k cl)
                (fun r => Except.ok (cl, Sum.inl r))
                (fun msg => Except.ok (cl, Sum.inr msg))
                (fun e => Except.error e)) <;>
              simp_all [Except.map, bind, Except.bind, pure, Except.pure]
      | ok r =>
          cases hrest : rest.mapM (fun cl =>
            Machine.applySelectCore.match_3
              (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
              (commitClause s env k cl)
              (fun r => Except.ok (cl, Sum.inl r))
              (fun msg => Except.ok (cl, Sum.inr msg))
              (fun e => Except.error e)) <;>
            simp_all [Except.map, bind, Except.bind, pure, Except.pure]

theorem applySelectCore_plug (s : ExecState)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    applySelectCore s clauses default? vs env (plugK env' k' k)
      = (applySelectCore s clauses default? vs env k).map
          (plugOutcome env' k') := by
  unfold applySelectCore
  cases hev : evalClauses clauses vs with
  | error e => simp [hev, bind, Except.bind, Except.map]
  | ok evs =>
      simp only [hev, bind, Except.bind]
      cases hrdy : readyClauses s evs with
      | error e => simp [Except.map]
      | ok ready =>
          match ready with
          | [] =>
              simp only [hrdy]
              cases default? <;>
                simp [plugOutcome, plugC, Except.map, pure, Except.pure]
          | [c] =>
              simp only [hrdy, commitClause_plug]
              cases hcc : commitClause s env k c <;>
                simp_all [Except.map, bind, Except.bind, pure, Except.pure,
                  plugOutcome]
          | c₁ :: c₂ :: rest =>
              simp only [hrdy]
              rw [mapM_commit_plug]
              cases hm : ((c₁ :: c₂ :: rest).mapM (fun cl =>
                Machine.applySelectCore.match_3
                  (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
                  (commitClause s env k cl)
                  (fun r => Except.ok (cl, Sum.inl r))
                  (fun msg => Except.ok (cl, Sum.inr msg))
                  (fun e => Except.error e))) <;>
                simp_all [Except.map, bind, Except.bind, pure, Except.pure,
                  plugOutcome]

theorem applySelect_plug (s : ExecState)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) (ch : Choices) :
    applySelect s clauses default? vs env (plugK env' k' k) ch
      = (applySelect s clauses default? vs env k ch).map
          (fun r => (plugC env' k' r.1, r.2.1, r.2.2.1, r.2.2.2)) := by
  unfold applySelect
  rw [applySelectCore_plug]
  cases hcore : applySelectCore s clauses default? vs env k with
  | error e => simp [Except.map, bind, Except.bind]
  | ok outcome =>
      cases outcome with
      | done c σ cl? =>
          simp [Except.map, bind, Except.bind, pure, Except.pure, plugOutcome]
      | picks commits =>
          simp only [Except.map, bind, Except.bind, pure, Except.pure,
            plugOutcome]
          cases hpair : Choices.consumeAt .l2Entry commits.length ch with
          | mk idx ch₂ =>
              simp only [List.length_map, hpair]
              cases hidx : commits[idx]? with
              | none =>
                  simp_all [List.getElem?_map, List.length_map, throw,
                    throwThe, MonadExceptOf.throw]
              | some p =>
                  obtain ⟨cl, r⟩ := p
                  cases r with
                  | inl pr =>
                      simp_all [List.getElem?_map, List.length_map, plugC]
                  | inr msg =>
                      simp_all [List.getElem?_map, List.length_map, plugC]

/-! ## Barrier preservation through the builders (the walk's
classification for the opaque-result apply arms) -/

theorem enterRecvTargets_bar {s : ExecState} {targets : List Assignee}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState}
    (h : enterRecvTargets s targets vals body env k = .ok (c', s'))
    (hb : hasBarrierK k = true) : hasBarrierC c' = true := by
  unfold enterRecvTargets at h
  repeat' split at h
  all_goals first
    | exact (Except.noConfusion h)
    | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp_all [hasBarrierC, hasBarrierK]
       done)
    | (rename_i heq
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp only [hasBarrierC]
       exact enterRecvTargets_bar' heq hb)
    | simp_all [hasBarrierC, hasBarrierK]

theorem enterRecvTargets_bar' {s : ExecState} {targets : List Assignee}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    {pr : Config × ExecState}
    (h : enterRecvTargets s targets vals body env k = .ok pr)
    (hb : hasBarrierK k = true) : hasBarrierC pr.1 = true := by
  obtain ⟨c', s'⟩ := pr
  exact enterRecvTargets_bar h hb

theorem applyChanOp_bar {s : ExecState} {op : ChanStOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {c' : Config} {s' : ExecState}
    (h : applyChanOp s op vs env k = .ok (c', s'))
    (hb : hasBarrierK k = true) : hasBarrierC c' = true := by
  unfold applyChanOp at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact (Except.noConfusion h)
    | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp_all [hasBarrierC, hasBarrierK]
       done)
    | (rename_i heq
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp only [hasBarrierC]
       exact enterRecvTargets_bar' heq hb)
    | simp_all [hasBarrierC, hasBarrierK]

theorem applySyncOp_bar {s : ExecState} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {c' : Config} {s' : ExecState}
    (h : applySyncOp s op vs env k = .ok (c', s'))
    (hb : hasBarrierK k = true) : hasBarrierC c' = true := by
  unfold applySyncOp at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact (Except.noConfusion h)
    | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp_all [hasBarrierC, hasBarrierK]
       done)
    | (rename_i heq
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp only [hasBarrierC]
       exact enterRecvTargets_bar' heq hb)
    | simp_all [hasBarrierC, hasBarrierK]

theorem commitClause_bar {s : ExecState} {env : LocalEnv} {k : Cont}
    {cl : EvClause} {c' : Config} {s' : ExecState}
    (h : commitClause s env k cl = .ok (c', s'))
    (hb : hasBarrierK k = true) : hasBarrierC c' = true := by
  unfold commitClause at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact (Except.noConfusion h)
    | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp_all [hasBarrierC, hasBarrierK]
       done)
    | (rename_i heq
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       rw [← h1]
       simp only [hasBarrierC]
       exact enterRecvTargets_bar' heq hb)
    | simp_all [hasBarrierC, hasBarrierK]

private theorem mapM_ok_forall {α β : Type} {F : α → Except GoError β}
    {P : β → Prop} (hF : ∀ a b, F a = .ok b → P b) :
    ∀ {l : List α} {out : List β}, l.mapM F = .ok out → ∀ b ∈ out, P b := by
  intro l
  induction l with
  | nil =>
      intro out h b hb
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      cases hb
  | cons a as ih =>
      intro out h b hb
      simp only [List.mapM_cons, bind, Except.bind] at h
      cases hA : F a <;> rw [hA] at h
      · exact absurd h (by simp)
      · cases hAs : as.mapM F <;> rw [hAs] at h
        · exact absurd h (by simp)
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hb with hb | hb
          · subst hb; exact hF a _ hA
          · exact ih hAs b hb

private theorem mapM_commit_bar {s : ExecState} {env : LocalEnv} {k : Cont}
    (hb : hasBarrierK k = true)
    {ready : List EvClause}
    {commits : List (EvClause × (Config × ExecState ⊕ String))}
    (h : (ready.mapM (fun cl =>
        Machine.applySelectCore.match_3
          (fun _ => Except GoError (EvClause × (Config × ExecState ⊕ String)))
          (commitClause s env k cl)
          (fun r => Except.ok (cl, Sum.inl r))
          (fun msg => Except.ok (cl, Sum.inr msg))
          (fun e => Except.error e))) = .ok commits) :
    ∀ p ∈ commits, ∀ c₂ s₂, p.2 = .inl (c₂, s₂) → hasBarrierC c₂ = true := by
  refine mapM_ok_forall ?_ h
  intro a b hab
  split at hab
  · rename_i r hcc
    injection hab with hab
    subst hab
    intro c₂ s₂ he2
    simp only [Sum.inl.injEq] at he2
    obtain ⟨r1, r2⟩ := r
    simp only [Prod.mk.injEq] at he2
    rw [← he2.1]
    exact commitClause_bar hcc hb
  · rename_i msg hcc
    injection hab with hab
    subst hab
    intro c₂ s₂ he2
    simp at he2
  · exact absurd hab (by simp)

theorem commitClause_bar' {s : ExecState} {env : LocalEnv} {k : Cont}
    {cl : EvClause} {pr : Config × ExecState}
    (h : commitClause s env k cl = .ok pr)
    (hb : hasBarrierK k = true) : hasBarrierC pr.1 = true := by
  obtain ⟨c', s'⟩ := pr
  exact commitClause_bar h hb

theorem applySelect_bar {s : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    {c' : Config} {s' : ExecState} {ch₂ : Choices} {cl? : Option EvClause}
    (h : applySelect s clauses default? vs env k ch = .ok (c', s', ch₂, cl?))
    (hb : hasBarrierK k = true) : hasBarrierC c' = true := by
  unfold applySelect at h
  cases hcore : applySelectCore s clauses default? vs env k <;>
    rw [hcore] at h
  case error e => exact absurd h (by simp [bind, Except.bind])
  case ok outcome =>
      cases outcome with
      | done c σ cl₂ =>
          have hdone : hasBarrierC c = true := by
            unfold applySelectCore at hcore
            simp only [bind, Except.bind, pure, Except.pure] at hcore
            repeat' split at hcore
            all_goals first
              | exact (Except.noConfusion hcore)
              | (simp only [Except.ok.injEq, SelectOutcome.done.injEq] at hcore
                 obtain ⟨h1, h2, h3⟩ := hcore
                 rw [← h1]
                 simp_all [hasBarrierC, hasBarrierK]
                 done)
              | (rename_i hcc
                 simp only [Except.ok.injEq, SelectOutcome.done.injEq] at hcore
                 obtain ⟨h1, h2, h3⟩ := hcore
                 rw [← h1]
                 exact commitClause_bar' hcc hb)
              | simp at hcore
          simp only [bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, -⟩ := h
          rw [← h1]
          exact hdone
      | picks commits =>
          have hentries : ∀ p ∈ commits, ∀ c₂ s₂, p.2 = .inl (c₂, s₂) →
              hasBarrierC c₂ = true := by
            unfold applySelectCore at hcore
            simp only [bind, Except.bind, pure, Except.pure] at hcore
            repeat' split at hcore
            all_goals first
              | exact (Except.noConfusion hcore)
              | (rename_i hmm
                 simp only [Except.ok.injEq, SelectOutcome.picks.injEq] at hcore
                 subst hcore
                 exact mapM_commit_bar hb hmm)
              | simp at hcore
          simp only [bind, Except.bind] at h
          cases hpair : Choices.consumeAt .l2Entry commits.length ch with
          | mk idx ch₃ =>
              rw [hpair] at h
              cases hidx : commits[idx]? <;> rw [hidx] at h
              · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
              · rename_i p
                obtain ⟨cl, r⟩ := p
                cases r with
                | inl pr =>
                    simp only [pure, Except.pure, Except.ok.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨h1, -⟩ := h
                    rw [← h1]
                    exact hentries (cl, .inl pr)
                      (List.mem_of_getElem? hidx) pr.1 pr.2 rfl
                | inr msg =>
                    simp only [pure, Except.pure, Except.ok.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨h1, -⟩ := h
                    rw [← h1]
                    simp [hasBarrierC, hb]

end GoLean.Frame
