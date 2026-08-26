import GoLeanProofs.FastEval.Shared

/-!
# FastEval — frames, sync, and the map-iter tower (campaign Arc 2, U4
wave, worker C)

Mirrors + one-directional sims per the U4 template
(`docs/campaign-arc2-log.md`); design
`docs/2026-08-22_fasteval-design.md`. UNTRUSTED METHOD — no name from
this module may appear in any headline statement's closure.

Per-def decisions (each by reading the original):

MIRRORED (transitively reach `loadLoc`/`storeLoc`/`alloc`):
- `allocDeclsF`, `bindParamsF` (allocation loops), `enterFrameF`
  (via the two + `dynamicDispatchF?`), `dynamicDispatchF?` (ONE heap
  read: the pointer-box receiver auto-deref), `syncCellF`,
  `applySyncOpF` (census-exercised `lock`/`unlock` mutex arms only —
  everything else fail-closed stubs), `mapRangeStartSetsF`,
  `mapIterLiveEntriesF`, `mapIterCandidatesF` (only the live-entries
  read is fast; filtering/validation are heap-pure and shared),
  `bindIterVarsF` (normalize is pure; the two allocs are fast).

PURE LAZY-VIEW (state only feeds heap-pure helpers — `valueEq`/
normalize/type towers; the original is called at `γF σF`, zero sim):
`keyInKeyList`/`keyInKeys` (valueEq), `filterCandidateList`,
`mandatoryInList`/`mapIterMandatoryRemains`, `removeKeyList`,
`pruneIterFramesKey` (its state reaches only `removeKeyList` →
`valueEq`), `pinResultLocs` (env-only).

PURE, SHARED AS-IS (no state at all / tables only):
`snapshotEntriesSelfNormalized(List)` (TypeEnv), `pruneIterFramesAll`
(Cont walk), `valueAsMap`/`valueAsLoc`/`valueAsInt`, `syncPlan`.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## Mirrors -/

/-- `allocDecls`, fast. -/
def allocDeclsF : LocalEnv → ExecStateF → List Param →
    Except GoError (LocalEnv × ExecStateF)
  | env, σF, [] => return (env, σF)
  | env, σF, p :: rest => do
      let v ← defaultValue (ctxF σF) p.typ
      let (loc, σF₁) := allocF σF v (some p.typ)
      allocDeclsF (env.declare p.id loc) σF₁ rest

/-- `bindParams`, fast. -/
def bindParamsF : LocalEnv → ExecStateF → List Param → List GoValue →
    Except GoError (LocalEnv × ExecStateF)
  | env, σF, [], [] => return (env, σF)
  | env, σF, p :: ps, v :: vs => do
      let v' ← normalizeValueForTy (ctxF σF) p.typ v
      let (loc, σF₁) := allocF σF v' (some p.typ)
      bindParamsF (env.declare p.id loc) σF₁ ps vs
  | _, _, [], _ :: _ => stuck "extra argument value"
  | _, _, _ :: _, [] => stuck "missing argument"

/-- `dynamicDispatch?`, fast — everything is table/method-set reads
except the pointer-box receiver auto-deref, which is the one heap
read. -/
def dynamicDispatchF? (σF : ExecStateF) (func : Func) (argValues : Array GoValue) :
    Except GoError (Option (Func × Array GoValue)) := do
  match methodInfoByFuncId? (ctxF σF) func.id with
  | none => return none
  | some method =>
      match methodRecvInterfaceName? (ctxF σF) method with
      | none => return none
      | some _ =>
          match argValues[0]? with
          | some (GoValue.interface dynTy inner) =>
              match concreteMethodForDynamic? (ctxF σF) dynTy method.name with
              | some (concrete, needsDeref) =>
                  let targetFunc ←
                    match findFunctionIn? (ctxF σF).functions concrete.funcId with
                    | some func => pure func
                    | none => stuck s!"GoCore dynamic method target not found: {concrete.funcId.key}"
                  let recvValue ←
                    if needsDeref then
                      match inner with
                      | .addr loc => loadLocF σF loc
                      | _ => stuck "fastEval-stub: dynamicDispatch.derefRecv (non-addr, unexercised)"
                    else
                      pure inner
                  return some (targetFunc, argValues.set! 0 recvValue)
              | none =>
                  stuck "fastEval-stub: dynamicDispatch.noConcreteMethod (error path, unexercised)"
          | some GoValue.nil =>
              stuck "fastEval-stub: dynamicDispatch.nilInterfaceRecv (unexercised)"
          | _ => stuck "fastEval-stub: dynamicDispatch.nonInterfaceArg0 (unexercised)"

/-- `enterFrame`, fast. -/
def enterFrameF (σF : ExecStateF) (fid : FuncId) (argVals : List GoValue) :
    Except GoError (Func × LocalEnv × List Loc × ExecStateF) := do
  let func ←
    match findFunctionIn? (ctxF σF).functions fid with
    | some func => pure func
    | none => stuck s!"GoCore function not found: {fid.key}"
  if func.args.size != argVals.length then
    stuck s!"function {fid.key} expected {func.args.size} argument(s), got {argVals.length}"
  let (func, argVals) ←
    match ← dynamicDispatchF? σF func argVals.toArray with
    | some (targetFunc, targetArgs) => pure (targetFunc, targetArgs.toList)
    | none => pure (func, argVals)
  if func.args.size != argVals.length then
    stuck s!"function {func.id.key} expected {func.args.size} argument(s), got {argVals.length}"
  let (argsEnv, σF₁) ← bindParamsF [] σF func.args.toList argVals
  let (frameEnv, σF₂) ← allocDeclsF argsEnv σF₁ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  return (func, frameEnv, resultLocs, σF₂)

/-- `syncCell`, fast. -/
def syncCellF (σF : ExecStateF) (loc : Loc) : Except GoError SyncPrim := do
  match ← loadLocF σF loc with
  | .syncData p => return p
  | other => stuck s!"expected sync primitive data, got {repr other}"

/-- `applySyncOp`, fast — the census-exercised mutex `lock`/`unlock`
arms only; every other op is a fail-closed stub (the twin's only sync
traffic is the `$deferSync0` mutex shims, probe D). -/
def applySyncOpF (σF : ExecStateF) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except GoError (Config × ExecStateF) := do
  match op, vs with
  | .lock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCellF σF loc with
      | .mutex locked =>
          if locked then return (.blockedSync .lock loc env k, σF)
          else do
            let σF' ← storeLocF σF loc (.syncData (.mutex true))
            return (.opDone .postOp (.next k), σF')
      | other => stuck s!"Lock on a non-mutex sync cell: {repr other}"
  | .unlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCellF σF loc with
      | .mutex locked =>
          if locked then do
            let σF' ← storeLocF σF loc (.syncData (.mutex false))
            return (.opDone .postOp (.next k), σF')
          else throw (.fatal "sync: unlock of unlocked mutex")
      | other => stuck s!"Unlock on a non-mutex sync cell: {repr other}"
  | _, _ => stuck "fastEval-stub: applySyncOp (non-mutex op unmirrored)"

/-- `mapRangeStartSets`, fast. -/
def mapRangeStartSetsF (σF : ExecStateF) (v : GoValue) :
    Except GoError (Option Loc × Array GoValue) := do
  let map ← valueAsMap v
  match map.base with
  | none => return (none, #[])
  | some base =>
      match ← loadLocF σF base with
      | .mapData es => return (some base, es.map (·.1))
      | other => stuck s!"expected map data for range, got {repr other}"

/-- `mapIterLiveEntries`, fast. -/
def mapIterLiveEntriesF (σF : ExecStateF) (base : Option Loc) :
    Except GoError (Array (GoValue × GoValue)) := do
  match base with
  | none => return #[]
  | some l =>
      match ← loadLocF σF l with
      | .mapData es => return es
      | other => stuck s!"expected map data for range, got {repr other}"

/-- `mapIterCandidates`, fast — only the live-entries read is fast;
filtering and self-normalization validation are heap-pure (lazy
view). -/
def mapIterCandidatesF (σF : ExecStateF) (keyTy valTy : Ty)
    (base : Option Loc) (produced : Array GoValue) :
    Except GoError (Array (GoValue × GoValue)) := do
  let entries ← mapIterLiveEntriesF σF base
  let out := (← filterCandidateList (ctxF σF) keyTy produced entries.toList).toArray
  if snapshotEntriesSelfNormalized (ctxF σF).types keyTy valTy out then
    return out
  else
    throw (.stuck s!"map range live entry not self-normalized at range \
key/value types ({repr keyTy}, {repr valTy})")

/-- `bindIterVars`, fast. -/
def bindIterVarsF (env : LocalEnv) (σF : ExecStateF) (keyVar valVar : Option String)
    (keyTy valTy : Ty) (key value : GoValue) :
    Except GoError (LocalEnv × ExecStateF) := do
  let (env, σF) ←
    match keyVar with
    | some name => do
        let kv ← normalizeValueForTy (ctxF σF) keyTy key
        let (loc, σF') := allocF σF kv (some keyTy)
        pure (env.declare name loc, σF')
    | none => pure (env, σF)
  match valVar with
  | some name => do
      let vv ← normalizeValueForTy (ctxF σF) valTy value
      let (loc, σF') := allocF σF vv (some valTy)
      pure (env.declare name loc, σF')
  | none => pure (env, σF)

/-! ## Sims -/

/-- `stuck` is a literal error (delta/instance reduction). -/
theorem stuck_eq_error {α : Type} (m : String) :
    (stuck m : Except GoError α) = Except.error (.stuck m) := rfl

theorem throw_eq_error {α : Type} (e : GoError) :
    (throw e : Except GoError α) = Except.error e := rfl

theorem stuck_absurd {α : Type} {m : String} {r : α}
    (h : (stuck m : Except GoError α) = .ok r) : False := by
  rw [stuck_eq_error] at h; simp at h

theorem throw_absurd {α : Type} {e : GoError} {r : α}
    (h : (throw e : Except GoError α) = .ok r) : False := by
  rw [throw_eq_error] at h; simp at h

theorem stuckBind_absurd {α β : Type} {m : String}
    {k : α → Except GoError β} {r : β}
    (h : (stuck m >>= k) = .ok r) : False := by
  rw [stuck_eq_error] at h
  simp [Bind.bind, Except.bind] at h

theorem throwBind_absurd {α β : Type} {e : GoError}
    {k : α → Except GoError β} {r : β}
    (h : (throw e >>= k) = .ok r) : False := by
  rw [throw_eq_error] at h
  simp [Bind.bind, Except.bind] at h

/-- Close a goal from an impossible fast-side hypothesis (an
error-headed computation equated to `.ok`), whatever its bind shape. -/
macro "goErrAbsurd " h:ident : tactic =>
  `(tactic| first
    | exact (stuck_absurd $h).elim
    | exact (stuckBind_absurd $h).elim
    | exact (throw_absurd $h).elim
    | exact (throwBind_absurd $h).elim
    | exact Except.noConfusion $h
    | simp [Bind.bind, Except.bind, stuck_eq_error, throw_eq_error] at $h:ident)


theorem allocDeclsF_ok :
    ∀ {ps : List Param} {env : LocalEnv} {σF : ExecStateF}
      {env' : LocalEnv} {σF' : ExecStateF},
    allocDeclsF env σF ps = .ok (env', σF') →
    allocDecls env (γF σF) ps = .ok (env', γF σF') := by
  intro ps
  induction ps with
  | nil =>
      intro env σF env' σF' h
      simp only [allocDeclsF, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      simp [allocDecls, pure, Except.pure, h.1, h.2]
  | cons p rest ih =>
      intro env σF env' σF' h
      unfold allocDeclsF at h
      simp only [defaultValue_ctx] at h
      cases hd : defaultValue (γF σF) p.typ with
      | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
      | ok v =>
          rw [hd] at h
          simp only [Bind.bind, Except.bind] at h
          simp only [allocDecls, hd, Bind.bind, Except.bind]
          rw [← allocF_loc σF v (some p.typ), ← allocF_state σF v (some p.typ)]
          exact ih h

theorem bindParamsF_ok :
    ∀ {ps : List Param} {vs : List GoValue} {env : LocalEnv} {σF : ExecStateF}
      {env' : LocalEnv} {σF' : ExecStateF},
    bindParamsF env σF ps vs = .ok (env', σF') →
    bindParams env (γF σF) ps vs = .ok (env', γF σF') := by
  intro ps
  induction ps with
  | nil =>
      intro vs env σF env' σF' h
      cases vs with
      | nil =>
          simp only [bindParamsF, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          simp [bindParams, pure, Except.pure, h.1, h.2]
      | cons v vs => simp [bindParamsF] at h
  | cons p rest ih =>
      intro vs env σF env' σF' h
      cases vs with
      | nil => simp [bindParamsF] at h
      | cons v vs =>
          unfold bindParamsF at h
          simp only [normalizeValueForTy_ctx] at h
          cases hd : normalizeValueForTy (γF σF) p.typ v with
          | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
          | ok v' =>
              rw [hd] at h
              simp only [Bind.bind, Except.bind] at h
              simp only [bindParams, hd, Bind.bind, Except.bind]
              rw [← allocF_loc σF v' (some p.typ), ← allocF_state σF v' (some p.typ)]
              exact ih h

theorem dynamicDispatchF?_ok {σF : ExecStateF} {func : Func}
    {argValues : Array GoValue} {r : Option (Func × Array GoValue)} :
    dynamicDispatchF? σF func argValues = .ok r →
    dynamicDispatch? (γF σF) func argValues = .ok r := by
  intro h
  unfold dynamicDispatchF? at h
  rw [methodInfoByFuncId?_ctx, methodRecvInterfaceName?_ctx,
    concreteMethodForDynamic?_ctx, ctxF_functions] at h
  unfold dynamicDispatch?
  split at h
  case h_1 hm => simp only [hm]; exact h
  case h_2 method hm =>
      simp only [hm]
      split at h
      case h_1 hri => simp only [hri]; exact h
      case h_2 _iname hri =>
          simp only [hri]
          split at h
          case h_2 harg => goErrAbsurd h
          case h_3 harg _hne => goErrAbsurd h
          case h_1 dynTy inner harg =>
              simp only [harg]
              split at h
              case h_2 hc => goErrAbsurd h
              case h_1 concrete needsDeref hc =>
                  simp only [hc]
                  split at h <;> rename_i hderef
                  · -- needsDeref = true; empirically the next split is
                    -- the receiver match, then the function lookup
                    split at h
                    case h_1 _old loc =>
                        split at h
                        case h_2 hfind => goErrAbsurd h
                        case h_1 targetFunc hfind =>
                            simp only [Bind.bind, Except.bind, pure,
                              Except.pure] at h
                            cases hl : loadLocF σF loc with
                            | error e =>
                                rw [hl] at h
                                simp [Bind.bind, Except.bind] at h
                            | ok rv =>
                                rw [hl] at h
                                simp only [Bind.bind, Except.bind, pure,
                                  Except.pure, Except.ok.injEq] at h
                                subst h
                                simp [hfind, hderef, loadLocF_ok hl,
                                  Bind.bind, Except.bind, pure, Except.pure]
                    case h_2 =>
                        split at h <;> goErrAbsurd h
                  · -- needsDeref = false
                    split at h
                    case h_2 hfind => goErrAbsurd h
                    case h_1 targetFunc hfind =>
                        simp only [Bind.bind, Except.bind, pure,
                          Except.pure, Except.ok.injEq] at h
                        subst h
                        simp [hfind, hderef, Bind.bind, Except.bind,
                          pure, Except.pure]

theorem enterFrameF_ok {σF : ExecStateF} {fid : FuncId} {argVals : List GoValue}
    {func : Func} {env : LocalEnv} {locs : List Loc} {σF' : ExecStateF} :
    enterFrameF σF fid argVals = .ok (func, env, locs, σF') →
    enterFrame (γF σF) fid argVals = .ok (func, env, locs, γF σF') := by
  intro h
  unfold enterFrameF at h
  try simp only [ctxF_functions] at h
  unfold enterFrame
  split at h
  case h_2 hfind => simp [Bind.bind, Except.bind] at h
  case h_1 f0 hfind =>
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    split at h <;> rename_i harity
    · simp [Bind.bind, Except.bind] at h
    · cases hd : dynamicDispatchF? σF f0 argVals.toArray with
      | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
      | ok disp =>
          rw [hd] at h
          simp only [Bind.bind, Except.bind] at h
          split at h
          case h_1 _o tf ta =>
              try simp only [pure, Except.pure, Bind.bind, Except.bind] at h
              split at h <;> rename_i harity2
              · goErrAbsurd h
              · try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                cases hb : bindParamsF [] σF tf.args.toList ta.toList with
                | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
                | ok p1 =>
                    obtain ⟨argsEnv, σF₁⟩ := p1
                    rw [hb] at h
                    simp only [Bind.bind, Except.bind] at h
                    cases ha : allocDeclsF argsEnv σF₁ tf.results.toList with
                    | error e => rw [ha] at h; simp [Bind.bind, Except.bind] at h
                    | ok p2 =>
                        obtain ⟨frameEnv, σF₂⟩ := p2
                        rw [ha] at h
                        simp only [Bind.bind, Except.bind] at h
                        cases hp : pinResultLocs frameEnv tf.results.toList with
                        | error e => rw [hp] at h; simp [Bind.bind, Except.bind] at h
                        | ok rls =>
                            rw [hp] at h
                            simp only [Bind.bind, Except.bind, pure,
                              Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                            obtain ⟨h1, h2, h3, h4⟩ := h
                            subst h1; subst h2; subst h3; subst h4
                            have hsz0 : tf.args.size = ta.toList.length := by
                              have h' := harity2
                              simp only [bne_iff_ne] at h'
                              omega
                            have hsz : tf.args.size = ta.size := by
                              rw [hsz0, Array.length_toList]
                            simp [hfind, harity, dynamicDispatchF?_ok hd,
                              hsz, bindParamsF_ok hb,
                              allocDeclsF_ok ha, hp,
                              Bind.bind, Except.bind, pure, Except.pure]
          case h_2 =>
              try simp only [pure, Except.pure, Bind.bind, Except.bind] at h
              split at h
              · rename_i err hb
                exact absurd h (by simp)
              · rename_i v hb
                obtain ⟨argsEnv, σF₁⟩ := v
                split at h
                · rename_i err ha
                  exact absurd h (by simp)
                · rename_i w ha
                  obtain ⟨frameEnv, σF₂⟩ := w
                  split at h
                  · rename_i err hp2
                    exact absurd h (by simp)
                  · rename_i rls hp2
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨h1, h2, h3, h4⟩ := h
                    subst h1; subst h2; subst h3; subst h4
                    have hsz1 : f0.args.size = argVals.length := by
                      have h' := harity
                      simp only [bne_iff_ne] at h'
                      omega
                    simp [hfind, harity, hsz1, dynamicDispatchF?_ok hd,
                      bindParamsF_ok hb, allocDeclsF_ok ha, hp2,
                      Bind.bind, Except.bind, pure, Except.pure]

theorem syncCellF_ok {σF : ExecStateF} {loc : Loc} {p : SyncPrim} :
    syncCellF σF loc = .ok p → syncCell (γF σF) loc = .ok p := by
  intro h
  unfold syncCellF at h
  unfold syncCell
  cases hl : loadLocF σF loc with
  | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
  | ok v =>
      rw [hl] at h
      rw [loadLocF_ok hl]
      simp only [Bind.bind, Except.bind] at h ⊢
      exact h

theorem applySyncOpF_ok {σF : ExecStateF} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {c : Config} {σF' : ExecStateF} :
    applySyncOpF σF op vs env k = .ok (c, σF') →
    applySyncOp (γF σF) op vs env k = .ok (c, γF σF') := by
  intro h
  unfold applySyncOpF at h
  unfold applySyncOp
  split at h
  case h_1 av =>
      -- lock
      cases hloc : valueAsLoc av with
      | error e => rw [hloc] at h; goErrAbsurd h
      | ok loc =>
          rw [hloc] at h
          simp only [Bind.bind, Except.bind] at h
          cases hsc : syncCellF σF loc with
          | error e => rw [hsc] at h; goErrAbsurd h
          | ok p =>
              rw [hsc] at h
              simp only [Bind.bind, Except.bind] at h
              split at h
              case h_2 => goErrAbsurd h
              case h_1 _p locked =>
                  split at h <;> rename_i hlk
                  · simp only [pure, Except.pure, Except.ok.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨h1, h2⟩ := h
                    simp [hloc, syncCellF_ok hsc, hlk, h1, ← h2,
                      Bind.bind, Except.bind, pure, Except.pure]
                  · cases hs : storeLocF σF loc (.syncData (.mutex true)) with
                    | error e => rw [hs] at h; goErrAbsurd h
                    | ok σF₁ =>
                        rw [hs] at h
                        simp only [Bind.bind, Except.bind, pure, Except.pure,
                          Except.ok.injEq, Prod.mk.injEq] at h
                        obtain ⟨h1, h2⟩ := h
                        simp [hloc, syncCellF_ok hsc, hlk,
                          storeLocF_ok hs, h1, ← h2,
                          Bind.bind, Except.bind, pure, Except.pure]
  case h_2 av =>
      -- unlock
      cases hloc : valueAsLoc av with
      | error e => rw [hloc] at h; goErrAbsurd h
      | ok loc =>
          rw [hloc] at h
          simp only [Bind.bind, Except.bind] at h
          cases hsc : syncCellF σF loc with
          | error e => rw [hsc] at h; goErrAbsurd h
          | ok p =>
              rw [hsc] at h
              simp only [Bind.bind, Except.bind] at h
              split at h
              case h_2 => goErrAbsurd h
              case h_1 _p locked =>
                  split at h <;> rename_i hlk
                  · cases hs : storeLocF σF loc (.syncData (.mutex false)) with
                    | error e => rw [hs] at h; goErrAbsurd h
                    | ok σF₁ =>
                        rw [hs] at h
                        simp only [Bind.bind, Except.bind, pure, Except.pure,
                          Except.ok.injEq, Prod.mk.injEq] at h
                        obtain ⟨h1, h2⟩ := h
                        simp [hloc, syncCellF_ok hsc, hlk,
                          storeLocF_ok hs, h1, ← h2,
                          Bind.bind, Except.bind, pure, Except.pure]
                  · goErrAbsurd h
  case h_3 => goErrAbsurd h

theorem mapRangeStartSetsF_ok {σF : ExecStateF} {v : GoValue}
    {r : Option Loc × Array GoValue} :
    mapRangeStartSetsF σF v = .ok r →
    mapRangeStartSets (γF σF) v = .ok r := by
  intro h
  unfold mapRangeStartSetsF at h
  unfold mapRangeStartSets
  cases hm : valueAsMap v with
  | error e => rw [hm] at h; goErrAbsurd h
  | ok map =>
      rw [hm] at h
      simp only [Bind.bind, Except.bind] at h
      split at h
      case h_1 hb =>
          rw [← h]
          simp [hm, hb, Bind.bind, Except.bind, pure, Except.pure]
      case h_2 base hb =>
          cases hl : loadLocF σF base with
          | error e => rw [hl] at h; goErrAbsurd h
          | ok bv =>
              rw [hl] at h
              split at h
              · rename_i err hes; exact absurd hes (by simp)
              · rename_i v hv
                injection hv with hbv
                subst hbv
                split at h
                · rename_i es
                  rw [← h]
                  simp [hm, hb, loadLocF_ok hl, Bind.bind, Except.bind,
                    pure, Except.pure]
                · goErrAbsurd h

theorem mapIterLiveEntriesF_ok {σF : ExecStateF} {base : Option Loc}
    {r : Array (GoValue × GoValue)} :
    mapIterLiveEntriesF σF base = .ok r →
    mapIterLiveEntries (γF σF) base = .ok r := by
  intro h
  unfold mapIterLiveEntriesF at h
  unfold mapIterLiveEntries
  split at h
  · exact h
  · rename_i l
    cases hl : loadLocF σF l with
    | error e => rw [hl] at h; goErrAbsurd h
    | ok bv =>
        rw [hl] at h
        simp only [Bind.bind, Except.bind] at h
        split at h
        · rename_i es
          rw [← h]
          simp [loadLocF_ok hl, Bind.bind, Except.bind, pure, Except.pure]
        · goErrAbsurd h
        

theorem mapIterCandidatesF_ok {σF : ExecStateF} {keyTy valTy : Ty}
    {base : Option Loc} {produced : Array GoValue}
    {r : Array (GoValue × GoValue)} :
    mapIterCandidatesF σF keyTy valTy base produced = .ok r →
    mapIterCandidates (γF σF) keyTy valTy base produced = .ok r := by
  intro h
  unfold mapIterCandidatesF at h
  simp only [filterCandidateList_ctx, ctxF_types] at h
  unfold mapIterCandidates
  cases he : mapIterLiveEntriesF σF base with
  | error e => rw [he] at h; goErrAbsurd h
  | ok entries =>
      rw [he] at h
      rw [mapIterLiveEntriesF_ok he]
      simp only [Bind.bind, Except.bind] at h ⊢
      exact h

theorem bindIterVarsF_ok {env : LocalEnv} {σF : ExecStateF}
    {keyVar valVar : Option String} {keyTy valTy : Ty} {key value : GoValue}
    {env' : LocalEnv} {σF' : ExecStateF} :
    bindIterVarsF env σF keyVar valVar keyTy valTy key value = .ok (env', σF') →
    bindIterVars env (γF σF) keyVar valVar keyTy valTy key value
      = .ok (env', γF σF') := by
  intro h
  unfold bindIterVarsF at h
  simp only [normalizeValueForTy_ctx] at h
  unfold bindIterVars
  cases keyVar with
  | none =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h ⊢
      cases valVar with
      | none =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          exact ⟨h.1, h.2 ▸ rfl⟩
      | some vname =>
          simp only [] at h ⊢
          cases hvn : normalizeValueForTy (γF σF) valTy value with
          | error e => rw [hvn] at h; goErrAbsurd h
          | ok vv =>
              rw [hvn] at h
              simp only [Bind.bind, Except.bind] at h ⊢
              rw [← allocF_loc σF vv (some valTy),
                ← allocF_state σF vv (some valTy)]
              simp only [pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h ⊢
              exact ⟨h.1, h.2 ▸ rfl⟩
  | some kname =>
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hkn : normalizeValueForTy (γF σF) keyTy key with
      | error e => rw [hkn] at h; goErrAbsurd h
      | ok kv =>
          rw [hkn] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          rw [← allocF_loc σF kv (some keyTy),
            ← allocF_state σF kv (some keyTy)]
          cases valVar with
          | none =>
              simp only [pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h ⊢
              exact ⟨h.1, h.2 ▸ rfl⟩
          | some vname =>
              simp only [pure, Except.pure] at h ⊢
              cases hvn : normalizeValueForTy
                  (γF (allocF σF kv (some keyTy)).2) valTy value with
              | error e => rw [hvn] at h; goErrAbsurd h
              | ok vv =>
                  rw [hvn] at h
                  simp only [Bind.bind, Except.bind] at h ⊢
                  rw [← allocF_loc (allocF σF kv (some keyTy)).2 vv (some valTy),
                    ← allocF_state (allocF σF kv (some keyTy)).2 vv (some valTy)]
                  simp only [pure, Except.pure, Except.ok.injEq,
                    Prod.mk.injEq] at h ⊢
                  exact ⟨h.1, h.2 ▸ rfl⟩

end GoLean.FastEval
