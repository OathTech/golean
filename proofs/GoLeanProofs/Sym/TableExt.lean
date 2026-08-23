import GoLeanProofs.Sym.Refine

/-!
# The handler-fragment extension, class 1: TYPE-TABLE INPUT
(campaign Arc 4, A4-U2 slice 1; design
`docs/2026-08-22_campaign-arc4-sym-extension-design.md` §2)

The Q4a lever, layered FULLY ADDITIVELY over the untouched Sym core:
store-time normalization at `.defined` types proceeds against an input
`TypeEnv` `T`, so struct-field stores — the raft handlers' bread and
butter, and the pilot's measured cost center — transport inside
windows instead of costing a conditioned kit step each.

Mechanism (design §0's additivity plan, realized even more strictly —
ZERO edits to the existing Sym modules):

- `normalizeValueForTyFuelT T` — the mirror normalizer with the
  machine's `.defined` arm (`Ops.lean:958-966` mirrored verbatim:
  alias/defined re-target, struct via `normalizeFieldsWith'` +
  `emptyStructAssignable'`; `interfaceDef`/`unsupported`/unknown stay
  quits). At `T = []` every defined lookup fails ⇒ behaviorally the
  shipped normalizer.
- `storeLocT`/`storeTargetT` — the store chain over it.
- `stepFnT T` — the extended step: ONE overridden arm
  (`.next (.storeK …)`, routed through `storeTargetT`), everything
  else DELEGATES to the shipped `stepFn'`. `symEvalWindowT` iterates
  it.
- Soundness/refinement: the same template as `Refine.lean` plus ONE
  premise, `SubTable T σ.types` — every successful lookup on the
  input table agrees with the run state's. `SubTable [] U` is
  trivial, so the shipped theorems are the degenerate instance and
  none of their statements move.

Outside the TCB by construction, like everything in `GoLean.Sym`
(the statement-TCB walker's third refusal class bans the prefix).
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

/-! ## The table-agreement premise -/

/-- Every successful lookup on the INPUT table agrees with the
carrier's table. Weaker than equality on purpose: a window emitted at
the pin's table transports into any state whose types extend it. -/
def SubTable (T U : TypeEnv) : Prop :=
  ∀ id d, TypeEnv.lookup T id = some d → TypeEnv.lookup U id = some d

/-- The empty input is a sub-table of anything — the degenerate
instance under which this module's theorems collapse to the shipped
ones. -/
theorem SubTable.nil (U : TypeEnv) : SubTable [] U := by
  intro id d h
  simp [TypeEnv.lookup] at h

/-- Table equality is the everyday discharge at a pinned program. -/
theorem SubTable.of_eq {T U : TypeEnv} (h : U = T) : SubTable T U := by
  intro id d hl
  rw [h]
  exact hl

/-! ## The mirror normalizer at an input table -/

/-- Mirror of `emptyStructAssignable` (payloads never read). -/
def emptyStructAssignable' (actual name : TypeId)
    (fields : Array FieldDef) (fieldsValue : Array (String × Value D)) : Bool :=
  (actual.key == "struct{}" || name.key == "struct{}") &&
    fields.isEmpty && fieldsValue.isEmpty

/-- Mirror of `normalizeFieldsWith` (field names concrete; payloads
through the parameterized element normalizer). -/
def normalizeFieldsWith' (f : Ty → Value D → M (Value D)) :
    List FieldDef → List (String × Value D) →
    M (Array (String × Value D))
  | field :: fieldRest, (actualField, value) :: valueRest => do
      if actualField != field.name then quit .q11Internal
      else do
        let head ← f field.typ value
        let tail ← normalizeFieldsWith' f fieldRest valueRest
        .ok (#[(field.name, head)] ++ tail)
  | _, _ => .ok #[]

/-- Mirror of `normalizeStructValueWith`. -/
def normalizeStructValueWith' (f : Ty → Value D → M (Value D))
    (name : TypeId) (fields : Array FieldDef) : Value D → M (Value D)
  | .struct actual fieldsValue => do
      if actual != name then
        if emptyStructAssignable' actual name fields fieldsValue then
          .ok (.struct name #[])
        else quit .q11Internal
      else if fieldsValue.size != fields.size then quit .q11Internal
      else do
        let out ← normalizeFieldsWith' f fields.toList fieldsValue.toList
        .ok (.struct name out)
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- The mirror normalizer WITH the defined-type arm, against the input
table `T`. Non-defined arms are the shipped
`normalizeValueForTyFuel'`'s, verbatim; the `.defined` arm mirrors the
machine's dispatch, quitting where the machine diagnoses
(`interfaceDef`/`unsupported`) or the input table has no answer. -/
def normalizeValueForTyFuelT (T : TypeEnv) : Nat → Ty → Value D → M (Value D)
  | 0, _, _ => quit .q11Internal
  | _ + 1, .int kind, .int value _ => .ok (.int (D.norm kind value) kind)
  | _ + 1, .int _, .atom _ => quit .q10Atom
  | _ + 1, .int _, _ => quit .q11Internal
  | _ + 1, .float kind, .float bits k =>
      if k == kind then .ok (.float (kind.normalizeBits bits) kind)
      else quit .q11Internal
  | _ + 1, .float _, .atom _ => quit .q10Atom
  | _ + 1, .float _, _ => quit .q11Internal
  | fuel + 1, .array length elem, .array values => do
      if values.size != length then quit .q11Internal
      else
        Value.array <$>
          normalizeListWith' (normalizeValueForTyFuelT T fuel elem) values.toList
  | _ + 1, .array _ _, .atom _ => quit .q10Atom
  | _ + 1, .array _ _, _ => quit .q11Internal
  | _ + 1, .interface _, value => .ok value
  | _ + 1, .funcType _ _ _, .funcVal fid captured => .ok (.funcVal fid captured)
  | _ + 1, .funcType _ _ _, .nil => .ok .nil
  | _ + 1, .funcType _ _ _, .atom _ => quit .q10Atom
  | _ + 1, .funcType _ _ _, _ => quit .q11Internal
  | _ + 1, .chan _ _, .chan cv => .ok (.chan cv)
  | _ + 1, .chan _ _, .nil => .ok (.chan { base := none })
  | _ + 1, .chan _ _, .atom _ => quit .q10Atom
  | _ + 1, .chan _ _, _ => quit .q11Internal
  | _ + 1, .sync kind, .syncData p =>
      if p.kind == kind then .ok (.syncData p) else quit .q11Internal
  | _ + 1, .sync _, .atom _ => quit .q10Atom
  | _ + 1, .sync _, _ => quit .q11Internal
  | fuel + 1, .defined name, value =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => normalizeValueForTyFuelT T fuel target value
       | some (.defined target) => normalizeValueForTyFuelT T fuel target value
       | some (.struct fields) =>
           normalizeStructValueWith' (normalizeValueForTyFuelT T fuel)
             name fields value
       | some (.unsupported _) => quit .q11Internal
       | some (.interfaceDef _) => quit .q11Internal
       | none => quit .q4Program)
  | _ + 1, .unsupported _, _ => quit .q11Internal
  | _ + 1, _, value => .ok value

def normalizeValueForTyT (T : TypeEnv) (ty : Ty) (value : Value D) :
    M (Value D) :=
  normalizeValueForTyFuelT T typeResolutionFuel ty value

/-! ## The store chain over it -/

/-- `storeLoc'` with the table-aware normalizer (untyped cells still
coerce via the shipped `coerceStoredValue'`). -/
def storeLocT (T : TypeEnv) (s : State D) : Loc → Value D → M (State D)
  | loc@(.base _), value => do
      match Heap.lookup s.heap loc with
      | some (.mk declaredTy oldValue) => do
          let value ←
            match declaredTy with
            | some ty => normalizeValueForTyT T ty value
            | none => coerceStoredValue' oldValue value
          .ok { s with heap := Heap.set s.heap loc (.mk declaredTy value) }
      | some (.atom _) => quit .q10Atom
      | none =>
          .ok { s with heap := Heap.set s.heap loc (.mk none value) }
  | .field base typeId fieldName, value => do
      match ← loadLoc' s base with
      | .struct actualType fields =>
          if actualType != typeId then quit .q11Internal
          else do
            let updated ← StructFields.set' fields fieldName value
            storeLocT T s base (.struct actualType updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .index base index, value => do
      match ← loadLoc' s base with
      | .array values => do
          let updated ← arraySet' values index value
          storeLocT T s base (.array updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal

/-- `storeTarget'` with the table-aware store (the `mapElem` arm stays
the shipped one — map assigns at defined key/value types remain
quits, the recorded class-1 scope line). -/
def storeTargetT (T : TypeEnv) (s : State D) (r : TargetRef D)
    (v : Value D) : M (State D) := do
  match r with
  | .chain anchor idxs steps => do
      let resolved ← resolveChain' s anchor steps idxs
      let loc ← resolved.asLoc
      storeLocT T s loc v
  | .mapElem b k kt vt => mapAssignValue' s kt vt b k v

/-! ## Slice 2 — sequential sync-ops (design §3, class 3)

The pilot census (arc log): the handler fragment consumes exactly
`SyncStmtOp.lock`/`unlock` on plain `sync.Mutex` cells (lockedRand,
MemoryStorage) — no Once, no RWMutex on the path; the deferred-Unlock
DISCHARGE at frame exit additionally needs class 2 (a deferred call is
a frame entry). Only the consumed ops proceed; the rest of the family
stays Q7 (wider coverage is a later strengthening). The sync apply
consumes no choices (StepFn's arm), so the `ch`-unchanged theorem form
is untouched. Blocked acquisitions mirror the machine's
`.blockedSync` configuration faithfully (a dead end for a window, but
sound). -/

/-- Mirror of `syncCell`. -/
def syncCell' (s : State D) (loc : Loc) : M SyncPrim := do
  match ← loadLoc' s loc with
  | .syncData p => .ok p
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- Mirror of `applySyncOp`, the census subset: `lock`/`unlock` on a
mutex. Failure paths (unlock of unlocked = the machine's `.fatal`)
quit Q6; every other op quits Q7 as before. -/
def applySyncOp' (T : TypeEnv) (s : State D) (op : SyncOp) (vs : List (Value D))
    (env : LocalEnv) (k : Cont D) : M (Config D × State D) := do
  match op, vs with
  | .lock, [av] => do
      let loc ← av.asLoc
      match ← syncCell' s loc with
      | .mutex locked =>
          if locked then .ok (.blockedSync .lock loc env k, s)
          else do
            let s' ← storeLocT T s loc (.syncData (.mutex true))
            .ok (.opDone .postOp (.next k), s')
      | _ => quit .q11Internal
  | .unlock, [av] => do
      let loc ← av.asLoc
      match ← syncCell' s loc with
      | .mutex locked =>
          if locked then do
            let s' ← storeLocT T s loc (.syncData (.mutex false))
            .ok (.opDone .postOp (.next k), s')
          else quit .q6Panic
      | _ => quit .q11Internal
  | _, _ => quit .q7Concurrency

/-! ## The extended step and window driver -/

/-- The extended mirror step: the store arm through the table-aware
chain, every other configuration DELEGATED verbatim to the shipped
`stepFn'`. At `T = []` this is behaviorally the shipped step. -/
def stepFnT (T : TypeEnv) (s : State D) (c : Config D) :
    M (Config D × State D) :=
  match c with
  | .next (.storeK refs vals body env k') =>
      (match refs, vals with
       | r :: rs, val :: vrest => do
          let s' ← storeTargetT T s r val
          .ok (.next (.storeK rs vrest body env k'), s')
       | [], [] => .ok (.exec body env k', s)
       | _, _ => quit .q11Internal)
  -- slice 2: sync-statement entry (the machine's operand-plan arm)
  | .exec (.syncStmt op args targets) env k =>
      (match syncPlan (.syncStmt op args targets) with
       | some (sop, e :: rest) =>
           .ok (.evalE e env (.syncStK sop [] rest env k), s)
       | some (_, []) => quit .q11Internal
       | none => quit .q11Internal)
  -- slice 2: sync operand collection + the apply
  | .retV v (.syncStK op done pending env k') =>
      (match pending with
       | e :: rest =>
           .ok (.evalE e env (.syncStK op (v :: done) rest env k'), s)
       | [] => applySyncOp' T s op (v :: done).reverse env k')
  -- slice 2: the sequential completion-marker strip
  | .opDone _ inner => .ok (inner, s)
  | c => stepFn' s c

/-- The extended step at the symbolic domain. -/
def stepFnST (T : TypeEnv) (S : SymState) (C : SymConfig) :
    M (SymConfig × SymState) :=
  stepFnT T S C

/-- The extended window driver (shape identical to `symEvalWindow`). -/
def symEvalWindowT (T : TypeEnv) :
    Nat → SymState → SymConfig → Nat × SymState × SymConfig
  | 0, S, C => (0, S, C)
  | budget + 1, S, C =>
      match stepFnST T S C with
      | .error _ => (0, S, C)
      | .ok (C', S') =>
          let (n, S'', C'') := symEvalWindowT T budget S' C'
          (n + 1, S'', C'')

/-! ## Soundness (the drift layer, table-conditioned) -/

/-- Field-walk commutation, parameterized like
`normalizeListWith_conc`. -/
theorem normalizeFieldsWith_conc {f : Ty → Value D → M (Value D)}
    {g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v out, f ty v = .ok out → g ty (concV I v) = .ok (concV I out)) :
    ∀ {fds : List FieldDef} {fvs : List (String × Value D)}
      {out : Array (String × Value D)},
      normalizeFieldsWith' f fds fvs = .ok out →
      normalizeFieldsWith g fds (fvs.map (fun p => (p.1, concV I p.2)))
        = .ok (out.map (fun p => (p.1, concV I p.2))) := by
  intro fds
  induction fds with
  | nil =>
      intro fvs out h
      cases fvs with
      | nil =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
      | cons a rest =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
  | cons fd fdRest ih =>
      intro fvs out h
      cases fvs with
      | nil =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
      | cons fv rest =>
          obtain ⟨actualField, value⟩ := fv
          simp only [normalizeFieldsWith', quit] at h
          by_cases hname : (actualField != fd.name) = true
          · rw [if_pos hname] at h
            cases h
          · rw [if_neg hname] at h
            obtain ⟨head, hhead, h2⟩ := bind_eq_ok.mp h
            obtain ⟨tail, htail, h3⟩ := bind_eq_ok.mp h2
            cases h3
            simp only [List.map_cons, normalizeFieldsWith]
            rw [if_neg hname]
            simp only [Bind.bind, Except.bind, pure, Except.pure]
            rw [hfg _ _ _ hhead, ih htail]
            simp [Array.map_append]

/-- The `.defined`-arm transport, factored out so the master induction
can close all value shapes uniformly. -/
private theorem normalizeFuelT_defined_conc (_hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) (fuel : Nat)
    (ih : ∀ (ty : Ty) (v out : Value D),
      normalizeValueForTyFuelT T fuel ty v = .ok out →
      normalizeValueForTyFuel fuel σ ty (concV I v) = .ok (concV I out))
    {name : TypeId} {v out : Value D}
    (h : (match TypeEnv.lookup T name with
          | some (.alias target) => normalizeValueForTyFuelT T fuel target v
          | some (.defined target) => normalizeValueForTyFuelT T fuel target v
          | some (.struct fields) =>
              normalizeStructValueWith' (normalizeValueForTyFuelT T fuel)
                name fields v
          | some (.unsupported _) => quit .q11Internal
          | some (.interfaceDef _) => quit .q11Internal
          | none => quit .q4Program) = .ok out) :
    normalizeValueForTyFuel (fuel + 1) σ (.defined name) (concV I v)
      = .ok (concV I out) := by
  revert h
  rcases hlk : TypeEnv.lookup T name with _ | td
  · intro h
    simp only [quit] at h
    cases h
  · intro h
    have hσlk := hsub name td hlk
    cases td with
    | alias target =>
        simp only [normalizeValueForTyFuel, hσlk]
        exact ih _ _ _ h
    | defined target =>
        simp only [normalizeValueForTyFuel, hσlk]
        exact ih _ _ _ h
    | struct fields =>
        simp only [normalizeValueForTyFuel, hσlk]
        revert h
        cases v
        case struct actual fieldsValue =>
            intro h
            simp only [normalizeStructValueWith', quit] at h
            by_cases hne : (actual != name) = true
            · rw [if_pos hne] at h
              by_cases hemp : emptyStructAssignable' actual name fields
                  fieldsValue = true
              · rw [if_pos hemp] at h
                cases h
                simp only [concV_struct, normalizeStructValueWith]
                rw [if_pos hne]
                have hemp2 : emptyStructAssignable actual name fields
                    (fieldsValue.map (fun p => (p.1, concV I p.2))) = true := by
                  simp only [emptyStructAssignable',
                    Bool.and_eq_true] at hemp
                  have hfv : fieldsValue = #[] := by
                    simpa using hemp.2
                  subst hfv
                  simp [emptyStructAssignable, hemp.1.1, hemp.1.2]
                rw [if_pos hemp2]
                simp
              · rw [if_neg hemp] at h
                cases h
            · rw [if_neg hne] at h
              by_cases hsz : (fieldsValue.size != fields.size) = true
              · rw [if_pos hsz] at h
                cases h
              · rw [if_neg hsz] at h
                obtain ⟨out2, hout, h2⟩ := bind_eq_ok.mp h
                cases h2
                simp only [concV_struct, normalizeStructValueWith]
                rw [if_neg hne]
                rw [if_neg (by simpa using hsz)]
                have hf := normalizeFieldsWith_conc (I := I)
                  (g := normalizeValueForTyFuel fuel σ)
                  (fun ty v out hv => ih ty v out hv) hout
                simp only [Array.toList_map] at hf ⊢
                rw [hf]
                simp [Functor.map, Except.map]
        case atom a =>
            intro h
            simp only [normalizeStructValueWith', quit] at h
            cases h
        all_goals
          intro h
          simp only [normalizeStructValueWith', quit] at h
          cases h
    | unsupported f =>
        simp only [quit] at h
        cases h
    | interfaceDef sigs =>
        simp only [quit] at h
        cases h

/-- THE TABLE-CONDITIONED NORMALIZER COMMUTATION: a successful mirror
normalization at input table `T` transports to the machine at any
state whose types extend `T`. Non-defined arms replay the shipped
`normalizeFuel_conc`'s cases; the `.defined` arm rides `hsub`. -/
theorem normalizeFuelT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) (v out : Value D),
      normalizeValueForTyFuelT T fuel ty v = .ok out →
      normalizeValueForTyFuel fuel σ ty (concV I v) = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v out h
      simp only [normalizeValueForTyFuelT, quit] at h
      cases h
  | succ fuel ih =>
      intro ty v out h
      cases ty <;> cases v <;>
        simp only [normalizeValueForTyFuelT, quit] at h <;>
        first
          | (cases h; done)
          | (cases h; simp [normalizeValueForTyFuel]; done)
          | skip
      all_goals try (cases h; done)
      case succ.int.int =>
        rename_i kind payload kind1
        cases h
        simp [normalizeValueForTyFuel, hI.norm]
      case succ.float.float =>
        rename_i kind bits k
        by_cases hk : (k == kind) = true
        · rw [if_pos hk] at h
          cases h
          simp only [concV_float, normalizeValueForTyFuel]
          rw [if_pos hk]
          rfl
        · rw [if_neg hk] at h
          cases h
      case succ.array.array =>
        rename_i length elem values
        by_cases hsz : (values.size != length) = true
        · rw [if_pos hsz] at h
          cases h
        · rw [if_neg hsz] at h
          rcases hok : normalizeListWith' (normalizeValueForTyFuelT T fuel elem)
              values.toList with _ | arr
          · rw [hok] at h
            exact absurd h (by simp [Functor.map, Except.map])
          · rw [hok] at h
            simp only [Functor.map, Except.map] at h
            cases h
            have := normalizeListWith_conc (fun v out hv => ih elem v out hv)
              values.toList arr hok
            simp only [concV_array, normalizeValueForTyFuel]
            rw [if_neg (by simp_all)]
            simp only [Array.toList_map] at this ⊢
            rw [this]
            simp [Functor.map, Except.map]
      case succ.sync.syncData =>
        rename_i kind p
        by_cases hp : (p.kind == kind) = true
        · rw [if_pos hp] at h
          cases h
          simp only [concV_syncData, normalizeValueForTyFuel]
          rw [if_pos hp]
          rfl
        · rw [if_neg hp] at h
          cases h
      all_goals exact normalizeFuelT_defined_conc hI σ hsub fuel ih h

theorem normalizeT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {ty : Ty} {v out : Value D}
    (h : normalizeValueForTyT T ty v = .ok out) :
    normalizeValueForTy σ ty (concV I v) = .ok (concV I out) := by
  simp only [normalizeValueForTy]
  exact normalizeFuelT_conc hI σ hsub _ ty v out h

set_option linter.unusedSimpArgs false in
/-- `storeLoc_conc`, table-conditioned (proof = the shipped one with
`normalizeT_conc` at the typed-cell arm). -/
theorem storeLocT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D} :
    ∀ {loc : Loc} {v : Value D} {s' : State D}, storeLocT T s loc v = .ok s' →
      storeLoc (concS I σ s) loc (concV I v) = .ok (concS I σ s') := by
  intro loc
  induction loc with
  | base a =>
      intro v s' h
      simp only [storeLocT, quit] at h
      rcases hq : Heap.lookup s.heap (.base a) with _ | cell
      · rw [hq] at h
        cases h
        simp only [storeLoc, concS]
        rw [lookup_conc, hq]
        simp only [Option.map]
        rw [show ({ value := concV I v } : GoCore.HeapCell)
              = concCell I (.mk none v) from rfl, set_conc]
        rfl
      · rw [hq] at h
        rcases cell with ⟨dty, oldv⟩ | ca
        case atom => cases h
        cases dty with
        | none =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            refine ⟨concV I nv, coerce_conc hI hnv, ?_⟩
            rw [show ({ declaredTy := none, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk none nv) from rfl,
              set_conc]
            rfl
        | some ty =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            have hsub' : SubTable T (concS I σ s).types := hsub
            refine ⟨concV I nv, normalizeT_conc hI (concS I σ s) hsub' hnv, ?_⟩
            rw [show ({ declaredTy := some ty, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk (some ty) nv) from rfl,
              set_conc]
            rfl
  | field base tid fname ih =>
      intro v s' h
      simp only [storeLocT, bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next actual fields =>
        simp only [concV_struct]
        by_cases hty : (actual != tid) = true
        · rw [if_pos hty] at h2
          cases h2
        · rw [if_neg hty] at h2
          have hty2 : ¬(actual != tid
              && !structTagCompatible (concS I σ s) actual tid) = true := by
            simp only [Bool.not_eq_true] at hty
            simp [hty]
          rw [if_neg hty2]
          simp only [bind_eq_ok] at h2
          obtain ⟨updated, hupd, h3⟩ := h2
          simp only [pure_bind, bind_eq_ok]
          refine ⟨_, structSet_conc hupd, ?_⟩
          have := ih h3
          simpa [concV_struct] using this
  | index base i ih =>
      intro v s' h
      simp only [storeLocT, bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next values =>
        simp only [concV_array]
        simp only [bind_eq_ok] at h2
        obtain ⟨updated, hupd, h3⟩ := h2
        simp only [bind_eq_ok]
        refine ⟨_, arraySet_conc hI hupd, ?_⟩
        have := ih h3
        simpa using this

/-- `storeTarget_conc`, table-conditioned. -/
theorem storeTargetT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D}
    {r : TargetRef D} {v : Value D} {s' : State D}
    (h : storeTargetT T s r v = .ok s') :
    storeTarget (concS I σ s) (concRef I r) (concV I v)
      = .ok (concS I σ s') := by
  cases r with
  | chain anchor idxs steps =>
      simp only [storeTargetT] at h
      obtain ⟨resolved, hres, h⟩ := bind_eq_ok.mp h
      obtain ⟨loc, hloc, h⟩ := bind_eq_ok.mp h
      simp only [storeTarget, concRef]
      refine bind_eq_ok.mpr ⟨concV I resolved,
        resolveChain_conc hI σ steps anchor idxs hres, ?_⟩
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      exact storeLocT_conc hI σ hsub h
  | mapElem b k kt vt =>
      simp only [storeTargetT] at h
      simpa [storeTarget, concRef] using mapAssignValue_conc hI σ h

set_option linter.unusedSimpArgs false in
/-- `applySyncOp'` transports (census subset; `storeLoc_conc` carries
the flag store — sync cells normalize at the concrete `.sync` arm, no
table needed). -/
theorem applySyncOp_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D}
    {op : SyncOp} {vs : List (Value D)} {env : LocalEnv} {k : Cont D}
    {c' : Config D} {s' : State D}
    (h : applySyncOp' T s op vs env k = .ok (c', s')) :
    applySyncOp (concS I σ s) op (vs.map (concV I)) env (concK I k)
      = .ok (concC I c', concS I σ s') := by
  cases op <;> simp only [applySyncOp', quit] at h <;> try (cases h; done)
  case lock =>
      match vs, h with
      | [av], h =>
        obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
        obtain ⟨p, hp, h3⟩ := bind_eq_ok.mp h2
        simp only [List.map_cons, List.map_nil, applySyncOp]
        refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
        simp only [syncCell'] at hp
        obtain ⟨pv, hpv, hp2⟩ := bind_eq_ok.mp hp
        have hload := loadLoc_conc (I := I) σ hpv
        cases pv <;> simp only [quit] at hp2 <;> try (cases hp2; done)
        case syncData prim =>
          cases hp2
          refine bind_eq_ok.mpr ⟨p, ?_, ?_⟩
          · simp only [syncCell, hload, concV_syncData, Bind.bind,
              Except.bind, pure, Except.pure]
          · cases p <;> simp only [quit] at h3 <;> try (cases h3; done)
            case mutex locked =>
              by_cases hl : locked = true
              · subst hl
                rw [if_pos rfl] at h3
                cases h3
                simp [concC, concK]
              · rw [if_neg hl] at h3
                obtain ⟨s2, hst, h4⟩ := bind_eq_ok.mp h3
                cases h4
                simp only [Bool.not_eq_true] at hl
                subst hl
                have hstc := storeLocT_conc hI σ hsub hst
                simp only [concV_syncData] at hstc
                simp [hstc, concC, concK, Bind.bind, Except.bind, pure,
                  Except.pure]
  case unlock =>
      match vs, h with
      | [av], h =>
        obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
        obtain ⟨p, hp, h3⟩ := bind_eq_ok.mp h2
        simp only [List.map_cons, List.map_nil, applySyncOp]
        refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
        simp only [syncCell'] at hp
        obtain ⟨pv, hpv, hp2⟩ := bind_eq_ok.mp hp
        have hload := loadLoc_conc (I := I) σ hpv
        cases pv <;> simp only [quit] at hp2 <;> try (cases hp2; done)
        case syncData prim =>
          cases hp2
          refine bind_eq_ok.mpr ⟨p, ?_, ?_⟩
          · simp only [syncCell, hload, concV_syncData, Bind.bind,
              Except.bind, pure, Except.pure]
          · cases p <;> simp only [quit] at h3 <;> try (cases h3; done)
            case mutex locked =>
              by_cases hl : locked = true
              · subst hl
                rw [if_pos rfl] at h3
                obtain ⟨s2, hst, h4⟩ := bind_eq_ok.mp h3
                cases h4
                have hstc := storeLocT_conc hI σ hsub hst
                simp only [concV_syncData] at hstc
                simp [hstc, concC, concK, Bind.bind, Except.bind, pure,
                  Except.pure]
              · rw [if_neg hl] at h3
                cases h3


/-! ## The extended master step + window, sound -/

/-- The extended step transports: the overridden arm via
`storeTargetT_conc`, every delegated arm via the SHIPPED master walk
`stepFn'_conc` — which is what makes this module additive. -/
theorem stepFnT_conc (hI : I.Sound) (σ : ExecState) (ch : Choices)
    {T : TypeEnv} (hsub : SubTable T σ.types)
    {s : State D} {c : Config D} {c₁ : Config D} {s₁ : State D}
    (h : stepFnT T s c = .ok (c₁, s₁)) :
    stepFn (concS I σ s) (concC I c) ch
      = .ok (concC I c₁, concS I σ s₁, ch) := by
  cases c with
  | next k =>
      cases k with
      | storeK refs vals body env k' =>
          simp only [stepFnT] at h
          cases refs with
          | nil =>
              cases vals with
              | nil =>
                  cases h
                  rfl
              | cons a b => simp [quit] at h
          | cons r rs =>
              cases vals with
              | nil => simp [quit] at h
              | cons val vrest =>
                  obtain ⟨s2, hstore, h2⟩ := bind_eq_ok.mp h
                  have hout : c₁ = .next (.storeK rs vrest body env k')
                      ∧ s₁ = s2 := by
                    simpa [pure, Except.pure, eq_comm, and_comm] using h2
                  rw [hout.1, hout.2]
                  simp only [concC, concK, stepFn, List.map_cons]
                  rw [storeTargetT_conc hI σ hsub hstore]
                  rfl
      | _ => exact stepFn'_conc hI σ ch h
  | exec stmt env k =>
      cases stmt with
      | syncStmt op args targets =>
          simp only [stepFnT] at h
          revert h
          rcases hplan : syncPlan (.syncStmt op args targets) with _ | ⟨sop, es⟩
          · intro h
            simp [quit] at h
          · cases es with
            | nil =>
                intro h
                simp [quit] at h
            | cons e rest =>
                intro h
                cases h
                simp only [concC, concK, stepFn]
                split
                all_goals simp_all
      | _ => exact stepFn'_conc hI σ ch h
  | retV v k =>
      cases k with
      | syncStK op done pending env k' =>
          simp only [stepFnT] at h
          cases pending with
          | cons e rest =>
              cases h
              rfl
          | nil =>
              have happ := applySyncOp_conc (I := I) hI σ hsub h
              rw [List.map_reverse] at happ
              simp only [concC, concK, stepFn]
              rw [show (concV I v :: List.map (concV I) done)
                    = List.map (concV I) (v :: done) from rfl, happ]
              rfl
      | _ => exact stepFn'_conc hI σ ch h
  | opDone sched inner =>
      cases h
      rfl
  | _ => exact stepFn'_conc hI σ ch h

/-- The symbolic instance of the extended step (the refinement
theorem's per-step half; mirrors `stepFnS_sound`). -/
theorem stepFnST_sound (ρ : Valuation) (σ : ExecState) (ch : Choices)
    {T : TypeEnv} (hsub : SubTable T σ.types)
    {S : SymState} {C C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnST T S C = .ok (C₁, S₁)) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) :=
  stepFnT_conc (symInterp_sound ρ) σ ch hsub h

/-- **THE TABLE-CONDITIONED REFINEMENT THEOREM** — the shipped
template (`symEvalWindow_refines`) plus exactly one premise:
`SubTable T σ.types`. At `T = []` this IS the shipped theorem (via
`SubTable.nil`). -/
theorem symEvalWindowT_refines :
    ∀ {T : TypeEnv} {budget : Nat} {S : SymState} {C : SymConfig} {n : Nat}
      {S' : SymState} {C' : SymConfig},
      symEvalWindowT T budget S C = (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        SubTable T σ.types →
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S' , ch) := by
  intro T budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch hsub
      simp only [symEvalWindowT, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch hsub
      simp only [symEvalWindowT] at h
      rcases hstep : stepFnST T S C with q | ⟨C₁, S₁⟩ <;> rw [hstep] at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · simp only [] at h
        rcases hrec : symEvalWindowT T budget S₁ C₁ with ⟨m, S₂, C₂⟩
        rw [hrec] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := stepFnST_sound ρ σ ch hsub hstep
        simp only [stepFnIter, h1, Bind.bind, Except.bind]
        exact ih hrec ρ σ ch hsub

/-- The projection-form corollary (the emission seam; mirrors
`symEvalWindow_refines'`). -/
theorem symEvalWindowT_refines' {T : TypeEnv} {budget n : Nat}
    {S : SymState} {C : SymConfig}
    (hn : (symEvalWindowT T budget S C).1 = n)
    (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hsub : SubTable T σ.types) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (symEvalWindowT T budget S C).2.2,
          γS ρ σ (symEvalWindowT T budget S C).2.1, ch) :=
  symEvalWindowT_refines (by rw [← hn]) ρ σ ch hsub

/-! ## Slice-2 discharge witness (constitution §3.3): a lock/unlock
pair crossed IN-window — the sync arms exercised end to end on a
concrete mutex cell (the `#eval` check ran first: 12 steps, final
state unlocked — the standing rule). No table needed (`SubTable.nil`),
so this also witnesses the degenerate-instance claim. -/

def syncWitS : SymState :=
  { heap := [(.base ⟨0⟩, .mk (some (.sync .mutex)) (.syncData (.mutex false)))],
    nextAddr := 1 }

def syncWitC : SymConfig :=
  .exec (.seqn #[.syncStmt .lock #[.locLit (.base ⟨0⟩)] #[],
                 .syncStmt .unlock #[.locLit (.base ⟨0⟩)] #[]])
    [] (.seq [] [] .stop)

theorem syncWit_window_n : (symEvalWindowT [] 12 syncWitS syncWitC).1 = 12 := by
  rfl

/-- The transported lock/unlock window, ∀ρ ∀σ ∀ch — and the witness
that the sync arms' claims are not vacuous. -/
theorem syncWit_refines (ρ : Valuation) (σ : ExecState) (ch : Choices) :
    stepFnIter 12 (γS ρ σ syncWitS) (γC ρ syncWitC) ch
      = .ok (γC ρ (symEvalWindowT [] 12 syncWitS syncWitC).2.2,
          γS ρ σ (symEvalWindowT [] 12 syncWitS syncWitC).2.1, ch) :=
  symEvalWindowT_refines' syncWit_window_n ρ σ ch (SubTable.nil _)

/-- The window's post-heap: the mutex ends UNLOCKED (both ops ran). -/
theorem syncWit_final :
    (symEvalWindowT [] 12 syncWitS syncWitC).2.1.heap
      = [(.base ⟨0⟩, .mk (some (.sync .mutex)) (.syncData (.mutex false)))] := by
  rfl


/-! ## Slice 3 — call entry (design §3, class 2): ONE lever for fid
calls, closure call-values, deferred-call drains, and interface
dispatch, all through a mirrored `enterFrame` at an input TABLE PACK.

The delegation-vs-refactor decision (deferred at slice 1, decided
here from contact): DELEGATION AGAIN, LAYERED — `stepFnTB` overrides
the four call/drain configuration shapes and delegates everything
else to `stepFnT` (which delegates to the shipped `stepFn'`). The
override sets are disjoint config shapes, so the layers never
interleave; slice-1's theorems (and their weaker `SubTable`-only
premise, which store-only windows keep) survive verbatim. A refactor
into one step function is re-posed only if a future class needs to
interleave with an existing override.

The premise strengthens for THIS layer: `SymTables.Agrees` demands
table EQUALITY, not sub-table — alias-resolution walks
(`canonicalTy`, `resolveDefinedAliases`) return partial answers on a
MISS rather than failing, so a sub-table's miss is indistinguishable
from a genuine absence and equality is the honest condition
(recorded; the store layer keeps sub-table). -/

/-- The call-entry input pack. -/
structure SymTables where
  types : TypeEnv := []
  functions : Array Func := #[]
  methods : Array MethodInfo := #[]
  methodSets : Array MethodSetRecord := #[]

/-- The pack as a heapless machine state — the carrier the MACHINE'S
OWN table helpers run against inside the mirror (zero
re-implementation of the dispatch walks). -/
def SymTables.toState (TB : SymTables) : ExecState :=
  { types := TB.types, functions := TB.functions,
    methods := TB.methods, methodSets := TB.methodSets }

/-- Table agreement (equality on all four components — see the module
docstring for why not sub-table here). -/
def SymTables.Agrees (TB : SymTables) (σ : ExecState) : Prop :=
  σ.types = TB.types ∧ σ.functions = TB.functions
    ∧ σ.methods = TB.methods ∧ σ.methodSets = TB.methodSets

/-! ### Table-only congruence for the machine's dispatch helpers -/

theorem resolveDefinedAliasesFuel_types {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) :
    ∀ (fuel : Nat) (ty : Ty),
      resolveDefinedAliasesFuel fuel σ₁ ty
        = resolveDefinedAliasesFuel fuel σ₂ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; rfl
  | succ fuel ih =>
      intro ty
      cases ty <;> simp only [resolveDefinedAliasesFuel]
      next name =>
        rw [h]
        cases TypeEnv.lookup σ₂.types name with
        | none => rfl
        | some td => cases td <;> simp [ih]

theorem methodInfoByFuncId_tables {σ₁ σ₂ : ExecState}
    (h : σ₁.methods = σ₂.methods) (fid : FuncId) :
    methodInfoByFuncId? σ₁ fid = methodInfoByFuncId? σ₂ fid := by
  simp only [methodInfoByFuncId?, h]

theorem methodRecvInterfaceName_tables {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) (m : MethodInfo) :
    methodRecvInterfaceName? σ₁ m = methodRecvInterfaceName? σ₂ m := by
  simp only [methodRecvInterfaceName?, resolveDefinedAliases,
    resolveDefinedAliasesFuel_types h]

/-! ### The mirrored frame entry -/

/-- Mirror of `bindParams` at the pack's type table. -/
def bindParamsT (T : TypeEnv) :
    LocalEnv → State D → List Param → List (Value D) → M (LocalEnv × State D)
  | env, s, [], [] => .ok (env, s)
  | env, s, p :: ps, v :: vs => do
      let v' ← normalizeValueForTyT T p.typ v
      match s.alloc v' (some p.typ) with
      | (loc, s₁) => bindParamsT T (env.declare p.id loc) s₁ ps vs
  | _, _, [], _ :: _ => quit .q11Internal
  | _, _, _ :: _, [] => quit .q11Internal

/-- `pinResultLocs` is env-only; the machine's own function serves,
error-converted. -/
def pinResultLocs' (env : LocalEnv) (ps : List Param) : M (List Loc) :=
  match pinResultLocs env ps with
  | .ok locs => .ok locs
  | .error _ => quit .q11Internal

/-- Mirror of `dynamicDispatch?`, the census subset: the NON-dispatch
paths (a plain function, or a method with a concrete receiver — the
overwhelming bulk of the census: every raft/tracker/log method).
INTERFACE-receiver methods quit Q4 for now — the census path's single
interface call is the harness logger's empty `Infof`, one window
split per logging handler; the dispatch-walk congruence
(`canonicalTy` and the method-set fold under table agreement) is
where the cost lives, and it is recorded as the residual class 2b
rather than paid for one empty body (arc log). -/
def dynamicDispatchT (TB : SymTables) (func : Func) :
    M Unit :=
  match methodInfoByFuncId? TB.toState func.id with
  | none => .ok ()
  | some method =>
      match methodRecvInterfaceName? TB.toState method with
      | none => .ok ()
      | some _ => quit .q4Program

/-- Mirror of `enterFrame` at the pack (census subset — see
`dynamicDispatchT`). -/
def enterFrameT (TB : SymTables) (s : State D) (fid : FuncId)
    (args : List (Value D)) : M (Func × LocalEnv × List Loc × State D) := do
  let func ←
    match findFunctionIn? TB.functions fid with
    | some f => .ok f
    | none => quit .q4Program
  if func.args.size != args.length then quit .q11Internal
  else do
    let _ ← dynamicDispatchT TB func
    let (argsEnv, s₁) ← bindParamsT TB.types [] s func.args.toList args
    let (frameEnv, s₂) ← allocDecls' argsEnv s₁ func.results.toList
    let resultLocs ← pinResultLocs' frameEnv func.results.toList
    .ok (func, frameEnv, resultLocs, s₂)

/-! ### Call-entry soundness -/

theorem bindParamsT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (ps : List Param) (vs : List (Value D)) (env : LocalEnv) {s : State D}
      {env' : LocalEnv} {s' : State D},
      bindParamsT T env s ps vs = .ok (env', s') →
      bindParams env (concS I σ s) ps (vs.map (concV I))
        = .ok (env', concS I σ s') := by
  intro ps
  induction ps with
  | nil =>
      intro vs env s env' s' h
      cases vs with
      | nil =>
          simp only [bindParamsT] at h
          cases h
          simp [bindParams, pure, Except.pure]
      | cons a rest =>
          simp only [bindParamsT, quit] at h
          cases h
  | cons p ps ih =>
      intro vs env s env' s' h
      cases vs with
      | nil =>
          simp only [bindParamsT, quit] at h
          cases h
      | cons v vrest =>
          simp only [bindParamsT] at h
          obtain ⟨nv, hnv, h2⟩ := bind_eq_ok.mp h
          rcases halloc : s.alloc nv (some p.typ) with ⟨loc, s₁⟩
          rw [halloc] at h2
          simp only [List.map_cons, bindParams, bind_eq_ok]
          refine ⟨concV I nv, normalizeT_conc hI (concS I σ s) hsub hnv, ?_⟩
          rw [alloc_conc, halloc]
          exact ih _ _ h2

theorem dynamicDispatchT_conc (σ : ExecState)
    {TB : SymTables} (hag : TB.Agrees σ) {s : State D}
    {func : Func} (args : Array GoValue)
    (h : dynamicDispatchT TB func = Except.ok ()) :
    dynamicDispatch? (concS I σ s) func args = .ok none := by
  obtain ⟨ht, hf, hm, hms⟩ := hag
  have hmi := methodInfoByFuncId_tables (σ₁ := concS I σ s)
    (σ₂ := TB.toState) (by simp [concS, hm, SymTables.toState]) func.id
  simp only [dynamicDispatchT] at h
  revert h
  rcases hinfo : methodInfoByFuncId? TB.toState func.id with _ | method
  · intro _
    simp only [dynamicDispatch?, hmi, hinfo]
    rfl
  · have hri := methodRecvInterfaceName_tables (σ₁ := concS I σ s)
      (σ₂ := TB.toState) (by simp [concS, ht, SymTables.toState]) method
    rcases hrecv : methodRecvInterfaceName? TB.toState method with _ | iname
    · intro _
      simp only [dynamicDispatch?, hmi, hinfo, hri, hrecv]
      rfl
    · intro h
      simp only [hrecv] at h
      simp [quit] at h

/-- Frame entry transports (census subset), composing the table
congruences with the mirrored binding chain. -/
theorem enterFrameT_conc (hI : I.Sound) (σ : ExecState) {TB : SymTables}
    (hag : TB.Agrees σ) {s : State D} {fid : FuncId} {args : List (Value D)}
    {func : Func} {env : LocalEnv} {locs : List Loc} {s' : State D}
    (h : enterFrameT TB s fid args = .ok (func, env, locs, s')) :
    enterFrame (concS I σ s) fid (args.map (concV I))
      = .ok (func, env, locs, concS I σ s') := by
  have hf : (concS I σ s).functions = TB.functions := by
    simp [concS, hag.2.1]
  simp only [enterFrameT] at h
  revert h
  rcases hfind : findFunctionIn? TB.functions fid with _ | f0
  · intro h
    simp [quit, Bind.bind, Except.bind] at h
  · intro h
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    by_cases harity : (f0.args.size != args.length) = true
    · rw [if_pos harity] at h
      simp [quit] at h
    · rw [if_neg harity] at h
      obtain ⟨u, hdisp, h2⟩ := bind_eq_ok.mp h
      obtain ⟨⟨argsEnv, s₁⟩, hbind, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨⟨frameEnv, s₂⟩, halloc, h4⟩ := bind_eq_ok.mp h3
      obtain ⟨rlocs, hpin, h5⟩ := bind_eq_ok.mp h4
      cases h5
      have harityF : (func.args.size != args.length) = false := by
        simpa using harity
      have hdc := dynamicDispatchT_conc (I := I) σ hag (s := s)
        ((args.map (concV I)).toArray) hdisp
      have hb := bindParamsT_conc (I := I) hI σ (SubTable.of_eq hag.1)
        func.args.toList args [] hbind
      have hal := allocDecls_conc (I := I) hI σ _ _ halloc
      have hpinM : pinResultLocs frameEnv func.results.toList
          = .ok locs := by
        revert hpin
        simp only [pinResultLocs']
        rcases pinResultLocs frameEnv func.results.toList with e | ls
        · intro hpin
          simp [quit] at hpin
        · intro hpin
          cases hpin
          rfl
      simp only [enterFrame, hf, hfind, Bind.bind, Except.bind, pure,
        Except.pure, List.length_map, harityF, hdc, hb, hal, hpinM,
        Bool.false_eq_true, if_false]

/-- The class-2 layered step: the four call/drain configuration
shapes through `enterFrameT`; EVERYTHING else delegates to the
slice-1/2 `stepFnT` (which delegates to the shipped `stepFn'`). The
layers never interleave — the override sets are disjoint config
shapes (the deferred delegation-vs-refactor decision, resolved:
delegation again; see the slice-3 docstring above). -/
def stepFnTB (TB : SymTables) (s : State D) (c : Config D) :
    M (Config D × State D) :=
  match c with
  | .retV v (.callArgsK fid plans vals pending env k') =>
      (match pending with
       | a :: rest =>
           .ok (.evalE a env
             (.callArgsK fid plans (vals ++ [v]) rest env k'), s)
       | [] => do
           let (func, frameEnv, resultLocs, s') ←
             enterFrameT TB s fid (vals ++ [v])
           .ok (.exec func.body frameEnv
             (.frame plans env resultLocs [] k' func.wrapper), s'))
  | .retV v (.callValArgsK cv plans vals pending env k') =>
      (match pending with
       | a :: rest =>
           .ok (.evalE a env
             (.callValArgsK cv plans (vals ++ [v]) rest env k'), s)
       | [] =>
           match cv with
           | .funcVal fid captured => do
               let (func, frameEnv, resultLocs, s') ←
                 enterFrameT TB s fid (captured ++ vals ++ [v])
               .ok (.exec func.body frameEnv
                 (.frame plans env resultLocs [] k' func.wrapper), s')
           | .nil => quit .q6Panic
           | .atom _ => quit .q10Atom
           | _ => quit .q11Internal)
  | .next (.frame targets tenv results ((cv, dargs) :: ds) k' w) =>
      (match cv with
       | .funcVal fid captured => do
           let (func, frameEnv, _, s') ←
             enterFrameT TB s fid (captured ++ dargs)
           .ok (.exec func.body frameEnv
             (.frame [] [] [] []
               (.frame targets tenv results ds k' w) func.wrapper), s')
       | .nil => quit .q6Panic
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .returning (.frame targets tenv results ((cv, dargs) :: ds) k' w) =>
      (match cv with
       | .funcVal fid captured => do
           let (func, frameEnv, _, s') ←
             enterFrameT TB s fid (captured ++ dargs)
           .ok (.exec func.body frameEnv
             (.frame [] [] [] []
               (.frame targets tenv results ds k' w) func.wrapper), s')
       | .nil => quit .q6Panic
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | c => stepFnT TB.types s c

/-- The layered step transports (the class-2 arms via
`enterFrameT_conc`; the pending-cons operand steps structurally;
everything else via the slice-1/2 `stepFnT_conc`). -/
theorem stepFnTB_conc (hI : I.Sound) (σ : ExecState) (ch : Choices)
    {TB : SymTables} (hag : TB.Agrees σ)
    {s : State D} {c : Config D} {c₁ : Config D} {s₁ : State D}
    (h : stepFnTB TB s c = .ok (c₁, s₁)) :
    stepFn (concS I σ s) (concC I c) ch
      = .ok (concC I c₁, concS I σ s₁, ch) := by
  have hsub : SubTable TB.types σ.types := SubTable.of_eq hag.1
  cases c with
  | retV v k =>
      cases k with
      | callArgsK fid plans vals pending env k' =>
          simp only [stepFnTB] at h
          cases pending with
          | cons a rest =>
              cases h
              simp [concC, concK, stepFn, List.map_append]
          | nil =>
              obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                bind_eq_ok.mp h
              cases h2
              have hef := enterFrameT_conc (I := I) hI σ hag hent
              simp only [concC, concK, stepFn, enterFrameStep,
                List.map_append, List.map_cons, List.map_nil] at hef ⊢
              rw [hef]
      | callValArgsK cv plans vals pending env k' =>
          simp only [stepFnTB] at h
          cases pending with
          | cons a rest =>
              cases h
              simp [concC, concK, stepFn, List.map_append]
          | nil =>
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | next k =>
      cases k with
      | frame targets tenv results defers k' w =>
          cases defers with
          | nil => exact stepFnT_conc hI σ ch hsub h
          | cons d ds =>
              obtain ⟨cv, dargs⟩ := d
              simp only [stepFnTB] at h
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | returning k =>
      cases k with
      | frame targets tenv results defers k' w =>
          cases defers with
          | nil => exact stepFnT_conc hI σ ch hsub h
          | cons d ds =>
              obtain ⟨cv, dargs⟩ := d
              simp only [stepFnTB] at h
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | _ => exact stepFnT_conc hI σ ch hsub h

/-- The layered step at the symbolic domain. -/
def stepFnSTB (TB : SymTables) (S : SymState) (C : SymConfig) :
    M (SymConfig × SymState) :=
  stepFnTB TB S C

theorem stepFnSTB_sound (ρ : Valuation) (σ : ExecState) (ch : Choices)
    {TB : SymTables} (hag : TB.Agrees σ)
    {S : SymState} {C C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnSTB TB S C = .ok (C₁, S₁)) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) :=
  stepFnTB_conc (symInterp_sound ρ) σ ch hag h

/-- The class-2 window driver. -/
def symEvalWindowTB (TB : SymTables) :
    Nat → SymState → SymConfig → Nat × SymState × SymConfig
  | 0, S, C => (0, S, C)
  | budget + 1, S, C =>
      match stepFnSTB TB S C with
      | .error _ => (0, S, C)
      | .ok (C', S') =>
          let (n, S'', C'') := symEvalWindowTB TB budget S' C'
          (n + 1, S'', C'')

/-- **THE PACK-CONDITIONED REFINEMENT THEOREM** — the shipped
template + the `SymTables.Agrees` premise (equality on the four
tables; see the slice-3 docstring for why not sub-table). -/
theorem symEvalWindowTB_refines :
    ∀ {TB : SymTables} {budget : Nat} {S : SymState} {C : SymConfig}
      {n : Nat} {S' : SymState} {C' : SymConfig},
      symEvalWindowTB TB budget S C = (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        TB.Agrees σ →
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S', ch) := by
  intro TB budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch hag
      simp only [symEvalWindowTB, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch hag
      simp only [symEvalWindowTB] at h
      rcases hstep : stepFnSTB TB S C with q | ⟨C₁, S₁⟩ <;> rw [hstep] at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · simp only [] at h
        rcases hrec : symEvalWindowTB TB budget S₁ C₁ with ⟨m, S₂, C₂⟩
        rw [hrec] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := stepFnSTB_sound ρ σ ch hag hstep
        simp only [stepFnIter, h1, Bind.bind, Except.bind]
        exact ih hrec ρ σ ch hag

/-- The projection-form corollary at the pack. -/
theorem symEvalWindowTB_refines' {TB : SymTables} {budget n : Nat}
    {S : SymState} {C : SymConfig}
    (hn : (symEvalWindowTB TB budget S C).1 = n)
    (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : TB.Agrees σ) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (symEvalWindowTB TB budget S C).2.2,
          γS ρ σ (symEvalWindowTB TB budget S C).2.1, ch) :=
  symEvalWindowTB_refines (by rw [← hn]) ρ σ ch hag

end GoLean.Sym
