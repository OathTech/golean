import GoLeanProofs.Sym.Drift

/-!
# Drift/commutation helper layer, tranche 2 (WP arc slice 4, phase 2)

The remaining LAYER-2 helpers from the S4.4 park inventory
(`docs/wp-arc-log/s4.md`), success-only over any sound interpretation
(`… = .ok r → machine = .ok (conc r)`; quit outcomes assert nothing):
the decided equality family, the self-normalization family, key
hashability, closed-int ops, conversion, declaration allocation, and the
map-entry machinery. The loop transports and the strict/wide apply
tables live in `Sym/DriftApply.lean`; the master walk consumes both in
`Sym/Walk.lean`.

Proof-shape note (new in this tranche): wide multi-discriminant mirror
matches are dismantled with `split at h` — one goal per COMPILED arm —
rather than the constructor bash the two-discriminant helpers use; the
quit arms refute uniformly and only the success arms touch the machine.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

/-! ## Target-ref completion (hoisted from the spike per the park
record, generalized to any interpretation) -/

theorem completeRef_conc (I : Interp D) (sh : TargetShape)
    (vs : List (Value D)) :
    completeTargetRef sh (vs.map (concV I))
      = (completeTargetRef' sh vs).map (concRef I) := by
  cases sh with
  | chain steps =>
      cases vs with
      | nil => rfl
      | cons a rest =>
          simp only [List.map_cons, completeTargetRef, completeTargetRef',
            List.length_map]
          by_cases hlen : rest.length = indexStepCount steps
          · rw [if_pos hlen, if_pos hlen]
            rfl
          · rw [if_neg hlen, if_neg hlen]
            rfl
  | mapElem kt vt =>
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp [completeTargetRef, completeTargetRef', concRef]

/-! ## The decided equality family -/

theorem valueEqListWith_conc {f : Value D → Value D → M Bool}
    {g : GoValue → GoValue → Except GoError Bool}
    (hf : ∀ l r b, f l r = .ok b → g (concV I l) (concV I r) = .ok b) :
    ∀ (ls rs : List (Value D)) {b : Bool},
      valueEqListWith' f ls rs = .ok b →
      valueEqListWith g (ls.map (concV I)) (rs.map (concV I)) = .ok b := by
  intro ls
  induction ls with
  | nil =>
      intro rs b h
      cases rs <;> simp_all [valueEqListWith', valueEqListWith]
  | cons l lrest ih =>
      intro rs b h
      cases rs with
      | nil => simp_all [valueEqListWith', valueEqListWith]
      | cons r rrest =>
          simp only [valueEqListWith', bind_eq_ok] at h
          obtain ⟨hit, hhit, h2⟩ := h
          simp only [List.map_cons, valueEqListWith, bind_eq_ok]
          refine ⟨hit, hf _ _ _ hhit, ?_⟩
          cases hit with
          | true => simpa using ih _ h2
          | false => simpa using h2

set_option maxHeartbeats 3200000 in
theorem valueEqBFuel_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (l r : Value D) {b : Bool},
      valueEqBFuel' fuel ty l r = .ok b →
      valueEqFuel fuel σ ty (concV I l) (concV I r) = .ok b := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty l r b h
      simp [valueEqBFuel', quit] at h
  | succ fuel ih =>
      intro ty l r b h
      cases ty with
      | bool =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case bool.bool lb rb =>
            rcases hlb : D.toBool? lb with _ | l0 <;> rw [hlb] at h
            · cases h
            rcases hrb : D.toBool? rb with _ | r0 <;> rw [hrb] at h
            · cases h
            cases h
            simp [valueEqFuel, hI.toBool? _ _ hlb, hI.toBool? _ _ hrb,
              pure, Except.pure]
      | int kind =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case int.int lv lk rv rk =>
            rcases hlv : D.toInt? lv with _ | l0 <;> rw [hlv] at h
            · cases h
            rcases hrv : D.toInt? rv with _ | r0 <;> rw [hrv] at h
            · cases h
            cases h
            simp [valueEqFuel, hI.toInt? _ _ hlv, hI.toInt? _ _ hrv,
              pure, Except.pure]
      | float kind =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case float.float lb lk rb rk =>
            by_cases hk : (lk == kind && rk == kind) = true
            · rw [if_pos hk] at h
              cases kind <;> cases h <;>
                simp [valueEqFuel, hk, pure, Except.pure]
            · rw [if_neg hk] at h
              cases h
      | string =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case string.string ls rs =>
            cases h
            simp [valueEqFuel, pure, Except.pure]
      | funcType args results =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          all_goals (cases h; simp [valueEqFuel, pure, Except.pure])
      | pointer inner =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          all_goals (cases h; simp [valueEqFuel, pure, Except.pure])
      | array length elem =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case array.array left right =>
            by_cases hsl : (left.size != length) = true
            · rw [if_pos hsl] at h
              cases h
            · rw [if_neg hsl] at h
              by_cases hsr : (right.size != length) = true
              · rw [if_pos hsr] at h
                cases h
              · rw [if_neg hsr] at h
                have := valueEqListWith_conc (I := I)
                  (fun l r b hb => ih elem l r hb) left.toList right.toList h
                simp only [concV_array, valueEqFuel]
                rw [if_neg (by simp_all), if_neg (by simp_all)]
                simpa [Array.toList_map, Bind.bind, Except.bind] using this
      | slice elem =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case slice.slice left right =>
            rcases hvl : validateSlice' left with e | u <;> rw [hvl] at h
            · cases h
            obtain ⟨⟩ := u
            rcases hvr : validateSlice' right with e | u <;> rw [hvr] at h
            · cases h
            obtain ⟨⟩ := u
            simp only [Bind.bind, Except.bind] at h
            simp only [concV_slice, valueEqFuel, Bind.bind, Except.bind,
              validateSlice_conc hvl, validateSlice_conc hvr]
            rcases hlb : left.base with _ | lb <;>
              rcases hrb : right.base with _ | rb <;>
              (try rw [hlb] at h) <;> (try rw [hrb] at h) <;>
              first
                | (cases h; done)
                | (cases h; simp [pure, Except.pure])
          case slice.nil left =>
            rcases hvl : validateSlice' left with e | u <;> rw [hvl] at h
            · cases h
            obtain ⟨⟩ := u
            simp only [Bind.bind, Except.bind] at h
            cases h
            simp [valueEqFuel, Bind.bind, Except.bind,
              validateSlice_conc hvl, pure, Except.pure]
          case nil.slice right =>
            rcases hvr : validateSlice' right with e | u <;> rw [hvr] at h
            · cases h
            obtain ⟨⟩ := u
            simp only [Bind.bind, Except.bind] at h
            cases h
            simp [valueEqFuel, Bind.bind, Except.bind,
              validateSlice_conc hvr, pure, Except.pure]
      | map keyTy valTy =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          case map.map left right =>
            rcases hlb : left.base with _ | lb <;>
              rcases hrb : right.base with _ | rb <;>
              rw [hlb, hrb] at h <;>
              first
                | (cases h; done)
                | (cases h; simp [valueEqFuel, hlb, hrb, pure, Except.pure])
          case map.nil left =>
            cases h; simp [valueEqFuel, pure, Except.pure]
          case nil.map right =>
            cases h; simp [valueEqFuel, pure, Except.pure]
      | chan dir elem =>
          cases l <;> cases r <;>
            simp only [valueEqBFuel', quit] at h <;> try (cases h; done)
          all_goals (cases h; simp [valueEqFuel, pure, Except.pure])
      | interface name => simp [valueEqBFuel', quit] at h
      | sync kind => simp [valueEqBFuel', quit] at h
      | defined name => simp [valueEqBFuel', quit] at h
      | unsupported feature => simp [valueEqBFuel', quit] at h

@[inherit_doc valueEqBFuel_conc]
theorem valueEqB_conc (hI : I.Sound) (σ : ExecState) {ty : Ty}
    {l r : Value D} {b : Bool} (h : valueEqB' ty l r = .ok b) :
    valueEq σ ty (concV I l) (concV I r) = .ok b := by
  simp only [valueEq]
  exact valueEqBFuel_conc hI σ _ ty l r h

/-- The value-producing equality (`eqCmp`/`neqCmp`): int operands form
`eqI` terms; everything else routes through the decided family. -/
theorem valueEqR_conc (hI : I.Sound) (σ : ExecState) {ty : Ty}
    {l r : Value D} {b : D.BoolR} (h : valueEqR' ty l r = .ok b) :
    valueEq σ ty (concV I l) (concV I r) = .ok (I.boolV b) := by
  unfold valueEqR' at h
  split at h
  · -- int former arm
    cases h
    simp only [concV_int, valueEq]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [valueEqFuel, hI.eqI, pure, Except.pure]
  · -- decided-family arm
    simp only [bind_eq_ok] at h
    obtain ⟨b0, hb0, h2⟩ := h
    cases h2
    rw [valueEqB_conc hI σ hb0, hI.litB]

/-! ## The self-normalization family -/

theorem isNormalListWith_conc {f : Value D → M Bool} {g : GoValue → Bool}
    (hf : ∀ v b, f v = .ok b → g (concV I v) = b) :
    ∀ (l : List (Value D)) {b : Bool},
      isNormalListWith' f l = .ok b →
      isNormalListWith g (l.map (concV I)) = b := by
  intro l
  induction l with
  | nil =>
      intro b h
      simp only [isNormalListWith'] at h
      cases h
      simp [isNormalListWith]
  | cons v rest ih =>
      intro b h
      simp only [isNormalListWith', bind_eq_ok] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [List.map_cons, isNormalListWith, hf _ _ hbv]
      cases bv with
      | true => simpa using ih h2
      | false =>
          cases h2
          simp

set_option maxHeartbeats 3200000 in
theorem isNormalFuel_conc (hI : I.Sound) (types : TypeEnv) :
    ∀ (fuel : Nat) (ty : Ty) (v : Value D) {b : Bool},
      isNormalForTyFuel' fuel ty v = .ok b →
      isNormalForTyFuel fuel types ty (concV I v) = b := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v b h
      simp only [isNormalForTyFuel'] at h
      cases h
      rfl
  | succ fuel ih =>
      intro ty v b h
      cases ty <;>
        try (cases v <;>
             simp_all [isNormalForTyFuel', isNormalForTyFuel, quit] <;>
             done)
      case int kind =>
        cases v <;>
          simp only [isNormalForTyFuel', quit] at h <;>
          first
            | (cases h; done)
            | (cases h; simp [isNormalForTyFuel]; done)
            | skip
        case int value k =>
          rcases hv : D.toInt? value with _ | n <;> rw [hv] at h
          · cases h
          cases h
          simp [isNormalForTyFuel, hI.toInt? _ _ hv]
      case array length elem =>
        cases v <;>
          simp only [isNormalForTyFuel', quit] at h <;>
          first
            | (cases h; done)
            | (cases h; simp [isNormalForTyFuel]; done)
            | skip
        case array values =>
          by_cases hs : values.size = length
          · rw [if_pos hs] at h
            have := isNormalListWith_conc (I := I)
              (fun v b hb => ih elem v hb) values.toList h
            simp only [concV_array, isNormalForTyFuel, Array.size_map,
              Array.toList_map]
            simp [hs, this]
          · rw [if_neg hs] at h
            cases h
            simp [isNormalForTyFuel, hs]

@[inherit_doc isNormalFuel_conc]
theorem isNormal_conc (hI : I.Sound) (types : TypeEnv) {ty : Ty}
    {v : Value D} {b : Bool} (h : isNormalForTy' ty v = .ok b) :
    isNormalForTy types ty (concV I v) = b := by
  simp only [isNormalForTy]
  exact isNormalFuel_conc hI types _ ty v h

/-! ## Key hashability -/

theorem hashabilityFuel_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (fuel : Nat) (v : Value D) {b : Bool},
      valueHashabilityFuel' fuel v = .ok b →
      b = true ∧ valueHashability σ (concV I v) = .hashable := by
  intro fuel
  induction fuel with
  | zero =>
      intro v b h
      simp [valueHashabilityFuel', quit] at h
  | succ fuel ih =>
      have hlist : ∀ (l : List (Value D)) {b : Bool},
          hashabilityListWith' (valueHashabilityFuel' fuel) l = .ok b →
          b = true ∧ valueHashabilityList σ (l.map (concV I)) = .hashable := by
        intro l
        induction l with
        | nil =>
            intro b h
            simp only [hashabilityListWith'] at h
            cases h
            exact ⟨rfl, rfl⟩
        | cons v rest ihl =>
            intro b h
            simp only [hashabilityListWith', bind_eq_ok] at h
            obtain ⟨bv, hbv, h2⟩ := h
            obtain ⟨rfl, hmv⟩ := ih v hbv
            rw [if_pos rfl] at h2
            obtain ⟨rfl, hml⟩ := ihl h2
            refine ⟨rfl, ?_⟩
            simp [valueHashabilityList, hmv, hml]
      have hfields : ∀ (fs : List (String × Value D)) {b : Bool},
          hashabilityListWith' (valueHashabilityFuel' fuel)
              (fs.map Prod.snd) = .ok b →
          b = true ∧ valueHashabilityFields σ
              (fs.map (fun p => (p.1, concV I p.2))) = .hashable := by
        intro fs
        induction fs with
        | nil =>
            intro b h
            simp only [List.map_nil, hashabilityListWith'] at h
            cases h
            exact ⟨rfl, rfl⟩
        | cons p rest ihf =>
            intro b h
            simp only [List.map_cons, hashabilityListWith', bind_eq_ok] at h
            obtain ⟨bv, hbv, h2⟩ := h
            obtain ⟨rfl, hmv⟩ := ih p.2 hbv
            rw [if_pos rfl] at h2
            obtain ⟨rfl, hml⟩ := ihf h2
            refine ⟨rfl, ?_⟩
            simp [valueHashabilityFields, hmv, hml]
      intro v b h
      cases v <;>
        simp only [valueHashabilityFuel', quit] at h <;>
        first
          | (cases h; done)
          | (cases h; exact ⟨rfl, by simp [valueHashability]⟩)
          | skip
      case struct tid fields =>
        obtain ⟨rfl, hm⟩ := hfields fields.toList h
        refine ⟨rfl, ?_⟩
        simp only [concV_struct, valueHashability]
        rw [Array.toList_map]
        exact hm
      case array values =>
        obtain ⟨rfl, hm⟩ := hlist values.toList h
        refine ⟨rfl, ?_⟩
        simp only [concV_array, valueHashability]
        rw [Array.toList_map]
        exact hm

/-- Hashability precheck commutation, for EVERY flag pair — the machine
flags only pick the panic message, and the success path ignores them. -/
theorem checkKeyHashable_conc (hI : I.Sound) (σ : ExecState)
    {key : Value D} (h : checkKeyHashable' key = .ok ())
    (isInsert nonEmpty : Bool) :
    checkKeyHashable σ (concV I key) isInsert nonEmpty = .ok () := by
  simp only [checkKeyHashable', valueHashability', bind_eq_ok] at h
  obtain ⟨b, hb, h2⟩ := h
  obtain ⟨rfl, hm⟩ := hashabilityFuel_conc hI σ _ key hb
  simp [checkKeyHashable, hm, pure, Except.pure]

/-! ## Closed-int ops (bitwise/shift: both operands close, the GoCore
helper computes, the result re-injects as a literal) -/

theorem closedIntOp_conc (hI : I.Sound)
    {lift : Int → IntKind → Int → IntKind → Except GoError GoValue}
    {l r out : Value D} (h : closedIntOp lift l r = .ok out) :
    ∃ lv lk rv rk, concV I l = .int lv lk ∧ concV I r = .int rv rk ∧
      lift lv lk rv rk = .ok (concV I out) := by
  cases l <;> cases r <;>
    simp only [closedIntOp, quit] at h <;> try (cases h; done)
  case int.int lv lk rv rk =>
    rcases hlv : D.toInt? lv with _ | l0 <;> rw [hlv] at h
    · cases h
    rcases hrv : D.toInt? rv with _ | r0 <;> rw [hrv] at h
    · cases h
    simp only [] at h
    refine ⟨l0, lk, r0, rk, by simp [hI.toInt? _ _ hlv],
      by simp [hI.toInt? _ _ hrv], ?_⟩
    rcases hlift : lift l0 lk r0 rk with e | gv <;> rw [hlift] at h
    · rcases e <;> cases h
    · cases gv <;> try (cases h; done)
      next n kind =>
        cases h
        simp [hI.litI]

/-- Decided `<` (the `min`/`max`/`sortSlice` inspection). -/
theorem valueLessB_conc (hI : I.Sound) {l r : Value D} {b : Bool}
    (h : valueLessB' l r = .ok b) :
    valueLess (concV I l) (concV I r) = .ok b := by
  simp only [valueLessB', bind_eq_ok] at h
  obtain ⟨bR, hbR, h2⟩ := h
  rcases ht : D.toBool? bR with _ | bb <;> rw [ht] at h2
  · simp only [quit] at h2; cases h2
  · cases h2
    rw [valueLess_conc hI hbR, hI.toBool? _ _ ht]

/-! ## Float binary results (concrete payloads) -/

theorem floatBinary_conc {op64 op32 : Nat → Nat → Nat}
    {l r out : Value D} (name : String)
    (h : floatBinaryResult' op64 op32 l r = .ok out) :
    floatBinaryResult name op64 op32 (concV I l) (concV I r)
      = .ok (concV I out) := by
  cases l <;> cases r <;>
    simp only [floatBinaryResult', quit] at h <;> try (cases h; done)
  case float.float lb lk rb rk =>
    by_cases hk : (lk == rk) = true
    · rw [if_pos hk] at h
      cases lk <;> cases h <;>
        simp_all [floatBinaryResult, pure, Except.pure]
    · rw [if_neg hk] at h
      cases h

/-! ## Conversion -/

set_option maxHeartbeats 3200000 in
theorem convertFuel_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (v out : Value D),
      convertValueToTyFuel' fuel ty v = .ok out →
      convertValueToTyFuel fuel σ ty (concV I v) = .ok (concV I out) := by
  intro fuel ty v out h
  cases ty
  case int kind =>
    cases v <;> simp only [convertValueToTyFuel', quit] at h <;>
      try (cases h; done)
    case int value k =>
      cases h
      simp [convertValueToTyFuel, hI.norm, pure, Except.pure]
    case float bits fk =>
      cases fk with
      | float64 =>
          simp only [convertValueToTyFuel'] at h
          rcases hn : FloatBits.f64truncInt? bits with _ | n <;>
            rw [hn] at h <;> simp only [] at h
          · cases h
          by_cases hfit : (kind.normalize n == n) = true
          · rw [if_pos hfit] at h
            cases h
            simp [convertValueToTyFuel, hn, hfit, hI.litI,
              pure, Except.pure]
          · rw [if_neg hfit] at h
            cases h
      | float32 =>
          simp only [convertValueToTyFuel'] at h
          rcases hn : FloatBits.f32truncInt? bits with _ | n <;>
            rw [hn] at h <;> simp only [] at h
          · cases h
          by_cases hfit : (kind.normalize n == n) = true
          · rw [if_pos hfit] at h
            cases h
            simp [convertValueToTyFuel, hn, hfit, hI.litI,
              pure, Except.pure]
          · rw [if_neg hfit] at h
            cases h
  case float kind =>
    cases v <;> simp only [convertValueToTyFuel', quit] at h <;>
      try (cases h; done)
    case float bits fk =>
      cases kind <;> cases fk <;> cases h <;>
        simp [convertValueToTyFuel, pure, Except.pure]
    case int value k =>
      rcases hv : D.toInt? value with _ | n <;> rw [hv] at h
      · cases h
      cases h
      simp [convertValueToTyFuel, hI.toInt? _ _ hv, hI.litI,
        pure, Except.pure]
  case defined name =>
    cases fuel <;> simp [convertValueToTyFuel', quit] at h
  all_goals
    (cases v <;> simp only [convertValueToTyFuel', quit] at h <;>
      first
        | (cases h; done)
        | (cases h; simp [convertValueToTyFuel, pure, Except.pure]; done)
        | skip)

@[inherit_doc convertFuel_conc]
theorem convert_conc (hI : I.Sound) (σ : ExecState) {ty : Ty}
    {v out : Value D} (h : convertValueToTy' ty v = .ok out) :
    convertValueToTy σ ty (concV I v) = .ok (concV I out) := by
  simp only [convertValueToTy]
  exact convertFuel_conc hI σ _ ty v out h

/-! ## Declaration allocation -/

theorem allocDecls_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (ps : List Param) (env : LocalEnv) {s : State D}
      {env' : LocalEnv} {s' : State D},
      allocDecls' env s ps = .ok (env', s') →
      allocDecls env (concS I σ s) ps = .ok (env', concS I σ s') := by
  intro ps
  induction ps with
  | nil =>
      intro env s env' s' h
      simp only [allocDecls'] at h
      cases h
      simp [allocDecls, pure, Except.pure]
  | cons p rest ih =>
      intro env s env' s' h
      simp only [allocDecls', bind_eq_ok] at h
      obtain ⟨v, hv, h2⟩ := h
      rcases halloc : s.alloc v (some p.typ) with ⟨loc, s₁⟩
      rw [halloc] at h2
      simp only [allocDecls, bind_eq_ok]
      refine ⟨concV I v, default_conc hI (concS I σ s) hv, ?_⟩
      rw [alloc_conc, halloc]
      exact ih _ h2

/-! ## Map entries -/

/-- The image of a mirror entry array under concretization. -/
abbrev concEntries (I : Interp D) (es : Array (Value D × Value D)) :
    Array (GoValue × GoValue) :=
  es.map (fun q => (concV I q.1, concV I q.2))

theorem mapEntries_conc (σ : ExecState) {s : State D} {map : MapValue}
    {r : Option (Loc × Array (Value D × Value D))}
    (h : mapEntries' s map = .ok r) :
    mapEntries (concS I σ s) map
      = .ok (r.map (fun p => (p.1, concEntries I p.2))) := by
  rcases hb : map.base with _ | baseLoc <;>
    simp only [mapEntries', hb] at h
  · cases h
    simp [mapEntries, hb, pure, Except.pure]
  · simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h2⟩ := h
    simp only [mapEntries, hb, bind_eq_ok]
    refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
    cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
    next entries =>
      cases h2
      simp [concV_mapData, concEntries, pure, Except.pure]

/-! ## The mapRange start family (BUG-005 (L): base + start keys; the
snapshot transports are retired with the snapshot itself) -/

theorem mapRangeStartSets_conc (σ : ExecState) {s : State D} {v : Value D}
    {bs : Option Loc × Array (Value D)}
    (h : mapRangeStartSets' s v = .ok bs) :
    mapRangeStartSets (concS I σ s) (concV I v)
      = .ok (bs.1, bs.2.map (concV I)) := by
  simp only [mapRangeStartSets', bind_eq_ok] at h
  obtain ⟨map, hmap, h2⟩ := h
  simp only [mapRangeStartSets, bind_eq_ok]
  refine ⟨map, asMap_conc hmap, ?_⟩
  rcases hb : map.base with _ | base <;> rw [hb] at h2
  · cases h2
    simp [pure, Except.pure]
  · simp only [bind_eq_ok] at h2
    obtain ⟨bv, hbv, h3⟩ := h2
    simp only [bind_eq_ok]
    refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
    cases bv <;> simp only [quit] at h3 <;> try (cases h3; done)
    next entries =>
      cases h3
      simp [concV_mapData, pure, Except.pure, Array.map_map, Function.comp]

/-! ## Loop transports (the `forIn` shapes of the mirrored op-table
loops; `forIn_conc` in `Sym/Drift.lean` is the mapped-list base) -/

/-- `forIn_conc` at the SAME element list (range loops and loops whose
elements are concrete on both sides). -/
theorem forInR_conc {A β β' : Type} {R : β → β' → Prop}
    {f : A → β → M (ForInStep β)}
    {g : A → β' → Except GoError (ForInStep β')} :
    ∀ {l : List A} {x : β} {y : β'}, R x y →
      (∀ a ∈ l, ∀ x y, R x y → ∀ st, f a x = .ok st →
        ∃ st', g a y = .ok st' ∧ StepConc R st st') →
      ∀ {out : β}, forIn l x f = .ok out →
        ∃ out', forIn l y g = .ok out' ∧ R out out' := by
  intro l x y hR hstep out h
  have := forIn_conc (t := (id : A → A)) hR
    (by simpa using hstep) h
  simpa using this

/-- Same-STATE loop transport (mapped elements, shared state type,
bodies agreeing on success) — `refine`-able directly against a machine
loop goal, which is what the master walk's loop arms use. -/
theorem forIn_conc_id {A B β : Type} {t : A → B}
    {f : A → β → M (ForInStep β)}
    {g : B → β → Except GoError (ForInStep β)} :
    ∀ {l : List A} {x : β},
      (∀ a ∈ l, ∀ x st, f a x = .ok st → g (t a) x = .ok st) →
      ∀ {out : β}, forIn l x f = .ok out →
        forIn (l.map t) x g = .ok out := by
  intro l
  induction l with
  | nil =>
      intro x _ out h
      simp only [List.forIn_nil] at h
      have hx : out = x := by simpa [pure, Except.pure, eq_comm] using h
      subst hx
      simp [List.forIn_nil, pure, Except.pure]
  | cons a as ih =>
      intro x hstep out h
      simp only [List.forIn_cons, bind_eq_ok] at h
      obtain ⟨st, hst, hrest⟩ := h
      simp only [List.map_cons, List.forIn_cons]
      refine bind_eq_ok.mpr ⟨st, hstep a List.mem_cons_self x st hst, ?_⟩
      cases st with
      | done b =>
          have hb : out = b := by
            simpa [pure, Except.pure, eq_comm] using hrest
          subst hb
          rfl
      | yield b =>
          exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha'))
            hrest

/-- Visible slice elements, transported (the first range-loop
consumer). -/
theorem sliceVisible_conc (σ : ExecState) {s : State D}
    {slice : SliceValue} {vs : Array (Value D)}
    (h : sliceVisibleValues' s slice = .ok vs) :
    sliceVisibleValues (concS I σ s) slice = .ok (vs.map (concV I)) := by
  unfold sliceVisibleValues' at h
  unfold sliceVisibleValues
  rcases hval : validateSlice' slice with e | u <;> rw [hval] at h
  · exact absurd h (by simp [Bind.bind, Except.bind])
  obtain ⟨⟩ := u
  obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
  obtain ⟨r, hloop, hr⟩ := bind_eq_ok.mp h
  have hrvs : r = vs := by simpa [pure, Except.pure] using hr
  subst hrvs
  refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval, ?_⟩
  refine bind_eq_ok.mpr ⟨r.map (concV I), ?_, rfl⟩
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop ⊢
  have hbody : ∀ i ∈ List.range' (Std.Legacy.Range.mk 0 slice.len 1 (by decide)).start
      (Std.Legacy.Range.mk 0 slice.len 1 (by decide)).size
      (Std.Legacy.Range.mk 0 slice.len 1 (by decide)).step,
      ∀ (x : Array (Value D)) (y : Array GoValue),
      y = x.map (concV I) → ∀ st,
      (do
        let loc ← sliceIndexLoc' slice (Int.ofNat i)
        let v ← loadLoc' s loc
        pure PUnit.unit
        pure (ForInStep.yield (x.push v))) = .ok st →
      ∃ st', (do
        let loc ← sliceIndexLoc slice (Int.ofNat i)
        let v ← loadLoc (concS I σ s) loc
        pure PUnit.unit
        pure (ForInStep.yield (y.push v))) = .ok st' ∧
        StepConc (fun (a : Array (Value D)) (a' : Array GoValue) =>
          a' = a.map (concV I)) st st' := by
    intro i _ x y hR st hst
    subst hR
    obtain ⟨loc, hloc, hst⟩ := bind_eq_ok.mp hst
    obtain ⟨v, hv, hst⟩ := bind_eq_ok.mp hst
    obtain ⟨_, _, hst⟩ := bind_eq_ok.mp hst
    have hstv : st = .yield (x.push v) := by
      simpa [pure, Except.pure, eq_comm] using hst
    subst hstv
    refine ⟨.yield ((x.map (concV I)).push (concV I v)), ?_,
      .yield (by simp)⟩
    refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
    refine bind_eq_ok.mpr ⟨concV I v, loadLoc_conc σ hv, ?_⟩
    exact bind_eq_ok.mpr ⟨PUnit.unit, rfl, rfl⟩
  obtain ⟨out', hout', hR⟩ := forInR_conc
    (R := fun (a : Array (Value D)) (a' : Array GoValue) =>
      a' = a.map (concV I))
    (y := (#[] : Array GoValue)) (by simp) hbody hloop
  rw [hR] at hout'
  exact hout'

/-- The map-key scan, transported (decided equality on concrete keys;
∀ machine flag — the flags pick panic messages only). -/
theorem mapEntryIndex_conc (hI : I.Sound) (σ : ExecState) {keyTy : Ty}
    {entries : Array (Value D × Value D)} {key : Value D} {r : Option Nat}
    (h : mapEntryIndex?' keyTy entries key = .ok r) (isInsert : Bool) :
    mapEntryIndex? σ keyTy (concEntries I entries) (concV I key) isInsert
      = .ok r := by
  unfold mapEntryIndex?' at h
  unfold mapEntryIndex?
  obtain ⟨u, hchk, h⟩ := bind_eq_ok.mp h
  obtain ⟨rp, hloop, hpost⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨(), checkKeyHashable_conc hI σ hchk _ _, ?_⟩
  refine bind_eq_ok.mpr ⟨rp, ?_, ?_⟩
  · -- the scan loop: mapped elements, shared state
    rw [← Array.forIn_toList] at hloop
    rw [← Array.forIn_toList,
      show (concEntries I entries).toList
          = entries.toList.map (fun q => (concV I q.1, concV I q.2))
        from by simp [concEntries]]
    refine forIn_conc_id (fun a ha x st hst => ?_) hloop
    obtain ⟨k, v⟩ := a
    simp only [] at hst ⊢
    obtain ⟨hit, hhit, hst⟩ := bind_eq_ok.mp hst
    refine bind_eq_ok.mpr ⟨hit, valueEqB_conc hI σ hhit, ?_⟩
    by_cases hb : hit = true
    · rw [if_pos hb] at hst ⊢
      have hstv : st = .done ⟨some (some x.snd), x.snd⟩ := by
        simpa [pure, Except.pure, eq_comm] using hst
      subst hstv
      rfl
    · rw [if_neg hb] at hst ⊢
      have hstv : st = .yield ⟨none, x.snd + 1⟩ := by
        simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
          using hst
      subst hstv
      simp [pure, Except.pure, Bind.bind, Except.bind]
  · rcases hfst : rp.fst with _ | a <;> rw [hfst] at hpost
    · have hr : r = none := by
        simpa [Bind.bind, Except.bind, pure, Except.pure, eq_comm]
          using hpost
      subst hr
      simp [Bind.bind, Except.bind, pure, Except.pure]
    · have hr : r = a := by
        simpa [pure, Except.pure, eq_comm] using hpost
      subst hr
      simp [pure, Except.pure]

/-- `Array.setIfInBounds` commutes with `map` unconditionally (sizes
agree under `map`; out-of-bounds is a no-op on both sides). -/
theorem map_setIfInBounds {α β : Type _} (f : α → β)
    (es : Array α) (i : Nat) (a : α) :
    (es.setIfInBounds i a).map f = (es.map f).setIfInBounds i (f a) := by
  unfold Array.setIfInBounds
  by_cases hi : i < es.size
  · rw [dif_pos hi, dif_pos (by simpa using hi)]
    simp [Array.map_set]
  · rw [dif_neg hi, dif_neg (by simpa using hi)]

theorem mapLookupValue_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {map : MapValue} {key : Value D} {keyTy valueTy : Ty}
    {pr : Value D × Bool}
    (h : mapLookupValue' s map key keyTy valueTy = .ok pr) :
    mapLookupValue (concS I σ s) map (concV I key) keyTy valueTy
      = .ok (concV I pr.1, pr.2) := by
  unfold mapLookupValue' at h
  unfold mapLookupValue
  obtain ⟨me, hme, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr
    ⟨me.map (fun p => (p.1, concEntries I p.2)), mapEntries_conc σ hme, ?_⟩
  rcases me with _ | ⟨baseLoc, entries⟩
  · simp only [Option.map_none] at *
    obtain ⟨u, hchk, h⟩ := bind_eq_ok.mp h
    obtain ⟨zero, hzero, h⟩ := bind_eq_ok.mp h
    have hpr : pr = (zero, false) := by
      simpa [pure, Except.pure, eq_comm] using h
    subst hpr
    refine bind_eq_ok.mpr ⟨(), checkKeyHashable_conc hI (concS I σ s) hchk _ _, ?_⟩
    refine bind_eq_ok.mpr ⟨concV I zero, default_conc hI _ hzero, rfl⟩
  · simp only [Option.map_some] at *
    obtain ⟨idx, hidx, h⟩ := bind_eq_ok.mp h
    refine bind_eq_ok.mpr ⟨idx, mapEntryIndex_conc hI (concS I σ s) hidx _, ?_⟩
    rcases idx with _ | i <;> simp only [] at h ⊢
    · obtain ⟨zero, hzero, h⟩ := bind_eq_ok.mp h
      have hpr : pr = (zero, false) := by
        simpa [pure, Except.pure, eq_comm] using h
      subst hpr
      refine bind_eq_ok.mpr ⟨concV I zero, default_conc hI _ hzero, rfl⟩
    · rcases hget : entries[i]? with _ | ⟨ek, ev⟩ <;> rw [hget] at h
      · cases h
      · have hpr : pr = (ev, true) := by
          simpa [pure, Except.pure, eq_comm] using h
        subst hpr
        rw [show (concEntries I entries)[i]?
              = some (concV I ek, concV I ev)
            from by simp [concEntries, Array.getElem?_map, hget]]
        rfl

theorem mapAssignValue_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {keyTy valueTy : Ty} {baseV keyV valueV : Value D} {s' : State D}
    (h : mapAssignValue' s keyTy valueTy baseV keyV valueV = .ok s') :
    mapAssignValue (concS I σ s) keyTy valueTy (concV I baseV)
      (concV I keyV) (concV I valueV) = .ok (concS I σ s') := by
  unfold mapAssignValue' at h
  unfold mapAssignValue
  obtain ⟨map, hmap, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
  obtain ⟨key, hkey, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨concV I key, normalize_conc hI _ hkey, ?_⟩
  obtain ⟨value, hvalue, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨concV I value, normalize_conc hI _ hvalue, ?_⟩
  obtain ⟨me, hme, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr
    ⟨me.map (fun p => (p.1, concEntries I p.2)), mapEntries_conc σ hme, ?_⟩
  rcases me with _ | ⟨baseLoc, entries⟩
  · cases h
  simp only [Option.map_some] at *
  obtain ⟨idx, hidx, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨idx, mapEntryIndex_conc hI (concS I σ s) hidx _, ?_⟩
  rcases idx with _ | i <;> simp only [] at h ⊢
  · -- push
    obtain ⟨es, hes, h⟩ := bind_eq_ok.mp h
    have hesv : es = entries.push (key, value) := by
      simpa [pure, Except.pure, eq_comm] using hes
    subst hesv
    refine bind_eq_ok.mpr
      ⟨(concEntries I entries).push (concV I key, concV I value), rfl, ?_⟩
    have := storeLoc_conc hI σ (loc := baseLoc)
      (v := .mapData (entries.push (key, value))) (s' := s') h
    simpa [concV_mapData, concEntries, Array.map_push] using this
  · -- overwrite
    obtain ⟨es, hes, h⟩ := bind_eq_ok.mp h
    have hesv : es = entries.set! i (key, value) := by
      simpa [pure, Except.pure, eq_comm] using hes
    subst hesv
    refine bind_eq_ok.mpr
      ⟨(concEntries I entries).set! i (concV I key, concV I value), rfl, ?_⟩
    have := storeLoc_conc hI σ (loc := baseLoc)
      (v := .mapData (entries.set! i (key, value))) (s' := s') h
    simpa [concV_mapData, concEntries, Array.set!, map_setIfInBounds]
      using this

/-! ## The comma-ok value sources -/

theorem applyRhsOp_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {rop : RhsOp} {vs out : List (Value D)}
    (h : applyRhsOp' s rop vs = .ok out) :
    applyRhsOp (concS I σ s) rop (vs.map (concV I))
      = .ok (out.map (concV I)) := by
  cases rop with
  | vals =>
      simp only [applyRhsOp'] at h
      cases h
      simp [applyRhsOp, pure, Except.pure]
  | typeAssert targetTy =>
      rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        simp [applyRhsOp', quit] at h
  | mapLookup keyTy valueTy =>
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp only [applyRhsOp', quit] at h <;> try (cases h; done)
      obtain ⟨map, hmap, h⟩ := bind_eq_ok.mp h
      obtain ⟨key, hkey, h⟩ := bind_eq_ok.mp h
      obtain ⟨pr, hpr, h⟩ := bind_eq_ok.mp h
      have hout : out = [pr.1, .bool (D.litB pr.2)] := by
        simpa [pure, Except.pure, eq_comm] using h
      subst hout
      simp only [List.map_cons, List.map_nil, applyRhsOp]
      refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
      refine bind_eq_ok.mpr ⟨concV I key, normalize_conc hI _ hkey, ?_⟩
      refine bind_eq_ok.mpr ⟨(concV I pr.1, pr.2),
        mapLookupValue_conc hI σ hpr, ?_⟩
      simp [hI.litB, pure, Except.pure]

/-! ## The target-store spine (phase-2 stores) -/

theorem resolveChain_conc (hI : I.Sound) (σ : ExecState) {s : State D} :
    ∀ (steps : List TargetStep) (cur : Value D) (idxs : List (Value D))
      {out : Value D},
      resolveChain' s cur steps idxs = .ok out →
      resolveChain (concS I σ s) (concV I cur) steps
        (idxs.map (concV I)) = .ok (concV I out) := by
  intro steps
  induction steps with
  | nil =>
      intro cur idxs out h
      cases idxs with
      | nil =>
          simp only [resolveChain'] at h
          cases h
          simp [resolveChain, pure, Except.pure]
      | cons i rest => simp [resolveChain', quit] at h
  | cons step rest ih =>
      intro cur idxs out h
      cases step with
      | index =>
          cases idxs with
          | nil => simp [resolveChain', quit] at h
          | cons i irest =>
              simp only [resolveChain'] at h
              obtain ⟨loc, hloc, h⟩ := bind_eq_ok.mp h
              simp only [List.map_cons, resolveChain]
              refine bind_eq_ok.mpr ⟨loc,
                indexTargetLoc_conc hI σ hloc, ?_⟩
              simpa using ih (.addr loc) irest h
      | field tid f =>
          simp only [resolveChain'] at h
          obtain ⟨loc, hloc, h⟩ := bind_eq_ok.mp h
          simp only [resolveChain]
          refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
          simpa using ih (.addr (.field loc tid f)) idxs h

theorem storeTarget_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {r : TargetRef D} {v : Value D} {s' : State D}
    (h : storeTarget' s r v = .ok s') :
    storeTarget (concS I σ s) (concRef I r) (concV I v)
      = .ok (concS I σ s') := by
  cases r with
  | chain anchor idxs steps =>
      simp only [storeTarget'] at h
      obtain ⟨resolved, hres, h⟩ := bind_eq_ok.mp h
      obtain ⟨loc, hloc, h⟩ := bind_eq_ok.mp h
      simp only [storeTarget, concRef]
      refine bind_eq_ok.mpr ⟨concV I resolved,
        resolveChain_conc hI σ steps anchor idxs hres, ?_⟩
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      exact storeLoc_conc hI σ h
  | mapElem b k kt vt =>
      simp only [storeTarget'] at h
      simpa [storeTarget, concRef] using mapAssignValue_conc hI σ h

end GoLean.Sym
