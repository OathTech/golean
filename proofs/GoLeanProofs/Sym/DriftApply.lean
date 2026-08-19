import GoLeanProofs.Sym.DriftOps

/-!
# Drift/commutation helper layer, tranche 3: the apply tables
(WP arc slice 4, phase 2)

The strict-op and wide-statement apply tables, transported success-only
over any sound interpretation — the last LAYER-2 stratum under the
master walk (`Sym/Walk.lean`). Loop-bearing arms ride the
`forIn_conc_map`/`forIn_conc_id` transports from `Sym/DriftOps.lean`.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

/-- `pure *> x = x` at `Except` (the `validateSlice *> …` shape),
proven definitionally; a local simp lemma for the apply-table
closers. -/
@[simp] theorem ok_seqRight {ε α β : Type} (a : α) (x : Except ε β) :
    (Except.ok a *> x) = x := rfl

/-- `pure >>= f` collapse at `Except` — the statement-if unit bind. -/
@[simp] theorem ok_bind {ε α β : Type} (a : α)
    (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-! ## Functional (image-state) loop transport -/

/-- The image of a loop-step outcome under a state map. -/
def stepImage {β β' : Type} (φ : β → β') : ForInStep β → ForInStep β'
  | .done b => .done (φ b)
  | .yield b => .yield (φ b)

/-- Loop transport along a FUNCTIONAL state image (mapped elements,
image states) — the shape of every state-threading op-table loop
(store loops at `concS`, accumulator loops at `Array.map`). -/
theorem forIn_conc_map {A B β β' : Type} {φ : β → β'} {t : A → B}
    {f : A → β → M (ForInStep β)}
    {g : B → β' → Except GoError (ForInStep β')} :
    ∀ {l : List A} {x : β},
      (∀ a ∈ l, ∀ x st, f a x = .ok st →
        g (t a) (φ x) = .ok (stepImage φ st)) →
      ∀ {out : β}, forIn l x f = .ok out →
        forIn (l.map t) (φ x) g = .ok (φ out) := by
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
      refine bind_eq_ok.mpr
        ⟨stepImage φ st, hstep a List.mem_cons_self x st hst, ?_⟩
      cases st with
      | done b =>
          have hb : out = b := by
            simpa [pure, Except.pure, eq_comm] using hrest
          subst hb
          rfl
      | yield b =>
          exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha'))
            hrest

/-- `forIn_conc_map` at the SAME element list (range loops with a
state image). -/
theorem forIn_conc_mapS {A β β' : Type} {φ : β → β'}
    {f : A → β → M (ForInStep β)}
    {g : A → β' → Except GoError (ForInStep β')} :
    ∀ {l : List A} {x : β},
      (∀ a ∈ l, ∀ x st, f a x = .ok st →
        g a (φ x) = .ok (stepImage φ st)) →
      ∀ {out : β}, forIn l x f = .ok out →
        forIn l (φ x) g = .ok (φ out) := by
  intro l x hstep out h
  have := forIn_conc_map (t := (id : A → A)) (φ := φ)
    (by simpa using hstep) h
  simpa using this

/-! ## Shape inversions (mirror success forces value heads) -/

theorem asIntR_shape {v : Value D} {r : D.IntR × IntKind}
    (h : v.asIntR = .ok r) : v = .int r.1 r.2 := by
  cases v <;> simp only [Value.asIntR, quit] at h <;>
    first
      | (cases h; done)
      | (cases h; rfl)

theorem asIntAt_shape {q : QuitSite} {v : Value D} {n : Int}
    (h : v.asIntAt q = .ok n) : ∃ p k, v = .int p k := by
  cases v <;>
    first
      | exact ⟨_, _, rfl⟩
      | simp [Value.asIntAt, quit] at h

theorem intBinaryResult'_shape {opD : D.IntR → D.IntR → D.IntR}
    {l r out : Value D} (h : intBinaryResult' opD l r = .ok out) :
    ∃ lv lk rv rk, l = .int lv lk ∧ r = .int rv rk := by
  simp only [intBinaryResult', bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, hl, ⟨rv, rk⟩, hr, _⟩ := h
  exact ⟨lv, lk, rv, rk, asIntR_shape hl, asIntR_shape hr⟩

/-! ## Array-literal construction -/

theorem buildArrayValue_conc (hI : I.Sound) (σ : ExecState)
    {length : Nat} {elem : Ty} {args : Array (Int × Value D)}
    {out : Value D}
    (h : buildArrayValue' length elem args = .ok out) :
    buildArrayValue σ length elem
      (args.map (fun p => (p.1, concV I p.2))) = .ok (concV I out) := by
  unfold buildArrayValue' at h
  unfold buildArrayValue
  obtain ⟨defs, hdefs, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨defs.map (concV I), ?_, ?_⟩
  · -- the default-fill loop: same range, image state
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hdefs ⊢
    rw [show (#[] : Array GoValue)
          = Array.map (concV I) (#[] : Array (Value D)) from by simp]
    refine forIn_conc_mapS
      (φ := fun a : Array (Value D) => a.map (concV I))
      (fun i _ x st hst => ?_) hdefs
    obtain ⟨d, hd, hst⟩ := bind_eq_ok.mp hst
    have hstv : st = .yield (x.push d) := by
      simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm] using hst
    subst hstv
    refine bind_eq_ok.mpr ⟨concV I d, default_conc hI σ hd, ?_⟩
    simp [stepImage, pure, Except.pure, Bind.bind, Except.bind,
      Array.map_push]
  · -- the keyed-store loop: mapped elements, image on the values
    obtain ⟨rp, hloop, hpost⟩ := bind_eq_ok.mp h
    rw [← Array.forIn_toList] at hloop
    refine bind_eq_ok.mpr
      ⟨⟨rp.fst, rp.snd.map (concV I)⟩, ?_, ?_⟩
    · rw [← Array.forIn_toList,
        show (args.map (fun p => (p.1, concV I p.2))).toList
            = args.toList.map (fun p => (p.1, concV I p.2))
          from by simp]
      refine forIn_conc_map
        (t := fun p : Int × Value D => (p.1, concV I p.2))
        (φ := fun m : MProd (Array Int) (Array (Value D)) =>
          (⟨m.fst, m.snd.map (concV I)⟩ :
            MProd (Array Int) (Array GoValue)))
        (fun a _ x st hst => ?_) hloop
      obtain ⟨key, value⟩ := a
      simp only [] at hst ⊢
      by_cases hseen : x.fst.contains key
      · rw [if_pos hseen] at hst
        exact absurd hst (by simp [quit, Bind.bind, Except.bind])
      · rw [if_neg hseen] at hst
        rw [if_neg hseen]
        by_cases hneg : key < 0
        · rw [if_pos hneg] at hst
          exact absurd hst (by simp [quit, Bind.bind, Except.bind])
        · rw [if_neg hneg] at hst
          rw [if_neg hneg]
          simp only [Bind.bind, Except.bind, pure, Except.pure] at hst ⊢
          rcases hget : x.snd[key.toNat]? with _ | old <;>
            rw [hget] at hst
          · cases hst
          · rw [show (x.snd.map (concV I))[key.toNat]?
                  = some (concV I old)
                from by simp [Array.getElem?_map, hget]]
            obtain ⟨normd, hnorm, hst⟩ := bind_eq_ok.mp hst
            obtain ⟨coerced, hco, hst⟩ := bind_eq_ok.mp hst
            have hstv : st = .yield
                ⟨x.fst.push key, x.snd.set! key.toNat coerced⟩ := by
              simpa [pure, Except.pure, eq_comm] using hst
            subst hstv
            refine bind_eq_ok.mpr
              ⟨concV I normd, normalize_conc hI σ hnorm, ?_⟩
            refine bind_eq_ok.mpr
              ⟨concV I coerced, coerce_conc hI hco, ?_⟩
            simp [stepImage, Array.set!, map_setIfInBounds]
    · have hout : out = .array rp.snd := by
        simpa [pure, Except.pure, eq_comm] using hpost
      subst hout
      simp [concV_array, pure, Except.pure]

theorem buildDefaultArrayValue_conc (hI : I.Sound) (σ : ExecState)
    {length : Nat} {elem : Ty} {out : Value D}
    (h : buildDefaultArrayValue' length elem = .ok out) :
    buildDefaultArrayValue σ length elem = .ok (concV I out) := by
  have := buildArrayValue_conc hI σ (args := #[]) h
  simpa [buildDefaultArrayValue, buildDefaultArrayValue'] using this

/-! ## More inversions and small bridges -/

theorem asIntAt_inv {q : QuitSite} {v : Value D} {n : Int}
    (h : v.asIntAt q = .ok n) :
    ∃ p k, v = .int p k ∧ D.toInt? p = some n := by
  cases v <;>
    first
      | (simp only [Value.asIntAt, quit] at h; cases h; done)
      | skip
  next p k =>
    simp only [Value.asIntAt] at h
    rcases ht : D.toInt? p with _ | m <;> rw [ht] at h
    · cases h
    · cases h
      exact ⟨p, k, rfl, ht⟩

/-- No-atom operand lists concretize with their float-headedness
intact (the min/max guard's bridge; JC-9). -/
theorem anyFloat_conc {vs : List (Value D)}
    (hna : anyAtomOperand' vs = false) :
    anyFloatOperand (vs.map (concV I)) = anyFloatOperand' vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      simp only [anyAtomOperand', List.any_cons, Bool.or_eq_false_iff]
        at hna
      obtain ⟨hv, hrest⟩ := hna
      simp only [List.map_cons, anyFloatOperand, anyFloatOperand',
        List.any_cons]
      have hr := ih (by simpa [anyAtomOperand'] using hrest)
      simp only [anyFloatOperand, anyFloatOperand'] at hr
      rw [hr]
      congr 1
      cases v <;> simp_all

/-! ## THE STRICT-OP APPLY TABLE -/

set_option maxHeartbeats 6400000 in
/-- The strict-op apply, transported arm-for-arm: a successful mirror
apply transports to the machine at every sound interpretation. Quit
arms (structLit/toInterface/typeAssert Q4; atoms Q10; payload
inspections Q5; panics Q6) assert nothing. -/
theorem applyStrictOp_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {op : StrictOp} {vs : List (Value D)} {out : Value D} {s' : State D}
    (h : applyStrictOp' s op vs = .ok (out, s')) :
    applyStrictOp (concS I σ s) op (vs.map (concV I))
      = .ok (concV I out, concS I σ s') := by
  cases op with
  | add =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases l <;> cases r <;> simp only [quit] at h <;> try (cases h; done)
      case int.int lv lk rv rk =>
        obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using intBinaryResult_conc hI hI.add hv
      case float.float lb lk rb rk =>
        obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        simp only [List.map_cons, List.map_nil, concV_float, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using floatBinary_conc "+" hv
      case string.string ls rs =>
        cases h
        simp [applyStrictOp, pure, Except.pure]
  | sub =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      split at h
      · -- float/float
        obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        simp only [List.map_cons, List.map_nil, concV_float, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using floatBinary_conc "-" hv
      · obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        obtain ⟨lv, lk, rv, rk, rfl, rfl⟩ := intBinaryResult'_shape hv
        simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using intBinaryResult_conc hI hI.sub hv
  | mul =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      split at h
      · obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        simp only [List.map_cons, List.map_nil, concV_float, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using floatBinary_conc "*" hv
      · obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        obtain ⟨lv, lk, rv, rk, rfl, rfl⟩ := intBinaryResult'_shape hv
        simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using intBinaryResult_conc hI hI.mul hv
  | div =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      split at h
      · obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using hfin
        simp only [List.map_cons, List.map_nil, concV_float, applyStrictOp]
        refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
        simpa using floatBinary_conc "/" hv
      · obtain ⟨divisor, hdiv, h⟩ := bind_eq_ok.mp h
        obtain ⟨rv, rk₀, rfl, hrt⟩ := asIntAt_inv hdiv
        by_cases hz : (divisor == 0) = true
        · rw [if_pos hz] at h
          exact absurd h (by simp [quit])
        · rw [if_neg hz] at h
          obtain ⟨⟨lv, lk⟩, hl, h2⟩ := bind_eq_ok.mp h
          obtain ⟨⟨rv2, rk⟩, hr, h3⟩ := bind_eq_ok.mp h2
          simp only [] at hl hr h3 ⊢
          obtain rfl := asIntR_shape hl
          have hrshape := asIntR_shape hr
          simp only [Value.int.injEq] at hrshape
          obtain ⟨hrv2, hrk⟩ := hrshape
          rcases hcomp : IntKind.compatibleResult lk rk with _ | kind <;>
            rw [hcomp] at h3
          · exact absurd h3 (by simp [quit])
          · simp only [] at h3
            obtain ⟨rfl, rfl⟩ : out = .int (D.norm kind (D.divC lv divisor)) kind
                ∧ s' = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h3
            simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
            refine bind_eq_ok.mpr ⟨divisor,
              by simp [valueAsInt, hI.toInt? _ _ hrt], ?_⟩
            rw [if_neg hz]
            refine bind_eq_ok.mpr ⟨PUnit.unit, rfl, ?_⟩
            refine bind_eq_ok.mpr ⟨.int (kind.normalize
              (Int.tdiv (I.intV lv) divisor)) kind, ?_, ?_⟩
            · simp only [intBinaryResult, valueAsIntValue, bind_eq_ok]
              refine ⟨(I.intV lv, lk), rfl, (I.intV rv, rk₀), rfl, ?_⟩
              simp only []
              rw [hrk, hcomp]
              rw [show I.intV rv = divisor from hI.toInt? _ _ hrt]
              simp [Bind.bind, Except.bind, pure, Except.pure]
            · simp [concV_int, hI.norm, hI.divC, pure, Except.pure]
  | mod =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨divisor, hdiv, h⟩ := bind_eq_ok.mp h
      obtain ⟨rv, rk₀, rfl, hrt⟩ := asIntAt_inv hdiv
      by_cases hz : (divisor == 0) = true
      · rw [if_pos hz] at h
        exact absurd h (by simp [quit])
      · rw [if_neg hz] at h
        obtain ⟨⟨lv, lk⟩, hl, h2⟩ := bind_eq_ok.mp h
        obtain ⟨⟨rv2, rk⟩, hr, h3⟩ := bind_eq_ok.mp h2
        simp only [] at hl hr h3 ⊢
        obtain rfl := asIntR_shape hl
        have hrshape := asIntR_shape hr
        simp only [Value.int.injEq] at hrshape
        obtain ⟨hrv2, hrk⟩ := hrshape
        rcases hcomp : IntKind.compatibleResult lk rk with _ | kind <;>
          rw [hcomp] at h3
        · exact absurd h3 (by simp [quit])
        · simp only [] at h3
          obtain ⟨rfl, rfl⟩ : out = .int (D.norm kind (D.modC lv divisor)) kind
              ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h3
          simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
          refine bind_eq_ok.mpr ⟨divisor,
            by simp [valueAsInt, hI.toInt? _ _ hrt], ?_⟩
          rw [if_neg hz]
          refine bind_eq_ok.mpr ⟨PUnit.unit, rfl, ?_⟩
          refine bind_eq_ok.mpr ⟨.int (kind.normalize
            (Int.tmod (I.intV lv) divisor)) kind, ?_, ?_⟩
          · simp only [intBinaryResult, valueAsIntValue, bind_eq_ok]
            refine ⟨(I.intV lv, lk), rfl, (I.intV rv, rk₀), rfl, ?_⟩
            simp only []
            rw [hrk, hcomp]
            rw [show I.intV rv = divisor from hI.toInt? _ _ hrt]
            simp [Bind.bind, Except.bind, pure, Except.pure]
          · simp [concV_int, hI.norm, hI.modC, pure, Except.pure]
  | shiftLeft =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | shiftRight =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | bitAnd =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | bitOr =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | bitXor =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | bitClear =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨v, hv, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = v ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      obtain ⟨lv, lk, rv, rk, hcl, hcr, hlift⟩ := closedIntOp_conc hI hv
      simp only [List.map_cons, List.map_nil, applyStrictOp, hcl, hcr]
      exact bind_eq_ok.mpr ⟨concV I out, hlift, rfl⟩
  | bitNeg =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      next value kind =>
        rcases ht : D.toInt? value with _ | n <;> rw [ht] at h
        · cases h
        try simp only [] at h
        rcases hres : intBitNegResult (.int n kind) with e | gv <;>
          rw [hres] at h <;> (try simp only [] at h)
        · cases h
        · cases gv <;> simp only [quit] at h <;> try (cases h; done)
          next m mk =>
            cases h
            simp only [List.map_cons, List.map_nil, concV_int,
              applyStrictOp]
            rw [show I.intV value = n from hI.toInt? _ _ ht]
            exact bind_eq_ok.mpr ⟨.int m mk, hres, by simp [hI.litI]⟩
  | neg =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      · next value kind =>
          cases h
          simp [applyStrictOp, hI.norm, hI.neg, pure, Except.pure]
      · next bits kind =>
          cases h
          simp [applyStrictOp, pure, Except.pure]
  | floatLit num den kind =>
      rcases vs with _ | ⟨x, rest⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      by_cases hden : (den == 0) = true
      · rw [if_pos hden] at h
        cases h
      · rw [if_neg hden] at h
        cases h
        simp only [List.map_nil, applyStrictOp]
        rw [if_neg hden]
        simp [pure, Except.pure]
  | not =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      next b =>
        cases h
        simp [applyStrictOp, valueAsBool, hI.notB, Bind.bind,
          Except.bind, pure, Except.pure]
  | eqCmp ty =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool b ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      exact bind_eq_ok.mpr ⟨I.boolV b, valueEqR_conc hI _ hb, rfl⟩
  | neqCmp ty =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool (D.notB b) ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      refine bind_eq_ok.mpr ⟨I.boolV b, valueEqR_conc hI _ hb, ?_⟩
      simp [hI.notB, pure, Except.pure]
  | atMostCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool b ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      exact bind_eq_ok.mpr ⟨I.boolV b, valueAtMost_conc hI hb, rfl⟩
  | atLeastCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool b ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      exact bind_eq_ok.mpr ⟨I.boolV b, valueAtLeast_conc hI hb, rfl⟩
  | lessCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool b ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      exact bind_eq_ok.mpr ⟨I.boolV b, valueLess_conc hI hb, rfl⟩
  | greaterCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨b, hb, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .bool b ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp, concV_bool]
      exact bind_eq_ok.mpr ⟨I.boolV b, valueGreater_conc hI hb, rfl⟩
  | convert ty =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨w, hw, hfin⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using hfin
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      exact bind_eq_ok.mpr ⟨concV I out, convert_conc hI _ hw, rfl⟩
  | bytesFromString =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      next str =>
        rcases halloc : s.alloc
            (.array (str.bytes.map
              (fun b => Value.int (D := D) (D.litI (Int.ofNat b.toNat)) .uint8)))
            (some (.array (str.bytes.map
              (fun b : UInt8 =>
                Value.int (D := D) (D.litI (Int.ofNat b.toNat)) .uint8)).size
              (.int .uint8)))
          with ⟨base, s₁⟩
        rw [halloc] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
          (v := .array (str.bytes.map
            (fun b => Value.int (D := D) (D.litI (Int.ofNat b.toNat)) .uint8)))
          (ty := some (.array (str.bytes.map
            (fun b : UInt8 =>
              Value.int (D := D) (D.litI (Int.ofNat b.toNat)) .uint8)).size
            (.int .uint8)))
        rw [halloc] at hallocm
        simp only [concV_array, Array.map_map, Function.comp_def,
          concV_int, hI.litI, Array.size_map] at hallocm
        simp only [List.map_cons, List.map_nil, concV_string,
          applyStrictOp, Array.size_map]
        rw [hallocm]
        simp [concV_slice, Array.size_map, pure, Except.pure]
  | stringFromByteSlice =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok.mp h
      obtain ⟨values, hvis, h⟩ := bind_eq_ok.mp h
      obtain ⟨bytes, hbytes, h⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .string { bytes := bytes } ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨sl, asSlice_conc hsl, ?_⟩
      refine bind_eq_ok.mpr
        ⟨values.map (concV I), sliceVisible_conc σ hvis, ?_⟩
      refine bind_eq_ok.mpr ⟨bytes, ?_, by simp [pure, Except.pure]⟩
      -- the byte-collection loop: mapped elements, same state
      rw [← Array.forIn_toList] at hbytes
      rw [← Array.forIn_toList, Array.toList_map]
      refine forIn_conc_id (fun a ha x st hst => ?_) hbytes
      cases a <;> (try simp only [quit] at hst) <;> try (cases hst; done)
      next byteR kd =>
        cases kd <;> (try simp only [quit] at hst) <;>
          try (cases hst; done)
        rcases ht : D.toInt? byteR with _ | byte <;> rw [ht] at hst <;>
          (try simp only [] at hst)
        · exact absurd hst (by simp [quit, Bind.bind, Except.bind])
        simp only [concV_int, show I.intV byteR = byte
          from hI.toInt? _ _ ht]
        by_cases hrange : (byte < 0 || byte > 255) = true
        · rw [if_pos hrange] at hst
          exact absurd hst (by simp [quit, Bind.bind, Except.bind])
        · rw [if_neg hrange] at hst
          rw [if_neg hrange]
          have hstv : st = .yield (x.push (UInt8.ofNat byte.toNat)) := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst
          subst hstv
          simp [pure, Except.pure, Bind.bind, Except.bind]
  | stringFromRune =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨code, hcode, h2⟩ := bind_eq_ok.mp h
      obtain ⟨rv, rk, rfl, hrt⟩ := asIntAt_inv hcode
      obtain ⟨rfl, rfl⟩ : out = .string (GoString.fromCodePoint code)
          ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h2
      simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
      simp [valueAsInt, hI.toInt? _ _ hrt, Bind.bind, Except.bind,
        pure, Except.pure]
  | deref ty =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
      obtain ⟨w, hw, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h3
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      refine bind_eq_ok.mpr ⟨concV I out, loadLoc_conc σ hw, ?_⟩
      simp [pure, Except.pure]
  | fieldGet tid fname =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      next actual fields =>
        by_cases hty : (actual != tid) = true
        · rw [if_pos hty] at h
          cases h
        · rw [if_neg hty] at h
          have hty2 : ¬(actual != tid
              && !structTagCompatible (concS I σ s) actual tid) = true := by
            simp only [Bool.not_eq_true] at hty
            simp [hty]
          rcases hf : StructFields.lookup' fields fname with _ | w <;>
            rw [hf] at h
          · cases h
          cases h
          simp only [List.map_cons, List.map_nil, concV_struct,
            applyStrictOp]
          rw [if_neg hty2, structLookup_conc, hf]
          simp [pure, Except.pure, Bind.bind, Except.bind]
  | fieldAddr tid fname =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .addr (.field loc tid fname) ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h2
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      simp [concV_addr, pure, Except.pure]
  | addrOfDeref =>
      -- BUG-056: nil-assert + pass-through; fieldAddr's shape minus
      -- the field constructor.
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .addr loc ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h2
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      simp [concV_addr, pure, Except.pure]
  | structLit ty =>
      simp [applyStrictOp', quit] at h
  | arrayLit n elem keys =>
      simp only [applyStrictOp', quit] at h
      by_cases hlen : (keys.length != vs.length) = true
      · rw [if_pos hlen] at h
        cases h
      · rw [if_neg hlen] at h
        obtain ⟨w, hw, h⟩ := bind_eq_ok.mp h
        obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h
        simp only [applyStrictOp]
        rw [if_neg (by simpa using hlen)]
        refine bind_eq_ok.mpr ⟨PUnit.unit, rfl, ?_⟩
        refine bind_eq_ok.mpr ⟨concV I out, ?_,
          by simp [pure, Except.pure]⟩
        have hb := buildArrayValue_conc hI (concS I σ s')
          (args := (keys.zip vs).toArray) hw
        rw [show (keys.zip (vs.map (concV I))).toArray
              = (keys.zip vs).toArray.map (fun p => (p.1, concV I p.2))
            from by
              simp only [List.zip_map_right]
              simp [List.map_toArray, Prod.map]]
        exact hb
  | toInterface target dynamic =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp [applyStrictOp', quit] at h
  | typeAssert target source =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp [applyStrictOp', quit] at h
  | indexGet =>
      rcases vs with _ | ⟨b, _ | ⟨i, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨iv, hiv, h2⟩ := bind_eq_ok.mp h
      obtain ⟨ip, ik, rfl, hit⟩ := asIntAt_inv hiv
      cases b <;> simp only [quit] at h2 <;> try (cases h2; done)
      case string str =>
        obtain ⟨w, hw, h3⟩ := bind_eq_ok.mp h2
        obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h3
        simp only [List.map_cons, List.map_nil, concV_string, concV_int,
          applyStrictOp]
        refine bind_eq_ok.mpr ⟨iv,
          by simp [valueAsInt, hI.toInt? _ _ hit], ?_⟩
        refine bind_eq_ok.mpr ⟨concV I out, stringByteGet_conc hI hw, ?_⟩
        simp [pure, Except.pure]
      case array values =>
        obtain ⟨w, hw, h3⟩ := bind_eq_ok.mp h2
        obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h3
        simp only [List.map_cons, List.map_nil, concV_array, concV_int,
          applyStrictOp]
        refine bind_eq_ok.mpr ⟨iv,
          by simp [valueAsInt, hI.toInt? _ _ hit], ?_⟩
        refine bind_eq_ok.mpr ⟨concV I out, arrayGet_conc hw, ?_⟩
        simp [pure, Except.pure]
      case slice sl =>
        obtain ⟨loc, hloc, h3⟩ := bind_eq_ok.mp h2
        obtain ⟨w, hw, h4⟩ := bind_eq_ok.mp h3
        obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h4
        simp only [List.map_cons, List.map_nil, concV_slice, concV_int,
          applyStrictOp]
        refine bind_eq_ok.mpr ⟨iv,
          by simp [valueAsInt, hI.toInt? _ _ hit], ?_⟩
        refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
        refine bind_eq_ok.mpr ⟨concV I out, loadLoc_conc σ hw, ?_⟩
        simp [pure, Except.pure]
      case addr baseLoc =>
        -- pointer-to-array read (triage L5): load, then the projection
        obtain ⟨bv, hbv, h3⟩ := bind_eq_ok.mp h2
        cases bv <;> simp only [quit] at h3 <;> try (cases h3; done)
        case array values =>
          obtain ⟨w, hw, h4⟩ := bind_eq_ok.mp h3
          obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h4
          simp only [List.map_cons, List.map_nil, concV_addr, concV_int,
            applyStrictOp]
          refine bind_eq_ok.mpr ⟨iv,
            by simp [valueAsInt, hI.toInt? _ _ hit], ?_⟩
          refine bind_eq_ok.mpr
            ⟨concV I (.array values), loadLoc_conc σ hbv, ?_⟩
          simp only [concV_array]
          refine bind_eq_ok.mpr ⟨concV I out, arrayGet_conc hw, ?_⟩
          simp [pure, Except.pure]
  | indexAddr =>
      rcases vs with _ | ⟨b, _ | ⟨i, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .addr loc ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h2
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨loc, indexTargetLoc_conc hI σ hloc, ?_⟩
      simp [concV_addr, pure, Except.pure]
  | mapGet keyTy valueTy =>
      rcases vs with _ | ⟨b, _ | ⟨i, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨map, hmap, h2⟩ := bind_eq_ok.mp h
      obtain ⟨key, hkey, h3⟩ := bind_eq_ok.mp h2
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
      refine bind_eq_ok.mpr ⟨concV I key, normalize_conc hI _ hkey, ?_⟩
      rcases hb : map.base with _ | baseLoc <;> rw [hb] at h3
      · obtain ⟨u, hchk, h4⟩ := bind_eq_ok.mp h3
        obtain ⟨zero, hzero, h5⟩ := bind_eq_ok.mp h4
        have hov : out = zero ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h5
        rw [hov.1, hov.2]
        refine bind_eq_ok.mpr
          ⟨(), checkKeyHashable_conc hI (concS I σ s) hchk _ _, ?_⟩
        exact bind_eq_ok.mpr ⟨concV I zero, default_conc hI _ hzero, rfl⟩
      · obtain ⟨bv, hbv, h4⟩ := bind_eq_ok.mp h3
        refine bind_eq_ok.mpr ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
        cases bv <;> (try simp only [quit] at h4) <;>
          try (cases h4; done)
        next entries =>
          simp only [concV_mapData]
          obtain ⟨idx, hidx, h5⟩ := bind_eq_ok.mp h4
          refine bind_eq_ok.mpr
            ⟨idx, mapEntryIndex_conc hI (concS I σ s) hidx _, ?_⟩
          rcases idx with _ | j <;> simp only [] at h5 ⊢
          · obtain ⟨zero, hzero, h6⟩ := bind_eq_ok.mp h5
            have hov : out = zero ∧ s' = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h6
            rw [hov.1, hov.2]
            exact bind_eq_ok.mpr
              ⟨concV I zero, default_conc hI _ hzero, rfl⟩
          · rcases hget : entries[j]? with _ | ⟨ek, ev⟩ <;>
              rw [hget] at h5
            · cases h5
            have hov : out = ev ∧ s' = s := by
              simpa [pure, Except.pure, eq_comm, and_comm] using h5
            rw [hov.1, hov.2]
            rw [show (concEntries I entries)[j]?
                  = some (concV I ek, concV I ev)
                from by simp [concEntries, Array.getElem?_map, hget]]
            simp [pure, Except.pure]
  | sliceExpr hasMax =>
      cases hasMax
      · rcases vs with _ | ⟨b, _ | ⟨lo, _ | ⟨hi, _ | ⟨x, rest⟩⟩⟩⟩ <;>
          simp only [applyStrictOp', quit] at h <;> try (cases h; done)
        obtain ⟨lowValue, hlo, h2⟩ := bind_eq_ok.mp h
        obtain ⟨highValue, hhi, h3⟩ := bind_eq_ok.mp h2
        obtain ⟨w, hw, h4⟩ := bind_eq_ok.mp h3
        obtain ⟨lp, lk, rfl, hlt⟩ := asIntAt_inv hlo
        obtain ⟨hp, hk, rfl, hht⟩ := asIntAt_inv hhi
        have hov : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h4
        rw [hov.1, hov.2]
        simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
        refine bind_eq_ok.mpr ⟨lowValue,
          by simp [valueAsInt, hI.toInt? _ _ hlt], ?_⟩
        refine bind_eq_ok.mpr ⟨highValue,
          by simp [valueAsInt, hI.toInt? _ _ hht], ?_⟩
        exact applySlice_conc σ hw
      · rcases vs with _ | ⟨b, _ | ⟨lo, _ | ⟨hi, _ | ⟨m, _ | ⟨x, rest⟩⟩⟩⟩⟩ <;>
          simp only [applyStrictOp', quit] at h <;> try (cases h; done)
        obtain ⟨lowValue, hlo, h2⟩ := bind_eq_ok.mp h
        obtain ⟨highValue, hhi, h3⟩ := bind_eq_ok.mp h2
        obtain ⟨maxValue, hm, h4⟩ := bind_eq_ok.mp h3
        obtain ⟨w, hw, h5⟩ := bind_eq_ok.mp h4
        obtain ⟨lp, lk, rfl, hlt⟩ := asIntAt_inv hlo
        obtain ⟨hp, hk, rfl, hht⟩ := asIntAt_inv hhi
        obtain ⟨mp, mk, rfl, hmt⟩ := asIntAt_inv hm
        have hov : out = w ∧ s' = s := by
          simpa [pure, Except.pure, eq_comm, and_comm] using h5
        rw [hov.1, hov.2]
        simp only [List.map_cons, List.map_nil, concV_int, applyStrictOp]
        refine bind_eq_ok.mpr ⟨lowValue,
          by simp [valueAsInt, hI.toInt? _ _ hlt], ?_⟩
        refine bind_eq_ok.mpr ⟨highValue,
          by simp [valueAsInt, hI.toInt? _ _ hht], ?_⟩
        refine bind_eq_ok.mpr ⟨maxValue,
          by simp [valueAsInt, hI.toInt? _ _ hmt], ?_⟩
        exact applySlice_conc σ hw
  | funcValOf fid =>
      simp only [applyStrictOp'] at h
      cases h
      simp [applyStrictOp, concV_funcVal, pure, Except.pure]
  | defaultValueOf ty =>
      rcases vs with _ | ⟨x, rest⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨w, hw, h⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = w ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h
      simp only [List.map_nil, applyStrictOp]
      exact bind_eq_ok.mpr ⟨concV I out, default_conc hI _ hw, rfl⟩
  | nilLit typ =>
      rcases vs with _ | ⟨x, rest⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      rcases typ with _ | ty
      · cases h
        simp [applyStrictOp, concV_nil, pure, Except.pure]
      · cases ty <;> (try simp only [quit] at h) <;> try (cases h; done)
        case pointer elem =>
          try simp only [] at h
          have hov : out = .nil ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h
          rw [hov.1, hov.2]
          simp [applyStrictOp, concV_nil, pure, Except.pure]
        all_goals (
          (try simp only [] at h)
          obtain ⟨w, hw, h2⟩ := bind_eq_ok.mp h
          have hov : out = w ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [List.map_nil, applyStrictOp]
          exact bind_eq_ok.mpr ⟨concV I w, default_conc hI _ hw,
            by simp [pure, Except.pure]⟩)
  | minOf =>
      rcases vs with _ | ⟨v, rest⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      by_cases hatom : anyAtomOperand' (v :: rest) = true
      · rw [if_pos hatom] at h
        cases h
      · rw [if_neg (by simpa using hatom)] at h
        by_cases hfl : anyFloatOperand' (v :: rest) = true
        · -- the IEEE float fold (triage L3)
          rw [if_pos hfl] at h
          obtain ⟨best, hfold, h⟩ := bind_eq_ok.mp h
          obtain ⟨rfl, rfl⟩ : out = best ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h
          simp only [List.map_cons, applyStrictOp]
          rw [show anyFloatOperand (concV I v :: rest.map (concV I))
                = true from by
              rw [show concV I v :: rest.map (concV I)
                    = (v :: rest).map (concV I) from rfl,
                anyFloat_conc (by simpa using hatom)]
              simpa using hfl]
          rw [if_pos rfl]
          refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
          refine forIn_conc_map (t := concV I) (φ := concV I)
            (fun a _ x st hst => ?_) hfold
          obtain ⟨c, hc, hst⟩ := bind_eq_ok.mp hst
          refine bind_eq_ok.mpr ⟨concV I c, floatMinMax_conc hc, ?_⟩
          have hstv : st = .yield c := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst
          subst hstv
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
        · rw [if_neg (by simpa using hfl)] at h
          obtain ⟨best, hfold, h⟩ := bind_eq_ok.mp h
          obtain ⟨rfl, rfl⟩ : out = best ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h
          simp only [List.map_cons, applyStrictOp]
          rw [show anyFloatOperand (concV I v :: rest.map (concV I))
                = false from by
              rw [show concV I v :: rest.map (concV I)
                    = (v :: rest).map (concV I) from rfl,
                anyFloat_conc (by simpa using hatom)]
              simpa using hfl]
          simp only [Bool.false_eq_true, if_false]
          refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
          refine forIn_conc_map (t := concV I) (φ := concV I)
            (fun a _ x st hst => ?_) hfold
          obtain ⟨lt, hlt, hst⟩ := bind_eq_ok.mp hst
          refine bind_eq_ok.mpr ⟨lt, valueLessB_conc hI hlt, ?_⟩
          by_cases hb : lt = true
          · rw [if_pos hb] at hst ⊢
            have hstv : st = .yield a := by
              simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
                using hst
            subst hstv
            simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
          · rw [if_neg hb] at hst ⊢
            have hstv : st = .yield x := by
              simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
                using hst
            subst hstv
            simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
  | maxOf =>
      rcases vs with _ | ⟨v, rest⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      by_cases hatom : anyAtomOperand' (v :: rest) = true
      · rw [if_pos hatom] at h
        cases h
      · rw [if_neg (by simpa using hatom)] at h
        by_cases hfl : anyFloatOperand' (v :: rest) = true
        · -- the IEEE float fold (triage L3)
          rw [if_pos hfl] at h
          obtain ⟨best, hfold, h⟩ := bind_eq_ok.mp h
          obtain ⟨rfl, rfl⟩ : out = best ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h
          simp only [List.map_cons, applyStrictOp]
          rw [show anyFloatOperand (concV I v :: rest.map (concV I))
                = true from by
              rw [show concV I v :: rest.map (concV I)
                    = (v :: rest).map (concV I) from rfl,
                anyFloat_conc (by simpa using hatom)]
              simpa using hfl]
          rw [if_pos rfl]
          refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
          refine forIn_conc_map (t := concV I) (φ := concV I)
            (fun a _ x st hst => ?_) hfold
          obtain ⟨c, hc, hst⟩ := bind_eq_ok.mp hst
          refine bind_eq_ok.mpr ⟨concV I c, floatMinMax_conc hc, ?_⟩
          have hstv : st = .yield c := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst
          subst hstv
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
        · rw [if_neg (by simpa using hfl)] at h
          obtain ⟨best, hfold, h⟩ := bind_eq_ok.mp h
          obtain ⟨rfl, rfl⟩ : out = best ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h
          simp only [List.map_cons, applyStrictOp]
          rw [show anyFloatOperand (concV I v :: rest.map (concV I))
                = false from by
              rw [show concV I v :: rest.map (concV I)
                    = (v :: rest).map (concV I) from rfl,
                anyFloat_conc (by simpa using hatom)]
              simpa using hfl]
          simp only [Bool.false_eq_true, if_false]
          refine bind_eq_ok.mpr ⟨concV I out, ?_, rfl⟩
          refine forIn_conc_map (t := concV I) (φ := concV I)
            (fun a _ x st hst => ?_) hfold
          obtain ⟨lt, hlt, hst⟩ := bind_eq_ok.mp hst
          refine bind_eq_ok.mpr ⟨lt, valueLessB_conc hI hlt, ?_⟩
          by_cases hb : lt = true
          · rw [if_pos hb] at hst ⊢
            have hstv : st = .yield a := by
              simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
                using hst
            subst hstv
            simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
          · rw [if_neg hb] at hst ⊢
            have hstv : st = .yield x := by
              simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
                using hst
            subst hstv
            simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
  | runeAt =>
      rcases vs with _ | ⟨sv, _ | ⟨ov, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases sv <;> simp only [quit] at h <;> try (cases h; done)
      next str =>
        obtain ⟨off, hoff, h2⟩ := bind_eq_ok.mp h
        obtain ⟨op, ok, rfl, hot⟩ := asIntAt_inv hoff
        by_cases hneg : (off < 0)
        · rw [if_pos hneg] at h2
          exact absurd h2 (by simp [quit, Bind.bind, Except.bind])
        · rw [if_neg hneg] at h2
          have hov : out = .int (D.litI (decodeRuneAt str off.toNat).1)
              .int32 ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [List.map_cons, List.map_nil, concV_string, concV_int,
            applyStrictOp]
          refine bind_eq_ok.mpr ⟨off,
            by simp [valueAsInt, hI.toInt? _ _ hot], ?_⟩
          rw [if_neg hneg]
          simp [hI.litI, pure, Except.pure, Bind.bind, Except.bind]
  | runeSizeAt =>
      rcases vs with _ | ⟨sv, _ | ⟨ov, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases sv <;> simp only [quit] at h <;> try (cases h; done)
      next str =>
        obtain ⟨off, hoff, h2⟩ := bind_eq_ok.mp h
        obtain ⟨op, ok, rfl, hot⟩ := asIntAt_inv hoff
        by_cases hneg : (off < 0)
        · rw [if_pos hneg] at h2
          exact absurd h2 (by simp [quit, Bind.bind, Except.bind])
        · rw [if_neg hneg] at h2
          have hov : out = .int
              (D.litI (Int.ofNat (decodeRuneAt str off.toNat).2)) .int
              ∧ s' = s := by
            simpa [pure, Except.pure, eq_comm, and_comm] using h2
          rw [hov.1, hov.2]
          simp only [List.map_cons, List.map_nil, concV_string, concV_int,
            applyStrictOp]
          refine bind_eq_ok.mpr ⟨off,
            by simp [valueAsInt, hI.toInt? _ _ hot], ?_⟩
          rw [if_neg hneg]
          simp [hI.litI, pure, Except.pure, Bind.bind, Except.bind]
  | runesFromString =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      cases v <;> simp only [quit] at h <;> try (cases h; done)
      next str =>
        rcases halloc : s.alloc
            (.array ((runesOfString str).map
              (fun r => Value.int (D := D) (D.litI r) .int32)))
            (some (.array ((runesOfString str).map
              (fun r : Int =>
                Value.int (D := D) (D.litI r) .int32)).size
              (.int .int32)))
          with ⟨base, s₁⟩
        rw [halloc] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
          (v := .array ((runesOfString str).map
            (fun r => Value.int (D := D) (D.litI r) .int32)))
          (ty := some (.array ((runesOfString str).map
            (fun r : Int =>
              Value.int (D := D) (D.litI r) .int32)).size
            (.int .int32)))
        rw [halloc] at hallocm
        simp only [concV_array, Array.map_map, Function.comp_def,
          concV_int, hI.litI, Array.size_map] at hallocm
        simp only [List.map_cons, List.map_nil, concV_string,
          applyStrictOp, Array.size_map]
        rw [hallocm]
        simp [concV_slice, Array.size_map, pure, Except.pure]
  | stringFromRuneSlice =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok.mp h
      obtain ⟨values, hvis, h⟩ := bind_eq_ok.mp h
      obtain ⟨str, hstr, h⟩ := bind_eq_ok.mp h
      obtain ⟨rfl, rfl⟩ : out = .string str ∧ s' = s := by
        simpa [pure, Except.pure, eq_comm, and_comm] using h
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      refine bind_eq_ok.mpr ⟨sl, asSlice_conc hsl, ?_⟩
      refine bind_eq_ok.mpr
        ⟨values.map (concV I), sliceVisible_conc σ hvis, ?_⟩
      refine bind_eq_ok.mpr ⟨str, ?_, by simp [pure, Except.pure]⟩
      -- the rune-append loop: mapped elements, same state
      rw [← Array.forIn_toList] at hstr
      rw [← Array.forIn_toList, Array.toList_map]
      refine forIn_conc_id (fun a ha x st hst => ?_) hstr
      cases a <;> (try simp only [quit] at hst) <;> try (cases hst; done)
      next rR kd =>
        cases kd <;> (try simp only [quit] at hst) <;>
          try (cases hst; done)
        rcases ht : D.toInt? rR with _ | r <;> rw [ht] at hst <;>
          (try simp only [] at hst)
        · exact absurd hst (by simp [quit, Bind.bind, Except.bind])
        have hstv : st = .yield (x.append (GoString.fromCodePoint r)) := by
          simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
            using hst
        subst hstv
        simp only [concV_int, show I.intV rR = r from hI.toInt? _ _ ht]
        simp [pure, Except.pure, Bind.bind, Except.bind]
  | lengthOf typ =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      split at h
      · -- pointer-to-array type: length from the type, v uninspected
        cases h
        simp [hI.litI, pure, Except.pure, Bind.bind, Except.bind]
      · rename_i hno
        split
        · exact absurd rfl (hno _ _)
        · cases v <;> (try simp only [quit] at h) <;>
            try (cases h; done)
          case array values =>
            cases h
            simp [concV_array, Array.size_map, hI.litI, pure, Except.pure,
              Bind.bind, Except.bind]
          case addr baseLoc =>
            obtain ⟨bv, hbv, h⟩ := bind_eq_ok.mp h
            simp only [concV_addr, bind_eq_ok]
            refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
            cases bv <;> simp only [quit] at h <;> try (cases h; done)
            next values =>
              cases h
              simp [concV_array, Array.size_map, hI.litI, pure,
                Except.pure]
          case string str =>
            cases h
            simp [concV_string, hI.litI, pure, Except.pure,
              Bind.bind, Except.bind]
          case slice sl =>
            rcases hval : validateSlice' sl with e | u <;> rw [hval] at h
            · exact absurd h (by simp [quit, Bind.bind, Except.bind])
            obtain ⟨⟩ := u
            simp only [Bind.bind, Except.bind] at h
            cases h
            simp [concV_slice, validateSlice_conc hval, hI.litI,
              Bind.bind, Except.bind, pure, Except.pure, Seq.seq]
          case map mv =>
            rcases hb : mv.base with _ | baseLoc <;> rw [hb] at h
            · cases h
              simp [concV_map, hb, hI.litI, pure, Except.pure]
            · obtain ⟨bv, hbv, h⟩ := bind_eq_ok.mp h
              simp only [concV_map, hb, bind_eq_ok]
              refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
              cases bv <;> simp only [quit] at h <;> try (cases h; done)
              next entries =>
                cases h
                simp [concV_mapData, Array.size_map, hI.litI, pure,
                  Except.pure]
          case chan cv =>
            rcases hb : cv.base with _ | baseLoc <;> rw [hb] at h
            · cases h
              simp [concV_chan, hb, hI.litI, pure, Except.pure]
            · obtain ⟨bv, hbv, h⟩ := bind_eq_ok.mp h
              simp only [concV_chan, hb, bind_eq_ok]
              refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
              cases bv <;> simp only [quit] at h <;> try (cases h; done)
              next buf capacity closed =>
                cases h
                simp [concV_chanData, Array.size_map, hI.litI, pure,
                  Except.pure]
  | capacityOf typ =>
      rcases vs with _ | ⟨v, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStrictOp', quit] at h <;> try (cases h; done)
      simp only [List.map_cons, List.map_nil, applyStrictOp]
      split at h
      · cases h
        simp [hI.litI, pure, Except.pure, Bind.bind, Except.bind]
      · rename_i hno
        split
        · exact absurd rfl (hno _ _)
        · cases v <;> (try simp only [quit] at h) <;>
            try (cases h; done)
          case array values =>
            cases h
            simp [concV_array, Array.size_map, hI.litI, pure, Except.pure,
              Bind.bind, Except.bind]
          case addr baseLoc =>
            obtain ⟨bv, hbv, h⟩ := bind_eq_ok.mp h
            simp only [concV_addr, bind_eq_ok]
            refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
            cases bv <;> simp only [quit] at h <;> try (cases h; done)
            next values =>
              cases h
              simp [concV_array, Array.size_map, hI.litI, pure,
                Except.pure]
          case slice sl =>
            rcases hval : validateSlice' sl with e | u <;> rw [hval] at h
            · exact absurd h (by simp [quit, Bind.bind, Except.bind])
            obtain ⟨⟩ := u
            simp only [Bind.bind, Except.bind] at h
            cases h
            simp [concV_slice, validateSlice_conc hval, hI.litI,
              Bind.bind, Except.bind, pure, Except.pure, Seq.seq]
          case chan cv =>
            rcases hb : cv.base with _ | baseLoc <;> rw [hb] at h
            · cases h
              simp [concV_chan, hb, hI.litI, pure, Except.pure]
            · obtain ⟨bv, hbv, h⟩ := bind_eq_ok.mp h
              simp only [concV_chan, hb, bind_eq_ok]
              refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
              cases bv <;> simp only [quit] at h <;> try (cases h; done)
              next buf capacity closed =>
                cases h
                simp [concV_chanData, hI.litI, pure, Except.pure]

/-! ## THE WIDE-STATEMENT APPLY TABLES -/

/-- `Array.eraseIdx!` commutes with `map` (equal sizes ⇒ same branch;
the out-of-bounds branch is the default array on both sides). -/
private theorem list_map_eraseIdx {α β : Type _} (f : α → β) :
    ∀ (l : List α) (i : Nat),
      (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a as ih =>
      intro i
      cases i with
      | zero => simp
      | succ j => simp [List.eraseIdx, ih]

theorem map_eraseIdx! {α β : Type _}
    (f : α → β) (es : Array α) (i : Nat) :
    (es.eraseIdx! i).map f = (es.map f).eraseIdx! i := by
  unfold Array.eraseIdx!
  by_cases hi : i < es.size
  · rw [dif_pos hi, dif_pos (by simpa using hi)]
    have : ((es.eraseIdx i hi).map f).toList
        = ((es.map f).eraseIdx i (by simpa using hi)).toList := by
      simp [Array.toList_eraseIdx, list_map_eraseIdx]
    exact Array.toList_inj.mp this
  · rw [dif_neg hi, dif_neg (by simpa using hi)]
    -- position literals pinned to this toolchain's `Array.eraseIdx!`;
    -- a core bump that moves them shows up as a broken `rfl` HERE
    have hpA : (panicWithPosWithDecl (α := Array α) "Init.Data.Array.Basic"
        "Array.eraseIdx!" 1820 47 "invalid index") = #[] := rfl
    have hpB : (panicWithPosWithDecl (α := Array β) "Init.Data.Array.Basic"
        "Array.eraseIdx!" 1820 47 "invalid index") = #[] := rfl
    rw [hpA, hpB]
    simp

set_option maxHeartbeats 6400000 in
/-- The choices-free wide-op core, transported (∀ machine `nt` — the
core never reads it). -/
theorem applyStmtOpCore_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {op : StmtOp} {vs : List (Value D)} {s' : State D}
    (h : applyStmtOpCore' s op vs = .ok s') (nt : Nat) :
    applyStmtOpCore (concS I σ s) op nt (vs.map (concV I))
      = .ok (concS I σ s') := by
  cases op with
  | newValue typ =>
      rcases vs with _ | ⟨tv, _ | ⟨value, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
      rcases halloc : s.alloc value typ with ⟨nloc, s₁⟩
      rw [halloc] at h2
      simp only [] at h2
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      rw [alloc_conc, halloc]
      simp only []
      refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
      have := storeLoc_conc hI σ (loc := loc) (v := .addr nloc) h2
      simpa using this
  | makeSlice elem hasCap =>
      cases hasCap with
      | false =>
          rcases vs with _ | ⟨tv, _ | ⟨lenV, _ | ⟨x, rest⟩⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          obtain ⟨lenValue, hlen, h2⟩ := bind_eq_ok.mp h
          obtain ⟨lp, lk, rfl, hlt⟩ := asIntAt_inv hlen
          by_cases hneg : (lenValue < 0)
          · rw [if_pos hneg] at h2
            exact absurd h2 (by simp [quit])
          rw [if_neg hneg, if_neg hneg] at h2
          by_cases hcl : (lenValue.toNat < lenValue.toNat)
          · exact absurd hcl (by omega)
          rw [if_neg hcl] at h2
          obtain ⟨backing, hback, h3⟩ := bind_eq_ok.mp h2
          rcases halloc : s.alloc backing
              (some (.array lenValue.toNat elem)) with ⟨base, s₁⟩
          rw [halloc] at h3
          try simp only [] at h3
          obtain ⟨loc, hloc, h4⟩ := bind_eq_ok.mp h3
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind, concV_int]
          rw [show valueAsInt (GoValue.int (I.intV lp) lk)
                = .ok lenValue from by
              simp [valueAsInt, hI.toInt? _ _ hlt]]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt
                "runtime error: makeslice: len out of range" lenValue
                = .ok lenValue.toNat from by
              simp [natFromNonnegativeInt, hneg, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt
                "runtime error: makeslice: cap out of range" lenValue
                = .ok lenValue.toNat from by
              simp [natFromNonnegativeInt, hneg, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          rw [if_neg hcl]
          try simp only [ok_bind, pure_bind]
          rw [show buildDefaultArrayValue (concS I σ s) lenValue.toNat elem
                = .ok (concV I backing)
              from buildDefaultArrayValue_conc hI (concS I σ s) hback]
          simp only [ok_bind, pure_bind]
          rw [alloc_conc, halloc]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := Value.slice (D := D)
              ⟨some base, 0, lenValue.toNat, lenValue.toNat⟩) h4
          simpa using this
      | true =>
          rcases vs with _ | ⟨tv, _ | ⟨lenV, _ | ⟨capV, _ | ⟨x, rest⟩⟩⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          obtain ⟨lenValue, hlen, h2⟩ := bind_eq_ok.mp h
          obtain ⟨capValue, hcap, h3⟩ := bind_eq_ok.mp h2
          obtain ⟨lp, lk, rfl, hlt⟩ := asIntAt_inv hlen
          obtain ⟨cp, ck, rfl, hct⟩ := asIntAt_inv hcap
          by_cases hneg : (lenValue < 0)
          · rw [if_pos hneg] at h3
            exact absurd h3 (by simp [quit])
          rw [if_neg hneg] at h3
          by_cases hneg2 : (capValue < 0)
          · rw [if_pos hneg2] at h3
            exact absurd h3 (by simp [quit])
          rw [if_neg hneg2] at h3
          by_cases hcl : (capValue.toNat < lenValue.toNat)
          · rw [if_pos hcl] at h3
            exact absurd h3 (by simp [quit])
          rw [if_neg hcl] at h3
          obtain ⟨backing, hback, h4⟩ := bind_eq_ok.mp h3
          rcases halloc : s.alloc backing
              (some (.array capValue.toNat elem)) with ⟨base, s₁⟩
          rw [halloc] at h4
          try simp only [] at h4
          obtain ⟨loc, hloc, h5⟩ := bind_eq_ok.mp h4
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind, concV_int]
          rw [show valueAsInt (GoValue.int (I.intV lp) lk)
                = .ok lenValue from by
              simp [valueAsInt, hI.toInt? _ _ hlt]]
          simp only [ok_bind, pure_bind]
          rw [show valueAsInt (GoValue.int (I.intV cp) ck)
                = .ok capValue from by
              simp [valueAsInt, hI.toInt? _ _ hct]]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt
                "runtime error: makeslice: len out of range" lenValue
                = .ok lenValue.toNat from by
              simp [natFromNonnegativeInt, hneg, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt
                "runtime error: makeslice: cap out of range" capValue
                = .ok capValue.toNat from by
              simp [natFromNonnegativeInt, hneg2, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          rw [if_neg hcl]
          try simp only [ok_bind, pure_bind]
          rw [show buildDefaultArrayValue (concS I σ s) capValue.toNat elem
                = .ok (concV I backing)
              from buildDefaultArrayValue_conc hI (concS I σ s) hback]
          simp only [ok_bind, pure_bind]
          rw [alloc_conc, halloc]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := Value.slice (D := D)
              ⟨some base, 0, lenValue.toNat, capValue.toNat⟩) h5
          simpa using this
  | makeMap hasSpace =>
      cases hasSpace with
      | false =>
          rcases vs with _ | ⟨tv, _ | ⟨x, rest⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          rcases halloc : s.alloc (Value.mapData (D := D) #[]) none
            with ⟨base, s₁⟩
          rw [halloc] at h
          try simp only [] at h
          obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind]
          have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
            (v := Value.mapData (D := D) #[]) (ty := none)
          rw [halloc] at hallocm
          simp only [concV_mapData, Array.map_empty] at hallocm
          rw [hallocm]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := .map { base := some base }) h2
          simpa using this
      | true =>
          rcases vs with _ | ⟨tv, _ | ⟨spaceV, _ | ⟨x, rest⟩⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          obtain ⟨size, hsize, h2⟩ := bind_eq_ok.mp h
          obtain ⟨sp, sk, rfl, hst'⟩ := asIntAt_inv hsize
          by_cases hneg : (size < 0)
          · rw [if_pos hneg] at h2
            exact absurd h2 (by simp [quit, Bind.bind, Except.bind])
          rw [if_neg hneg] at h2
          rcases halloc : s.alloc (Value.mapData (D := D) #[]) none
            with ⟨base, s₁⟩
          rw [halloc] at h2
          try simp only [] at h2
          obtain ⟨loc, hloc, h4⟩ := bind_eq_ok.mp h2
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind, concV_int]
          rw [show valueAsInt (GoValue.int (I.intV sp) sk)
                = .ok size from by
              simp [valueAsInt, hI.toInt? _ _ hst']]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt "makemap: size out of range" size
                = .ok size.toNat from by
              simp [natFromNonnegativeInt, hneg, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
            (v := Value.mapData (D := D) #[]) (ty := none)
          rw [halloc] at hallocm
          simp only [concV_mapData, Array.map_empty] at hallocm
          rw [hallocm]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := .map { base := some base }) h4
          simpa using this
  | makeChan hasCap =>
      cases hasCap with
      | false =>
          rcases vs with _ | ⟨tv, _ | ⟨x, rest⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          rcases halloc : s.alloc (Value.chanData (D := D) #[] 0 false) none
            with ⟨base, s₁⟩
          rw [halloc] at h
          try simp only [] at h
          obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind]
          have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
            (v := Value.chanData (D := D) #[] 0 false) (ty := none)
          rw [halloc] at hallocm
          simp only [concV_chanData, Array.map_empty] at hallocm
          rw [hallocm]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := .chan { base := some base }) h2
          simpa using this
      | true =>
          rcases vs with _ | ⟨tv, _ | ⟨capV, _ | ⟨x, rest⟩⟩⟩ <;>
            simp only [applyStmtOpCore', quit, pure_bind] at h <;>
            first
              | (cases h; done)
              | (simp [quit, Bind.bind, Except.bind] at h; done)
              | skip
          obtain ⟨size, hsize, h2⟩ := bind_eq_ok.mp h
          obtain ⟨sp, sk, rfl, hst'⟩ := asIntAt_inv hsize
          by_cases hneg : (size < 0)
          · rw [if_pos hneg] at h2
            exact absurd h2 (by simp [quit, Bind.bind, Except.bind])
          rw [if_neg hneg] at h2
          obtain ⟨loc, hloc, h4⟩ := bind_eq_ok.mp h2
          rcases halloc : s.alloc
              (Value.chanData (D := D) #[] size.toNat false) none
            with ⟨base, s₁⟩
          rw [halloc] at h4
          try simp only [] at h4
          simp only [List.map_cons, List.map_nil, applyStmtOpCore,
            pure_bind, concV_int]
          rw [show valueAsInt (GoValue.int (I.intV sp) sk)
                = .ok size from by
              simp [valueAsInt, hI.toInt? _ _ hst']]
          simp only [ok_bind, pure_bind]
          rw [show natFromNonnegativeInt "makechan: size out of range" size
                = .ok size.toNat from by
              simp [natFromNonnegativeInt, hneg, pure, Except.pure,
                Bind.bind, Except.bind]]
          simp only [ok_bind, pure_bind]
          have hallocm := alloc_conc (I := I) (σ := σ) (s := s)
            (v := Value.chanData (D := D) #[] size.toNat false) (ty := none)
          rw [halloc] at hallocm
          simp only [concV_chanData, Array.map_empty] at hallocm
          rw [hallocm]
          simp only []
          rw [show valueAsLoc (concV I tv) = .ok loc from asLoc_conc hloc]
          simp only [ok_bind, pure_bind]
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := .chan { base := some base }) h4
          simpa using this
  | mapAssign keyTy valueTy =>
      rcases vs with _ | ⟨baseV, _ | ⟨keyV, _ | ⟨valueV, _ | ⟨x, rest⟩⟩⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      simpa [applyStmtOpCore] using mapAssignValue_conc hI σ h
  | mapDelete keyTy =>
      rcases vs with _ | ⟨baseV, _ | ⟨keyV, _ | ⟨x, rest⟩⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨map, hmap, h2⟩ := bind_eq_ok.mp h
      obtain ⟨key, hkey, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨me, hme, h4⟩ := bind_eq_ok.mp h3
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
      refine bind_eq_ok.mpr ⟨concV I key, normalize_conc hI _ hkey, ?_⟩
      refine bind_eq_ok.mpr
        ⟨me.map (fun p => (p.1, concEntries I p.2)),
          mapEntries_conc σ hme, ?_⟩
      rcases me with _ | ⟨baseLoc, entries⟩
      · obtain ⟨u, hchk, h5⟩ := bind_eq_ok.mp h4
        have hss : s' = s := by
          simpa [pure, Except.pure, eq_comm] using h5
        rw [hss]
        simp only [Option.map_none]
        refine bind_eq_ok.mpr
          ⟨(), checkKeyHashable_conc hI (concS I σ s) hchk _ _, rfl⟩
      · simp only [Option.map_some] at *
        obtain ⟨idx, hidx, h5⟩ := bind_eq_ok.mp h4
        refine bind_eq_ok.mpr
          ⟨idx, mapEntryIndex_conc hI (concS I σ s) hidx _, ?_⟩
        rcases idx with _ | i <;> simp only [] at h5 ⊢
        · have hss : s' = s := by
            simpa [pure, Except.pure, eq_comm] using h5
          rw [hss]
          rfl
        · have := storeLoc_conc hI σ (loc := baseLoc)
            (v := .mapData (entries.eraseIdx! i)) h5
          refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
          simpa [concV_mapData, concEntries, map_eraseIdx!] using this
  | clearMap =>
      rcases vs with _ | ⟨baseV, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨map, hmap, h2⟩ := bind_eq_ok.mp h
      obtain ⟨me, hme, h3⟩ := bind_eq_ok.mp h2
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
      refine bind_eq_ok.mpr
        ⟨me.map (fun p => (p.1, concEntries I p.2)),
          mapEntries_conc σ hme, ?_⟩
      rcases me with _ | ⟨baseLoc, entries⟩
      · have hss : s' = s := by
          simpa [pure, Except.pure, eq_comm] using h3
        rw [hss]
        rfl
      · simp only [Option.map_some]
        have := storeLoc_conc hI σ (loc := baseLoc)
          (v := Value.mapData (D := D) #[]) h3
        refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
        simpa [concV_mapData] using this
  | clearSlice elem =>
      rcases vs with _ | ⟨baseV, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨sl, hsl, h2⟩ := bind_eq_ok.mp h
      obtain ⟨u, hval, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨⟩ := u
      obtain ⟨zero, hzero, h4⟩ := bind_eq_ok.mp h3
      obtain ⟨fin, hloop, h5⟩ := bind_eq_ok.mp h4
      have hfin : s' = fin := by
        simpa [pure, Except.pure, eq_comm] using h5
      subst hfin
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨sl, asSlice_conc hsl, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval, ?_⟩
      refine bind_eq_ok.mpr
        ⟨concV I zero, default_conc hI (concS I σ s) hzero, ?_⟩
      refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop ⊢
      refine forIn_conc_mapS (φ := concS I σ)
        (fun i _ cur st hst => ?_) hloop
      obtain ⟨loc, hloc, hst2⟩ := bind_eq_ok.mp hst
      obtain ⟨cur', hstore, hst3⟩ := bind_eq_ok.mp hst2
      have hstv : st = .yield cur' := by
        simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
          using hst3
      subst hstv
      refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
      refine bind_eq_ok.mpr
        ⟨concS I σ cur', storeLoc_conc hI σ hstore, ?_⟩
      simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
  | sortSlice elem =>
      rcases vs with _ | ⟨baseV, _ | ⟨x, rest⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨sl, hsl, h2⟩ := bind_eq_ok.mp h
      obtain ⟨u, hval, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨⟩ := u
      obtain ⟨rp, hload, h4⟩ := bind_eq_ok.mp h3
      obtain ⟨fin, hstore, h5⟩ := bind_eq_ok.mp h4
      have hfin : s' = fin := by
        simpa [pure, Except.pure, eq_comm] using h5
      subst hfin
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨sl, asSlice_conc hsl, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval, ?_⟩
      refine bind_eq_ok.mpr ⟨rp, ?_, ?_⟩
      · -- the load loop: same range, same state type, state equal
        rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hload ⊢
        refine forIn_conc_mapS
          (φ := fun a : Array (Int × IntKind) => a)
          (fun i _ acc st hst => ?_) hload
        obtain ⟨loc, hloc, hst2⟩ := bind_eq_ok.mp hst
        obtain ⟨w, hw, hst3⟩ := bind_eq_ok.mp hst2
        refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
        refine bind_eq_ok.mpr ⟨concV I w, loadLoc_conc σ hw, ?_⟩
        cases w <;> (try simp only [quit] at hst3) <;>
          try (cases hst3; done)
        next vR kind =>
          rcases ht : D.toInt? vR with _ | n <;> rw [ht] at hst3 <;>
            (try simp only [] at hst3)
          · exact absurd hst3 (by simp [quit, Bind.bind, Except.bind])
          have hstv : st = .yield (acc.push (n, kind)) := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst3
          subst hstv
          simp only [concV_int, show I.intV vR = n from hI.toInt? _ _ ht]
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
      · -- the store loop: same range, image state
        refine bind_eq_ok.mpr ⟨concS I σ s', ?_, rfl⟩
        rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hstore ⊢
        refine forIn_conc_mapS (φ := concS I σ)
          (fun i _ cur st hst => ?_) hstore
        split at hst
        · rename_i n kind hget
          obtain ⟨loc, hloc, hst2⟩ := bind_eq_ok.mp hst
          obtain ⟨cur', hstore', hst3⟩ := bind_eq_ok.mp hst2
          have hstv : st = .yield cur' := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst3
          subst hstv
          rw [hget]
          simp only []
          refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
          have := storeLoc_conc hI σ (loc := loc)
            (v := Value.int (D := D) (D.litI n) kind) hstore'
          simp only [concV_int, hI.litI] at this
          refine bind_eq_ok.mpr ⟨concS I σ cur', this, ?_⟩
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
        · exact absurd hst (by simp [quit, Bind.bind, Except.bind])
  | copySlice =>
      rcases vs with _ | ⟨tv, _ | ⟨dstV, _ | ⟨srcV, _ | ⟨x, rest⟩⟩⟩⟩ <;>
        simp only [applyStmtOpCore', quit] at h <;> try (cases h; done)
      obtain ⟨dstSlice, hdst, h2⟩ := bind_eq_ok.mp h
      obtain ⟨srcSlice, hsrc, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨u, hval1, h4⟩ := bind_eq_ok.mp h3
      obtain ⟨⟩ := u
      obtain ⟨u, hval2, h5⟩ := bind_eq_ok.mp h4
      obtain ⟨⟩ := u
      obtain ⟨values, hloadloop, h6⟩ := bind_eq_ok.mp h5
      obtain ⟨rp, hstoreloop, h7⟩ := bind_eq_ok.mp h6
      obtain ⟨tloc, htloc, h8⟩ := bind_eq_ok.mp h7
      simp only [List.map_cons, List.map_nil, applyStmtOpCore]
      refine bind_eq_ok.mpr ⟨dstSlice, asSlice_conc hdst, ?_⟩
      refine bind_eq_ok.mpr ⟨srcSlice, asSlice_conc hsrc, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval1, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval2, ?_⟩
      refine bind_eq_ok.mpr ⟨values.map (concV I), ?_, ?_⟩
      · -- load loop
        rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloadloop ⊢
        rw [show (#[] : Array GoValue)
              = Array.map (concV I) (#[] : Array (Value D)) from by simp]
        refine forIn_conc_mapS
          (φ := fun a : Array (Value D) => a.map (concV I))
          (fun i _ acc st hst => ?_) hloadloop
        obtain ⟨loc, hloc, hst2⟩ := bind_eq_ok.mp hst
        obtain ⟨w, hw, hst3⟩ := bind_eq_ok.mp hst2
        have hstv : st = .yield (acc.push w) := by
          simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
            using hst3
        subst hstv
        refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
        refine bind_eq_ok.mpr ⟨concV I w, loadLoc_conc σ hw, ?_⟩
        simp [stepImage, pure, Except.pure, Bind.bind, Except.bind,
          Array.map_push]
      · -- store loop then target store
        refine bind_eq_ok.mpr
          ⟨⟨concS I σ rp.fst, rp.snd⟩, ?_, ?_⟩
        · rw [← Array.forIn_toList] at hstoreloop
          rw [← Array.forIn_toList, Array.toList_map]
          refine forIn_conc_map (t := concV I)
            (φ := fun m : MProd (State D) Nat =>
              (⟨concS I σ m.fst, m.snd⟩ : MProd ExecState Nat))
            (fun a _ m st hst => ?_) hstoreloop
          obtain ⟨loc, hloc, hst2⟩ := bind_eq_ok.mp hst
          obtain ⟨cur', hstore', hst3⟩ := bind_eq_ok.mp hst2
          have hstv : st = .yield ⟨cur', m.snd + 1⟩ := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst3
          subst hstv
          refine bind_eq_ok.mpr ⟨loc, sliceIndexLoc_conc hloc, ?_⟩
          refine bind_eq_ok.mpr
            ⟨concS I σ cur', storeLoc_conc hI σ hstore', ?_⟩
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
        · refine bind_eq_ok.mpr ⟨tloc, asLoc_conc htloc, ?_⟩
          have := storeLoc_conc hI σ (loc := tloc)
            (v := Value.int (D := D)
              (D.litI (Int.ofNat (Nat.min dstSlice.len srcSlice.len)))
              .int) h8
          simp only [concV_int, hI.litI] at this
          refine bind_eq_ok.mpr ⟨concS I σ s', this, rfl⟩
  | appendSlice elem =>
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨x, rest⟩⟩⟩⟩ <;>
        simp [applyStmtOpCore', quit] at h

set_option maxHeartbeats 6400000 in
/-- The wide-statement apply, transported: `appendSlice` in-cap
computes; the SPILL quits Q3, so the mirror's success is `ch`-invariant
by construction — ∀ machine choice streams, unchanged. -/
theorem applyStmtOp_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {op : StmtOp} {vs : List (Value D)} {s' : State D}
    (h : applyStmtOp' s op vs = .ok s') (nt : Nat) (choices : Choices) :
    applyStmtOp (concS I σ s) choices op nt (vs.map (concV I))
      = .ok (concS I σ s', choices) := by
  cases op with
  | appendSlice elem =>
      rcases vs with _ | ⟨tv, _ | ⟨sliceV, _ | ⟨elemsV, _ | ⟨x, rest⟩⟩⟩⟩ <;>
        simp only [applyStmtOp', quit] at h <;> try (cases h; done)
      obtain ⟨sl, hsl, h2⟩ := bind_eq_ok.mp h
      obtain ⟨els, hels, h3⟩ := bind_eq_ok.mp h2
      obtain ⟨u, hval1, h4⟩ := bind_eq_ok.mp h3
      obtain ⟨⟩ := u
      obtain ⟨u, hval2, h5⟩ := bind_eq_ok.mp h4
      obtain ⟨⟩ := u
      obtain ⟨elemValues, hvis, h6⟩ := bind_eq_ok.mp h5
      obtain ⟨tloc, htloc, h7⟩ := bind_eq_ok.mp h6
      simp only [List.map_cons, List.map_nil, applyStmtOp]
      refine bind_eq_ok.mpr ⟨sl, asSlice_conc hsl, ?_⟩
      refine bind_eq_ok.mpr ⟨els, asSlice_conc hels, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval1, ?_⟩
      refine bind_eq_ok.mpr ⟨(), validateSlice_conc hval2, ?_⟩
      refine bind_eq_ok.mpr
        ⟨elemValues.map (concV I), sliceVisible_conc σ hvis, ?_⟩
      refine bind_eq_ok.mpr ⟨tloc, asLoc_conc htloc, ?_⟩
      simp only [Array.size_map]
      by_cases hcap : (sl.len + elemValues.size ≤ sl.cap)
      · rw [if_pos hcap] at h7
        rw [if_pos hcap]
        obtain ⟨rp, hloop, h8⟩ := bind_eq_ok.mp h7
        refine bind_eq_ok.mpr
          ⟨⟨concS I σ rp.fst, rp.snd⟩, ?_, ?_⟩
        · rw [← Array.forIn_toList] at hloop
          rw [← Array.forIn_toList, Array.toList_map]
          refine forIn_conc_map (t := concV I)
            (φ := fun m : MProd (State D) Nat =>
              (⟨concS I σ m.fst, m.snd⟩ : MProd ExecState Nat))
            (fun a _ m st hst => ?_) hloop
          rcases hbase : sl.base with _ | base <;> rw [hbase] at hst <;>
            (try simp only [] at hst)
          · exact absurd hst (by simp [quit, Bind.bind, Except.bind])
          obtain ⟨cur', hstore', hst2⟩ := bind_eq_ok.mp hst
          have hstv : st = .yield ⟨cur', m.snd + 1⟩ := by
            simpa [pure, Except.pure, Bind.bind, Except.bind, eq_comm]
              using hst2
          subst hstv
          simp only []
          refine bind_eq_ok.mpr
            ⟨concS I σ cur', storeLoc_conc hI σ hstore', ?_⟩
          simp [stepImage, pure, Except.pure, Bind.bind, Except.bind]
        · have := storeLoc_conc hI σ (loc := tloc)
            (v := Value.slice (D := D)
              { sl with len := sl.len + elemValues.size }) h8
          simp only [concV_slice] at this
          refine bind_eq_ok.mpr ⟨concS I σ s', this, rfl⟩
      · rw [if_neg hcap] at h7
        exact absurd h7 (by simp [quit])
  | _ =>
      simp only [applyStmtOp'] at h
      simp only [applyStmtOp]
      refine bind_eq_ok.mpr
        ⟨concS I σ s', applyStmtOpCore_conc hI σ h nt, rfl⟩

end GoLean.Sym
