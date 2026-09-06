import GoLean.GoCore.RecoveryEnvironment
import GoLean.GoCore.RecoveryStatements

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

/-- Sort-preserving first-match inclusion, unlike Boolean name membership. -/
def Included (Γ Δ : Context) : Prop := ∀ name sort, Has Γ name sort → Has Δ name sort

theorem Included.refl (Γ : Context) : Included Γ Γ := fun _ _ h => h
theorem Included.trans {Γ Δ Ξ} (h : Included Γ Δ) (h' : Included Δ Ξ) :
    Included Γ Ξ := fun name sort hn => h' name sort (h name sort hn)

theorem lookup_append (Γ Δ : Context) (name : String) :
    RecoveryTyping.lookup (Γ ++ Δ) name =
      (RecoveryTyping.lookup Γ name).orElse (fun _ => RecoveryTyping.lookup Δ name) := by
  induction Γ with
  | nil => rfl
  | cons scope rest ih =>
    simp only [List.cons_append, RecoveryTyping.lookup]
    cases scopeLookup scope name <;> simp [ih]

theorem Included.declare {Γ Δ} (h : Included Γ Δ) (p : Param) :
    Included (RecoveryTyping.declare Γ p) (RecoveryTyping.declare Δ p) := by
  rintro name sort ⟨ty, hl, ht⟩
  rw [RecoveryTyping.lookup_declare] at hl
  by_cases hn : p.id = name
  · exact ⟨ty, by simpa [RecoveryTyping.lookup_declare, hn] using hl, ht⟩
  · have old : Has Γ name sort := ⟨ty, by simpa [hn] using hl, ht⟩
    obtain ⟨ty', hl', ht'⟩ := h name sort old
    exact ⟨ty', by simpa [RecoveryTyping.lookup_declare, hn] using hl', ht'⟩

theorem Included.push {Γ Δ} (h : Included Γ Δ) (ps : Array Param) :
    Included (RecoveryTyping.push Γ ps) (RecoveryTyping.push Δ ps) := by
  rintro name sort ⟨ty, hl, ht⟩
  simp only [RecoveryTyping.push, RecoveryTyping.lookup] at hl ⊢
  cases hs : scopeLookup (ps.toList.map (fun p => (p.id, p.typ))) name with
  | some ty' => exact ⟨ty, by simpa [RecoveryTyping.lookup, hs] using hl, ht⟩
  | none =>
    obtain ⟨ty', hl', ht'⟩ := h name sort ⟨ty, by simpa [hs] using hl, ht⟩
    exact ⟨ty', by simpa [RecoveryTyping.lookup, hs] using hl', ht'⟩

theorem Included.append_left (Γ Δ : Context) : Included Γ (Γ ++ Δ) := by
  rintro name sort ⟨ty, hl, ht⟩
  exact ⟨ty, by simp [lookup_append, hl], ht⟩

theorem AddressTyped.unique {world left right loc}
    (hl : AddressTyped world left loc) (hr : AddressTyped world right loc) : left = right := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨b, hb, hbr⟩ := hr
  cases hb
  exact Option.some.inj (ha.symm.trans hbr)

theorem EnvTyped.compatible {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) {name left right}
    (hl : Has Γ name left) (hr : Has Δ name right) : left = right := by
  obtain ⟨loc, he, ha⟩ := h.has hl
  obtain ⟨loc', he', ha'⟩ := h'.has hr
  have hloc : loc = loc' := Option.some.inj (he.symm.trans he')
  subst loc'
  exact ha.unique ha'

theorem EnvTyped.append {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) : EnvTyped world (Γ ++ Δ) env := by
  refine ⟨h.bindings, ?_⟩
  intro name ty ht
  rw [lookup_append] at ht
  cases hh : RecoveryTyping.lookup Γ name with
  | none => exact h'.lookup name ty (by simpa [hh] using ht)
  | some ty' =>
    have he : ty' = ty := by simpa [hh] using ht
    subst ty'
    exact h.lookup name ty hh

/-- Shared actual lookup makes the two static contexts compatible. This
lemma is used only when combining neutral statement lists: a declaration
can overwrite a name's sort and does not preserve arbitrary right contexts. -/
theorem EnvTyped.included_append_right {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) : Included Δ (Γ ++ Δ) := by
  rintro name sort ⟨ty, hl, ht⟩
  cases hh : RecoveryTyping.lookup Γ name with
  | none => exact ⟨ty, by simp [lookup_append, hh, hl], ht⟩
  | some ty' =>
    obtain ⟨loc, _, kind, hk, _⟩ := h.lookup name ty' hh
    have he : kind = sort := h.compatible h' ⟨ty', hh, hk⟩ ⟨ty, hl, ht⟩
    subst kind
    exact ⟨ty', by simp [lookup_append, hh], hk⟩

theorem expr_weaken {Γ Δ e sort} (h : ExprTyped Γ e sort) (inc : Included Γ Δ) :
    ExprTyped Δ e sort := by
  induction h with
  | var hn => exact .var (inc _ _ hn)
  | boolean b => exact .boolean b
  | string s => exact .string s
  | nil hn => exact .nil hn
  | not _ ih => exact .not ih
  | and _ _ ih ih' => exact .and ih ih'
  | or _ _ ih ih' => exact .or ih ih'
  | ref hn => exact .ref (inc _ _ hn)
  | deref _ ih => exact .deref ih
  | box ht _ ih => exact .box ht ih
  | recover => exact .recover
  | eqBool ht _ _ ih ih' => exact .eqBool ht ih ih'
  | neqBool ht _ _ ih ih' => exact .neqBool ht ih ih'
  | eqNil ht _ _ hn ih ih' => exact .eqNil ht ih ih' hn
  | neqNil ht _ _ hn ih ih' => exact .neqNil ht ih ih' hn

theorem exprAt_weaken {Γ Δ e ty} (h : ExprAt Γ e ty) (inc : Included Γ Δ) :
    ExprAt Δ e ty := by
  cases h with
  | typed ht he => exact .typed ht (expr_weaken he inc)

theorem target_weaken {Γ Δ target sort} (h : TargetTyped Γ target sort)
    (inc : Included Γ Δ) : TargetTyped Δ target sort := by
  cases h with
  | var hn => exact .var (inc _ _ hn)
  | addr he => exact .addr (expr_weaken he inc)

theorem targetAt_weaken {Γ Δ target ty} (h : TargetAt Γ target ty)
    (inc : Included Γ Δ) : TargetAt Δ target ty := by
  cases h with
  | typed ht ha => exact .typed ht (target_weaken ha inc)

theorem arguments_weaken {Γ Δ es ps} (h : Arguments Γ es ps) (inc : Included Γ Δ) :
    Arguments Δ es ps := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (exprAt_weaken he inc) ih

theorem targets_weaken {Γ Δ targets ps} (h : Targets Γ targets ps) (inc : Included Γ Δ) :
    Targets Δ targets ps := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (targetAt_weaken he inc) ih

theorem captures_weaken {Γ Δ es} (h : Captures Γ es) (inc : Included Γ Δ) :
    Captures Δ es := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (expr_weaken he inc) ih

end GoLean.GoCore.RecoveryRuntime
