import GoLean.GoCore.RecoveryAdmission
import GoLean.GoCore.RecoveryAllocation
import GoLean.GoCore.BooleanInitialization

/-! Structural facts needed by actual recovery entry. The source syntax
contains no preallocated machine addresses, and distinct signature keys
connect ordered static lookup with the real reverse-order declarations. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem expr_locSup {Γ e sort} (h : ExprTyped Γ e sort) : Expr.locSup e = 0 := by
  induction h <;> simp_all [Expr.locSup]

theorem target_locSup {Γ a sort} (h : TargetTyped Γ a sort) : Assignee.locSup a = 0 := by
  cases h with
  | var => rfl
  | addr he => exact expr_locSup he

theorem arguments_locSup {Γ es ps} (h : Arguments Γ es ps) : exprListSup es = 0 := by
  induction h with
  | nil => rfl
  | cons he _ ih =>
    cases he with
    | typed _ he => simp [exprListSup, expr_locSup he, ih]

theorem targets_locSup {Γ as ps} (h : Targets Γ as ps) : assigneeListSup as = 0 := by
  induction h with
  | nil => rfl
  | cons ha _ ih =>
    cases ha with
    | typed _ ha => simp [assigneeListSup, target_locSup ha, ih]

mutual
theorem statement_locSup {fs b Γ s} (h : Statement fs b Γ s) : Stmt.locSup s = 0 := by
  cases h with
  | seqn hs => exact statements_locSup hs
  | block _ _ hs => exact statements_locSup hs
  | initialization => rfl
  | assign ha =>
    cases ha with
    | typed ht he => simp [Stmt.locSup, target_locSup ht, expr_locSup he]
  | branch he ht hf _ _ =>
    simp [Stmt.locSup, expr_locSup he, statement_locSup ht, statement_locSup hf]
  | call hc =>
    obtain ⟨_, _, ha, ht⟩ := hc
    simp [Stmt.locSup, targets_locSup ht, arguments_locSup ha]
  | closureCall hc =>
    cases hc with
    | known _ _ ha ht =>
      have he := arguments_locSup ha
      rw [exprListSup_append] at he
      simp only [Stmt.locSup, Expr.locSup, targets_locSup ht, Nat.zero_max]
      exact he
  | deferCall hc =>
    cases hc with
    | known _ _ ha =>
      simpa [Stmt.locSup, Expr.locSup, exprListSup_append] using arguments_locSup ha
  | panic he =>
    cases he with
    | stringBox _ he => simpa [Stmt.locSup, Expr.locSup] using expr_locSup he
  | ret => rfl
termination_by structural s
theorem statements_locSup {fs Γ ss} (h : Statements fs Γ ss) : stmtListSup ss = 0 := by
  cases h with
  | nil => rfl
  | cons hs hss => simp [stmtListSup, statement_locSup hs, statements_locSup hss]
termination_by structural ss
end

theorem program_funcListSup {p : Program} (h : ProgramTyped p) :
    funcListSup p.funcs.toList = 0 := by
  have hall : ∀ f ∈ p.funcs.toList, Func.locSup f = 0 := by
    intro f hf
    exact statement_locSup (h.2.2.1 f hf).2.2.2.2.1
  generalize p.funcs.toList = fs at *
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [funcListSup, hall f (by simp), Nat.zero_max]
    exact ih (fun g hg => hall g (by simp [hg]))

theorem programState_wf {p : Program} (h : ProgramTyped p) :
    StateWf (BooleanRuntime.programState p) := by
  simp [StateWf, ExecState.locSup, BooleanRuntime.programState, Heap.locSup,
    heapCellsSup, ExecState.nextAddr, program_funcListSup h]

theorem program_no_init {p : Program} (h : ProgramTyped p) :
    findFunctionIn? p.funcs pkgInitFuncId = none :=
  BooleanRuntime.findFunction_none (fun f hf => (h.2.2.1 f hf).1.1)

theorem declareMany_append (Γ : Context) (ps qs : List Param) :
    declareMany Γ (ps ++ qs) = declareMany (declareMany Γ ps) qs := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih => exact ih (RecoveryTyping.declare Γ p)

theorem declareMany_lookup_absent (Γ : Context) (ps : List Param) (name : String)
    (h : name ∉ ps.map Param.id) :
    RecoveryTyping.lookup (declareMany Γ ps) name = RecoveryTyping.lookup Γ name := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [declareMany, ih _ h.2, RecoveryTyping.lookup_declare,
      if_neg (Ne.symm h.1)]

theorem declareMany_lookup_member (Γ : Context) (ps : List Param)
    (hd : (ps.map Param.id).Nodup) (p : Param) (hp : p ∈ ps) :
    RecoveryTyping.lookup (declareMany Γ ps) p.id = some p.typ := by
  induction ps generalizing Γ with
  | nil => simp at hp
  | cons q ps ih =>
    have hn := List.nodup_cons.mp hd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [declareMany, declareMany_lookup_absent _ _ _ hn.1,
        RecoveryTyping.lookup_declare, ↓reduceIte]
    · exact ih (RecoveryTyping.declare Γ q) hn.2 hp

theorem scopeLookup_member {scope : RecoveryTyping.Scope} {name ty}
    (h : scopeLookup scope name = some ty) : (name, ty) ∈ scope := by
  induction scope with
  | nil => simp [scopeLookup] at h
  | cons binding rest ih =>
    rcases binding with ⟨key, value⟩
    simp only [scopeLookup] at h
    split at h
    · rename_i hk
      cases hk
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem EnvTyped.initialContext {world env f}
    (h : EnvTyped world (declareMany [] (f.args.toList ++ f.results.toList)) env)
    (hd : SignatureDistinct f) : EnvTyped world (initialContext f) env := by
  refine ⟨h.bindings, ?_⟩
  intro name ty ht
  have hs : scopeLookup ((f.args.toList ++ f.results.toList).map
      (fun p => (p.id, p.typ))) name = some ty := by
    change (match scopeLookup ((f.args.toList ++ f.results.toList).map
      (fun p => (p.id, p.typ))) name with
      | some value => some value | none => none) = some ty at ht
    split at ht <;> simp_all
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (scopeLookup_member hs)
  rcases Prod.mk.inj he with ⟨rfl, rfl⟩
  exact h.lookup p.id p.typ (declareMany_lookup_member [] _ hd p hp)

theorem scopeLookup_none_iff (scope : RecoveryTyping.Scope) (name : String) :
    scopeLookup scope name = none ↔ name ∉ scope.map Prod.fst := by
  induction scope with
  | nil => simp [scopeLookup]
  | cons binding rest ih =>
    rcases binding with ⟨key, ty⟩
    by_cases hk : key = name
    · subst key
      simp [scopeLookup]
    · simp [scopeLookup, hk, Ne.symm hk, ih]

/-- Block allocation reverses its own fresh scope's bindings. Distinct
parameter keys make that lookup equivalent to the source's ordered scope;
the outer context keeps its exact first-match meaning, including shadowing. -/
theorem EnvTyped.pushedDecls {world Γ env ps}
    (h : EnvTyped world (declareMany (RecoveryTyping.push Γ #[]) ps) env)
    (hd : (ps.map Param.id).Nodup) :
    EnvTyped world (RecoveryTyping.push Γ ps.toArray) env := by
  refine ⟨h.bindings, ?_⟩
  intro name ty ht
  change (match scopeLookup (ps.map (fun p => (p.id, p.typ))) name with
    | some value => some value | none => RecoveryTyping.lookup Γ name) = some ty at ht
  cases hs : scopeLookup (ps.map (fun p => (p.id, p.typ))) name with
  | some value =>
    have he : value = ty := by simpa [hs] using ht
    subst value
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (scopeLookup_member hs)
    rcases Prod.mk.inj he with ⟨rfl, rfl⟩
    exact h.lookup p.id p.typ (declareMany_lookup_member _ _ hd p hp)
  | none =>
    have hn : name ∉ ps.map Param.id := by
      simpa [List.map_map, Function.comp_def] using
        (scopeLookup_none_iff _ name).mp hs
    apply h.lookup name ty
    rw [declareMany_lookup_absent _ _ _ hn]
    simpa [RecoveryTyping.push, RecoveryTyping.lookup, scopeLookup, hs] using ht

end GoLean.GoCore.RecoveryRuntime
