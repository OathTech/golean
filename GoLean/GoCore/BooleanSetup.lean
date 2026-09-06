import GoLean.GoCore.BooleanStore
import GoLean.GoCore.Admission
import GoLean.GoCore.StepFn

/-! Generic Boolean entry/setup facts for the actual program driver.
This module derives setup success; it does not assume an execution succeeds
or claim that A3a's syntax predicate supplies a typed control configuration. -/
namespace GoLean.GoCore.BooleanRuntime
open Machine Admission

theorem boolExpr_locSup {e : Expr} (h : BoolExpr e) : Expr.locSup e = 0 := by
  induction h <;> simp_all [Expr.locSup]

mutual
theorem boolStmt_locSup {s : Stmt} (h : BoolStmt s) : Stmt.locSup s = 0 := by
  cases h with
  | seqn hs => exact boolStmts_locSup hs
  | block _ hs => exact boolStmts_locSup hs
  | initialization _ => rfl
  | assign he => simp [Stmt.locSup, Assignee.locSup, boolExpr_locSup he]
  | branch he ht hf =>
    simp [Stmt.locSup, boolExpr_locSup he, boolStmt_locSup ht, boolStmt_locSup hf]
  | ret => rfl
termination_by structural s
theorem boolStmts_locSup {ss : List Stmt} (h : BoolStmts ss) : stmtListSup ss = 0 := by
  cases h with
  | nil => rfl
  | cons hs hss => simp [stmtListSup, boolStmt_locSup hs, boolStmts_locSup hss]
termination_by structural ss
end

set_option maxRecDepth 4096 in
theorem reservedPrefix_runtime {types : TypeEnv} (h : ReservedPrefix types) :
    types.hasReservedPrefix = true := by
  have hlist := reservedPrefix_exact h
  have he : types.extract 0 2 = TypeEnv.reserved := by
    apply Array.toList_inj.mp
    simpa using hlist
  rw [TypeEnv.hasReservedPrefix, he]
  rfl

/-- The exact immutable fields with which the real program driver starts. -/
def programState (p : Program) : ExecState :=
  { types := p.typeDefs, functions := p.funcs, methods := p.methods,
    methodSets := p.methodSets, typeDisplays := p.typeDisplays }

theorem booleanSyntax_funcListSup {p : Program} (h : BooleanSyntax p) :
    funcListSup p.funcs.toList = 0 := by
  have hall : ∀ f ∈ p.funcs.toList, Func.locSup f = 0 := by
    intro f hf
    exact boolStmt_locSup (h.2.2 f hf).2.2.2.2.2
  generalize p.funcs.toList = fs at *
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [funcListSup, hall f (by simp), Nat.zero_max]
    exact ih (fun g hg => hall g (by simp [hg]))

theorem programState_wf {p : Program} (h : BooleanSyntax p) :
    StateWf (programState p) := by
  simp [StateWf, ExecState.locSup, programState, Heap.locSup,
    heapCellsSup, ExecState.nextAddr, booleanSyntax_funcListSup h]

theorem funcId_beq_iff (a b : FuncId) : (a == b) = true ↔ a = b := by
  cases a; cases b
  simp [BEq.beq, instBEqFuncId.beq]

theorem findFunction_none {funcs : Array Func} {fid : FuncId}
    (h : ∀ f ∈ funcs.toList, f.id ≠ fid) : findFunctionIn? funcs fid = none := by
  unfold findFunctionIn?
  rw [← Array.foldl_toList]
  generalize funcs.toList = fs at *
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have hn : (f.id == fid) = false := by
      cases hb : (f.id == fid) with
      | false => rfl
      | true => exact False.elim (h f (by simp) ((funcId_beq_iff f.id fid).mp hb))
    simpa only [List.foldl_cons, hn, Bool.false_eq_true, ↓reduceIte] using
      ih (fun g hg => h g (by simp [hg]))

theorem booleanSyntax_no_init {p : Program} (h : BooleanSyntax p) :
    findFunctionIn? p.funcs pkgInitFuncId = none :=
  findFunction_none (fun f hf => (h.2.2 f hf).1)

theorem seedGlobals_empty (p : Program) :
    seedGlobals (programState p) #[] = .ok (programState p) := by
  simp [seedGlobals, programState, ExecState.nextAddr]
  rfl

theorem findFunction_mem {funcs : Array Func} {fid : FuncId} {f : Func}
    (h : findFunctionIn? funcs fid = some f) : f ∈ funcs.toList := by
  unfold findFunctionIn? at h
  rw [← Array.foldl_toList] at h
  suffices haux : ∀ (fs : List Func) (acc : Option Func),
      fs.foldl (fun found fn => match found with
        | some prev => some prev
        | none => if fn.id == fid then some fn else none) acc = some f →
      acc = some f ∨ f ∈ fs by
    rcases haux funcs.toList none h with hnone | hmem
    · cases hnone
    · exact hmem
  intro fs
  induction fs with
  | nil => intro acc h; exact .inl h
  | cons fn fs ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with hacc | hmem
    · cases acc with
      | some prev => exact .inl hacc
      | none =>
        simp only at hacc
        split at hacc
        · cases hacc; exact .inr (by simp)
        · cases hacc
    · exact .inr (by simp [hmem])

theorem initialArguments_bools {args : Array GoValue} (h : InitialArguments args) :
    ∃ bs : List Bool, args.toList = bs.map GoValue.bool := by
  suffices haux : ∀ (vs : List GoValue),
      (∀ v ∈ vs, InitialValueHasType v .bool) →
      ∃ bs : List Bool, vs = bs.map GoValue.bool from haux args.toList h
  intro vs
  induction vs with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons v vs ih =>
    intro hv
    have hhead := hv v (by simp)
    cases hhead with
    | boolean b =>
      obtain ⟨bs, hbs⟩ := ih (fun w hw => hv w (by simp [hw]))
      exact ⟨b :: bs, by simp [hbs]⟩

/-- A3a already suffices to construct typed parameter/result storage, even
though it does not type the body or imply progress. Stronger scoped admission
will supply the separate typed-control proof. Setup consumes no choices and
requires no fuel in this no-initializer profile. -/
theorem setup_boolean {p : Program} {name : String} {args : Array GoValue}
    (h : BooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (env : LocalEnv) (s : ExecState) (locs : List Loc),
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body env (.frame [] [] [] [] .stop), s, locs, ch) ∧
      BoolHeap s ∧ EnvRoots s env ∧
      NamesPresent ((f.args.toList ++ f.results.toList).map Param.id) env ∧
      (∀ loc ∈ locs, BoolRoot s loc) ∧ locs.length = f.results.size ∧
      SameContext (programState p) s ∧ s.heap.size = args.size + f.results.size := by
  have hentry := h.2.1
  have hsyntax := h.2.2
  cases hf : findFunctionIn? p.funcs ⟨name⟩ with
  | none => simp [Entry, hf] at hentry
  | some f =>
    have he : f.args.size = args.size ∧ BoolParams f.args ∧ InitialArguments args := by
      simpa [Entry, hf] using hentry
    obtain ⟨harity, hparams, hargs⟩ := he
    obtain ⟨bs, hbs⟩ := initialArguments_bools hargs
    have hlen : f.args.toList.length = bs.length := by
      have hb := congrArg List.length hbs
      simpa [harity] using hb
    have hresults : BoolParams f.results := (hsyntax.2.2 f (findFunction_mem hf)).2.2.2.2.1
    obtain ⟨env₁, s₁, hbind, hheap₁, henv₁, hnames₁⟩ :=
      bindParams_bool f.args.toList bs hparams hlen
        (BoolHeap.empty (s := programState p) rfl) (EnvRoots.nil _)
        (show NamesPresent [] [] from by simp [NamesPresent])
    obtain ⟨env₂, s₂, halloc, hheap₂, henv₂, hnames₂⟩ :=
      allocDecls_bool f.results.toList hresults hheap₁ henv₁ hnames₁
    obtain ⟨locs, hpin, hloclen, hroots⟩ := pinResultLocs_bool f.results.toList henv₂
      (hnames₂.mono (by intro n hn; simp [hn]))
    have hshape₁ := bindParams_shape _ _ hbind
    have hshape₂ := allocDecls_shape _ halloc
    have hg : p.globals = #[] := Array.eq_empty_of_size_eq_zero hsyntax.1
    have hreserved := reservedPrefix_runtime h.1.1
    have hw := programState_wf hsyntax
    have hinit := booleanSyntax_no_init hsyntax
    have hseed := seedGlobals_empty p
    dsimp only [programState] at hseed hw hbind
    refine ⟨f, env₂, s₂, locs, rfl, ?_, hheap₂, henv₂,
      hnames₂.mono ?_, hroots, by simpa using hloclen,
      hshape₁.1.trans hshape₂.1, ?_⟩
    · simp [runProgramSetupM, hf, harity, hreserved, hg,
        hseed, hw, runPkgInitM, hinit,
        hbs, hbind, halloc, hpin, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · intro n hn
      simpa [List.map_append, List.mem_append, or_comm] using hn
    · have hb := hshape₁.2
      have ha := hshape₂.2
      simp only [programState, Array.length_toList, Array.size_empty,
        Nat.zero_add] at hb ha
      omega

end GoLean.GoCore.BooleanRuntime
