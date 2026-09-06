import GoLean.GoCore.RecoverySetupShape

/-! Exact argument and zero-initialized result storage. These equations prove
what the existing binder and allocator construct; no replacement evaluator
or successful-execution premise defines the admitted domain. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

/-- A structural description of the profile's genuine Go zero values. -/
inductive ZeroValues : List Param → List GoValue → Prop
  | nil : ZeroValues [] []
  | boolean {p ps vs} : p.typ = .bool → ZeroValues ps vs →
      ZeroValues (p :: ps) (.bool false :: vs)
  | payload {p ps vs} : TypeClass p.typ .payload → ZeroValues ps vs →
      ZeroValues (p :: ps) (.nil :: vs)

theorem boolean_type_eq {ty : Ty} (h : TypeClass ty .boolean) : ty = .bool := by
  cases h
  rfl

theorem payload_default {ty : Ty} (h : TypeClass ty .payload) (s : ExecState) :
    defaultValue s ty = .ok .nil := by
  cases h
  rfl

theorem ZeroValues.exists (ps : List Param) (ht : ∀ p ∈ ps, StorageType p.typ) :
    ∃ vs, ZeroValues ps vs := by
  induction ps with
  | nil => exact ⟨[], .nil⟩
  | cons p ps ih =>
    obtain ⟨vs, hv⟩ := ih (fun q hq => ht q (by simp [hq]))
    rcases ht p (by simp) with hb | hp
    · exact ⟨.bool false :: vs, .boolean (boolean_type_eq hb) hv⟩
    · exact ⟨.nil :: vs, .payload hp hv⟩

theorem ZeroValues.typed {ps vs} (h : ZeroValues ps vs) (world : World) :
    ParamsValues world ps vs := by
  induction h with
  | nil => exact .nil
  | boolean hp _ ih => exact .cons ⟨.boolean, hp ▸ .boolean, .boolean false⟩ ih
  | payload hp _ ih => exact .cons ⟨.payload, hp, .nil⟩ ih

theorem ZeroValues.length {ps vs} (h : ZeroValues ps vs) : ps.length = vs.length :=
  (h.typed #[]).length

theorem ZeroValues.unique {ps vs ws} (h : ZeroValues ps vs) (h' : ZeroValues ps ws) :
    vs = ws := by
  induction h generalizing ws with
  | nil => cases h'; rfl
  | boolean hp _ ih =>
    cases h' with
    | boolean _ rest => simp [ih rest]
    | payload ht _ =>
      have impossible : TypeClass .bool .payload := hp ▸ ht
      cases impossible
  | payload ht _ ih =>
    cases h' with
    | boolean hp _ =>
      have impossible : TypeClass .bool .payload := hp ▸ ht
      cases impossible
    | payload _ rest => simp [ih rest]

def parameterCells (ps : List Param) (vs : List GoValue) : List HeapCell :=
  List.zipWith (fun p v => HeapCell.value p.typ v) ps vs

theorem parameterCells_length {world ps vs} (h : ParamsValues world ps vs) :
    (parameterCells ps vs).length = ps.length := by
  simp [parameterCells, h.length]

theorem bindParams_exact {world ps vs} (hv : ParamsValues world ps vs)
    (env : LocalEnv) (s : ExecState) :
    bindParams env s ps vs =
      .ok (BooleanRuntime.declareRoots env s.heap.size (ps.map Param.id),
        {s with heap := s.heap ++ (parameterCells ps vs).toArray}) := by
  induction hv generalizing env s with
  | nil => simp [bindParams, BooleanRuntime.declareRoots, parameterCells, pure, Except.pure]
  | @cons p ps v vs ht _ ih =>
    obtain ⟨sort, htype, _⟩ := ht
    have hr := ih (env.declare p.id (.base ⟨s.heap.size⟩)) (s.alloc v p.typ).2
    simpa only [bindParams, normalize_typed htype, Bind.bind, Except.bind,
      Pure.pure, Except.pure, List.map_cons, BooleanRuntime.declareRoots,
      ExecState.alloc, ExecState.allocCell, Array.size_push,
      parameterCells, List.zipWith_cons_cons, List.push_append_toArray] using hr

theorem allocDecls_exact {ps vs} (hv : ZeroValues ps vs)
    (env : LocalEnv) (s : ExecState) :
    allocDecls env s ps =
      .ok (BooleanRuntime.declareRoots env s.heap.size (ps.map Param.id),
        {s with heap := s.heap ++ (parameterCells ps vs).toArray}) := by
  induction hv generalizing env s with
  | nil => simp [allocDecls, BooleanRuntime.declareRoots, parameterCells, pure, Except.pure]
  | @boolean p ps vs hp _ ih =>
    have hd : defaultValue s p.typ = .ok (.bool false) := by simp [hp]
    have hr := ih (env.declare p.id (.base ⟨s.heap.size⟩)) (s.alloc (.bool false) p.typ).2
    simpa only [allocDecls, hd, Bind.bind, Except.bind, Pure.pure, Except.pure,
      List.map_cons, BooleanRuntime.declareRoots, ExecState.alloc, ExecState.allocCell,
      Array.size_push, parameterCells, List.zipWith_cons_cons,
      List.push_append_toArray] using hr
  | @payload p ps vs hp _ ih =>
    have hd : defaultValue s p.typ = .ok .nil := payload_default hp s
    have hr := ih (env.declare p.id (.base ⟨s.heap.size⟩)) (s.alloc .nil p.typ).2
    simpa only [allocDecls, hd, Bind.bind, Except.bind, Pure.pure, Except.pure,
      List.map_cons, BooleanRuntime.declareRoots, ExecState.alloc, ExecState.allocCell,
      Array.size_push, parameterCells, List.zipWith_cons_cons,
      List.push_append_toArray] using hr

theorem ParamsValues.booleans (ps : List Param) (bs : List Bool) (world : World)
    (ht : ∀ p ∈ ps, p.typ = .bool) (hlen : ps.length = bs.length) :
    ParamsValues world ps (bs.map GoValue.bool) := by
  induction ps generalizing bs with
  | nil =>
    have he : bs = [] := by simpa using hlen.symm
    subst bs
    exact .nil
  | cons p ps ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      exact .cons ⟨.boolean, (ht p (by simp)) ▸ .boolean, .boolean b⟩
        (ih bs (fun q hq => ht q (by simp [hq])) (by simpa using hlen))

end GoLean.GoCore.RecoveryRuntime
