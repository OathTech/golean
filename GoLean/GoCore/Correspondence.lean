import GoLean.GoCore.Rel
import GoLean.GoCore.Eval

/-!
# Interpreter/relation correspondence

States the intended relationship between the executable interpreter
(`GoLean.GoCore.Eval`) and the relational skeleton (`GoLean.GoCore.Rel`),
and proves small instances that exercise the relational rules.

Honest status (updated 2026-07-21, arc `eval-totalization` — design of
record: `docs/2026-07-21_eval-totalization-correspondence.md`): the big-step
cluster is now **total** (GoCore has 0 `partial def`s), so `execStmt … = .ok …`
hypotheses invert and the proof work is unblocked. But the two blanket
statements below are **false as literally stated**, for two now-understood
reasons:

1. **The interpreter is richer than the relation.** E.g. `add` also
   concatenates strings; the relation has no such rule, so an
   interpreter-successful string-add run reaches no relational derivation.
   The provable theorem is over the **scalar+pointer fragment**
   (syntactic fragment + fragment-shaped heap), built below.
2. **D1 — nested `.seqn` scoping.** The frontend lowers `x := 5` to a nested
   `.seqn #[init, assign]` spliced into the enclosing block's statement list;
   the interpreter's `.seqn` is scope-transparent (Go-correct: statement
   lists splice, only blocks scope), but the relation wraps every `.seqn` in
   its own `Cont.seq` and discards its env at `seqDone`, so the binding dies
   early and later uses are stuck. Correspondence over frontend-emitted
   programs needs the proposed splice rule (its own audited slice); until
   then the theorems carry a well-formedness side condition and cover the
   hand-modeled proof subjects.

The statements are kept as named `Prop`s recording the eventual unconditional
target; the theorems below prove fragment-scoped versions — BOTH sides as of
arc `rel-completion`: `interpreterSound_frag` (normal outcomes) and
`interpreterPanic_frag` (panics, D3b). The state bridge
(`withLocals` — the relation never reads or writes `ExecState.locals`) and
the substrate transport lemmas live in this file.
-/

namespace GoLean.GoCore.Correspondence

open GoLean GoLean.GoCore GoLean.GoCore.Rel

/-! ## State bridge: the relation is locals-agnostic

The interpreter resolves names via `ExecState.locals` and mutates it
(`declareLocal`, scope push/pop); the relation (CEK) resolves via
`Config.env` and never reads or writes `locals` — its rules touch only
heap/nextAddr and read types/functions. So along any relation derivation the
state's `locals` is frozen at its initial value while the interpreter's
evolves, and the correspondence relates the two **up to `locals`**:
interpreter state `σᵢ` corresponds to relation state `σᵢ.withLocals L` for
the run-initial `L`. The lemmas here transport every substrate operation the
relation's rule premises mention across `withLocals`. -/

/-- Replace the interpreter-bookkeeping `locals` field, leaving the
semantically shared components (heap, allocator, types, functions, methods)
untouched. -/
def _root_.GoLean.GoCore.ExecState.withLocals (σ : ExecState) (L : LocalEnv) : ExecState :=
  { σ with locals := L }

@[simp] theorem withLocals_heap (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).heap = σ.heap := rfl
@[simp] theorem withLocals_types (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).types = σ.types := rfl
@[simp] theorem withLocals_functions (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).functions = σ.functions := rfl
@[simp] theorem withLocals_methods (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).methods = σ.methods := rfl
@[simp] theorem withLocals_nextAddr (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).nextAddr = σ.nextAddr := rfl
@[simp] theorem withLocals_locals (σ : ExecState) (L : LocalEnv) :
    (σ.withLocals L).locals = L := rfl
@[simp] theorem withLocals_withLocals (σ : ExecState) (L L' : LocalEnv) :
    (σ.withLocals L).withLocals L' = σ.withLocals L' := rfl

theorem loadLoc_withLocals (σ : ExecState) (L : LocalEnv) (loc : Loc) :
    loadLoc (σ.withLocals L) loc = loadLoc σ loc := by
  induction loc with
  | base a => rfl
  | field base typeId fieldName ih => simp only [loadLoc, ih]
  | index base index ih => simp only [loadLoc, ih]

theorem alloc_withLocals (σ : ExecState) (L : LocalEnv) (v : GoValue) (t : Option Ty) :
    (σ.withLocals L).alloc v t = ((σ.alloc v t).1, (σ.alloc v t).2.withLocals L) := rfl

/-- The interpreter's `declareLocal` is exactly the relation's
`alloc` + env-`declare`, with the env extension recorded in `locals`. -/
theorem declareLocal_eq_alloc (σ : ExecState) (n : String) (t : Option Ty) (v : GoValue) :
    σ.declareLocal n t v =
      { (σ.alloc v t).2 with locals := LocalEnv.declare σ.locals n (σ.alloc v t).1 } := rfl

@[simp] theorem withLocals_set_heap (σ : ExecState) (L : LocalEnv) (H : Heap) :
    { σ.withLocals L with heap := H } = ExecState.withLocals { σ with heap := H } L := rfl

/-- Interpreter name resolution, unfolded to the relation's premise shape. -/
theorem lookupLoc_eq_ok {σ : ExecState} {id : String} {loc : Loc} :
    lookupLoc σ id = .ok loc ↔ LocalEnv.lookup σ.locals id = some loc := by
  unfold lookupLoc
  cases LocalEnv.lookup σ.locals id <;> simp [stuck, pure, Except.pure]

/-! ## The scalar+pointer fragment

Fragment **types** are the types the fragment declares and stores at. All
three substrate operations that consult declared types (`normalizeValueForTy`,
`defaultValue`, `valueEq`) are *state-independent* at fragment types — their
equations at `.int`/`.bool`/`.pointer` neither read `state.types` nor recurse
— which is what makes the `storeLoc` transport cheap. Widening the fragment
to `.defined`/struct/array types will need the general transport lemmas,
provable from `normalizeValueForTyFuel.mutual_induct` (and siblings). -/

inductive TyFrag : Ty → Prop where
  | int (kind : IntKind) : TyFrag (.int kind)
  | bool : TyFrag .bool
  | pointer (elem : Ty) : TyFrag (.pointer elem)

theorem normalizeValueForTy_state_indep (σ σ' : ExecState) {t : Ty} (h : TyFrag t)
    (v : GoValue) : normalizeValueForTy σ t v = normalizeValueForTy σ' t v := by
  cases h <;> cases v <;> simp [normalizeValueForTy, normalizeValueForTyFuel]

theorem defaultValue_state_indep (σ σ' : ExecState) {t : Ty} (h : TyFrag t) :
    defaultValue σ t = defaultValue σ' t := by
  cases h <;> simp [defaultValue, defaultValueFuel]

theorem valueEq_state_indep (σ σ' : ExecState) {t : Ty} (h : TyFrag t)
    (l r : GoValue) : valueEq σ t l r = valueEq σ' t l r := by
  cases h <;> cases l <;> cases r <;> simp [valueEq, valueEqFuel]

/-- Fragment **values**: what fragment expressions produce and fragment heap
cells hold. Note `.nil` is included (pointer defaults), `.string`/composites
are not — the interpreter is richer than the relation on those. -/
inductive FragVal : GoValue → Prop where
  | int (n : Int) (k : IntKind) : FragVal (.int n k)
  | bool (b : Bool) : FragVal (.bool b)
  | addr (l : Loc) : FragVal (.addr l)
  | nil : FragVal .nil

/-- Fragment-shaped heap: every cell holds a fragment value and is declared
(if at all) at a fragment type. Preserved by fragment stores and allocations;
makes `loadLoc` return only fragment values and never panic. -/
def HeapFrag (σ : ExecState) : Prop :=
  ∀ loc cell, Heap.lookup σ.heap loc = some cell →
    FragVal cell.value ∧ ∀ t, cell.declaredTy = some t → TyFrag t

/-! ### `Except`-bind inversion — the workhorses for inverting interpreter runs -/

@[simp] theorem pure_ne_error {ε α : Type} (a : α) (e : ε) :
    ((pure a : Except ε α) = .error e) ↔ False := by
  simp [pure, Except.pure]

@[simp] theorem stuck_def {α : Type} (m : String) :
    (stuck m : Except GoError α) = .error (.stuck m) := rfl
@[simp] theorem panic_def {α : Type} (m : String) :
    (GoCore.panic m : Except GoError α) = .error (.panic m) := rfl
@[simp] theorem unsupported_def {α : Type} (m : String) :
    (unsupported m : Except GoError α) = .error (.unsupported m) := rfl

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

theorem bind_eq_error {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε} :
    x >>= f = .error e ↔ x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- Loads from a fragment heap return fragment values (a non-base location
would need a struct/array cell, which `FragVal` excludes). -/
theorem loadLoc_frag {σ : ExecState} (hh : HeapFrag σ) :
    ∀ {loc : Loc} {v : GoValue}, loadLoc σ loc = .ok v → FragVal v := by
  intro loc
  induction loc with
  | base a =>
    intro v h
    simp only [loadLoc] at h
    cases hl : Heap.lookup σ.heap (.base a) with
    | some cell => rw [hl] at h; simp [pure, Except.pure] at h; exact h ▸ (hh _ _ hl).1
    | none => rw [hl] at h; simp at h
  | field base typeId fieldName ih =>
    intro v h
    simp only [loadLoc] at h
    rw [bind_eq_ok] at h
    obtain ⟨w, hw, h⟩ := h
    cases ih hw <;> simp at h
  | index base index ih =>
    intro v h
    simp only [loadLoc] at h
    rw [bind_eq_ok] at h
    obtain ⟨w, hw, h⟩ := h
    cases ih hw <;> simp at h

/-- Loads from a fragment heap never panic (base loads are lookup-or-stuck;
field/index loads need struct/array bases, excluded by `FragVal`). -/
theorem loadLoc_no_panic {σ : ExecState} (hh : HeapFrag σ) :
    ∀ {loc : Loc} {msg : String}, loadLoc σ loc ≠ .error (.panic msg) := by
  intro loc
  induction loc with
  | base a =>
    intro msg h
    simp only [loadLoc] at h
    cases hl : Heap.lookup σ.heap (.base a) with
    | some cell => rw [hl] at h; simp [pure, Except.pure] at h
    | none => rw [hl] at h; simp at h
  | field base typeId fieldName ih =>
    intro msg h
    simp only [loadLoc] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨w, hw, h⟩
    · exact ih h
    · cases loadLoc_frag hh hw <;> simp at h
  | index base index ih =>
    intro msg h
    simp only [loadLoc] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨w, hw, h⟩
    · exact ih h
    · cases loadLoc_frag hh hw <;> simp at h

/-- `storeLoc` at a base location transports across `withLocals`, provided the
target cell's declared type (if any) is a fragment type — store-time
normalization is then state-independent. Fragment runs only store at base
locations (no struct/array cells), so this is the only case needed. -/
theorem storeLoc_withLocals_base (σ : ExecState) (L : LocalEnv) (a : Addr) (v : GoValue)
    (hfrag : ∀ cell t, Heap.lookup σ.heap (.base a) = some cell →
      cell.declaredTy = some t → TyFrag t) :
    storeLoc (σ.withLocals L) (.base a) v
      = (storeLoc σ (.base a) v).map (·.withLocals L) := by
  cases hl : Heap.lookup σ.heap (.base a) with
  | none =>
    simp only [storeLoc, withLocals_heap, hl]
    rfl
  | some cell =>
    cases hd : cell.declaredTy with
    | none =>
      simp only [storeLoc, withLocals_heap, hl, hd]
      cases coerceStoredValue cell.value v <;> rfl
    | some t =>
      have hn := normalizeValueForTy_state_indep (σ.withLocals L) σ (hfrag cell t hl hd) v
      simp only [storeLoc, withLocals_heap, hl, hd, hn]
      cases normalizeValueForTy σ t v <;> rfl

/-- Intended soundness of the interpreter against the relation, for
supported deterministic terminating runs: a normal interpreter completion
is a reachable terminal of the step relation. (Analogous statements for
returned/broke/continued outcomes quantify over the matching unwinding
configurations, and interpreter panics correspond to `Config.panicked`.)

After Reshape B (oracle externalization,
`docs/2026-07-19_reshape-b-oracle-externalization.md`) the interpreter threads
the choice stream `ch → ch'` *externally*, so it never appears in the relation's
oracle-free `ExecState`. This is what removes master-plan §8 C1's obstruction:
the interpreter's nondeterminism consumption is invisible to the state the
relation compares. Still blocked on interpreter/substrate totality (module
header) — but now the statement is over clean states.

After the CEK reshape (`docs/2026-07-19_cek-reshape-plan.md`) the relation
carries locals in the control `env`, not the state. The initial control
environment is the interpreter's `s.locals` — that equality is the
correspondence bridge `σ.locals ≈ Config.env` — so the run starts from
`.exec stmt s.locals .stop`. -/
def interpreterSoundStatement : Prop :=
  ∀ (fuel : Nat) (s s' : ExecState) (stmt : Stmt) (ch ch' : Choices),
    execStmt fuel s ch stmt = .ok (.normal s', ch') →
    Steps (.exec stmt s.locals .stop) s (.next .stop) s'

/-- Intended panic agreement: if the interpreter reports a Go panic, the
relation reaches `panicked` with the same message (at some fault state). The
input choice stream is threaded but irrelevant to the panic message. Deferred. -/
def interpreterPanicStatement : Prop :=
  ∀ (fuel : Nat) (s : ExecState) (stmt : Stmt) (msg : String) (ch : Choices),
    execStmt fuel s ch stmt = .error (.panic msg) →
    ∃ s', Steps (.exec stmt s.locals .stop) s (.panicked msg) s'

/-! ## The expression bridge

Fragment **expressions**: the scalar+pointer expression grammar shared by the
interpreter and the relation. `evalExpr` on these is state-preserving, and a
successful run maps to an `ExprR` derivation with `env := σ.locals` over any
`withLocals`-transported state. -/

inductive ExprFrag : Expr → Prop where
  | var (id : String) : ExprFrag (.var id)
  | intLit (n : Int) (k : IntKind) : ExprFrag (.intLit n k)
  | boolLit (b : Bool) : ExprFrag (.boolLit b)
  | add {l r : Expr} : ExprFrag l → ExprFrag r → ExprFrag (.add l r)
  | sub {l r : Expr} : ExprFrag l → ExprFrag r → ExprFrag (.sub l r)
  | mul {l r : Expr} : ExprFrag l → ExprFrag r → ExprFrag (.mul l r)
  | div {l r : Expr} : ExprFrag l → ExprFrag r → ExprFrag (.div l r)
  | eqCmp {ty : Ty} {l r : Expr} :
      TyFrag ty → ExprFrag l → ExprFrag r → ExprFrag (.eqCmp ty l r)
  | ref (id : String) : ExprFrag (.ref id)
  | locLit (l : Loc) : ExprFrag (.locLit l)
  | deref {e : Expr} (ty : Ty) : ExprFrag e → ExprFrag (.deref e ty)

theorem pure_eq_ok {ε α : Type} {a : α} {b : α} :
    (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- `valueAsIntValue` succeeds exactly on integer values. -/
theorem valueAsIntValue_ok {v : GoValue} {p : Int × IntKind}
    (h : valueAsIntValue v = .ok p) : v = .int p.1 p.2 := by
  cases v <;> simp only [valueAsIntValue, pure_eq_ok, stuck_def, reduceCtorEq] at h
  rw [← h]

/-- Inversion for the interpreter's integer binary operations: success forces
integer operands, a compatible result kind, and the normalized result. -/
theorem intBinaryResult_ok {op : String} {f : Int → Int → Int} {l r v : GoValue}
    (h : intBinaryResult op f l r = .ok v) :
    ∃ lv lk rv rk k, l = .int lv lk ∧ r = .int rv rk ∧
      IntKind.compatibleResult lk rk = some k ∧
      v = .int (k.normalize (f lv rv)) k := by
  unfold intBinaryResult at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, hlp, h⟩ := h
  obtain ⟨⟨rv, rk⟩, hrp, h⟩ := h
  have hle := valueAsIntValue_ok hlp
  have hre := valueAsIntValue_ok hrp
  cases hc : IntKind.compatibleResult lk rk with
  | some k =>
    simp only [hc, bind_eq_ok, pure_eq_ok, exists_eq_left'] at h
    exact ⟨lv, lk, rv, rk, k, hle, hre, hc, h.symm⟩
  | none => simp only [hc, bind_eq_ok, stuck_def, reduceCtorEq, false_and,
      exists_const] at h

/-- **The expression bridge (normal outcomes).** A successful interpreter
evaluation of a fragment expression over a fragment heap (1) preserves the
state, (2) yields a fragment value, and (3) maps to an `ExprR` derivation
resolving through `env := σ.locals`, over the `withLocals`-transported state
for any `L` — the shape the statement-level simulation consumes. -/
theorem evalExpr_frag_ok {e : Expr} (hf : ExprFrag e) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {v : GoValue} {σ' : ExecState},
      evalExpr σ e = .ok (v, σ') →
      σ' = σ ∧ FragVal v ∧
        ∀ L, ExprR σ.locals (σ.withLocals L) e (.value v (σ.withLocals L)) := by
  induction hf with
  | var id =>
    intro σ hh v σ' h
    simp only [evalExpr, GoCore.lookup, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨w, ⟨loc, hloc, hload⟩, hw⟩ := h
    cases hw
    exact ⟨rfl, loadLoc_frag hh hload, fun L =>
      .var (lookupLoc_eq_ok.mp hloc) ((loadLoc_withLocals σ L loc).trans hload)⟩
  | intLit n k =>
    intro σ hh v σ' h
    simp only [evalExpr, pure_eq_ok] at h
    cases h
    exact ⟨rfl, .int _ _, fun L => .intLit⟩
  | boolLit b =>
    intro σ hh v σ' h
    simp only [evalExpr, pure_eq_ok] at h
    cases h
    exact ⟨rfl, .bool _, fun L => .boolLit⟩
  | add hl hr ihl ihr =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨lv, σ₁⟩, hl', h⟩ := h
    obtain ⟨rfl, hfl, hRl⟩ := ihl hh hl'
    rw [bind_eq_ok] at h
    obtain ⟨⟨rv, σ₂⟩, hr', h⟩ := h
    obtain ⟨rfl, hfr, hRr⟩ := ihr hh hr'
    cases hfl <;> cases hfr <;>
      simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq, stuck_def,
        reduceCtorEq] at h
    case int.int lvv lk rvv rk =>
      obtain ⟨w, hw, rfl, rfl⟩ := h
      obtain ⟨lv', lk', rv', rk', k, hle, hre, hk, rfl⟩ := intBinaryResult_ok hw
      obtain ⟨rfl, rfl⟩ : lvv = lv' ∧ lk = lk' := by simpa using hle
      obtain ⟨rfl, rfl⟩ : rvv = rv' ∧ rk = rk' := by simpa using hre
      exact ⟨rfl, .int _ _, fun L => .addInt (hRl L) (hRr L) hk⟩
  | sub hl hr ihl ihr =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨lv, σ₁⟩, hl', h⟩ := h
    obtain ⟨rfl, hfl, hRl⟩ := ihl hh hl'
    rw [bind_eq_ok] at h
    obtain ⟨⟨rv, σ₂⟩, hr', h⟩ := h
    obtain ⟨rfl, hfr, hRr⟩ := ihr hh hr'
    simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    obtain ⟨lv', lk', rv', rk', k, rfl, rfl, hk, rfl⟩ := intBinaryResult_ok hw
    exact ⟨rfl, .int _ _, fun L => .subInt (hRl L) (hRr L) hk⟩
  | mul hl hr ihl ihr =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨lv, σ₁⟩, hl', h⟩ := h
    obtain ⟨rfl, hfl, hRl⟩ := ihl hh hl'
    rw [bind_eq_ok] at h
    obtain ⟨⟨rv, σ₂⟩, hr', h⟩ := h
    obtain ⟨rfl, hfr, hRr⟩ := ihr hh hr'
    simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    obtain ⟨lv', lk', rv', rk', k, rfl, rfl, hk, rfl⟩ := intBinaryResult_ok hw
    exact ⟨rfl, .int _ _, fun L => .mulInt (hRl L) (hRr L) hk⟩
  | div hl hr ihl ihr =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨lv, σ₁⟩, hl', h⟩ := h
    obtain ⟨rfl, hfl, hRl⟩ := ihl hh hl'
    rw [bind_eq_ok] at h
    obtain ⟨⟨rv, σ₂⟩, hr', h⟩ := h
    obtain ⟨rfl, hfr, hRr⟩ := ihr hh hr'
    rw [bind_eq_ok] at h
    obtain ⟨d, hd, h⟩ := h
    cases hfr with
    | int rvv rk =>
      simp only [valueAsInt, pure_eq_ok] at hd
      rw [← hd] at h
      cases hz : (rvv == 0) with
      | true => rw [hz] at h; simp [bind_eq_ok] at h
      | false =>
        rw [hz] at h
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok, pure_eq_ok,
          Prod.mk.injEq] at h
        obtain ⟨_, -, w, hw, rfl, rfl⟩ := h
        obtain ⟨lv', lk', rv', rk', k, rfl, hre, hk, rfl⟩ := intBinaryResult_ok hw
        obtain ⟨rfl, rfl⟩ : rvv = rv' ∧ rk = rk' := by simpa using hre
        exact ⟨rfl, .int _ _, fun L =>
          .divInt (hRl L) (hRr L) (ne_of_beq_false hz) hk⟩
    | bool b => simp only [valueAsInt, stuck_def, reduceCtorEq] at hd
    | addr l => simp only [valueAsInt, stuck_def, reduceCtorEq] at hd
    | nil => simp only [valueAsInt, stuck_def, reduceCtorEq] at hd
  | eqCmp hty hl hr ihl ihr =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨lv, σ₁⟩, hl', h⟩ := h
    obtain ⟨rfl, hfl, hRl⟩ := ihl hh hl'
    rw [bind_eq_ok] at h
    obtain ⟨⟨rv, σ₂⟩, hr', h⟩ := h
    obtain ⟨rfl, hfr, hRr⟩ := ihr hh hr'
    simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact ⟨rfl, .bool _, fun L =>
      ExprR.eqCmp (hRl L) (hRr L)
        ((valueEq_state_indep _ _ hty lv rv).trans hb)⟩
  | ref id =>
    intro σ hh v σ' h
    simp only [evalExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    cases h
    exact ⟨rfl, .addr _, fun L => .ref (lookupLoc_eq_ok.mp hloc)⟩
  | locLit l =>
    intro σ hh v σ' h
    simp only [evalExpr, pure_eq_ok] at h
    cases h
    exact ⟨rfl, .addr _, fun L => .locLit⟩
  | deref ty hp ihp =>
    intro σ hh v σ' h
    simp only [evalExpr] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨pv, σ₁⟩, hp', h⟩ := h
    obtain ⟨rfl, hfp, hRp⟩ := ihp hh hp'
    rw [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    cases hfp with
    | addr l =>
      simp only [valueAsLoc, pure_eq_ok] at hloc
      subst hloc
      simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨w, hw, rfl, rfl⟩ := h
      exact ⟨rfl, loadLoc_frag hh hw, fun L =>
        .deref (hRp L) ((loadLoc_withLocals _ _ _).trans hw)⟩
    | int n k => simp only [valueAsLoc, stuck_def, reduceCtorEq] at hloc
    | bool b => simp only [valueAsLoc, stuck_def, reduceCtorEq] at hloc
    | nil => simp only [valueAsLoc, panic_def, reduceCtorEq] at hloc

/-! ## Fragment heap preservation

`Heap.set` results are the written cell or an untouched old cell — the one
fact all heap-mutation preservation proofs need, provable without any
`BEq` lawfulness reasoning. -/

theorem lookup_set_cases (h : Heap) (loc loc' : Loc) (c : HeapCell) :
    Heap.lookup (Heap.set h loc c) loc' = some c ∨
    Heap.lookup (Heap.set h loc c) loc' = Heap.lookup h loc' := by
  induction h with
  | nil =>
    simp only [Heap.set, Heap.lookup]
    split
    · exact .inl rfl
    · exact .inr rfl
  | cons hd rest ih =>
    obtain ⟨l, o⟩ := hd
    simp only [Heap.set]
    split
    · simp only [Heap.lookup]
      split
      · exact .inl rfl
      · exact .inr rfl
    · simp only [Heap.lookup]
      split
      · exact .inr rfl
      · exact ih

theorem heapFrag_set {σ : ExecState} (hh : HeapFrag σ) {c : HeapCell}
    (hcv : FragVal c.value) (hct : ∀ t, c.declaredTy = some t → TyFrag t)
    (loc : Loc) : HeapFrag { σ with heap := Heap.set σ.heap loc c } := by
  intro loc' cell hcell
  rcases lookup_set_cases σ.heap loc loc' c with hc | hc
  · rw [hcell] at hc
    cases hc
    exact ⟨hcv, hct⟩
  · exact hh loc' cell (hc ▸ hcell)

theorem heapFrag_alloc {σ : ExecState} (hh : HeapFrag σ) {v : GoValue}
    {t : Option Ty} (hv : FragVal v) (ht : ∀ t', t = some t' → TyFrag t') :
    HeapFrag (σ.alloc v t).2 := by
  have : HeapFrag { σ with nextAddr := σ.nextAddr + 1 } := hh
  exact heapFrag_set this hv ht _

/-- Fragment normalization yields fragment values (int-typed stores normalize
the int; bool/pointer-typed stores pass the value through). -/
theorem normalizeValueForTy_frag_val {σ : ExecState} {t : Ty} {v w : GoValue}
    (ht : TyFrag t) (hv : FragVal v)
    (h : normalizeValueForTy σ t v = .ok w) : FragVal w := by
  cases ht <;> cases hv <;>
    simp [normalizeValueForTy, normalizeValueForTyFuel, pure_eq_ok] at h <;>
    (subst h; constructor)

theorem coerceStoredValue_frag_val {old v w : GoValue} (hv : FragVal v)
    (h : coerceStoredValue old v = .ok w) : FragVal w := by
  cases old <;> cases hv <;>
    simp [coerceStoredValue, pure_eq_ok] at h <;>
    (subst h; constructor)

/-- Successful fragment stores happen at base locations (field/index stores
would need struct/array cells, which `FragVal` excludes), only touch the
heap, and preserve its fragment shape. -/
theorem storeLoc_frag {σ : ExecState} (hh : HeapFrag σ) {loc : Loc}
    {v : GoValue} {σf : ExecState} (hv : FragVal v)
    (h : storeLoc σ loc v = .ok σf) :
    (∃ a, loc = .base a) ∧ HeapFrag σf ∧ σf.locals = σ.locals := by
  cases loc with
  | base a =>
    refine ⟨⟨a, rfl⟩, ?_⟩
    cases hl : Heap.lookup σ.heap (.base a) with
    | some cell =>
      cases hd : cell.declaredTy with
      | some t =>
        simp only [storeLoc, hl, hd, bind_eq_ok, pure_eq_ok] at h
        obtain ⟨w, hw, h⟩ := h
        subst h
        exact ⟨heapFrag_set hh
          (normalizeValueForTy_frag_val ((hh _ _ hl).2 t hd) hv hw)
          (fun t' ht' => (hh _ _ hl).2 t' (hd ▸ ht')) _, rfl⟩
      | none =>
        simp only [storeLoc, hl, hd, bind_eq_ok, pure_eq_ok] at h
        obtain ⟨w, hw, h⟩ := h
        subst h
        exact ⟨heapFrag_set hh (coerceStoredValue_frag_val hv hw)
          (fun t' ht' => by cases ht') _, rfl⟩
    | none =>
      simp only [storeLoc, hl, pure_eq_ok] at h
      subst h
      exact ⟨heapFrag_set hh hv (fun t' ht' => by cases ht') _, rfl⟩
  | field base typeId fieldName =>
    simp only [storeLoc, bind_eq_ok] at h
    obtain ⟨w, hw, h⟩ := h
    cases loadLoc_frag hh hw <;> simp at h
  | index base index =>
    simp only [storeLoc, bind_eq_ok] at h
    obtain ⟨w, hw, h⟩ := h
    cases loadLoc_frag hh hw <;> simp at h

/-- `storeLoc` touches only the heap: every success — at any location shape —
is literally `{σ with heap := _}`. No fragment hypotheses needed. -/
theorem storeLoc_ctx {σ : ExecState} : ∀ {loc : Loc} {v : GoValue} {σ' : ExecState},
    storeLoc σ loc v = .ok σ' →
    σ'.types = σ.types ∧ σ'.functions = σ.functions ∧ σ'.methods = σ.methods ∧
      σ'.locals = σ.locals ∧ σ'.nextAddr = σ.nextAddr := by
  intro loc
  induction loc with
  | base a =>
    intro v σ' h
    cases hl : Heap.lookup σ.heap (.base a) with
    | some cell =>
      cases hd : cell.declaredTy with
      | some t =>
        simp only [storeLoc, hl, hd, bind_eq_ok, pure_eq_ok] at h
        obtain ⟨w, -, h⟩ := h
        subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | none =>
        simp only [storeLoc, hl, hd, bind_eq_ok, pure_eq_ok] at h
        obtain ⟨w, -, h⟩ := h
        subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | none =>
      simp only [storeLoc, hl, pure_eq_ok] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | field base typeId fieldName ih =>
    intro v σ' h
    simp only [storeLoc, bind_eq_ok] at h
    obtain ⟨w, -, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, stuck_def, reduceCtorEq, false_and,
          exists_const] at h
      · simp only [bind_eq_ok, pure_eq_ok] at h
        obtain ⟨-, -, u, -, h⟩ := h
        exact ih h
    · simp at h
  | index base index ih =>
    intro v σ' h
    simp only [storeLoc, bind_eq_ok] at h
    obtain ⟨w, -, h⟩ := h
    split at h
    · simp only [bind_eq_ok] at h
      obtain ⟨u, -, h⟩ := h
      exact ih h
    · simp at h

/-! ## The assignee bridge and the first statement-level correspondence -/

inductive AssigneeFrag : Assignee → Prop where
  | var (id : String) : AssigneeFrag (.var id)
  | addr {e : Expr} : ExprFrag e → AssigneeFrag (.addr e)

theorem evalAssigneeLoc_frag_ok {a : Assignee} (ha : AssigneeFrag a)
    {σ : ExecState} (hh : HeapFrag σ) {loc : Loc} {σ' : ExecState}
    (h : evalAssigneeLoc σ a = .ok (loc, σ')) :
    σ' = σ ∧ ∀ L, AssigneeR σ.locals (σ.withLocals L) a (.loc loc (σ.withLocals L)) := by
  cases ha with
  | var id =>
    simp only [evalAssigneeLoc, bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl⟩ := h
    exact ⟨rfl, fun L => .var (lookupLoc_eq_ok.mp hl)⟩
  | addr he =>
    simp only [evalAssigneeLoc] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨pv, σ₁⟩, hp, h⟩ := h
    obtain ⟨rfl, hfp, hRp⟩ := evalExpr_frag_ok he hh hp
    cases hfp with
    | addr l =>
      simp only [valueAsLoc, bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨a, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun L => .addr (hRp L)⟩
    | int n k => simp [valueAsLoc, Functor.map, Except.map] at h
    | bool b => simp [valueAsLoc, Functor.map, Except.map] at h
    | nil => simp [valueAsLoc, Functor.map, Except.map] at h

/-- **The first statement-level correspondence**: a successful interpreter
assignment maps to the relation's `Step.assign` — one small step from
`.exec (.assign a e) σ.locals k` to `.next k` over any transported state,
with the fragment heap shape preserved and locals untouched. The choice
stream is untouched (no nondeterminism in the fragment). -/
theorem execStmt_assign_ok {fuel : Nat} {σ : ExecState} {ch : Choices}
    {a : Assignee} {e : Expr} (ha : AssigneeFrag a) (he : ExprFrag e)
    (hh : HeapFrag σ) {out : ExecOutcome} {ch' : Choices}
    (h : execStmt fuel σ ch (.assign a e) = .ok (out, ch')) :
    ∃ σf, out = .normal σf ∧ ch' = ch ∧ HeapFrag σf ∧ σf.locals = σ.locals ∧
      σf.functions = σ.functions ∧ σf.methods = σ.methods ∧
      ∀ L k, Step (.exec (.assign a e) σ.locals k) (σ.withLocals L)
        (.next k) (σf.withLocals L) := by
  simp only [execStmt] at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨loc, σ₁⟩, hloc, h⟩ := h
  obtain ⟨rfl, hA⟩ := evalAssigneeLoc_frag_ok ha hh hloc
  rw [bind_eq_ok] at h
  obtain ⟨⟨v, σ₂⟩, hv', h⟩ := h
  obtain ⟨rfl, hfv, hRv⟩ := evalExpr_frag_ok he hh hv'
  simp only [assignLoc, bind_eq_ok, pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨σf, hst, rfl, rfl⟩ := h
  obtain ⟨⟨addr, rfl⟩, hhf, hlocals⟩ := storeLoc_frag hh hfv hst
  obtain ⟨-, hfns, hmth, -, -⟩ := storeLoc_ctx hst
  refine ⟨σf, rfl, rfl, hhf, hlocals, hfns, hmth, fun L k => ?_⟩
  refine Step.assign (hA L) (hRv L) ?_
  rw [storeLoc_withLocals_base _ L addr v
    (fun cell t hc ht => (hh _ _ hc).2 t ht), hst]
  rfl

/-! ## The statement layer: fragment statements simulate in the CEK relation -/

@[simp] theorem withLocals_set_locals (σ : ExecState) (X L : LocalEnv) :
    ExecState.withLocals { σ with locals := X } L = σ.withLocals L := rfl

theorem defaultValue_frag_val {σ : ExecState} {t : Ty} {v : GoValue}
    (ht : TyFrag t) (h : defaultValue σ t = .ok v) : FragVal v := by
  cases ht <;> simp [defaultValue, defaultValueFuel, pure_eq_ok] at h <;>
    (subst h; constructor)

theorem declare_popScope (E : LocalEnv) (n : String) (l : Loc) :
    (LocalEnv.declare E n l).popScope = E.popScope := by
  cases E <;> rfl

/-- Declaration-list bridge: the interpreter's `execDeclList` is the
relation's `DeclsR`, with the fragment heap preserved and only the top
scope touched. -/
theorem execDeclList_frag_sound {decls : List Param}
    (hd : ∀ p ∈ decls, TyFrag p.typ) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {σd : ExecState},
      execDeclList σ decls = .ok σd →
      HeapFrag σd ∧ σd.locals.popScope = σ.locals.popScope ∧
        σd.functions = σ.functions ∧ σd.methods = σ.methods ∧
        ∀ L, DeclsR σ.locals (σ.withLocals L) decls σd.locals (σd.withLocals L) := by
  induction decls with
  | nil =>
    intro σ hh σd h
    simp only [execDeclList, pure_eq_ok] at h
    subst h
    exact ⟨hh, rfl, rfl, rfl, fun L => .nil⟩
  | cons p rest ih =>
    intro σ hh σd h
    simp only [execDeclList, execDecl, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨σ₁, ⟨v, hv, hσ₁⟩, h⟩ := h
    have htp : TyFrag p.typ := hd p (by simp)
    have hfv : FragVal v := defaultValue_frag_val htp hv
    subst hσ₁
    have hh₁ : HeapFrag (σ.declareLocal p.id (some p.typ) v) := by
      rw [declareLocal_eq_alloc]
      exact heapFrag_alloc hh hfv (fun t' ht' => by cases ht'; exact htp)
    obtain ⟨hhd, hpop, hfns, hmth, hR⟩ := ih (fun q hq => hd q (by simp [hq])) hh₁ h
    refine ⟨hhd, ?_, hfns, hmth, fun L => ?_⟩
    · rw [hpop, declareLocal_eq_alloc]
      exact declare_popScope ..
    · refine DeclsR.cons (v := v) (loc := (σ.alloc v (some p.typ)).1)
        (s₁ := (σ.alloc v (some p.typ)).2.withLocals L)
        ((defaultValue_state_indep (σ.withLocals L) σ htp).trans hv)
        (alloc_withLocals σ L v (some p.typ)) ?_
      exact hR L

/-! ## The residual spine condition (D2-proper)

With result locations pinned at call time (`LookupsR` in `Step.call`), the
frame exit reads state, not environment — so Go-legal block-scoped shadowing
of result names is handled correctly and needs no side condition. What
remains is *top-of-frame spine* redeclaration of a result id (Go forbids it
statically: `ret := …` at function top level is a compile error): the
interpreter's exit read resolves ids in the exit locals, so spine inits must
not redirect a result id. `SpineFrag.init`'s `∉ avoid` condition carries
exactly that, and T2 concludes lookup-preservation for the avoided ids. -/

private theorem findAux_mem {id : FuncId} :
    ∀ (l : List Func) (acc : Option Func) (f : Func),
      List.foldl
        (fun found func =>
          match found with
          | some f => some f
          | none => if func.id == id then some func else none) acc l = some f →
      acc = some f ∨ f ∈ l := by
  intro l
  induction l with
  | nil => exact fun acc f h => .inl h
  | cons g rest ih =>
    intro acc f h
    simp only [List.foldl_cons] at h
    cases acc with
    | some g' =>
      rcases ih (some g') f h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')
    | none =>
      by_cases hg : (g.id == id) = true
      · rcases ih (some g) f (by simpa [hg] using h) with h' | h'
        · cases h'; exact .inr List.mem_cons_self
        · exact .inr (List.mem_cons_of_mem _ h')
      · rcases ih none f (by simpa [hg] using h) with h' | h'
        · exact absurd h' (by simp)
        · exact .inr (List.mem_cons_of_mem _ h')

theorem findFunctionIn?_mem {funcs : Array Func} {id : FuncId} {f : Func}
    (h : findFunctionIn? funcs id = some f) : f ∈ funcs := by
  rw [findFunctionIn?, ← Array.foldl_toList] at h
  rcases findAux_mem funcs.toList none f h with h' | h'
  · exact absurd h' (by simp)
  · simpa [← Array.mem_toList_iff] using h'

/-- With no methods in scope there is no dynamic dispatch. -/
theorem dynamicDispatch?_none {σ : ExecState} (hm : σ.methods = #[])
    (f : Func) (vs : Array GoValue) : dynamicDispatch? σ f vs = .ok none := by
  simp [dynamicDispatch?, methodInfoByFuncId?, hm, pure, Except.pure]

/-! ## The panic-side expression and assignee bridges (D3)

Fragment evaluations that panic map to `ExprR .panic` derivations. Loads,
lookups, and fragment-typed normalization/equality never panic (they fail
as `stuck`), so every fragment panic originates at division by zero or a
nil dereference and propagates through the strict operand positions. -/

theorem intBinaryResult_no_panic {op : String} {f : Int → Int → Int}
    {l r : GoValue} {msg : String} :
    intBinaryResult op f l r ≠ .error (.panic msg) := by
  unfold intBinaryResult
  cases l <;> cases r <;>
    simp [valueAsIntValue, bind_eq_error] <;>
  (cases hc : IntKind.compatibleResult _ _ <;>
    simp [Functor.map, Except.map])

theorem valueEq_frag_no_panic {t : Ty} (ht : TyFrag t) {σ : ExecState}
    (l r : GoValue) {msg : String} :
    valueEq σ t l r ≠ .error (.panic msg) := by
  cases ht <;> cases l <;> cases r <;> simp [valueEq, valueEqFuel]

theorem evalExpr_frag_panic {e : Expr} (hf : ExprFrag e) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      evalExpr σ e = .error (.panic msg) →
      ∀ L, ExprR σ.locals (σ.withLocals L) e (.panic msg) := by
  induction hf with
  | var id =>
    intro σ hh msg h L
    simp only [evalExpr, GoCore.lookup] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨w, hw, h⟩
    · rw [bind_eq_error] at h
      rcases h with h | ⟨loc, hloc, h⟩
      · unfold lookupLoc at h
        cases hl : LocalEnv.lookup σ.locals id <;> rw [hl] at h <;> simp at h
      · exact absurd h (loadLoc_no_panic hh)
    · simp at h
  | intLit n k => intro σ hh msg h L; simp [evalExpr] at h
  | boolLit b => intro σ hh msg h L; simp [evalExpr] at h
  | add hl hr ihl ihr =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨lv, σ₁⟩, hlv, h⟩
    · exact .binPanicLeft _ (.inl rfl) (ihl hh h L)
    · obtain ⟨heq, hfl, hRl⟩ := evalExpr_frag_ok hl hh hlv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨rv, σ₂⟩, hrv, h⟩
      · exact .binPanicRight _ (.inl rfl) (hRl L) (ihr hh h L)
      · obtain ⟨heq2, hfr, hRr⟩ := evalExpr_frag_ok hr hh hrv
        subst heq2
        cases hfl <;> cases hfr <;> dsimp only at h <;>
          first
            | (rw [bind_eq_error] at h
               rcases h with h | ⟨w, hw, h⟩
               · exact absurd h intBinaryResult_no_panic
               · simp at h)
            | simp at h
  | sub hl hr ihl ihr =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨lv, σ₁⟩, hlv, h⟩
    · exact .binPanicLeft _ (.inr (.inl rfl)) (ihl hh h L)
    · obtain ⟨heq, hfl, hRl⟩ := evalExpr_frag_ok hl hh hlv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨rv, σ₂⟩, hrv, h⟩
      · exact .binPanicRight _ (.inr (.inl rfl)) (hRl L) (ihr hh h L)
      · obtain ⟨heq2, hfr, hRr⟩ := evalExpr_frag_ok hr hh hrv
        subst heq2
        cases hfl <;> cases hfr <;> dsimp only at h <;>
          first
            | (rw [bind_eq_error] at h
               rcases h with h | ⟨w, hw, h⟩
               · exact absurd h intBinaryResult_no_panic
               · simp at h)
            | simp at h
  | mul hl hr ihl ihr =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨lv, σ₁⟩, hlv, h⟩
    · exact .binPanicLeft _ (.inr (.inr (.inl rfl))) (ihl hh h L)
    · obtain ⟨heq, hfl, hRl⟩ := evalExpr_frag_ok hl hh hlv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨rv, σ₂⟩, hrv, h⟩
      · exact .binPanicRight _ (.inr (.inr (.inl rfl))) (hRl L) (ihr hh h L)
      · obtain ⟨heq2, hfr, hRr⟩ := evalExpr_frag_ok hr hh hrv
        subst heq2
        cases hfl <;> cases hfr <;> dsimp only at h <;>
          first
            | (rw [bind_eq_error] at h
               rcases h with h | ⟨w, hw, h⟩
               · exact absurd h intBinaryResult_no_panic
               · simp at h)
            | simp at h
  | div hl hr ihl ihr =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨lv, σ₁⟩, hlv, h⟩
    · exact .binPanicLeft _ (.inr (.inr (.inr rfl))) (ihl hh h L)
    · obtain ⟨heq, hfl, hRl⟩ := evalExpr_frag_ok hl hh hlv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨rv, σ₂⟩, hrv, h⟩
      · exact .binPanicRight _ (.inr (.inr (.inr rfl))) (hRl L) (ihr hh h L)
      · obtain ⟨heq2, hfr, hRr⟩ := evalExpr_frag_ok hr hh hrv
        subst heq2
        cases hfr with
        | int rvv rk =>
          rw [bind_eq_error] at h
          rcases h with h | ⟨d, hd, h⟩
          · simp [valueAsInt] at h
          · simp only [valueAsInt, pure_eq_ok] at hd
            subst hd
            cases hz : (rvv == 0) with
            | true =>
              have hz' : rvv = 0 := by simpa using hz
              subst hz'
              rw [hz] at h
              simp only [reduceIte, panic_def] at h
              rw [bind_eq_error] at h
              rcases h with h | ⟨u, hu, h⟩
              · injection h with hmsg
                injection hmsg with hmsg'
                subst hmsg'
                exact .divByZero (hRl L) (hRr L)
              · simp at hu
            | false =>
              rw [hz] at h
              simp only [Bool.false_eq_true, reduceIte] at h
              rw [bind_eq_error] at h
              rcases h with h | ⟨w, hw, h⟩
              · simp at h
              · rw [bind_eq_error] at h
                rcases h with h | ⟨u, hu, h⟩
                · exact absurd h intBinaryResult_no_panic
                · simp at h
        | bool b =>
          rw [bind_eq_error] at h
          rcases h with h | ⟨d, hd, h⟩
          · simp [valueAsInt] at h
          · simp [valueAsInt] at hd
        | addr l =>
          rw [bind_eq_error] at h
          rcases h with h | ⟨d, hd, h⟩
          · simp [valueAsInt] at h
          · simp [valueAsInt] at hd
        | nil =>
          rw [bind_eq_error] at h
          rcases h with h | ⟨d, hd, h⟩
          · simp [valueAsInt] at h
          · simp [valueAsInt] at hd
  | eqCmp hty hl hr ihl ihr =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨lv, σ₁⟩, hlv, h⟩
    · exact .eqPanicLeft (ihl hh h L)
    · obtain ⟨heq, hfl, hRl⟩ := evalExpr_frag_ok hl hh hlv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨rv, σ₂⟩, hrv, h⟩
      · exact .eqPanicRight (hRl L) (ihr hh h L)
      · obtain ⟨heq2, hfr, hRr⟩ := evalExpr_frag_ok hr hh hrv
        subst heq2
        rw [bind_eq_error] at h
        rcases h with h | ⟨b, hb, h⟩
        · exact absurd h (valueEq_frag_no_panic hty _ _)
        · simp at h
  | ref id =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨loc, hloc, h⟩
    · unfold lookupLoc at h
      cases hl : LocalEnv.lookup σ.locals id <;> rw [hl] at h <;> simp at h
    · simp at h
  | locLit l => intro σ hh msg h L; simp [evalExpr] at h
  | deref ty hp ihp =>
    intro σ hh msg h L
    simp only [evalExpr] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨pv, σ₁⟩, hpv, h⟩
    · exact .derefPanic (ihp hh h L)
    · obtain ⟨heq, hfp, hRp⟩ := evalExpr_frag_ok hp hh hpv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨loc, hloc, h⟩
      · cases hfp with
        | nil =>
          simp only [valueAsLoc, panic_def] at h
          injection h with hmsg
          injection hmsg with hmsg'
          subst hmsg'
          exact .derefNil (hRp L)
        | int n k => simp [valueAsLoc] at h
        | bool b => simp [valueAsLoc] at h
        | addr l => simp [valueAsLoc] at h
      · cases hfp with
        | addr l =>
          simp only [valueAsLoc, pure_eq_ok] at hloc
          subst hloc
          rw [bind_eq_error] at h
          rcases h with h | ⟨w, hw, h⟩
          · exact absurd h (loadLoc_no_panic hh)
          · simp at h
        | int n k => simp [valueAsLoc] at hloc
        | bool b => simp [valueAsLoc] at hloc
        | nil => simp [valueAsLoc] at hloc

theorem evalAssigneeLoc_frag_panic {a : Assignee} (ha : AssigneeFrag a) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      evalAssigneeLoc σ a = .error (.panic msg) →
      ∀ L, AssigneeR σ.locals (σ.withLocals L) a (.panic msg) := by
  cases ha with
  | var id =>
    intro σ hh msg h L
    simp only [evalAssigneeLoc] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨loc, hloc, h⟩
    · unfold lookupLoc at h
      cases hl : LocalEnv.lookup σ.locals id <;> rw [hl] at h <;> simp at h
    · simp at h
  | addr he =>
    intro σ hh msg h L
    simp only [evalAssigneeLoc] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨pv, σ₁⟩, hpv, h⟩
    · exact .addrPanic (evalExpr_frag_panic he hh h L)
    · obtain ⟨heq, hfp, hRp⟩ := evalExpr_frag_ok he hh hpv
      subst heq
      cases hfp with
      | nil =>
        simp only [valueAsLoc, panic_def] at h
        rw [bind_eq_error] at h
        rcases h with h | ⟨w, hw, h⟩
        · injection h with hmsg
          injection hmsg with hmsg'
          subst hmsg'
          exact .addrNil (hRp L)
        · simp at hw
      | int n k =>
        dsimp only at h
        simp [valueAsLoc, bind, Except.bind] at h
      | bool b =>
        dsimp only at h
        simp [valueAsLoc, bind, Except.bind] at h
      | addr l =>
        dsimp only at h
        simp [valueAsLoc, bind, Except.bind, pure, Except.pure] at h

/-! ## Panic-freedom of the fragment substrate (statement layer, D3b)

Stores, declarations, parameter binding, and result readback never panic
over the fragment — their failures are `stuck`. So every statement-level
panic originates in an expression/assignee leg (or a callee body). -/

theorem normalizeValueForTy_frag_no_panic {σ : ExecState} {t : Ty}
    (ht : TyFrag t) (v : GoValue) {msg : String} :
    normalizeValueForTy σ t v ≠ .error (.panic msg) := by
  cases ht <;> cases v <;> simp [normalizeValueForTy, normalizeValueForTyFuel]

theorem coerceStoredValue_no_panic {old v : GoValue} {msg : String}
    (hv : FragVal v) :
    coerceStoredValue old v ≠ .error (.panic msg) := by
  cases old <;> cases hv <;> simp [coerceStoredValue]

theorem storeLoc_frag_no_panic {σ : ExecState} (hh : HeapFrag σ) :
    ∀ {loc : Loc} {v : GoValue} {msg : String}, FragVal v →
      storeLoc σ loc v ≠ .error (.panic msg) := by
  intro loc
  induction loc with
  | base a =>
    intro v msg hv h
    cases hl : Heap.lookup σ.heap (.base a) with
    | some cell =>
      cases hd : cell.declaredTy with
      | some t =>
        simp only [storeLoc, hl, hd, bind_eq_error] at h
        rcases h with h | ⟨w, hw, h⟩
        · exact normalizeValueForTy_frag_no_panic ((hh _ _ hl).2 t hd) v h
        · simp at h
      | none =>
        simp only [storeLoc, hl, hd, bind_eq_error] at h
        rcases h with h | ⟨w, hw, h⟩
        · exact coerceStoredValue_no_panic hv h
        · simp at h
    | none => simp only [storeLoc, hl] at h; simp at h
  | field base typeId fieldName ih =>
    intro v msg hv h
    simp only [storeLoc, bind_eq_error] at h
    rcases h with h | ⟨w, hw, h⟩
    · exact loadLoc_no_panic hh h
    · cases loadLoc_frag hh hw <;> simp at h
  | index base index ih =>
    intro v msg hv h
    simp only [storeLoc, bind_eq_error] at h
    rcases h with h | ⟨w, hw, h⟩
    · exact loadLoc_no_panic hh h
    · cases loadLoc_frag hh hw <;> simp at h

theorem defaultValue_frag_total {σ : ExecState} {t : Ty} (ht : TyFrag t) :
    ∃ v, defaultValue σ t = .ok v ∧ FragVal v := by
  cases ht with
  | int k =>
    refine ⟨.int 0 k, ?_, .int _ _⟩
    simp [defaultValue, defaultValueFuel, pure_eq_ok]
  | bool =>
    refine ⟨.bool false, ?_, .bool _⟩
    simp [defaultValue, defaultValueFuel, pure_eq_ok]
  | pointer e =>
    refine ⟨.nil, ?_, .nil⟩
    simp [defaultValue, defaultValueFuel, pure_eq_ok]

theorem execDeclList_frag_no_panic {ds : List Param}
    (hts : ∀ p ∈ ds, TyFrag p.typ) :
    ∀ {σ : ExecState} {msg : String},
      execDeclList σ ds ≠ .error (.panic msg) := by
  induction ds with
  | nil => intro σ msg hc; simp [execDeclList] at hc
  | cons q qs ih =>
    intro σ msg hc
    obtain ⟨v, hv, -⟩ := defaultValue_frag_total (σ := σ) (hts q (by simp))
    simp only [execDeclList, execDecl, bind_eq_error, bind_eq_ok,
      pure_eq_ok, hv] at hc
    rcases hc with hc | ⟨σm, hm, hc⟩
    · simp at hc
    · exact ih (fun r hr => hts r (by simp [hr])) hc

theorem bindParamList_frag_no_panic {ps : List Param}
    (hts : ∀ p ∈ ps, TyFrag p.typ) :
    ∀ {vs : List GoValue} {σ : ExecState} {msg : String},
      bindParamList σ ps vs ≠ .error (.panic msg) := by
  induction ps with
  | nil =>
    intro vs σ msg hc
    cases vs <;> simp [bindParamList] at hc
  | cons q qs ih =>
    intro vs σ msg hc
    cases vs with
    | nil => simp [bindParamList] at hc
    | cons v vs' =>
      simp only [bindParamList, bind_eq_error] at hc
      rcases hc with hc | ⟨w, hw, hc⟩
      · exact normalizeValueForTy_frag_no_panic (hts q (by simp)) v hc
      · exact ih (fun r hr => hts r (by simp [hr])) hc

theorem readResultList_no_panic {rs : List Param} :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      readResultList σ rs ≠ .error (.panic msg) := by
  induction rs with
  | nil => intro σ hh msg hc; simp [readResultList] at hc
  | cons r rs' ih =>
    intro σ hh msg hc
    simp only [readResultList, GoCore.lookup, bind_eq_error] at hc
    rcases hc with hc | ⟨v, hv, hc⟩
    · rcases hc with hc | ⟨loc, hloc, hc⟩
      · unfold lookupLoc at hc
        cases hl : LocalEnv.lookup σ.locals r.id <;> rw [hl] at hc <;>
          simp at hc
      · exact loadLoc_no_panic hh hc
    · rcases hc with hc | ⟨tail, htail, hc⟩
      · exact ih hh hc
      · simp at hc

theorem assignLocList_frag_no_panic {locs : List Loc} :
    ∀ {vs : List GoValue}, (∀ v ∈ vs, FragVal v) →
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      assignLocList σ locs vs ≠ .error (.panic msg) := by
  induction locs with
  | nil =>
    intro vs hfv σ hh msg hc
    cases vs <;> simp [assignLocList] at hc
  | cons loc locs' ih =>
    intro vs hfv σ hh msg hc
    cases vs with
    | nil => simp [assignLocList] at hc
    | cons v vs' =>
      simp only [assignLocList, assignLoc, bind_eq_error] at hc
      rcases hc with hc | ⟨σ₁, hst, hc⟩
      · exact storeLoc_frag_no_panic hh (hfv v (by simp)) hc
      · obtain ⟨-, hh₁, -⟩ := storeLoc_frag hh (hfv v (by simp)) hst
        exact ih (fun w hw => hfv w (by simp [hw])) hh₁ hc

theorem lookup_declare_ne {L : LocalEnv} {n id : String} {loc : Loc}
    (h : n ≠ id) :
    LocalEnv.lookup (LocalEnv.declare L n loc) id = LocalEnv.lookup L id := by
  have hb : (n == id) = false := by simpa [beq_eq_false_iff_ne]
  cases L with
  | nil => simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hb]
  | cons s outer => simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hb]

theorem lookup_declare_mono {L : LocalEnv} {n : String} {l : Loc}
    {id : String} :
    (∃ loc, LocalEnv.lookup L id = some loc) →
    ∃ loc, LocalEnv.lookup (LocalEnv.declare L n l) id = some loc := by
  intro ⟨loc, hl⟩
  by_cases he : n = id
  · subst he
    cases L <;>
      exact ⟨l, by simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]⟩
  · exact ⟨loc, by rw [lookup_declare_ne he]; exact hl⟩

theorem declsR_lookup_mono {env : LocalEnv} {s : ExecState} {ps : List Param}
    {env' : LocalEnv} {s' : ExecState} (hd : DeclsR env s ps env' s')
    {id : String} :
    (∃ loc, LocalEnv.lookup env id = some loc) →
    ∃ loc, LocalEnv.lookup env' id = some loc := by
  induction hd with
  | nil => exact fun hx => hx
  | cons _ _ _ ih => exact fun hx => ih (lookup_declare_mono hx)

theorem declsR_lookup_exists {env : LocalEnv} {s : ExecState}
    {ps : List Param} {env' : LocalEnv} {s' : ExecState}
    (hd : DeclsR env s ps env' s') :
    ∀ q ∈ ps, ∃ loc, LocalEnv.lookup env' q.id = some loc := by
  induction hd with
  | nil => intro q hq; cases hq
  | @cons env₀ envf s₀ s₁ sf p rest v loc hdv ha hrest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · refine declsR_lookup_mono hrest ⟨loc, ?_⟩
      cases env₀ <;>
        simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
    · exact ih q hq'

theorem lookupsR_exists {env' : LocalEnv} {ps : List Param}
    (hex : ∀ q ∈ ps, ∃ loc, LocalEnv.lookup env' q.id = some loc) :
    ∃ rl, LookupsR env' ps rl := by
  induction ps with
  | nil => exact ⟨[], .nil⟩
  | cons q qs ih =>
    obtain ⟨loc, hloc⟩ := hex q (by simp)
    obtain ⟨rl, hrl⟩ := ih (fun r hr => hex r (by simp [hr]))
    exact ⟨loc :: rl, .cons hloc hrl⟩

/-! ## The call-leg panic bridges (fragment legs are state-preserving,
so the fault state is the entry state) -/

theorem evalAssigneeLocList_frag_panic {as : List Assignee}
    (hf : ∀ a ∈ as, AssigneeFrag a) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      evalAssigneeLocList σ as = .error (.panic msg) →
      ∀ L, AssigneesPanicR σ.locals (σ.withLocals L) as msg (σ.withLocals L) := by
  induction as with
  | nil => intro σ hh msg h L; simp [evalAssigneeLocList] at h
  | cons a rest ih =>
    intro σ hh msg h L
    simp only [evalAssigneeLocList] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨loc, σ₁⟩, hloc, h⟩
    · exact .here (evalAssigneeLoc_frag_panic (hf a (by simp)) hh h L)
    · obtain ⟨heq, hA⟩ := evalAssigneeLoc_frag_ok (hf a (by simp)) hh hloc
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨tail, σ₂⟩, htail, h⟩
      · exact .there (hA L) (ih (fun q hq => hf q (by simp [hq])) hh h L)
      · simp at h

theorem evalExprSeq_frag_panic {es : List Expr} (hf : ∀ e ∈ es, ExprFrag e) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {msg : String},
      evalExprSeq σ es = .error (.panic msg) →
      ∀ L, ArgsPanicR σ.locals (σ.withLocals L) es msg (σ.withLocals L) := by
  induction es with
  | nil => intro σ hh msg h L; simp [evalExprSeq] at h
  | cons e rest ih =>
    intro σ hh msg h L
    simp only [evalExprSeq] at h
    rw [bind_eq_error] at h
    rcases h with h | ⟨⟨v, σ₁⟩, hv, h⟩
    · exact .here (evalExpr_frag_panic (hf e (by simp)) hh h L)
    · obtain ⟨heq, hfv, hRv⟩ := evalExpr_frag_ok (hf e (by simp)) hh hv
      subst heq
      rw [bind_eq_error] at h
      rcases h with h | ⟨⟨tail, σ₂⟩, htail, h⟩
      · exact .there (hRv L) (ih (fun q hq => hf q (by simp [hq])) hh h L)
      · simp at h

/-! ## Call bridges: the interpreter's call path maps to the relation's
`ArgsR`/`AssigneesR`/`BindParamsR`/`ResultsR`/`StoreManyR` legs. -/

theorem evalExprSeq_frag_sound {es : List Expr} (hf : ∀ e ∈ es, ExprFrag e) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {vs : Array GoValue} {σ' : ExecState},
      evalExprSeq σ es = .ok (vs, σ') →
      σ' = σ ∧ (∀ v ∈ vs, FragVal v) ∧
        ∀ L, ArgsR σ.locals (σ.withLocals L) es vs.toList (σ.withLocals L) := by
  induction es with
  | nil =>
    intro σ hh vs σ' h
    simp only [evalExprSeq, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp, fun L => .nil⟩
  | cons e rest ih =>
    intro σ hh vs σ' h
    simp only [evalExprSeq] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨v, σ₁⟩, hv, h⟩ := h
    obtain ⟨heq, hfv, hRv⟩ := evalExpr_frag_ok (hf e (by simp)) hh hv
    rw [heq] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨tail, σ₂⟩, htail, h⟩ := h
    obtain ⟨rfl, hftail, hRtail⟩ := ih (fun e' he' => hf e' (by simp [he'])) hh htail
    simp only [pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, fun L => ?_⟩
    · intro w hw
      rcases (by simpa using hw : w = v ∨ w ∈ tail) with rfl | hw'
      · exact hfv
      · exact hftail w hw'
    · have : (#[v] ++ tail).toList = v :: tail.toList := by simp
      rw [this]
      exact .cons (hRv L) (hRtail L)

theorem evalAssigneeLocList_frag_sound {as : List Assignee}
    (hf : ∀ a ∈ as, AssigneeFrag a) :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {locs : List Loc} {σ' : ExecState},
      evalAssigneeLocList σ as = .ok (locs, σ') →
      σ' = σ ∧
        ∀ L, AssigneesR σ.locals (σ.withLocals L) as locs (σ.withLocals L) := by
  induction as with
  | nil =>
    intro σ hh locs σ' h
    simp only [evalAssigneeLocList, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun L => .nil⟩
  | cons a rest ih =>
    intro σ hh locs σ' h
    simp only [evalAssigneeLocList] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨loc, σ₁⟩, hloc, h⟩ := h
    obtain ⟨heq, hA⟩ := evalAssigneeLoc_frag_ok (hf a (by simp)) hh hloc
    rw [heq] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨tail, σ₂⟩, htail, h⟩ := h
    obtain ⟨rfl, hRtail⟩ := ih (fun a' ha' => hf a' (by simp [ha'])) hh htail
    simp only [pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun L => .cons (hA L) (hRtail L)⟩

theorem bindParamList_frag_sound {ps : List Param} (hts : ∀ p ∈ ps, TyFrag p.typ) :
    ∀ {vs : List GoValue}, ps.length = vs.length → (∀ v ∈ vs, FragVal v) →
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {σb : ExecState},
      bindParamList σ ps vs = .ok σb →
      HeapFrag σb ∧ σb.functions = σ.functions ∧ σb.methods = σ.methods ∧
        ∀ L, BindParamsR σ.locals (σ.withLocals L) ps vs σb.locals (σb.withLocals L) := by
  induction ps with
  | nil =>
    intro vs hlen hfv σ hh σb h
    cases vs with
    | nil =>
      simp only [bindParamList, pure_eq_ok] at h
      subst h
      exact ⟨hh, rfl, rfl, fun L => .nil⟩
    | cons v vs' => simp at hlen
  | cons p ps' ih =>
    intro vs hlen hfv σ hh σb h
    cases vs with
    | nil => simp at hlen
    | cons v vs' =>
      simp only [bindParamList, bind_eq_ok] at h
      obtain ⟨v', hv', h⟩ := h
      have htp : TyFrag p.typ := hts p (by simp)
      have hfv' : FragVal v' :=
        normalizeValueForTy_frag_val htp (hfv v (by simp)) hv'
      have hh₁ : HeapFrag (σ.declareLocal p.id (some p.typ) v') := by
        rw [declareLocal_eq_alloc]
        exact heapFrag_alloc hh hfv' (fun t' ht' => by cases ht'; exact htp)
      obtain ⟨hhb, hfns, hmth, hR⟩ := ih (fun q hq => hts q (by simp [hq]))
        (by simpa using hlen) (fun w hw => hfv w (by simp [hw])) hh₁ h
      refine ⟨hhb, hfns, hmth, fun L => ?_⟩
      refine BindParamsR.cons (v' := v') (loc := (σ.alloc v' (some p.typ)).1)
        (s₁ := (σ.alloc v' (some p.typ)).2.withLocals L)
        ((normalizeValueForTy_state_indep (σ.withLocals L) σ htp v).trans hv')
        (alloc_withLocals σ L v' (some p.typ)) ?_
      exact hR L

theorem assignLocList_frag_sound {locs : List Loc} :
    ∀ {vs : List GoValue}, locs.length = vs.length → (∀ v ∈ vs, FragVal v) →
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {σ' : ExecState},
      assignLocList σ locs vs = .ok σ' →
      HeapFrag σ' ∧ σ'.locals = σ.locals ∧ σ'.functions = σ.functions ∧
        σ'.methods = σ.methods ∧
        ∀ L, StoreManyR (σ.withLocals L) locs vs (σ'.withLocals L) := by
  induction locs with
  | nil =>
    intro vs hlen hfv σ hh σ' h
    cases vs with
    | nil =>
      simp only [assignLocList, pure_eq_ok] at h
      subst h
      exact ⟨hh, rfl, rfl, rfl, fun L => .nil⟩
    | cons v vs' => simp at hlen
  | cons loc locs' ih =>
    intro vs hlen hfv σ hh σ' h
    cases vs with
    | nil => simp at hlen
    | cons v vs' =>
      simp only [assignLocList, assignLoc, bind_eq_ok] at h
      obtain ⟨σ₁, hst, h⟩ := h
      obtain ⟨⟨a, rfl⟩, hh₁, hloc₁⟩ := storeLoc_frag hh (hfv v (by simp)) hst
      obtain ⟨-, hfns₁, hmth₁, -, -⟩ := storeLoc_ctx hst
      obtain ⟨hh', hloc', hfns', hmth', hR⟩ := ih (by simpa using hlen)
        (fun w hw => hfv w (by simp [hw])) hh₁ h
      refine ⟨hh', hloc'.trans hloc₁, hfns'.trans hfns₁, hmth'.trans hmth₁,
        fun L => ?_⟩
      refine StoreManyR.cons (s₁ := σ₁.withLocals L) ?_ (hR L)
      rw [storeLoc_withLocals_base _ L a v
        (fun cell t hc ht => (hh _ _ hc).2 t ht), hst]
      rfl

mutual
/-- Non-spine fragment statements — usable in any position. Excludes
`.initialization`: only the *governing* seq tracks a declaration's env
extension in the relation (D1), so declarations are fragment-legal only as
spine elements. Block spines are unrestricted (D2-proper: block pops cannot
redirect the frame's result read). -/
inductive StmtFragNS : Stmt → Prop where
  | assign {a : Assignee} {e : Expr} :
      AssigneeFrag a → ExprFrag e → StmtFragNS (.assign a e)
  | seqn {ss : Array Stmt} :
      (∀ s, s ∈ ss → StmtFragNS s) → StmtFragNS (.seqn ss)
  | block {decls : Array Param} {ss : Array Stmt} :
      (∀ p, p ∈ decls → TyFrag p.typ) →
      (∀ s, s ∈ ss → SpineFrag [] s) →
      StmtFragNS (.block decls ss)
  | ifThenElse {c : Expr} {t e : Stmt} :
      ExprFrag c → StmtFragNS t → StmtFragNS e →
      StmtFragNS (.ifThenElse c t e)
  | whileStmt {c : Expr} {b : Stmt} :
      ExprFrag c → StmtFragNS b → StmtFragNS (.while c b)
  | call {targets : Array Assignee} {funcId : FuncId} {args : Array Expr} :
      (∀ a, a ∈ targets → AssigneeFrag a) → (∀ e, e ∈ args → ExprFrag e) →
      StmtFragNS (.call targets funcId args)
  | returnStmt : StmtFragNS .returnStmt
  | breakStmt : StmtFragNS .breakStmt
  | continueStmt : StmtFragNS .continueStmt

/-- Spine (declaration-tracking) positions: elements of a function/block body
statement list. A spine init must avoid the `avoid` names (for a function
body's top-level spine these are the result ids — the Go-illegal
redeclaration shape that would redirect the interpreter's exit read). -/
inductive SpineFrag : List String → Stmt → Prop where
  | ns {avoid : List String} {s : Stmt} : StmtFragNS s → SpineFrag avoid s
  | init {avoid : List String} {p : Param} : TyFrag p.typ → p.id ∉ avoid →
      SpineFrag avoid (.initialization p)
  /-- A nested `.seqn` in spine position — declarations allowed (D1: the
  splice rule makes the relation scope-transparent here, matching the
  interpreter and Go statement lists; this is the shape the frontend emits
  for every declaration group). -/
  | seqnSpine {avoid : List String} {ss : Array Stmt} :
      (∀ s, s ∈ ss → SpineFrag avoid s) → SpineFrag avoid (.seqn ss)
end

/-- A fragment function: fragment-typed params and results, and a body that
is either a `.seqn` spine (inits avoiding the result ids) or a bare
non-spine statement. No fall-through condition (D2-proper: `frameFall`
performs the same result read/stores as `frameReturn`). -/
structure FuncFrag (f : Func) : Prop where
  argsTy : ∀ p, p ∈ f.args → TyFrag p.typ
  resultsTy : ∀ r, r ∈ f.results → TyFrag r.typ
  body : (∃ ss : Array Stmt, f.body = .seqn ss ∧
      (∀ s, s ∈ ss → SpineFrag (f.results.toList.map (·.id)) s)) ∨
    StmtFragNS f.body

def FuncsFrag (funcs : Array Func) : Prop := ∀ f, f ∈ funcs → FuncFrag f

/-- The program-level invariant threaded through the simulation:
fragment-shaped heap, no methods (no dynamic dispatch), every function in
scope fragment-shaped. Locals-independent by construction. -/
structure StInv (σ : ExecState) : Prop where
  heap : HeapFrag σ
  methods : σ.methods = #[]
  funcs : FuncsFrag σ.functions

/-- Transport `StInv` along a state whose functions/methods agree. -/
theorem StInv.transport {σ σf : ExecState} (hinv : StInv σ) (hh : HeapFrag σf)
    (hfns : σf.functions = σ.functions) (hmth : σf.methods = σ.methods) :
    StInv σf :=
  ⟨hh, hmth.trans hinv.methods, hfns ▸ hinv.funcs⟩

/-- Reading the frame's results at exit: inverts the interpreter's
`readResultList` and — given that the body run preserved the result ids'
resolutions (T2's lookup-preservation, D2-proper's residual condition) —
produces both call-time `LookupsR` locations and the exit-state `LoadsR`
values at those same locations. -/
theorem readResultList_locs_sound {rs : List Param} :
    ∀ {σ : ExecState}, HeapFrag σ → ∀ {vs : List GoValue},
      readResultList σ rs = .ok vs →
      (∀ v ∈ vs, FragVal v) ∧
      ∀ {E : LocalEnv},
        (∀ r ∈ rs, LocalEnv.lookup E r.id = LocalEnv.lookup σ.locals r.id) →
        ∃ locs, LookupsR E rs locs ∧ ∀ L, LoadsR (σ.withLocals L) locs vs := by
  induction rs with
  | nil =>
    intro σ hh vs h
    simp only [readResultList, pure_eq_ok] at h
    subst h
    exact ⟨by simp, fun _ => ⟨[], .nil, fun L => .nil⟩⟩
  | cons r rs' ih =>
    intro σ hh vs h
    simp only [readResultList, GoCore.lookup, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨v, ⟨loc, hloc, hload⟩, tail, htail, h⟩ := h
    subst h
    obtain ⟨hftail, hlocs⟩ := ih hh htail
    refine ⟨?_, fun {E} hpres => ?_⟩
    · intro w hw
      rcases (by simpa using hw : w = v ∨ w ∈ tail) with rfl | hw'
      · exact loadLoc_frag hh hload
      · exact hftail w hw'
    · obtain ⟨locs, hlk, hld⟩ := hlocs (fun q hq => hpres q (by simp [hq]))
      refine ⟨loc :: locs, .cons ?_ hlk, fun L =>
        .cons ((loadLoc_withLocals σ L loc).trans hload) (hld L)⟩
      rw [hpres r (by simp)]
      exact lookupLoc_eq_ok.mp hloc

set_option maxRecDepth 4096 in
mutual
/-- **T1 — statement simulation.** A successful interpreter execution of a
non-spine fragment statement maps to a `Steps` segment of the CEK relation,
from `.exec stmt σ.locals k` to the outcome's configuration over any
continuation `k` and transported state, preserving the program invariant.
Every outcome leaves `locals` untouched (blocks pop what they push on every
path; D2-proper: `returning` is env-free). -/
theorem execStmt_frag_sound {stmt : Stmt} (hf : StmtFragNS stmt)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hinv : StInv σ)
    {out : ExecOutcome} {ch' : Choices}
    (h : execStmt fuel σ ch stmt = .ok (out, ch')) :
    StInv out.state ∧
    match out with
    | .normal σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.next k) (σf.withLocals L)
    | .broke σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.breaking k.stripSeqs) (σf.withLocals L)
    | .continued σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.continuing k.stripSeqs) (σf.withLocals L)
    | .returned σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.returning k.stripSeqs) (σf.withLocals L) := by
  cases stmt with
  | initialization p => exact nomatch hf
  | assignMany l r => exact nomatch hf
  | newValue t v ty => exact nomatch hf
  | makeSlice t e l c => exact nomatch hf
  | makeMap t k v i => exact nomatch hf
  | mapAssign b i v kt vt => exact nomatch hf
  | mapLookup t o b i kt vt => exact nomatch hf
  | typeAssert t o e tt => exact nomatch hf
  | appendSlice t e s es => exact nomatch hf
  | copySlice t d s => exact nomatch hf
  | mapRange kv vv me kt vt b => exact nomatch hf
  | label n => exact nomatch hf
  | unsupported f => exact nomatch hf
  | assign a e =>
    cases hf with
    | assign ha he =>
      obtain ⟨σf, rfl, rfl, hhf, hloc, hfns, hmth, hstep⟩ :=
        execStmt_assign_ok ha he hinv.heap h
      exact ⟨hinv.transport hhf hfns hmth, hloc,
        fun L k => Steps.single (hstep L k)⟩
  | seqn ss =>
    cases hf with
    | seqn hss =>
      simp only [execStmt, execStmts] at h
      have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
      obtain ⟨hif, hrest⟩ :=
        execStmtList_frag_sound (avoid := [])
          (fun s hs => .ns (hss s (by simpa using hs))) fuel σ ch hinv h
      refine ⟨hif, ?_⟩
      cases out with
      | normal σf =>
        obtain ⟨-, hns, -, hsteps⟩ := hrest
        have hloc := hns (fun s hs => hss s (by simpa using hs))
        refine ⟨hloc, fun L k => (Steps.single Step.seqn).trans ?_⟩
        have hwrap : ∀ k₀ : Cont,
            seqCont ss.toList σ.locals k₀ = .seq ss.toList σ.locals k₀ →
            Steps (.next (seqCont ss.toList σ.locals k₀)) (σ.withLocals L)
              (.next k₀) (σf.withLocals L) := by
          intro k₀ he
          rw [he]
          have h0 := hsteps L k₀ []
          rw [List.append_nil] at h0
          exact h0.tail Step.seqDone
        match k with
        | .stop => exact hwrap .stop rfl
        | .loop c b env' k₂ => exact hwrap _ rfl
        | .frame t r k₂ => exact hwrap _ rfl
        | .seq rest env' k₂ =>
          by_cases henv : env' = σ.locals
          · subst henv
            have h0 := hsteps L k₂ rest
            rw [hloc] at h0
            rw [show seqCont ss.toList σ.locals (.seq rest σ.locals k₂)
                = .seq (ss.toList ++ rest) σ.locals k₂ by simp [seqCont]]
            exact h0
          · exact hwrap _ (by simp [seqCont, henv])
      | broke σf =>
        obtain ⟨-, hns, -, hsteps⟩ := hrest
        refine ⟨hns (fun s hs => hss s (by simpa using hs)),
          fun L k => (Steps.single Step.seqn).trans ?_⟩
        match k with
        | .stop =>
          have h0 := hsteps L .stop []
          rw [List.append_nil] at h0
          exact h0
        | .loop c b env' k₂ =>
          have h0 := hsteps L (.loop c b env' k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .frame t r k₂ =>
          have h0 := hsteps L (.frame t r k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .seq rest env' k₂ =>
          by_cases henv : env' = σ.locals
          · subst henv
            rw [show seqCont ss.toList σ.locals (.seq rest σ.locals k₂)
                = .seq (ss.toList ++ rest) σ.locals k₂ by simp [seqCont]]
            exact hsteps L k₂ rest
          · rw [show seqCont ss.toList σ.locals (.seq rest env' k₂)
                = .seq ss.toList σ.locals (.seq rest env' k₂) by
                  simp [seqCont, henv]]
            have h0 := hsteps L (.seq rest env' k₂) []
            rw [List.append_nil] at h0
            exact h0
      | continued σf =>
        obtain ⟨-, hns, -, hsteps⟩ := hrest
        refine ⟨hns (fun s hs => hss s (by simpa using hs)),
          fun L k => (Steps.single Step.seqn).trans ?_⟩
        match k with
        | .stop =>
          have h0 := hsteps L .stop []
          rw [List.append_nil] at h0
          exact h0
        | .loop c b env' k₂ =>
          have h0 := hsteps L (.loop c b env' k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .frame t r k₂ =>
          have h0 := hsteps L (.frame t r k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .seq rest env' k₂ =>
          by_cases henv : env' = σ.locals
          · subst henv
            rw [show seqCont ss.toList σ.locals (.seq rest σ.locals k₂)
                = .seq (ss.toList ++ rest) σ.locals k₂ by simp [seqCont]]
            exact hsteps L k₂ rest
          · rw [show seqCont ss.toList σ.locals (.seq rest env' k₂)
                = .seq ss.toList σ.locals (.seq rest env' k₂) by
                  simp [seqCont, henv]]
            have h0 := hsteps L (.seq rest env' k₂) []
            rw [List.append_nil] at h0
            exact h0
      | returned σf =>
        obtain ⟨-, hns, -, hsteps⟩ := hrest
        refine ⟨hns (fun s hs => hss s (by simpa using hs)),
          fun L k => (Steps.single Step.seqn).trans ?_⟩
        match k with
        | .stop =>
          have h0 := hsteps L .stop []
          rw [List.append_nil] at h0
          exact h0
        | .loop c b env' k₂ =>
          have h0 := hsteps L (.loop c b env' k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .frame t r k₂ =>
          have h0 := hsteps L (.frame t r k₂) []
          rw [List.append_nil] at h0
          exact h0
        | .seq rest env' k₂ =>
          by_cases henv : env' = σ.locals
          · subst henv
            rw [show seqCont ss.toList σ.locals (.seq rest σ.locals k₂)
                = .seq (ss.toList ++ rest) σ.locals k₂ by simp [seqCont]]
            exact hsteps L k₂ rest
          · rw [show seqCont ss.toList σ.locals (.seq rest env' k₂)
                = .seq ss.toList σ.locals (.seq rest env' k₂) by
                  simp [seqCont, henv]]
            have h0 := hsteps L (.seq rest env' k₂) []
            rw [List.append_nil] at h0
            exact h0
  | block decls ss =>
    cases hf with
    | block hdeclsTy hss =>
      simp only [execStmt, execStmts, execDecls, bind_eq_ok] at h
      obtain ⟨σd, hdecl, h⟩ := h
      obtain ⟨⟨oc, ch₁⟩, hbody, h⟩ := h
      simp only [pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨hout, rfl⟩ := h
      have hhent : HeapFrag { σ with locals := σ.locals.pushScope } := hinv.heap
      obtain ⟨hhd, hdpop, hdfns, hdmth, hdR⟩ :=
        execDeclList_frag_sound (fun p hp => hdeclsTy p (by simpa using hp))
          hhent hdecl
      have hdinv : StInv σd := hinv.transport hhd hdfns hdmth
      have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
      obtain ⟨hbinv, hrest⟩ := execStmtList_frag_sound (avoid := [])
        (fun s hs => hss s (by simpa using hs)) fuel σd ch hdinv hbody
      subst hout
      cases oc with
      | normal σbf =>
        obtain ⟨hpop, -, -, hsteps⟩ := hrest
        refine ⟨⟨hbinv.heap, hbinv.methods, hbinv.funcs⟩, ?_, fun L k => ?_⟩
        · show σbf.locals.popScope = σ.locals
          rw [hpop, hdpop]; rfl
        · have h0 := hsteps L k []
          rw [List.append_nil] at h0
          exact ((Steps.single (Step.block (hdR L))).trans h0).tail Step.seqDone
      | broke σbf =>
        obtain ⟨hpop, -, -, hsteps⟩ := hrest
        refine ⟨⟨hbinv.heap, hbinv.methods, hbinv.funcs⟩, ?_, fun L k => ?_⟩
        · show σbf.locals.popScope = σ.locals
          rw [hpop, hdpop]; rfl
        · have h0 := hsteps L k []
          rw [List.append_nil] at h0
          exact (Steps.single (Step.block (hdR L))).trans h0
      | continued σbf =>
        obtain ⟨hpop, -, -, hsteps⟩ := hrest
        refine ⟨⟨hbinv.heap, hbinv.methods, hbinv.funcs⟩, ?_, fun L k => ?_⟩
        · show σbf.locals.popScope = σ.locals
          rw [hpop, hdpop]; rfl
        · have h0 := hsteps L k []
          rw [List.append_nil] at h0
          exact (Steps.single (Step.block (hdR L))).trans h0
      | returned σbf =>
        obtain ⟨hpop, -, -, hsteps⟩ := hrest
        refine ⟨⟨hbinv.heap, hbinv.methods, hbinv.funcs⟩, ?_, fun L k => ?_⟩
        · show σbf.locals.popScope = σ.locals
          rw [hpop, hdpop]; rfl
        · have h0 := hsteps L k []
          rw [List.append_nil] at h0
          exact (Steps.single (Step.block (hdR L))).trans h0
  | ifThenElse c t e =>
    cases hf with
    | ifThenElse hc ht he =>
      simp only [execStmt] at h
      rw [bind_eq_ok] at h
      obtain ⟨⟨cv, σ₁⟩, hc', h⟩ := h
      obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hinv.heap hc'
      rw [heq] at h
      rw [bind_eq_ok] at h
      obtain ⟨b, hbv, h⟩ := h
      cases hfc with
      | bool bv =>
        simp only [valueAsBool, pure_eq_ok] at hbv
        subst hbv
        cases bv with
        | true =>
          simp only [reduceIte] at h
          obtain ⟨hif, hrest⟩ := execStmt_frag_sound ht fuel σ ch hinv h
          refine ⟨hif, ?_⟩
          cases out with
          | normal σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifTrue (hRc L))).trans (hsteps L k)⟩
          | broke σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifTrue (hRc L))).trans (hsteps L k)⟩
          | continued σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifTrue (hRc L))).trans (hsteps L k)⟩
          | returned σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifTrue (hRc L))).trans (hsteps L k)⟩
        | false =>
          simp only [Bool.false_eq_true, reduceIte] at h
          obtain ⟨hif, hrest⟩ := execStmt_frag_sound he fuel σ ch hinv h
          refine ⟨hif, ?_⟩
          cases out with
          | normal σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifFalse (hRc L))).trans (hsteps L k)⟩
          | broke σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifFalse (hRc L))).trans (hsteps L k)⟩
          | continued σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifFalse (hRc L))).trans (hsteps L k)⟩
          | returned σf =>
            obtain ⟨hl, hsteps⟩ := hrest
            exact ⟨hl, fun L k =>
              (Steps.single (Step.ifFalse (hRc L))).trans (hsteps L k)⟩
      | int n k => simp [valueAsBool] at hbv
      | addr l => simp [valueAsBool] at hbv
      | nil => simp [valueAsBool] at hbv
  | «while» c b =>
    cases hf with
    | whileStmt hc hb =>
      cases fuel with
      | zero => simp [execStmt] at h
      | succ fuel' =>
        simp only [execStmt] at h
        rw [bind_eq_ok] at h
        obtain ⟨⟨cv, σ₁⟩, hc', h⟩ := h
        obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hinv.heap hc'
        rw [heq] at h
        rw [bind_eq_ok] at h
        obtain ⟨bv', hbv, h⟩ := h
        cases hfc with
        | bool bv =>
          simp only [valueAsBool, pure_eq_ok] at hbv
          subst hbv
          cases bv with
          | false =>
            simp only [Bool.false_eq_true, reduceIte, pure_eq_ok,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hinv, rfl, fun L k => Steps.single (.whileFalse (hRc L))⟩
          | true =>
            simp only [reduceIte] at h
            rw [bind_eq_ok] at h
            obtain ⟨⟨ob, ch₁⟩, hbody, h⟩ := h
            obtain ⟨hbinv, hrest1⟩ :=
              execStmt_frag_sound hb (fuel' + 1) σ ch hinv hbody
            cases ob with
            | normal σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              obtain ⟨hif, hrest⟩ :=
                execStmt_frag_sound (.whileStmt hc hb) fuel' σb ch₁ hbinv h
              rw [hlb] at hrest
              refine ⟨hif, ?_⟩
              cases out with
              | normal σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | broke σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | continued σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | returned σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
            | continued σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              obtain ⟨hif, hrest⟩ :=
                execStmt_frag_sound (.whileStmt hc hb) fuel' σb ch₁ hbinv h
              rw [hlb] at hrest
              refine ⟨hif, ?_⟩
              cases out with
              | normal σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | broke σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | continued σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | returned σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
            | broke σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              simp only [pure_eq_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hbinv, hlb, fun L k =>
                ((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail Step.loopBreak⟩
            | returned σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              simp only [pure_eq_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hbinv, hlb, fun L k =>
                (((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopReturn).trans (Steps.returning_strip k _)⟩
        | int n k => simp [valueAsBool] at hbv
        | addr l => simp [valueAsBool] at hbv
        | nil => simp [valueAsBool] at hbv
  | call targets funcId args =>
    cases hf with
    | call htargets hargs =>
      simp only [execStmt] at h
      rw [bind_eq_ok] at h
      obtain ⟨⟨σfin, chfin⟩, hcall, h⟩ := h
      simp only [pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execFunctionCall, evalAssigneeLocs, bind_eq_ok, pure_eq_ok] at hcall
      obtain ⟨⟨tlocsA, σt⟩, ⟨⟨tlocs, σt₀⟩, htlist, htp⟩, hwl⟩ := hcall
      obtain ⟨heqt, hAss⟩ := evalAssigneeLocList_frag_sound
        (fun a ha => htargets a (by simpa using ha)) hinv.heap htlist
      subst σt₀
      simp only [Prod.mk.injEq] at htp
      obtain ⟨h1, h2⟩ := htp
      subst tlocsA
      subst σt
      simp only [execFunctionCallWithLocs] at hwl
      cases hfind : findFunctionIn? σ.functions funcId with
      | none =>
        rw [hfind] at hwl
        simp [bind_eq_ok] at hwl
      | some func =>
      rw [hfind] at hwl
      have hff : FuncFrag func := hinv.funcs func (findFunctionIn?_mem hfind)
      rw [bind_eq_ok] at hwl
      obtain ⟨y, hy, hwl⟩ := hwl
      simp only [pure_eq_ok] at hy
      subst hy
      cases hna : (func.args.size != args.size) with
      | true => rw [hna] at hwl; simp [bind_eq_ok] at hwl
      | false =>
      rw [hna] at hwl
      simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
      rw [bind_eq_ok] at hwl
      obtain ⟨⟨argValues, σa⟩, hargsEv, hwl⟩ := hwl
      obtain ⟨heqa, hfvals, hArgs⟩ := evalExprSeq_frag_sound
        (fun e he => hargs e (by simpa using he)) hinv.heap hargsEv
      subst σa
      rw [show dynamicDispatch? ((argValues, σ) : Array GoValue × ExecState).snd func
            ((argValues, σ) : Array GoValue × ExecState).fst = .ok none from
        dynamicDispatch?_none hinv.methods func argValues] at hwl
      simp only [bind_eq_ok, Except.ok.injEq] at hwl
      obtain ⟨d, hd, hwl⟩ := hwl
      subst hd
      cases fuel with
      | zero => simp [execFunctionWithValues] at hwl
      | succ fuel' =>
      simp only [execFunctionWithValues] at hwl
      cases hna2 : (func.args.size != argValues.size) with
      | true => rw [hna2] at hwl; simp [bind_eq_ok] at hwl
      | false =>
      rw [hna2] at hwl
      have hlen2 : func.args.size = argValues.size := by
        simpa using hna2
      simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
      rw [bind_eq_ok] at hwl
      obtain ⟨boundState, hbindP, hwl⟩ := hwl
      obtain ⟨hhb, hbfns, hbmth, hBind⟩ := bindParamList_frag_sound
        (fun p hp => hff.argsTy p (by simpa using hp))
        (by simpa using hlen2)
        (fun v hv => hfvals v (by simpa using hv))
        (show HeapFrag { σ with locals := [] } from hinv.heap) hbindP
      rw [bind_eq_ok] at hwl
      obtain ⟨callState, hdeclsR, hwl⟩ := hwl
      obtain ⟨hhc, hcpop, hcfns, hcmth, hDecls⟩ :=
        execDeclList_frag_sound (fun r hr => hff.resultsTy r (by simpa using hr))
          hhb hdeclsR
      have hcinv : StInv callState :=
        ⟨hhc, (hcmth.trans hbmth).trans hinv.methods,
          (hcfns.trans hbfns) ▸ hinv.funcs⟩
      rw [bind_eq_ok] at hwl
      obtain ⟨⟨outcome, ch₁⟩, hbody, hwl⟩ := hwl
      cases outcome with
      | broke σbf => simp [bind_eq_ok] at hwl
      | continued σbf => simp [bind_eq_ok] at hwl
      | normal σbf =>
        have hbodyRun : StInv σbf ∧
            (∀ r ∈ func.results.toList,
              LocalEnv.lookup callState.locals r.id
                = LocalEnv.lookup σbf.locals r.id) ∧
            ∀ L tl rl k₀, Steps
                (.exec func.body callState.locals (.frame tl rl k₀))
                (callState.withLocals L) (.next (.frame tl rl k₀))
                (σbf.withLocals L) := by
          rcases hff.body with ⟨bss, hbodyEq, hspine⟩ | hbodyNS
          · rw [hbodyEq] at hbody
            simp only [execStmt, execStmts] at hbody
            have hsz : sizeOf bss.toList < sizeOf bss := by
              cases bss; simp +arith
            obtain ⟨hoinv, hout2⟩ := execStmtList_frag_sound
              (avoid := func.results.toList.map (·.id))
              (fun s hs => hspine s (by simpa using hs)) fuel' callState ch
              hcinv hbody
            obtain ⟨-, -, hlk, hsteps⟩ := hout2
            refine ⟨hoinv, fun r hr =>
              (hlk r.id (List.mem_map_of_mem hr)).symm, fun L tl rl k₀ => ?_⟩
            rw [hbodyEq]
            have h0 := hsteps L (.frame tl rl k₀) []
            rw [List.append_nil] at h0
            exact ((Steps.single (Step.seqn (ss := bss)
              (env := callState.locals) (k := .frame tl rl k₀)
              (s := callState.withLocals L))).trans h0).tail Step.seqDone
          · obtain ⟨hoinv, hout2⟩ :=
              execStmt_frag_sound hbodyNS fuel' callState ch hcinv hbody
            obtain ⟨hl, hsteps⟩ := hout2
            exact ⟨hoinv, fun r hr => by rw [hl],
              fun L tl rl k₀ => hsteps L (.frame tl rl k₀)⟩
        obtain ⟨hoinv, hlkpres, hbsteps⟩ := hbodyRun
        rw [bind_eq_ok] at hwl
        obtain ⟨resultValues, hread, hwl⟩ := hwl
        obtain ⟨hfres, hlocs⟩ := readResultList_locs_sound
          (show HeapFrag σbf from hoinv.heap) hread
        obtain ⟨resultLocs, hLk, hLd⟩ := hlocs hlkpres
        simp only [assignLocs] at hwl
        cases hna3 : (tlocs.toArray.size != resultValues.toArray.size) with
        | true => rw [hna3] at hwl; simp [bind_eq_ok] at hwl
        | false =>
        rw [hna3] at hwl
        simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
        rw [bind_eq_ok] at hwl
        obtain ⟨σst, hstores, hwl⟩ := hwl
        simp only [pure_eq_ok, Prod.mk.injEq] at hwl
        obtain ⟨h1, h2⟩ := hwl
        subst σfin
        subst chfin
        have hstores' : assignLocList { σbf with locals := σ.locals }
            tlocs resultValues = .ok σst := by
          simpa using hstores
        have hlen3 : tlocs.length = resultValues.length := by
          have := (by simpa using hna3 :
            tlocs.toArray.size = resultValues.toArray.size)
          simpa using this
        obtain ⟨hhst, hlocst, hfnst, hmthst, hStoreR⟩ :=
          assignLocList_frag_sound hlen3 hfres
            (show HeapFrag { σbf with locals := σ.locals } from hoinv.heap)
            hstores'
        refine ⟨⟨hhst, hmthst.trans hoinv.methods, hfnst ▸ hoinv.funcs⟩,
          hlocst, fun L k => ?_⟩
        have hstep1 : Step (.exec (.call targets funcId args) σ.locals k)
            (σ.withLocals L)
            (.exec func.body callState.locals
              (.frame tlocs resultLocs k)) (callState.withLocals L) :=
          Step.call (hAss L) (hArgs L) hfind (hBind L) (hDecls L) hLk
        have hframe : Step (.next (.frame tlocs resultLocs k))
            (σbf.withLocals L) (.next k) (σst.withLocals L) :=
          Step.frameFall (hLd L) (hStoreR L)
        exact ((Steps.single hstep1).trans
          (hbsteps L tlocs resultLocs k)).tail hframe
      | returned σbf =>
        have hbodyRun : StInv σbf ∧
            (∀ r ∈ func.results.toList,
              LocalEnv.lookup callState.locals r.id
                = LocalEnv.lookup σbf.locals r.id) ∧
            ∀ L tl rl k₀, Steps
                (.exec func.body callState.locals (.frame tl rl k₀))
                (callState.withLocals L) (.returning (.frame tl rl k₀))
                (σbf.withLocals L) := by
          rcases hff.body with ⟨bss, hbodyEq, hspine⟩ | hbodyNS
          · rw [hbodyEq] at hbody
            simp only [execStmt, execStmts] at hbody
            have hsz : sizeOf bss.toList < sizeOf bss := by
              cases bss; simp +arith
            obtain ⟨hoinv, hout2⟩ := execStmtList_frag_sound
              (avoid := func.results.toList.map (·.id))
              (fun s hs => hspine s (by simpa using hs)) fuel' callState ch
              hcinv hbody
            obtain ⟨-, -, hlk, hsteps⟩ := hout2
            refine ⟨hoinv, fun r hr =>
              (hlk r.id (List.mem_map_of_mem hr)).symm, fun L tl rl k₀ => ?_⟩
            rw [hbodyEq]
            have h0 := hsteps L (.frame tl rl k₀) []
            rw [List.append_nil] at h0
            exact (Steps.single (Step.seqn (ss := bss)
              (env := callState.locals) (k := .frame tl rl k₀)
              (s := callState.withLocals L))).trans h0
          · obtain ⟨hoinv, hout2⟩ :=
              execStmt_frag_sound hbodyNS fuel' callState ch hcinv hbody
            obtain ⟨hl, hsteps⟩ := hout2
            exact ⟨hoinv, fun r hr => by rw [hl],
              fun L tl rl k₀ => hsteps L (.frame tl rl k₀)⟩
        obtain ⟨hoinv, hlkpres, hbsteps⟩ := hbodyRun
        rw [bind_eq_ok] at hwl
        obtain ⟨resultValues, hread, hwl⟩ := hwl
        obtain ⟨hfres, hlocs⟩ := readResultList_locs_sound
          (show HeapFrag σbf from hoinv.heap) hread
        obtain ⟨resultLocs, hLk, hLd⟩ := hlocs hlkpres
        simp only [assignLocs] at hwl
        cases hna3 : (tlocs.toArray.size != resultValues.toArray.size) with
        | true => rw [hna3] at hwl; simp [bind_eq_ok] at hwl
        | false =>
        rw [hna3] at hwl
        simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
        rw [bind_eq_ok] at hwl
        obtain ⟨σst, hstores, hwl⟩ := hwl
        simp only [pure_eq_ok, Prod.mk.injEq] at hwl
        obtain ⟨h1, h2⟩ := hwl
        subst σfin
        subst chfin
        have hstores' : assignLocList { σbf with locals := σ.locals }
            tlocs resultValues = .ok σst := by
          simpa using hstores
        have hlen3 : tlocs.length = resultValues.length := by
          have := (by simpa using hna3 :
            tlocs.toArray.size = resultValues.toArray.size)
          simpa using this
        obtain ⟨hhst, hlocst, hfnst, hmthst, hStoreR⟩ :=
          assignLocList_frag_sound hlen3 hfres
            (show HeapFrag { σbf with locals := σ.locals } from hoinv.heap)
            hstores'
        refine ⟨⟨hhst, hmthst.trans hoinv.methods, hfnst ▸ hoinv.funcs⟩,
          hlocst, fun L k => ?_⟩
        have hstep1 : Step (.exec (.call targets funcId args) σ.locals k)
            (σ.withLocals L)
            (.exec func.body callState.locals
              (.frame tlocs resultLocs k)) (callState.withLocals L) :=
          Step.call (hAss L) (hArgs L) hfind (hBind L) (hDecls L) hLk
        have hframe : Step (.returning (.frame tlocs resultLocs k))
            (σbf.withLocals L) (.next k) (σst.withLocals L) :=
          Step.frameReturn (hLd L) (hStoreR L)
        exact ((Steps.single hstep1).trans
          (hbsteps L tlocs resultLocs k)).tail hframe
  | returnStmt =>
    cases hf with
    | returnStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hinv, rfl, fun L k =>
        (Steps.single .returnStmt).trans (Steps.returning_strip k _)⟩
  | breakStmt =>
    cases hf with
    | breakStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hinv, rfl, fun L k =>
        (Steps.single .breakStmt).trans (Steps.breaking_strip k _)⟩
  | continueStmt =>
    cases hf with
    | continueStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hinv, rfl, fun L k =>
        (Steps.single .continueStmt).trans (Steps.continuing_strip k _)⟩
termination_by (fuel, sizeOf stmt)
decreasing_by all_goals (subst_vars; decreasing_tactic)

/-- **T2 — spine-list simulation**, generalized over a residual `tail` (D1):
a successful interpreter run of the spine `ss` maps to `Steps` processing the
`ss`-prefix of the combined list `.seq (ss ++ tail)` — landing at
`.seq tail` under the (possibly extended) final locals for normal
completion, or at the seq-stripped unwinding configuration otherwise.
`tail := []` plus one `seqDone` recovers the un-generalized form; the
generalization is what lets a spliced nested seqn (a `seqnSpine` head)
continue seamlessly into the enclosing rest. -/
theorem execStmtList_frag_sound {avoid : List String} {ss : List Stmt}
    (hf : ∀ s ∈ ss, SpineFrag avoid s)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hinv : StInv σ)
    {out : ExecOutcome} {ch' : Choices}
    (h : execStmtList fuel σ ch ss = .ok (out, ch')) :
    StInv out.state ∧
    match out with
    | .normal σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        (∀ id ∈ avoid, LocalEnv.lookup σf.locals id = LocalEnv.lookup σ.locals id) ∧
        ∀ L k tail, Steps (.next (.seq (ss ++ tail) σ.locals k)) (σ.withLocals L)
          (.next (.seq tail σf.locals k)) (σf.withLocals L)
    | .broke σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        (∀ id ∈ avoid, LocalEnv.lookup σf.locals id = LocalEnv.lookup σ.locals id) ∧
        ∀ L k tail, Steps (.next (.seq (ss ++ tail) σ.locals k)) (σ.withLocals L)
          (.breaking k.stripSeqs) (σf.withLocals L)
    | .continued σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        (∀ id ∈ avoid, LocalEnv.lookup σf.locals id = LocalEnv.lookup σ.locals id) ∧
        ∀ L k tail, Steps (.next (.seq (ss ++ tail) σ.locals k)) (σ.withLocals L)
          (.continuing k.stripSeqs) (σf.withLocals L)
    | .returned σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        (∀ id ∈ avoid, LocalEnv.lookup σf.locals id = LocalEnv.lookup σ.locals id) ∧
        ∀ L k tail, Steps (.next (.seq (ss ++ tail) σ.locals k)) (σ.withLocals L)
          (.returning k.stripSeqs) (σf.withLocals L) := by
  cases ss with
  | nil =>
    simp only [execStmtList, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hinv, rfl, fun _ => rfl, fun _ _ => rfl,
      fun L k tail => .refl _ _⟩
  | cons s rest =>
    simp only [execStmtList] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨o₁, ch₁⟩, hhead, h⟩ := h
    have hs : SpineFrag avoid s := hf s (by simp)
    cases hs with
    | @init _ p htp hpav =>
      simp only [execStmt, execDecl, bind_eq_ok, pure_eq_ok,
        Prod.mk.injEq] at hhead
      obtain ⟨σ₁, ⟨v, hv, hσ₁⟩, ho₁, rfl⟩ := hhead
      subst hσ₁
      subst ho₁
      have hfv := defaultValue_frag_val htp hv
      have hh₁ : HeapFrag (σ.declareLocal p.id (some p.typ) v) := by
        rw [declareLocal_eq_alloc]
        exact heapFrag_alloc hinv.heap hfv (fun t' ht' => by cases ht'; exact htp)
      have hinv₁ : StInv (σ.declareLocal p.id (some p.typ) v) :=
        hinv.transport hh₁ rfl rfl
      obtain ⟨hif, hrest⟩ := execStmtList_frag_sound
        (fun q hq => hf q (by simp [hq])) fuel _ ch hinv₁ h
      refine ⟨hif, ?_⟩
      have hpre : ∀ L k tail,
          Steps (.next (.seq ((Stmt.initialization p :: rest) ++ tail) σ.locals k))
            (σ.withLocals L)
            (.next (.seq (rest ++ tail)
              ((σ.declareLocal p.id (some p.typ) v).locals) k))
            ((σ.declareLocal p.id (some p.typ) v).withLocals L) := by
        intro L k tail
        refine (Steps.single Step.seqNext).tail
          (Step.initialization (v := v) (loc := (σ.alloc v (some p.typ)).1)
            ((defaultValue_state_indep (σ.withLocals L) σ htp).trans hv)
            (alloc_withLocals σ L v (some p.typ)))
      have hdpop : (σ.declareLocal p.id (some p.typ) v).locals.popScope
          = σ.locals.popScope := by
        rw [declareLocal_eq_alloc]
        exact declare_popScope ..
      have hdlk : ∀ id ∈ avoid,
          LocalEnv.lookup (σ.declareLocal p.id (some p.typ) v).locals id
            = LocalEnv.lookup σ.locals id := by
        intro id hid
        rw [declareLocal_eq_alloc]
        exact lookup_declare_ne (fun he => hpav (he ▸ hid))
      cases out with
      | normal σf =>
        obtain ⟨hpop, -, hlk, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_,
          fun id hid => (hlk id hid).trans (hdlk id hid),
          fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | broke σf =>
        obtain ⟨hpop, -, hlk, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_,
          fun id hid => (hlk id hid).trans (hdlk id hid),
          fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | continued σf =>
        obtain ⟨hpop, -, hlk, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_,
          fun id hid => (hlk id hid).trans (hdlk id hid),
          fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | returned σf =>
        obtain ⟨hpop, -, hlk, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_,
          fun id hid => (hlk id hid).trans (hdlk id hid),
          fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
    | @seqnSpine _ ss' hss' =>
      -- interpreter: scope-transparent nested list; relation: SPLICE (D1)
      simp only [execStmt, execStmts] at hhead
      have hsz1 : sizeOf ss'.toList < 1 + (1 + sizeOf ss') + sizeOf rest := by
        cases ss'; simp +arith
      obtain ⟨hinv₁, hout1⟩ := execStmtList_frag_sound
        (fun q hq => hss' q (by simpa using hq)) fuel σ ch hinv hhead
      have hsplice : ∀ L k tail,
          Steps (.next (.seq ((Stmt.seqn ss' :: rest) ++ tail) σ.locals k))
            (σ.withLocals L)
            (.next (.seq (ss'.toList ++ (rest ++ tail)) σ.locals k))
            (σ.withLocals L) := by
        intro L k tail
        refine (Steps.single Step.seqNext).tail ?_
        have := Step.seqn (ss := ss') (env := σ.locals)
          (k := .seq (rest ++ tail) σ.locals k) (s := σ.withLocals L)
        rwa [show seqCont ss'.toList σ.locals (.seq (rest ++ tail) σ.locals k)
            = .seq (ss'.toList ++ (rest ++ tail)) σ.locals k by
          simp [seqCont]] at this
      cases o₁ with
      | normal σ₁ =>
        obtain ⟨hpop1, hns1, hlk1, hsteps1⟩ := hout1
        obtain ⟨hif, hrest⟩ := execStmtList_frag_sound
          (fun q hq => hf q (by simp [hq])) fuel σ₁ ch₁ hinv₁ h
        refine ⟨hif, ?_⟩
        cases out with
        | normal σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          refine ⟨hpop.trans hpop1, ?_,
            fun id hid => (hlk id hid).trans (hlk1 id hid),
            fun L k tail => ?_⟩
          · intro hns'
            have hh := hns' (.seqn ss') (by simp)
            cases hh with
            | seqn hels =>
              exact (hnseq (fun q hq => hns' q (by simp [hq]))).trans
                (hns1 (fun q hq => hels q (by simpa using hq)))
          · exact ((hsplice L k tail).trans
              (hsteps1 L k (rest ++ tail))).trans (hsteps L k tail)
        | broke σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          refine ⟨hpop.trans hpop1, ?_,
            fun id hid => (hlk id hid).trans (hlk1 id hid),
            fun L k tail => ?_⟩
          · intro hns'
            have hh := hns' (.seqn ss') (by simp)
            cases hh with
            | seqn hels =>
              exact (hnseq (fun q hq => hns' q (by simp [hq]))).trans
                (hns1 (fun q hq => hels q (by simpa using hq)))
          · exact ((hsplice L k tail).trans
              (hsteps1 L k (rest ++ tail))).trans (hsteps L k tail)
        | continued σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          refine ⟨hpop.trans hpop1, ?_,
            fun id hid => (hlk id hid).trans (hlk1 id hid),
            fun L k tail => ?_⟩
          · intro hns'
            have hh := hns' (.seqn ss') (by simp)
            cases hh with
            | seqn hels =>
              exact (hnseq (fun q hq => hns' q (by simp [hq]))).trans
                (hns1 (fun q hq => hels q (by simpa using hq)))
          · exact ((hsplice L k tail).trans
              (hsteps1 L k (rest ++ tail))).trans (hsteps L k tail)
        | returned σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          refine ⟨hpop.trans hpop1, ?_,
            fun id hid => (hlk id hid).trans (hlk1 id hid),
            fun L k tail => ?_⟩
          · intro hns'
            have hh := hns' (.seqn ss') (by simp)
            cases hh with
            | seqn hels =>
              exact (hnseq (fun q hq => hns' q (by simp [hq]))).trans
                (hns1 (fun q hq => hels q (by simpa using hq)))
          · exact ((hsplice L k tail).trans
              (hsteps1 L k (rest ++ tail))).trans (hsteps L k tail)
      | broke σ₁ =>
        obtain ⟨hpop1, hns1, hlk1, hsteps1⟩ := hout1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hinv₁, hpop1, ?_, hlk1, fun L k tail =>
          (hsplice L k tail).trans (hsteps1 L k (rest ++ tail))⟩
        intro hns'
        have hh := hns' (.seqn ss') (by simp)
        cases hh with
        | seqn hels => exact hns1 (fun q hq => hels q (by simpa using hq))
      | continued σ₁ =>
        obtain ⟨hpop1, hns1, hlk1, hsteps1⟩ := hout1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hinv₁, hpop1, ?_, hlk1, fun L k tail =>
          (hsplice L k tail).trans (hsteps1 L k (rest ++ tail))⟩
        intro hns'
        have hh := hns' (.seqn ss') (by simp)
        cases hh with
        | seqn hels => exact hns1 (fun q hq => hels q (by simpa using hq))
      | returned σ₁ =>
        obtain ⟨hpop1, hns1, hlk1, hsteps1⟩ := hout1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hinv₁, hpop1, ?_, hlk1, fun L k tail =>
          (hsplice L k tail).trans (hsteps1 L k (rest ++ tail))⟩
        intro hns'
        have hh := hns' (.seqn ss') (by simp)
        cases hh with
        | seqn hels => exact hns1 (fun q hq => hels q (by simpa using hq))
    | ns hns =>
      obtain ⟨hhinv, hrest1⟩ := execStmt_frag_sound hns fuel σ ch hinv hhead
      cases o₁ with
      | normal σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        obtain ⟨hif, hrest⟩ := execStmtList_frag_sound
          (fun q hq => hf q (by simp [hq])) fuel σ₁ ch₁ hhinv h
        rw [hl₁] at hrest
        refine ⟨hif, ?_⟩
        have hpre : ∀ L k tail,
            Steps (.next (.seq ((s :: rest) ++ tail) σ.locals k)) (σ.withLocals L)
              (.next (.seq (rest ++ tail) σ.locals k)) (σ₁.withLocals L) :=
          fun L k tail =>
            (Steps.single Step.seqNext).trans
              (hsteps1 L (.seq (rest ++ tail) σ.locals k))
        cases out with
        | normal σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            hlk, fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        | broke σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            hlk, fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        | continued σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            hlk, fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
        | returned σf =>
          obtain ⟨hpop, hnseq, hlk, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            hlk, fun L k tail => (hpre L k tail).trans (hsteps L k tail)⟩
      | broke σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hhinv, by rw [hl₁], fun _ => hl₁, fun id _ => by rw [hl₁],
          fun L k tail => ?_⟩
        refine (Steps.single Step.seqNext).trans ?_
        have h0 := hsteps1 L (.seq (rest ++ tail) σ.locals k)
        exact h0
      | continued σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hhinv, by rw [hl₁], fun _ => hl₁, fun id _ => by rw [hl₁],
          fun L k tail => ?_⟩
        refine (Steps.single Step.seqNext).trans ?_
        exact hsteps1 L (.seq (rest ++ tail) σ.locals k)
      | returned σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hhinv, by rw [hl₁], fun _ => hl₁, fun id _ => by rw [hl₁],
          fun L k tail => ?_⟩
        refine (Steps.single Step.seqNext).trans ?_
        exact hsteps1 L (.seq (rest ++ tail) σ.locals k)
termination_by (fuel, sizeOf ss)
decreasing_by all_goals (subst_vars; decreasing_tactic)
end


set_option maxRecDepth 4096 in
mutual
/-- **T1p — statement panic simulation** (D3b). An interpreter panic on a
non-spine fragment statement maps to a `Steps` derivation reaching the
terminal `.panicked` configuration, from any continuation and transported
state; the fault state is existential (matching
`interpreterPanicStatement`'s shape). -/
theorem execStmt_frag_panic {stmt : Stmt} (hf : StmtFragNS stmt)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hinv : StInv σ)
    {msg : String}
    (h : execStmt fuel σ ch stmt = .error (.panic msg)) :
    ∃ σp : ExecState, ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
      (.panicked msg) (σp.withLocals L) := by
  cases stmt with
  | initialization p => exact nomatch hf
  | assignMany l r => exact nomatch hf
  | newValue t v ty => exact nomatch hf
  | makeSlice t e l c => exact nomatch hf
  | makeMap t k v i => exact nomatch hf
  | mapAssign b i v kt vt => exact nomatch hf
  | mapLookup t o b i kt vt => exact nomatch hf
  | typeAssert t o e tt => exact nomatch hf
  | appendSlice t e s es => exact nomatch hf
  | copySlice t d s => exact nomatch hf
  | mapRange kv vv me kt vt b => exact nomatch hf
  | label n => exact nomatch hf
  | unsupported f => exact nomatch hf
  | returnStmt => cases hf; simp [execStmt] at h
  | breakStmt => cases hf; simp [execStmt] at h
  | continueStmt => cases hf; simp [execStmt] at h
  | assign a e =>
    cases hf with
    | assign ha he =>
      simp only [execStmt] at h
      rw [bind_eq_error] at h
      rcases h with hpanic | ⟨⟨loc, σ₁⟩, hloc, hrest⟩
      · exact ⟨σ, fun L k => Steps.single
          (Step.assignTargetPanic
            (evalAssigneeLoc_frag_panic ha hinv.heap hpanic L))⟩
      · obtain ⟨heq, hA⟩ := evalAssigneeLoc_frag_ok ha hinv.heap hloc
        subst σ₁
        rw [bind_eq_error] at hrest
        rcases hrest with hpanic | ⟨⟨v, σ₂⟩, hv, hrest2⟩
        · exact ⟨σ, fun L k => Steps.single
            (Step.assignValuePanic (hA L)
              (evalExpr_frag_panic he hinv.heap hpanic L))⟩
        · obtain ⟨heq2, hfv, hRv⟩ := evalExpr_frag_ok he hinv.heap hv
          subst σ₂
          simp only [assignLoc, bind_eq_error] at hrest2
          rcases hrest2 with hpanic | ⟨σ₃, hst, hrest3⟩
          · exact absurd hpanic (storeLoc_frag_no_panic hinv.heap hfv)
          · simp at hrest3
  | seqn ss =>
    cases hf with
    | seqn hss =>
      simp only [execStmt, execStmts] at h
      have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
      obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic (avoid := [])
        (fun s hs => .ns (hss s (by simpa using hs))) fuel σ ch hinv h
      refine ⟨σp, fun L k => (Steps.single Step.seqn).trans ?_⟩
      match k with
      | .stop =>
        have h0 := hsteps L .stop []
        rw [List.append_nil] at h0
        exact h0
      | .loop c b env' k₂ =>
        have h0 := hsteps L (.loop c b env' k₂) []
        rw [List.append_nil] at h0
        exact h0
      | .frame t r k₂ =>
        have h0 := hsteps L (.frame t r k₂) []
        rw [List.append_nil] at h0
        exact h0
      | .seq rest env' k₂ =>
        by_cases henv : env' = σ.locals
        · subst henv
          rw [show seqCont ss.toList σ.locals (.seq rest σ.locals k₂)
              = .seq (ss.toList ++ rest) σ.locals k₂ by simp [seqCont]]
          exact hsteps L k₂ rest
        · rw [show seqCont ss.toList σ.locals (.seq rest env' k₂)
              = .seq ss.toList σ.locals (.seq rest env' k₂) by
                simp [seqCont, henv]]
          have h0 := hsteps L (.seq rest env' k₂) []
          rw [List.append_nil] at h0
          exact h0
  | block decls ss =>
    cases hf with
    | block hdeclsTy hss =>
      simp only [execStmt, execStmts, execDecls, bind_eq_error] at h
      rcases h with hdErr | ⟨σd, hdecl, hrest⟩
      · exact absurd hdErr (execDeclList_frag_no_panic
          (fun p hp => hdeclsTy p (by simpa using hp)))
      · obtain ⟨hhd, -, hdfns, hdmth, hdR⟩ :=
          execDeclList_frag_sound (fun p hp => hdeclsTy p (by simpa using hp))
            (show HeapFrag { σ with locals := σ.locals.pushScope }
              from hinv.heap) hdecl
        rcases hrest with hbodyErr | ⟨⟨oc, ch₁⟩, hbody, hrest2⟩
        · have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
          obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic (avoid := [])
            (fun s hs => hss s (by simpa using hs)) fuel σd ch
            (hinv.transport hhd hdfns hdmth) hbodyErr
          refine ⟨σp, fun L k => ?_⟩
          have h0 := hsteps L k []
          rw [List.append_nil] at h0
          exact (Steps.single (Step.block (hdR L))).trans h0
        · cases oc <;> simp at hrest2
  | ifThenElse c t e =>
    cases hf with
    | ifThenElse hc ht he =>
      simp only [execStmt] at h
      rw [bind_eq_error] at h
      rcases h with hpanic | ⟨⟨cv, σ₁⟩, hc', hrest⟩
      · exact ⟨σ, fun L k => Steps.single (Step.ifPanic
          (evalExpr_frag_panic hc hinv.heap hpanic L))⟩
      · obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hinv.heap hc'
        subst σ₁
        rw [bind_eq_error] at hrest
        rcases hrest with hbv | ⟨b, hbv, hrest2⟩
        · cases hfc <;> simp [valueAsBool] at hbv
        · cases hfc with
          | bool bv =>
            simp only [valueAsBool, pure_eq_ok] at hbv
            subst hbv
            cases bv with
            | true =>
              simp only [reduceIte] at hrest2
              obtain ⟨σp, hsteps⟩ :=
                execStmt_frag_panic ht fuel σ ch hinv hrest2
              exact ⟨σp, fun L k =>
                (Steps.single (Step.ifTrue (hRc L))).trans (hsteps L k)⟩
            | false =>
              simp only [Bool.false_eq_true, reduceIte] at hrest2
              obtain ⟨σp, hsteps⟩ :=
                execStmt_frag_panic he fuel σ ch hinv hrest2
              exact ⟨σp, fun L k =>
                (Steps.single (Step.ifFalse (hRc L))).trans (hsteps L k)⟩
          | int n k => simp [valueAsBool] at hbv
          | addr l => simp [valueAsBool] at hbv
          | nil => simp [valueAsBool] at hbv
  | «while» c b =>
    cases hf with
    | whileStmt hc hb =>
      cases fuel with
      | zero => simp [execStmt] at h
      | succ fuel' =>
        simp only [execStmt] at h
        rw [bind_eq_error] at h
        rcases h with hpanic | ⟨⟨cv, σ₁⟩, hc', hrest⟩
        · exact ⟨σ, fun L k => Steps.single (Step.whilePanic
            (evalExpr_frag_panic hc hinv.heap hpanic L))⟩
        · obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hinv.heap hc'
          subst σ₁
          rw [bind_eq_error] at hrest
          rcases hrest with hbv | ⟨bv', hbv, hrest2⟩
          · cases hfc <;> simp [valueAsBool] at hbv
          · cases hfc with
            | bool bv =>
              simp only [valueAsBool, pure_eq_ok] at hbv
              subst hbv
              cases bv with
              | false => simp at hrest2
              | true =>
                simp only [reduceIte] at hrest2
                rw [bind_eq_error] at hrest2
                rcases hrest2 with hbodyErr | ⟨⟨ob, ch₁⟩, hbody, hrest3⟩
                · obtain ⟨σp, hsteps⟩ :=
                    execStmt_frag_panic hb (fuel' + 1) σ ch hinv hbodyErr
                  exact ⟨σp, fun L k =>
                    (Steps.single (Step.whileTrue (hRc L))).trans
                      (hsteps L (.loop c b σ.locals k))⟩
                · obtain ⟨hbinv, hout1⟩ :=
                    execStmt_frag_sound hb (fuel' + 1) σ ch hinv hbody
                  cases ob with
                  | normal σb =>
                    obtain ⟨hlb, hbsteps⟩ := hout1
                    obtain ⟨σp, hsteps⟩ := execStmt_frag_panic
                      (.whileStmt hc hb) fuel' σb ch₁ hbinv hrest3
                    rw [hlb] at hsteps
                    exact ⟨σp, fun L k =>
                      (((Steps.single (Step.whileTrue (hRc L))).trans
                        (hbsteps L (.loop c b σ.locals k))).tail
                        Step.loopNext).trans (hsteps L k)⟩
                  | continued σb =>
                    obtain ⟨hlb, hbsteps⟩ := hout1
                    obtain ⟨σp, hsteps⟩ := execStmt_frag_panic
                      (.whileStmt hc hb) fuel' σb ch₁ hbinv hrest3
                    rw [hlb] at hsteps
                    exact ⟨σp, fun L k =>
                      (((Steps.single (Step.whileTrue (hRc L))).trans
                        (hbsteps L (.loop c b σ.locals k))).tail
                        Step.loopContinue).trans (hsteps L k)⟩
                  | broke σb => simp at hrest3
                  | returned σb => simp at hrest3
            | int n k => simp [valueAsBool] at hbv
            | addr l => simp [valueAsBool] at hbv
            | nil => simp [valueAsBool] at hbv
  | call targets funcId args =>
    cases hf with
    | call htargets hargs =>
      simp only [execStmt] at h
      rw [bind_eq_error] at h
      rcases h with hcall | ⟨⟨σfin, chfin⟩, hcallOk, hrest⟩
      case inr => simp at hrest
      case inl =>
      simp only [execFunctionCall] at hcall
      rw [bind_eq_error] at hcall
      rcases hcall with htErr | ⟨⟨tlocsA, σt⟩, htOk, hwl⟩
      · simp only [evalAssigneeLocs] at htErr
        rw [bind_eq_error] at htErr
        rcases htErr with hlistErr | ⟨⟨tlocs, σt₀⟩, hlist, hp⟩
        · exact ⟨σ, fun L k => Steps.single (Step.callTargetsPanic
            (evalAssigneeLocList_frag_panic
              (fun a ha => htargets a (by simpa using ha)) hinv.heap
              hlistErr L))⟩
        · simp at hp
      · simp only [evalAssigneeLocs, bind_eq_ok, pure_eq_ok] at htOk
        obtain ⟨⟨tlocs, σt₀⟩, hlist, hp⟩ := htOk
        obtain ⟨heqt, hAss⟩ := evalAssigneeLocList_frag_sound
          (fun a ha => htargets a (by simpa using ha)) hinv.heap hlist
        subst σt₀
        simp only [Prod.mk.injEq] at hp
        obtain ⟨h1, h2⟩ := hp
        subst tlocsA
        subst σt
        simp only [execFunctionCallWithLocs] at hwl
        cases hfind : findFunctionIn? σ.functions funcId with
        | none =>
          rw [hfind] at hwl
          simp [bind_eq_error] at hwl
        | some func =>
        rw [hfind] at hwl
        have hff : FuncFrag func := hinv.funcs func (findFunctionIn?_mem hfind)
        rw [bind_eq_error] at hwl
        rcases hwl with hwl | ⟨y, hy, hwl⟩
        · simp at hwl
        · simp only [pure_eq_ok] at hy
          subst hy
          cases hna : (func.args.size != args.size) with
          | true => rw [hna] at hwl; simp [bind_eq_error] at hwl
          | false =>
          rw [hna] at hwl
          simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
          rw [bind_eq_error] at hwl
          rcases hwl with hargsErr | ⟨⟨argValues, σa⟩, hargsEv, hwl⟩
          · exact ⟨σ, fun L k => Steps.single (Step.callArgsPanic (hAss L)
              (evalExprSeq_frag_panic
                (fun e he => hargs e (by simpa using he)) hinv.heap
                hargsErr L))⟩
          · obtain ⟨heqa, hfvals, hArgs⟩ := evalExprSeq_frag_sound
              (fun e he => hargs e (by simpa using he)) hinv.heap hargsEv
            subst σa
            rw [show dynamicDispatch?
                  ((argValues, σ) : Array GoValue × ExecState).snd func
                  ((argValues, σ) : Array GoValue × ExecState).fst
                = .ok none from
              dynamicDispatch?_none hinv.methods func argValues] at hwl
            rw [bind_eq_error] at hwl
            rcases hwl with hwl | ⟨d, hd, hwl⟩
            · simp at hwl
            · simp only [Except.ok.injEq] at hd
              subst hd
              cases fuel with
              | zero => simp [execFunctionWithValues] at hwl
              | succ fuel' =>
              simp only [execFunctionWithValues] at hwl
              cases hna2 : (func.args.size != argValues.size) with
              | true => rw [hna2] at hwl; simp [bind_eq_error] at hwl
              | false =>
              rw [hna2] at hwl
              simp only [Bool.false_eq_true, reduceIte, pure_bind] at hwl
              rw [bind_eq_error] at hwl
              rcases hwl with hbindErr | ⟨boundState, hbindP, hwl⟩
              · exact absurd hbindErr (bindParamList_frag_no_panic
                  (fun p hp => hff.argsTy p (by simpa using hp)))
              · obtain ⟨hhb, hbfns, hbmth, hBind⟩ := bindParamList_frag_sound
                  (fun p hp => hff.argsTy p (by simpa using hp))
                  (by simpa using hna2)
                  (fun v hv => hfvals v (by simpa using hv))
                  (show HeapFrag { σ with locals := [] } from hinv.heap) hbindP
                rw [bind_eq_error] at hwl
                rcases hwl with hdErr | ⟨callState, hdeclsR, hwl⟩
                · exact absurd hdErr (execDeclList_frag_no_panic
                    (fun r hr => hff.resultsTy r (by simpa using hr)))
                · obtain ⟨hhc, hcpop, hcfns, hcmth, hDecls⟩ :=
                    execDeclList_frag_sound
                      (fun r hr => hff.resultsTy r (by simpa using hr))
                      hhb hdeclsR
                  have hcinv : StInv callState :=
                    ⟨hhc, (hcmth.trans hbmth).trans hinv.methods,
                      (hcfns.trans hbfns) ▸ hinv.funcs⟩
                  -- result locations exist (needed for Step.call): the frame
                  -- just declared them
                  rw [bind_eq_error] at hwl
                  rcases hwl with hbodyErr | ⟨⟨outcome, ch₁⟩, hbody, hwl⟩
                  · -- the callee body panics: terminal — the panic IS the
                    -- program's panic; result locations for Step.call come
                    -- from the freshly-declared frame
                    obtain ⟨rl, hLk⟩ := lookupsR_exists
                      (declsR_lookup_exists (hDecls []))
                    have hstep1 : ∀ L k, Step
                        (.exec (.call targets funcId args) σ.locals k)
                        (σ.withLocals L)
                        (.exec func.body callState.locals
                          (.frame tlocs rl k)) (callState.withLocals L) :=
                      fun L k => Step.call (hAss L) (hArgs L) hfind
                        (hBind L) (hDecls L) hLk
                    rcases hff.body with ⟨bss, hbodyEq, hspine⟩ | hbodyNS
                    · rw [hbodyEq] at hbodyErr
                      simp only [execStmt, execStmts] at hbodyErr
                      have hsz : sizeOf bss.toList < sizeOf bss := by
                        cases bss; simp +arith
                      obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic
                        (avoid := func.results.toList.map (·.id))
                        (fun s hs => hspine s (by simpa using hs))
                        fuel' callState ch hcinv hbodyErr
                      refine ⟨σp, fun L k => ?_⟩
                      have h0 := hsteps L (.frame tlocs rl k) []
                      rw [List.append_nil] at h0
                      refine (Steps.single (hstep1 L k)).trans ?_
                      rw [hbodyEq]
                      exact (Steps.single (Step.seqn (ss := bss)
                        (env := callState.locals)
                        (k := .frame tlocs rl k)
                        (s := callState.withLocals L))).trans h0
                    · obtain ⟨σp, hsteps⟩ := execStmt_frag_panic hbodyNS
                        fuel' callState ch hcinv hbodyErr
                      exact ⟨σp, fun L k =>
                        (Steps.single (hstep1 L k)).trans
                          (hsteps L (.frame tlocs rl k))⟩
                  · -- the body completed; the remaining pipeline cannot panic
                    exfalso
                    -- finalState match
                    cases outcome with
                    | broke σbf => simp [bind_eq_error] at hwl
                    | continued σbf => simp [bind_eq_error] at hwl
                    | normal σbf =>
                      have hoinv : StInv σbf := by
                        rcases hff.body with ⟨bss, hbodyEq, hspine⟩ | hbodyNS
                        · rw [hbodyEq] at hbody
                          simp only [execStmt, execStmts] at hbody
                          have hsz : sizeOf bss.toList < sizeOf bss := by
                            cases bss; simp +arith
                          exact (execStmtList_frag_sound
                            (avoid := func.results.toList.map (·.id))
                            (fun s hs => hspine s (by simpa using hs))
                            fuel' callState ch hcinv hbody).1
                        · exact (execStmt_frag_sound hbodyNS fuel' callState
                            ch hcinv hbody).1
                      rw [bind_eq_error] at hwl
                      rcases hwl with hreadErr | ⟨resultValues, hread, hwl⟩
                      · exact readResultList_no_panic hoinv.heap hreadErr
                      · obtain ⟨hfres, -⟩ := readResultList_locs_sound
                          (show HeapFrag σbf from hoinv.heap) hread
                        simp only [assignLocs] at hwl
                        cases hna3 : (tlocs.toArray.size
                            != resultValues.toArray.size) with
                        | true => rw [hna3] at hwl; simp [bind_eq_error] at hwl
                        | false =>
                        rw [hna3] at hwl
                        simp only [Bool.false_eq_true, reduceIte,
                          pure_bind] at hwl
                        rw [bind_eq_error] at hwl
                        rcases hwl with hstErr | ⟨σst, hst, hwl⟩
                        · exact assignLocList_frag_no_panic hfres
                            (show HeapFrag { σbf with locals := σ.locals }
                              from hoinv.heap)
                            (by simpa using hstErr)
                        · simp at hwl
                    | returned σbf =>
                      have hoinv : StInv σbf := by
                        rcases hff.body with ⟨bss, hbodyEq, hspine⟩ | hbodyNS
                        · rw [hbodyEq] at hbody
                          simp only [execStmt, execStmts] at hbody
                          have hsz : sizeOf bss.toList < sizeOf bss := by
                            cases bss; simp +arith
                          exact (execStmtList_frag_sound
                            (avoid := func.results.toList.map (·.id))
                            (fun s hs => hspine s (by simpa using hs))
                            fuel' callState ch hcinv hbody).1
                        · exact (execStmt_frag_sound hbodyNS fuel' callState
                            ch hcinv hbody).1
                      rw [bind_eq_error] at hwl
                      rcases hwl with hreadErr | ⟨resultValues, hread, hwl⟩
                      · exact readResultList_no_panic hoinv.heap hreadErr
                      · obtain ⟨hfres, -⟩ := readResultList_locs_sound
                          (show HeapFrag σbf from hoinv.heap) hread
                        simp only [assignLocs] at hwl
                        cases hna3 : (tlocs.toArray.size
                            != resultValues.toArray.size) with
                        | true => rw [hna3] at hwl; simp [bind_eq_error] at hwl
                        | false =>
                        rw [hna3] at hwl
                        simp only [Bool.false_eq_true, reduceIte,
                          pure_bind] at hwl
                        rw [bind_eq_error] at hwl
                        rcases hwl with hstErr | ⟨σst, hst, hwl⟩
                        · exact assignLocList_frag_no_panic hfres
                            (show HeapFrag { σbf with locals := σ.locals }
                              from hoinv.heap)
                            (by simpa using hstErr)
                        · simp at hwl
termination_by (fuel, sizeOf stmt)
decreasing_by all_goals (subst_vars; decreasing_tactic)

/-- **T2p — spine-list panic simulation** (D3b). -/
theorem execStmtList_frag_panic {avoid : List String} {ss : List Stmt}
    (hf : ∀ s ∈ ss, SpineFrag avoid s)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hinv : StInv σ)
    {msg : String}
    (h : execStmtList fuel σ ch ss = .error (.panic msg)) :
    ∃ σp : ExecState, ∀ L k tail, Steps (.next (.seq (ss ++ tail) σ.locals k))
      (σ.withLocals L) (.panicked msg) (σp.withLocals L) := by
  cases ss with
  | nil => simp [execStmtList] at h
  | cons s rest =>
    simp only [execStmtList] at h
    rw [bind_eq_error] at h
    have hs : SpineFrag avoid s := hf s (by simp)
    rcases h with h | ⟨⟨o₁, ch₁⟩, hhead, h⟩
    · -- the head itself panics
      cases hs with
      | @init _ p htp hpav =>
        exfalso
        obtain ⟨v, hv, -⟩ := defaultValue_frag_total (σ := σ) htp
        simp only [execStmt, execDecl, bind_eq_error, bind_eq_ok,
          pure_eq_ok, hv] at h
        rcases h with h | ⟨σm, hm, h⟩
        · simp at h
        · simp at h
      | @seqnSpine _ ss' hss' =>
        simp only [execStmt, execStmts] at h
        have hsz1 : sizeOf ss'.toList < 1 + (1 + sizeOf ss') + sizeOf rest := by
          cases ss'; simp +arith
        obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic
          (fun q hq => hss' q (by simpa using hq)) fuel σ ch hinv h
        refine ⟨σp, fun L k tail => ?_⟩
        refine ((Steps.single Step.seqNext).tail ?_).trans
          (hsteps L k (rest ++ tail))
        have := Step.seqn (ss := ss') (env := σ.locals)
          (k := .seq (rest ++ tail) σ.locals k) (s := σ.withLocals L)
        rwa [show seqCont ss'.toList σ.locals (.seq (rest ++ tail) σ.locals k)
            = .seq (ss'.toList ++ (rest ++ tail)) σ.locals k by
          simp [seqCont]] at this
      | ns hns =>
        obtain ⟨σp, hsteps⟩ := execStmt_frag_panic hns fuel σ ch hinv h
        exact ⟨σp, fun L k tail => (Steps.single Step.seqNext).trans
          (hsteps L (.seq (rest ++ tail) σ.locals k))⟩
    · -- the head completes; only a normal outcome continues
      cases o₁ with
      | normal σ₁ =>
        cases hs with
        | @init _ p htp hpav =>
          simp only [execStmt, execDecl, bind_eq_ok, pure_eq_ok,
            Prod.mk.injEq] at hhead
          obtain ⟨σ₁', ⟨v, hv, hσ₁⟩, ho₁, rfl⟩ := hhead
          subst σ₁'
          injection ho₁ with ho₁'
          subst σ₁
          have hfv := defaultValue_frag_val htp hv
          have hh₁ : HeapFrag (σ.declareLocal p.id (some p.typ) v) := by
            rw [declareLocal_eq_alloc]
            exact heapFrag_alloc hinv.heap hfv
              (fun t' ht' => by cases ht'; exact htp)
          obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic
            (fun q hq => hf q (by simp [hq])) fuel _ ch
            (hinv.transport hh₁ rfl rfl) h
          refine ⟨σp, fun L k tail => ?_⟩
          refine ((Steps.single Step.seqNext).tail
            (Step.initialization (v := v) (loc := (σ.alloc v (some p.typ)).1)
              ((defaultValue_state_indep (σ.withLocals L) σ htp).trans hv)
              (alloc_withLocals σ L v (some p.typ)))).trans
            (hsteps L k tail)
        | @seqnSpine _ ss' hss' =>
          simp only [execStmt, execStmts] at hhead
          have hsz1 : sizeOf ss'.toList < 1 + (1 + sizeOf ss') + sizeOf rest := by
            cases ss'; simp +arith
          obtain ⟨hinv₁, hout1⟩ := execStmtList_frag_sound
            (fun q hq => hss' q (by simpa using hq)) fuel σ ch hinv hhead
          obtain ⟨-, -, -, hsteps1⟩ := hout1
          obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic
            (fun q hq => hf q (by simp [hq])) fuel σ₁ ch₁ hinv₁ h
          refine ⟨σp, fun L k tail => ?_⟩
          have hsplice : Steps
              (.next (.seq ((Stmt.seqn ss' :: rest) ++ tail) σ.locals k))
              (σ.withLocals L)
              (.next (.seq (ss'.toList ++ (rest ++ tail)) σ.locals k))
              (σ.withLocals L) := by
            refine (Steps.single Step.seqNext).tail ?_
            have := Step.seqn (ss := ss') (env := σ.locals)
              (k := .seq (rest ++ tail) σ.locals k) (s := σ.withLocals L)
            rwa [show seqCont ss'.toList σ.locals
                (.seq (rest ++ tail) σ.locals k)
                = .seq (ss'.toList ++ (rest ++ tail)) σ.locals k by
              simp [seqCont]] at this
          exact (hsplice.trans (hsteps1 L k (rest ++ tail))).trans
            (hsteps L k tail)
        | ns hns =>
          obtain ⟨hhinv, hout1⟩ := execStmt_frag_sound hns fuel σ ch hinv hhead
          obtain ⟨hl₁, hsteps1⟩ := hout1
          obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic
            (fun q hq => hf q (by simp [hq])) fuel σ₁ ch₁ hhinv h
          rw [hl₁] at hsteps
          refine ⟨σp, fun L k tail => ?_⟩
          exact ((Steps.single Step.seqNext).trans
            (hsteps1 L (.seq (rest ++ tail) σ.locals k))).trans
            (hsteps L k tail)
      | broke σ₁ => simp at h
      | continued σ₁ => simp at h
      | returned σ₁ => simp at h
termination_by (fuel, sizeOf ss)
decreasing_by all_goals (subst_vars; decreasing_tactic)
end

/-- **The fragment interpreter-panic theorem** — `interpreterPanicStatement`
restricted to the scalar+pointer fragment, in exactly its shape: an
interpreter panic on a fragment statement reaches the relation's terminal
`.panicked` configuration with the same message, at some fault state. -/
theorem interpreterPanic_frag (fuel : Nat) (σ : ExecState) (stmt : Stmt)
    (ch : Choices) (msg : String) (hf : StmtFragNS stmt) (hinv : StInv σ)
    (h : execStmt fuel σ ch stmt = .error (.panic msg)) :
    ∃ σp, Steps (.exec stmt σ.locals .stop) σ (.panicked msg) σp := by
  obtain ⟨σp, hsteps⟩ := execStmt_frag_panic hf fuel σ ch hinv h
  exact ⟨σp.withLocals σ.locals, hsteps σ.locals .stop⟩

/-- Spine-level panic entry (top-level declarations allowed). -/
theorem interpreterPanic_spineSeq (fuel : Nat) (σ : ExecState)
    (ss : Array Stmt) (ch : Choices) (msg : String)
    (hf : ∀ s ∈ ss.toList, SpineFrag [] s) (hinv : StInv σ)
    (h : execStmt fuel σ ch (.seqn ss) = .error (.panic msg)) :
    ∃ σp, Steps (.exec (.seqn ss) σ.locals .stop) σ (.panicked msg) σp := by
  simp only [execStmt, execStmts] at h
  obtain ⟨σp, hsteps⟩ := execStmtList_frag_panic hf fuel σ ch hinv h
  have h0 := hsteps σ.locals .stop []
  rw [List.append_nil] at h0
  exact ⟨σp.withLocals σ.locals,
    (Steps.single (Step.seqn (ss := ss) (env := σ.locals) (k := .stop)
      (s := σ.withLocals σ.locals))).trans h0⟩

/-- **The fragment interpreter-soundness theorem** — `interpreterSoundStatement`
restricted to the scalar+pointer fragment, in exactly its shape: a normal
interpreter completion of a fragment statement over a fragment heap is a
reachable terminal of the step relation, from the same state to the same
state. (For non-spine fragment statements the interpreter leaves `locals`
unchanged, so no `withLocals` appears in the statement.) -/
theorem interpreterSound_frag (fuel : Nat) (σ σ' : ExecState) (stmt : Stmt)
    (ch ch' : Choices) (hf : StmtFragNS stmt) (hinv : StInv σ)
    (h : execStmt fuel σ ch stmt = .ok (.normal σ', ch')) :
    Steps (.exec stmt σ.locals .stop) σ (.next .stop) σ' := by
  obtain ⟨_, hl, hsteps⟩ := execStmt_frag_sound hf fuel σ ch hinv h
  have hstep := hsteps σ.locals .stop
  have hσ : σ.withLocals σ.locals = σ := rfl
  have hσ' : σ'.withLocals σ.locals = σ' := by
    rw [← hl]; rfl
  rw [hσ, hσ'] at hstep
  exact hstep

/-- Spine-level entry: a `.seqn` program whose elements are spine fragments
(top-level declarations allowed — e.g. `r := 0; r = main()`). The relation's
final state agrees with the interpreter's up to the interpreter-bookkeeping
`locals` field (top-level declarations persist there). -/
theorem interpreterSound_spineSeq (fuel : Nat) (σ σ' : ExecState)
    (ss : Array Stmt) (ch ch' : Choices)
    (hf : ∀ s ∈ ss.toList, SpineFrag [] s) (hinv : StInv σ)
    (h : execStmt fuel σ ch (.seqn ss) = .ok (.normal σ', ch')) :
    Steps (.exec (.seqn ss) σ.locals .stop) σ (.next .stop)
      (σ'.withLocals σ.locals) := by
  simp only [execStmt, execStmts] at h
  obtain ⟨-, -, -, -, hsteps⟩ := execStmtList_frag_sound hf fuel σ ch hinv h
  have h0 := hsteps σ.locals .stop []
  rw [List.append_nil] at h0
  exact ((Steps.single (Step.seqn (ss := ss) (env := σ.locals) (k := .stop)
    (s := σ.withLocals σ.locals))).trans h0).tail Step.seqDone

/-! ## Proven instances

Concrete derivations over rules with no opaque function premises, checking
that the control-flow rules compose the way the interpreter behaves. -/

/-- An empty sequence completes normally in two steps. Any starting control
environment works — the empty sequence reads no variables. -/
theorem seqnNilSteps (s : ExecState) (env : LocalEnv) :
    Steps (.exec (.seqn #[]) env .stop) s (.next .stop) s :=
  ((Steps.single (Step.seqn (ss := #[]) (env := env) (k := .stop)
    (s := s))).tail .seqDone)

/-- `while false { body }` skips its body: condition literals evaluate by
rule, the loop exits normally. -/
theorem whileFalseSteps (s : ExecState) (body : Stmt) (env : LocalEnv) :
    Steps (.exec (.while (.boolLit false) body) env .stop) s (.next .stop) s :=
  Steps.single (.whileFalse .boolLit)

/-- `if true { return } else {}` reaches the returning configuration and
unwinds through sequence context (env-free after D2-proper). -/
theorem ifTrueReturnSteps (s : ExecState) (env : LocalEnv) :
    Steps
      (.exec (.seqn #[.ifThenElse (.boolLit true) .returnStmt (.seqn #[])]) env .stop) s
      (.returning .stop) s :=
  (((((Steps.single (Step.seqn
      (ss := #[.ifThenElse (.boolLit true) .returnStmt (.seqn #[])])
      (env := env) (k := .stop) (s := s))).tail
      .seqNext).tail
      (.ifTrue .boolLit)).tail
      .returnStmt).tail
      .seqReturn)

/-- `break` inside `while true` exits the loop normally: the breaking
configuration is absorbed by the loop context. -/
theorem whileTrueBreakSteps (s : ExecState) (env : LocalEnv) :
    Steps (.exec (.while (.boolLit true) .breakStmt) env .stop) s (.next .stop) s :=
  (((Steps.single (.whileTrue .boolLit)).tail
      .breakStmt).tail
      .loopBreak)

/-- Divide-by-zero is panic behavior, not stuckness: `x = 1 / 0` steps to
`panicked` with Go's message whenever the target local resolves. The target
`x` resolves against the control environment (CEK), not the state. -/
theorem divByZeroPanics (s : ExecState) (env : LocalEnv) (loc : Loc)
    (h : LocalEnv.lookup env "x" = some loc) :
    Steps
      (.exec (.assign (.var "x") (.div (.intLit 1) (.intLit 0))) env .stop) s
      (.panicked "runtime error: integer divide by zero") s :=
  Steps.single (.assignValuePanic (.var h) (.divByZero .intLit .intLit))

end GoLean.GoCore.Correspondence
