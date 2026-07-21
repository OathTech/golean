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
target; the theorems below prove fragment-scoped versions. The state bridge
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
    simp only [hc, bind_eq_ok, pure_eq_ok, exists_eq_left, exists_eq_left'] at h
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
      simp only [bind_eq_ok, pure_eq_ok, Prod.mk.injEq, stuck_def, reduceCtorEq,
        false_and, and_false, exists_const] at h
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
  refine ⟨σf, rfl, rfl, hhf, hlocals, fun L k => ?_⟩
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
        ∀ L, DeclsR σ.locals (σ.withLocals L) decls σd.locals (σd.withLocals L) := by
  induction decls with
  | nil =>
    intro σ hh σd h
    simp only [execDeclList, pure_eq_ok] at h
    subst h
    exact ⟨hh, rfl, fun L => .nil⟩
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
    obtain ⟨hhd, hpop, hR⟩ := ih (fun q hq => hd q (by simp [hq])) hh₁ h
    refine ⟨hhd, ?_, fun L => ?_⟩
    · rw [hpop, declareLocal_eq_alloc]
      exact declare_popScope ..
    · refine DeclsR.cons (v := v) (loc := (σ.alloc v (some p.typ)).1)
        (s₁ := (σ.alloc v (some p.typ)).2.withLocals L)
        ((defaultValue_state_indep (σ.withLocals L) σ htp).trans hv)
        (alloc_withLocals σ L v (some p.typ)) ?_
      exact hR L

mutual
/-- Non-spine fragment statements — usable in any position. Crucially
excludes `.initialization`: only the *governing* seq tracks a declaration's
env extension in the relation (D1), so declarations are fragment-legal only
as spine elements. Calls are the next layer (D2 conditions). -/
inductive StmtFragNS : Stmt → Prop where
  | assign {a : Assignee} {e : Expr} :
      AssigneeFrag a → ExprFrag e → StmtFragNS (.assign a e)
  | seqn {ss : Array Stmt} :
      (∀ s, s ∈ ss → StmtFragNS s) → StmtFragNS (.seqn ss)
  | block {decls : Array Param} {ss : Array Stmt} :
      (∀ p, p ∈ decls → TyFrag p.typ) → (∀ s, s ∈ ss → SpineFrag s) →
      StmtFragNS (.block decls ss)
  | ifThenElse {c : Expr} {t e : Stmt} :
      ExprFrag c → StmtFragNS t → StmtFragNS e → StmtFragNS (.ifThenElse c t e)
  | whileStmt {c : Expr} {b : Stmt} :
      ExprFrag c → StmtFragNS b → StmtFragNS (.while c b)
  | returnStmt : StmtFragNS .returnStmt
  | breakStmt : StmtFragNS .breakStmt
  | continueStmt : StmtFragNS .continueStmt

/-- Spine (declaration-tracking) positions: elements of a function/block
body statement list. -/
inductive SpineFrag : Stmt → Prop where
  | ns {s : Stmt} : StmtFragNS s → SpineFrag s
  | init {p : Param} : TyFrag p.typ → SpineFrag (.initialization p)
end

mutual
/-- **T1 — statement simulation.** A successful interpreter execution of a
non-spine fragment statement maps to a `Steps` segment of the CEK relation,
from `.exec stmt σ.locals k` to the outcome's configuration over any
continuation `k` and transported state, preserving the fragment heap.
Normal/broke/continued completions leave `locals` untouched; a `return`
reaches `.returning` with the return-point environment. -/
theorem execStmt_frag_sound {stmt : Stmt} (hf : StmtFragNS stmt)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hh : HeapFrag σ)
    {out : ExecOutcome} {ch' : Choices}
    (h : execStmt fuel σ ch stmt = .ok (out, ch')) :
    HeapFrag out.state ∧
    match out with
    | .normal σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.next k) (σf.withLocals L)
    | .broke σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.breaking k) (σf.withLocals L)
    | .continued σf => σf.locals = σ.locals ∧
        ∀ L k, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.continuing k) (σf.withLocals L)
    | .returned σf =>
        ∀ L k, ∃ Eret, Steps (.exec stmt σ.locals k) (σ.withLocals L)
          (.returning Eret k) (σf.withLocals L) := by
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
  | call t f a => exact nomatch hf
  | mapRange kv vv me kt vt b => exact nomatch hf
  | label n => exact nomatch hf
  | unsupported f => exact nomatch hf
  | assign a e =>
    cases hf with
    | assign ha he =>
      obtain ⟨σf, rfl, rfl, hhf, hloc, hstep⟩ := execStmt_assign_ok ha he hh h
      exact ⟨hhf, hloc, fun L k => Steps.single (hstep L k)⟩
  | seqn ss =>
    cases hf with
    | seqn hss =>
      simp only [execStmt, execStmts] at h
      have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
      obtain ⟨hhf, hrest⟩ :=
        execStmtList_frag_sound (fun s hs => .ns (hss s (by simpa using hs))) fuel σ ch hh h
      refine ⟨hhf, ?_⟩
      cases out with
      | normal σf =>
        obtain ⟨hpop, hns, hsteps⟩ := hrest
        exact ⟨hns (fun s hs => hss s (by simpa using hs)), fun L k =>
          (Steps.single .seqn).trans (hsteps L k)⟩
      | broke σf =>
        obtain ⟨hpop, hns, hsteps⟩ := hrest
        exact ⟨hns (fun s hs => hss s (by simpa using hs)), fun L k => (Steps.single .seqn).trans (hsteps L k)⟩
      | continued σf =>
        obtain ⟨hpop, hns, hsteps⟩ := hrest
        exact ⟨hns (fun s hs => hss s (by simpa using hs)), fun L k => (Steps.single .seqn).trans (hsteps L k)⟩
      | returned σf =>
        intro L k
        obtain ⟨Eret, hsteps⟩ := hrest L k
        exact ⟨Eret, (Steps.single .seqn).trans hsteps⟩
  | block decls ss =>
    cases hf with
    | block hdecls hss =>
      simp only [execStmt, execStmts, execDecls, bind_eq_ok] at h
      obtain ⟨σd, hdecl, h⟩ := h
      obtain ⟨⟨oc, ch₁⟩, hbody, h⟩ := h
      simp only [pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨hout, rfl⟩ := h
      have hhent : HeapFrag { σ with locals := σ.locals.pushScope } := hh
      obtain ⟨hhd, hdpop, hdR⟩ :=
        execDeclList_frag_sound (fun p hp => hdecls p (by simpa using hp)) hhent hdecl
      have hsz : sizeOf ss.toList < sizeOf ss := by cases ss; simp +arith
      obtain ⟨hhb, hrest⟩ := execStmtList_frag_sound
        (fun s hs => hss s (by simpa using hs)) fuel σd ch hhd hbody
      subst hout
      cases oc with
      | normal σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hhb, ?_, fun L k => ?_⟩
        · show σf.locals.popScope = σ.locals
          rw [hpop]; exact hdpop
        · exact (Steps.single (Step.block (hdR L))).trans (hsteps L k)
      | broke σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hhb, ?_, fun L k => ?_⟩
        · show σf.locals.popScope = σ.locals
          rw [hpop]; exact hdpop
        · exact (Steps.single (Step.block (hdR L))).trans (hsteps L k)
      | continued σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hhb, ?_, fun L k => ?_⟩
        · show σf.locals.popScope = σ.locals
          rw [hpop]; exact hdpop
        · exact (Steps.single (Step.block (hdR L))).trans (hsteps L k)
      | returned σf =>
        refine ⟨hhb, fun L k => ?_⟩
        obtain ⟨Eret, hsteps⟩ := hrest L k
        exact ⟨Eret, (Steps.single (Step.block (hdR L))).trans hsteps⟩
  | ifThenElse c t e =>
    cases hf with
    | ifThenElse hc ht he =>
      simp only [execStmt] at h
      rw [bind_eq_ok] at h
      obtain ⟨⟨cv, σ₁⟩, hc', h⟩ := h
      obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hh hc'
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
          obtain ⟨hhf, hrest⟩ := execStmt_frag_sound ht fuel σ ch hh h
          refine ⟨hhf, ?_⟩
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
            intro L k
            obtain ⟨Eret, hsteps⟩ := hrest L k
            exact ⟨Eret, (Steps.single (Step.ifTrue (hRc L))).trans hsteps⟩
        | false =>
          simp only [Bool.false_eq_true, reduceIte] at h
          obtain ⟨hhf, hrest⟩ := execStmt_frag_sound he fuel σ ch hh h
          refine ⟨hhf, ?_⟩
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
            intro L k
            obtain ⟨Eret, hsteps⟩ := hrest L k
            exact ⟨Eret, (Steps.single (Step.ifFalse (hRc L))).trans hsteps⟩
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
        obtain ⟨heq, hfc, hRc⟩ := evalExpr_frag_ok hc hh hc'
        rw [heq] at h
        rw [bind_eq_ok] at h
        obtain ⟨b, hbv, h⟩ := h
        cases hfc with
        | bool bv =>
          simp only [valueAsBool, pure_eq_ok] at hbv
          subst hbv
          cases bv with
          | false =>
            simp only [Bool.false_eq_true, reduceIte, pure_eq_ok,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hh, rfl, fun L k => Steps.single (.whileFalse (hRc L))⟩
          | true =>
            simp only [reduceIte] at h
            rw [bind_eq_ok] at h
            obtain ⟨⟨ob, ch₁⟩, hbody, h⟩ := h
            obtain ⟨hhb, hrest1⟩ := execStmt_frag_sound hb (fuel' + 1) σ ch hh hbody
            cases ob with
            | normal σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              obtain ⟨hhf, hrest⟩ :=
                execStmt_frag_sound (.whileStmt hc hb) fuel' σb ch₁ hhb h
              rw [hlb] at hrest
              refine ⟨hhf, ?_⟩
              cases out with
              | normal σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | broke σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | continued σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans (hsteps L k))
              | returned σf =>
                intro L k
                obtain ⟨Eret, hsteps⟩ := hrest L k
                exact ⟨Eret, (((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopNext).trans hsteps⟩
            | continued σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              obtain ⟨hhf, hrest⟩ :=
                execStmt_frag_sound (.whileStmt hc hb) fuel' σb ch₁ hhb h
              rw [hlb] at hrest
              refine ⟨hhf, ?_⟩
              cases out with
              | normal σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | broke σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | continued σf =>
                obtain ⟨hl, hsteps⟩ := hrest
                refine ⟨hl.trans hlb.symm ▸ hl, fun L k => ?_⟩
                exact ((((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans (hsteps L k))
              | returned σf =>
                intro L k
                obtain ⟨Eret, hsteps⟩ := hrest L k
                exact ⟨Eret, (((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail
                  Step.loopContinue).trans hsteps⟩
            | broke σb =>
              obtain ⟨hlb, hbsteps⟩ := hrest1
              simp only [pure_eq_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hhb, hlb, fun L k =>
                ((Steps.single (Step.whileTrue (hRc L))).trans
                  (hbsteps L (.loop c b σ.locals k))).tail Step.loopBreak⟩
            | returned σb =>
              simp only [pure_eq_ok, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨hhb, fun L k => ?_⟩
              obtain ⟨Eret, hbsteps⟩ := hrest1 L (.loop c b σ.locals k)
              exact ⟨Eret, ((Steps.single (Step.whileTrue (hRc L))).trans
                hbsteps).tail Step.loopReturn⟩
        | int n k => simp [valueAsBool] at hbv
        | addr l => simp [valueAsBool] at hbv
        | nil => simp [valueAsBool] at hbv
  | returnStmt =>
    cases hf with
    | returnStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh, fun L k => ⟨σ.locals, Steps.single .returnStmt⟩⟩
  | breakStmt =>
    cases hf with
    | breakStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh, rfl, fun L k => Steps.single .breakStmt⟩
  | continueStmt =>
    cases hf with
    | continueStmt =>
      simp only [execStmt, pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh, rfl, fun L k => Steps.single .continueStmt⟩
termination_by (fuel, sizeOf stmt)
decreasing_by all_goals (subst_vars; decreasing_tactic)

/-- **T2 — spine-list simulation.** A successful interpreter run of a spine
statement list maps to `Steps` from `.next (.seq ss σ.locals k)` to the
outcome's configuration; declarations extend the tracked seq env in
lockstep with the interpreter's locals. Only the top scope is touched, and
an initialization-free list leaves `locals` exactly unchanged. -/
theorem execStmtList_frag_sound {ss : List Stmt} (hf : ∀ s ∈ ss, SpineFrag s)
    (fuel : Nat) (σ : ExecState) (ch : Choices) (hh : HeapFrag σ)
    {out : ExecOutcome} {ch' : Choices}
    (h : execStmtList fuel σ ch ss = .ok (out, ch')) :
    HeapFrag out.state ∧
    match out with
    | .normal σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        ∀ L k, Steps (.next (.seq ss σ.locals k)) (σ.withLocals L)
          (.next k) (σf.withLocals L)
    | .broke σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        ∀ L k, Steps (.next (.seq ss σ.locals k)) (σ.withLocals L)
          (.breaking k) (σf.withLocals L)
    | .continued σf => σf.locals.popScope = σ.locals.popScope ∧
        ((∀ s ∈ ss, StmtFragNS s) → σf.locals = σ.locals) ∧
        ∀ L k, Steps (.next (.seq ss σ.locals k)) (σ.withLocals L)
          (.continuing k) (σf.withLocals L)
    | .returned σf =>
        ∀ L k, ∃ Eret, Steps (.next (.seq ss σ.locals k)) (σ.withLocals L)
          (.returning Eret k) (σf.withLocals L) := by
  cases ss with
  | nil =>
    simp only [execStmtList, pure_eq_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hh, rfl, fun _ => rfl, fun L k => Steps.single .seqDone⟩
  | cons s rest =>
    simp only [execStmtList] at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨o₁, ch₁⟩, hhead, h⟩ := h
    have hs : SpineFrag s := hf s (by simp)
    cases hs with
    | @init p htp =>
      simp only [execStmt, execDecl, bind_eq_ok, pure_eq_ok,
        Prod.mk.injEq] at hhead
      obtain ⟨σ₁, ⟨v, hv, hσ₁⟩, ho₁, rfl⟩ := hhead
      subst hσ₁
      subst ho₁
      have hfv := defaultValue_frag_val htp hv
      have hh₁ : HeapFrag (σ.declareLocal p.id (some p.typ) v) := by
        rw [declareLocal_eq_alloc]
        exact heapFrag_alloc hh hfv (fun t' ht' => by cases ht'; exact htp)
      obtain ⟨hhf, hrest⟩ := execStmtList_frag_sound
        (fun q hq => hf q (by simp [hq])) fuel _ ch hh₁ h
      refine ⟨hhf, ?_⟩
      have hpre : ∀ L k,
          Steps (.next (.seq (Stmt.initialization p :: rest) σ.locals k))
            (σ.withLocals L)
            (.next (.seq rest ((σ.declareLocal p.id (some p.typ) v).locals) k))
            ((σ.declareLocal p.id (some p.typ) v).withLocals L) := by
        intro L k
        refine (Steps.single Step.seqNext).tail
          (Step.initialization (v := v) (loc := (σ.alloc v (some p.typ)).1)
            ((defaultValue_state_indep (σ.withLocals L) σ htp).trans hv)
            (alloc_withLocals σ L v (some p.typ)))
      have hdpop : (σ.declareLocal p.id (some p.typ) v).locals.popScope
          = σ.locals.popScope := by
        rw [declareLocal_eq_alloc]
        exact declare_popScope ..
      cases out with
      | normal σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_, fun L k => (hpre L k).trans (hsteps L k)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | broke σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_, fun L k => (hpre L k).trans (hsteps L k)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | continued σf =>
        obtain ⟨hpop, _, hsteps⟩ := hrest
        refine ⟨hpop.trans hdpop, ?_, fun L k => (hpre L k).trans (hsteps L k)⟩
        intro hns
        exact absurd (hns (.initialization p) (by simp)) (by rintro ⟨⟩)
      | returned σf =>
        intro L k
        obtain ⟨Eret, hsteps⟩ := hrest L k
        exact ⟨Eret, (hpre L k).trans hsteps⟩
    | ns hns =>
      obtain ⟨hhb, hrest1⟩ := execStmt_frag_sound hns fuel σ ch hh hhead
      cases o₁ with
      | normal σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        obtain ⟨hhf, hrest⟩ := execStmtList_frag_sound
          (fun q hq => hf q (by simp [hq])) fuel σ₁ ch₁ hhb h
        rw [hl₁] at hrest
        refine ⟨hhf, ?_⟩
        have hpre : ∀ L k,
            Steps (.next (.seq (s :: rest) σ.locals k)) (σ.withLocals L)
              (.next (.seq rest σ.locals k)) (σ₁.withLocals L) := fun L k =>
          (Steps.single Step.seqNext).trans (hsteps1 L (.seq rest σ.locals k))
        cases out with
        | normal σf =>
          obtain ⟨hpop, hnseq, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            fun L k => (hpre L k).trans (hsteps L k)⟩
        | broke σf =>
          obtain ⟨hpop, hnseq, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            fun L k => (hpre L k).trans (hsteps L k)⟩
        | continued σf =>
          obtain ⟨hpop, hnseq, hsteps⟩ := hrest
          exact ⟨hpop, fun hns' => hnseq (fun q hq => hns' q (by simp [hq])),
            fun L k => (hpre L k).trans (hsteps L k)⟩
        | returned σf =>
          intro L k
          obtain ⟨Eret, hsteps⟩ := hrest L k
          exact ⟨Eret, (hpre L k).trans hsteps⟩
      | broke σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hhb, by rw [hl₁], fun _ => hl₁, fun L k =>
          ((Steps.single Step.seqNext).trans
            (hsteps1 L (.seq rest σ.locals k))).tail Step.seqBreak⟩
      | continued σ₁ =>
        obtain ⟨hl₁, hsteps1⟩ := hrest1
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hhb, by rw [hl₁], fun _ => hl₁, fun L k =>
          ((Steps.single Step.seqNext).trans
            (hsteps1 L (.seq rest σ.locals k))).tail Step.seqContinue⟩
      | returned σ₁ =>
        simp only [pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hhb, fun L k => ?_⟩
        obtain ⟨Eret, hsteps1⟩ := hrest1 L (.seq rest σ.locals k)
        exact ⟨Eret, ((Steps.single Step.seqNext).trans hsteps1).tail
          Step.seqReturn⟩
termination_by (fuel, sizeOf ss)
decreasing_by all_goals (subst_vars; decreasing_tactic)
end

/-- **The fragment interpreter-soundness theorem** — `interpreterSoundStatement`
restricted to the scalar+pointer fragment, in exactly its shape: a normal
interpreter completion of a fragment statement over a fragment heap is a
reachable terminal of the step relation, from the same state to the same
state. (For non-spine fragment statements the interpreter leaves `locals`
unchanged, so no `withLocals` appears in the statement.) -/
theorem interpreterSound_frag (fuel : Nat) (σ σ' : ExecState) (stmt : Stmt)
    (ch ch' : Choices) (hf : StmtFragNS stmt) (hh : HeapFrag σ)
    (h : execStmt fuel σ ch stmt = .ok (.normal σ', ch')) :
    Steps (.exec stmt σ.locals .stop) σ (.next .stop) σ' := by
  obtain ⟨_, hl, hsteps⟩ := execStmt_frag_sound hf fuel σ ch hh h
  have hstep := hsteps σ.locals .stop
  have hσ : σ.withLocals σ.locals = σ := rfl
  have hσ' : σ'.withLocals σ.locals = σ' := by
    rw [← hl]; rfl
  rw [hσ, hσ'] at hstep
  exact hstep

/-! ## Proven instances

Concrete derivations over rules with no opaque function premises, checking
that the control-flow rules compose the way the interpreter behaves. -/

/-- An empty sequence completes normally in two steps. Any starting control
environment works — the empty sequence reads no variables. -/
theorem seqnNilSteps (s : ExecState) (env : LocalEnv) :
    Steps (.exec (.seqn #[]) env .stop) s (.next .stop) s :=
  ((Steps.single .seqn).tail .seqDone)

/-- `while false { body }` skips its body: condition literals evaluate by
rule, the loop exits normally. -/
theorem whileFalseSteps (s : ExecState) (body : Stmt) (env : LocalEnv) :
    Steps (.exec (.while (.boolLit false) body) env .stop) s (.next .stop) s :=
  Steps.single (.whileFalse .boolLit)

/-- `if true { return } else {}` reaches the returning configuration and
unwinds through sequence context. The `returning` config carries the current
environment (so a frame could read named results). -/
theorem ifTrueReturnSteps (s : ExecState) (env : LocalEnv) :
    Steps
      (.exec (.seqn #[.ifThenElse (.boolLit true) .returnStmt (.seqn #[])]) env .stop) s
      (.returning env .stop) s :=
  (((((Steps.single .seqn).tail
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
