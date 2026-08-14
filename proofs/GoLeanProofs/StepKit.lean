import GoLean.GoCore.MachineSound

/-!
# The conditioned step-glue kit (consolidation slice, 2026-08-13)

The shared one-step/glue lemmas of the direct segment method — the
promotion-ledger rows P1 (conditioned one-step glue), P9
(`stepFn_seqn_splice`), and P11 (heap append/set reasoning at a
symbolic split) of `docs/2026-08-13_verified-examples-scale-out.md` §8,
lifted from 6–8 private per-example copies under the active-abstraction
loop (form note §12; consumers retrofitted in the same commit are the
fixture witnesses).

Everything here is UNTRUSTED METHOD (proof-side): none of these names
may appear in a headline statement closure. Each lemma is conditioned
on exactly the executable facts it needs (`applyStrictOp`/
`storeTarget`/`Heap.lookup` equations) and states the machine step over
an ABSTRACT `σ : ExecState` — the storm-diagnosis rule
(`docs/2026-08-13_consolidation-slice.md` §1): the unifier only ever
matches a variable state here, so no concrete heap front can enter an
isDefEq problem through these lemmas. At application sites that DO
mention big concrete states, pin the full result type on the `have`
(the E-form) — never leave a re-spelled state for the unifier.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-! ## P11: heap append/set reasoning at a symbolic split -/

theorem lookup_append_left {h₁ h₂ : Heap} {l : Loc} {c : HeapCell}
    (h : Heap.lookup h₁ l = some c) :
    Heap.lookup (h₁ ++ h₂) l = some c := by
  induction h₁ with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (k == l) with
      | true => simpa [hb] using h
      | false =>
          rw [hb] at h
          simpa [hb] using ih h

theorem lookup_append_right {h₁ h₂ : Heap} {l : Loc}
    (h : Heap.lookup h₁ l = none) :
    Heap.lookup (h₁ ++ h₂) l = Heap.lookup h₂ l := by
  induction h₁ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (k == l) with
      | true => simp [hb] at h
      | false =>
          rw [hb] at h
          simpa [hb] using ih h

theorem set_append_right {h₁ h₂ : Heap} {l : Loc} {c : HeapCell}
    (h : Heap.lookup h₁ l = none) :
    Heap.set (h₁ ++ h₂) l c = h₁ ++ Heap.set h₂ l c := by
  induction h₁ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at h
      cases hb : (k == l) with
      | true => simp [hb] at h
      | false =>
          rw [hb] at h
          simp only [List.cons_append, Heap.set, hb, Bool.false_eq_true,
            if_false]
          exact congrArg _ (ih h)

/-- Setting a fresh location appends the cell. -/
theorem set_fresh {h : Heap} {l : Loc} {c : HeapCell}
    (hmiss : Heap.lookup h l = none) :
    Heap.set h l c = h ++ [(l, c)] := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at hmiss
      cases hb : (k == l) with
      | true => simp [hb] at hmiss
      | false =>
          rw [hb] at hmiss
          simp only [Heap.set, hb, Bool.false_eq_true, if_false,
            List.cons_append]
          exact congrArg _ (ih hmiss)

theorem base_beq_false {a b : Nat} (h : a ≠ b) :
    ((Loc.base ⟨a⟩ : Loc) == Loc.base ⟨b⟩) = false :=
  beq_false_of_ne (by simp [h])

theorem lookup_cons_ne {k : Loc} {c : HeapCell} {h : Heap} {l : Loc}
    (hne : (k == l) = false) :
    Heap.lookup ((k, c) :: h) l = Heap.lookup h l := by
  simp [Heap.lookup, hne]

theorem set_singleton_self {l : Loc} {c₀ c : HeapCell} :
    Heap.set [(l, c₀)] l c = [(l, c)] := by
  simp [Heap.set]

theorem lookup_singleton_self {l : Loc} {c : HeapCell} :
    Heap.lookup [(l, c)] l = some c := by
  simp [Heap.lookup]

/-! ## P1: the conditioned one-step glue -/

/-- A single successful `stepFn` step is a 1-step `stepFnIter`. -/
theorem stepFnIter_one {σ : ExecState} {c : Config} {ch : Choices}
    {r : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok r) : stepFnIter 1 σ c ch = .ok r := by
  obtain ⟨c', σ', ch'⟩ := r
  simp [stepFnIter, h, Bind.bind, Except.bind]

/-- The strict-apply machine step, conditioned on the op fact. -/
theorem stepFn_strict_apply {σ σ' : ExecState} {op : StrictOp}
    {done : List GoValue} {v out : GoValue} {env : LocalEnv} {k : Cont}
    {ch : Choices}
    (h : applyStrictOp σ op (v :: done).reverse = .ok (out, σ')) :
    stepFn σ (.retV v (.strictK op done [] env k)) ch
      = .ok (.retV out k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The store machine step, conditioned on the `storeTarget` fact. -/
theorem stepFn_store_step {σ σ' : ExecState} {r : TargetRef}
    {val : GoValue} {rs : List TargetRef} {vs : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : storeTarget σ r val = .ok σ') :
    stepFn σ (.next (.storeK (r :: rs) (val :: vs) body env k)) ch
      = .ok (.next (.storeK rs vs body env k), σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The wide-op apply step, conditioned on the apply fact (mirror of
`stepFn_strict_apply` for the statement-op spine). -/
theorem stepFn_stmtOp_apply {σ σ' : ExecState} {op : StmtOp}
    {nt : Nat} {done : List GoValue} {v : GoValue} {env : LocalEnv}
    {k : Cont} {ch ch' : Choices}
    (h : applyStmtOp σ ch op nt (v :: done).reverse = .ok (σ', ch')) :
    stepFn σ (.retV v (.stmtOpK op nt done [] env k)) ch
      = .ok (.next k, σ', ch') := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The variable-read step at a symbolic heap address, conditioned on
the env binding and the cell lookup. -/
theorem stepFn_var {σ : ExecState} {x : String} {env : LocalEnv}
    {a : Addr} {k : Cont} {ch : Choices} {c : HeapCell}
    (henv : LocalEnv.lookup env x = some (.base a))
    (hlook : Heap.lookup σ.heap (.base a) = some c) :
    stepFn σ (.evalE (.var x) env k) ch = .ok (.retV c.value k, σ, ch) := by
  simp only [stepFn, henv, loadLoc, hlook, Bind.bind, Except.bind, pure,
    Except.pure]

/-- The `initialization` step under its governing sequence: allocate
the default value at the CURRENT `nextAddr` (symbolic in-loop),
declare. -/
theorem stepFn_init_seq {σ : ExecState} {p : Param}
    {rest : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices}
    {v : GoValue}
    (hdef : defaultValue σ p.typ = .ok v) :
    stepFn σ (.exec (.initialization p) env (.seq rest env k)) ch
      = .ok (.next (.seq rest (env.declare p.id (.base ⟨σ.nextAddr⟩)) k),
          { σ with heap := (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some p.typ, v⟩), nextAddr := σ.nextAddr + 1 }, ch) := by
  simp only [stepFn]
  rw [if_pos trivial]
  simp only [hdef, Bind.bind, Except.bind, pure, Except.pure,
    ExecState.alloc, ExecState.freshLoc]

/-- P9: `Expr`-free `seqn` under a same-env governing sequence splices
in ONE step — the `if_pos rfl` discharge for `seqCont`'s environment
`DecidableEq`, which otherwise blocks definitional evaluation whenever
the env carries a symbolic address. -/
theorem stepFn_seqn_splice {σ : ExecState} {ss : Array Stmt}
    {env : LocalEnv} {rest : List Stmt} {k : Cont} {ch : Choices} :
    stepFn σ (.exec (.seqn ss) env (.seq rest env k)) ch
      = .ok (.next (.seq (ss.toList ++ rest) env k), σ, ch) := by
  simp only [stepFn, seqCont]
  rw [if_pos trivial]
  rfl

/-- Popping the head of a sequence continuation. -/
theorem stepFn_seq_pop {σ : ExecState} {t : Stmt}
    {rest : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices} :
    stepFn σ (.next (.seq (t :: rest) env k)) ch
      = .ok (.exec t env (.seq rest env k), σ, ch) := rfl

/-- A drained store continuation runs its body. -/
theorem stepFn_storeK_nil {σ : ExecState} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} :
    stepFn σ (.next (.storeK [] [] body env k)) ch
      = .ok (.exec body env k, σ, ch) := rfl

/-- A plain-address store target is a `storeLoc` at its cell,
conditioned on the cell's presence and the value's normal form. -/
theorem storeTarget_addr {σ : ExecState} {a : Addr} {ty : Ty}
    {old v v' : GoValue}
    (hlook : Heap.lookup σ.heap (.base a) = some ⟨some ty, old⟩)
    (hnorm : normalizeValueForTy σ ty v = .ok v') :
    storeTarget σ (.chain (.addr (.base a)) [] []) v
      = .ok { σ with heap := Heap.set σ.heap (.base a) ⟨some ty, v'⟩ } := by
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
    pure, Except.pure, storeLoc, hlook, hnorm]

/-- The `mapAssign` wide-op apply step, conditioned on the
`mapAssignValue` fact (generic in the key/value types). -/
theorem stepFn_mapAssign_apply {σ σ' : ExecState} {kt vt : Ty}
    {b kv vv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : mapAssignValue σ kt vt b kv vv = .ok σ') :
    stepFn σ (.retV vv (.stmtOpK (.mapAssign kt vt) 0 [kv, b] [] env k))
      ch
      = .ok (.next k, σ', ch) := by
  simp only [stepFn, applyStmtOp, applyStmtOpCore, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, h, Bind.bind,
    Except.bind, pure, Except.pure]

/-- The `mapRangeK` snapshot step, conditioned on the snapshot fact
(generic in the key/value types and bound names). -/
theorem stepFn_snapshot {σ : ExecState} {v : GoValue} {kt vt : Ty}
    {ko vo : Option String}
    {entries : Array (GoValue × GoValue)} {body : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices}
    (h : mapRangeSnapshotEntries σ kt vt v = .ok entries) :
    stepFn σ (.retV v (.mapRangeK ko vo kt vt body env k)) ch
      = .ok (.next (.mapIterK ko vo kt vt body entries env k),
          σ, ch) := by
  simp only [stepFn, h, Bind.bind, Except.bind, pure, Except.pure]

/-! ## Shared op plumbing (P6-adjacent) -/

/-- A `Nat`-cast argument survives `natFromNonnegativeInt` (makeSlice's
length/cap checks at a symbolic `n`). -/
theorem natFromNonneg_cast (ctx : String) (n : Nat) :
    natFromNonnegativeInt ctx ((n : Nat) : Int) = .ok n := by
  simp only [natFromNonnegativeInt, Int.toNat_natCast]
  rw [if_neg (show ¬(((n : Nat) : Int) < 0) by omega)]
  rfl

end GoLean.Surface
