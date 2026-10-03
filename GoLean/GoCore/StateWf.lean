import GoLean.GoCore.Machine

/-!
# State/configuration well-formedness (sem-adequacy arc slice 3, 2026-08-04)

**The invariant**: every location occurring anywhere in the machine state or
control configuration has its ROOT BASE address strictly below the
allocator's `nextAddr`. The machine manufactures locations only through
`Store.alloc` (which hands out `nextAddr` and bumps it), so this holds
for every machine-reachable state of a real program; making it explicit
excludes the dangling-location pathologies that falsified the ∀-choices
correspondence kit (the `appendSlice` spill obstruction recorded in
`MachineSound.lean`, 2026-08-03: a target loc aliasing into the
yet-unallocated spill cell made step success depend on the consumed
capacity choice).

**Representation**: each carrier gets a `locSup` function — the strict
supremum of root-base ids of every location occurring in it (`0` when no
location occurs; a single location `l` contributes `l.rootBase + 1`).
"Every loc bounded by `b`" is then `locSup ≤ b`, so:
* monotonicity in the bound is `Nat.le_trans` — ONE lemma for every
  carrier, instead of a mono lemma per checker;
* decomposition is `Nat.max_le`, uniformly simp-usable;
* everything is total, STRUCTURALLY recursive (nested-inductive structural
  recursion — `brecOn`, no `WellFounded.fix`/`Acc.rec`; verified by
  environment scan, `.tmp/probe_wfscan3.lean`), and kernel-reducible, so
  well-formedness of a concrete seeded state discharges by `decide`.

Carrier inventory (checked against `Value.lean`/`State.lean`/`Syntax.lean`/
`Machine.lean`, 2026-08-04):
* `Loc` — the carrier itself (`.base`; recursion through `.field`/`.index`);
* `GoValue` — `.addr`, `.slice` (base), `.map` (base), `.chan` (base), and
  recursion through `.interface`/`.struct`/`.array`/`.funcVal`;
* `HeapCell`/`Heap` — value cells' values, map payloads' entries, channel
  payloads' buffers (A3: the payloads are CELLS, not values; `declaredTy`
  is a `Ty`: no locs). Since
  the dense heap (A2, 2026-09-04) addresses are INDICES: a key cannot
  dangle, so keys contribute nothing and `Heap.lookup_key_locSup` is the
  array bound;
* `Scope`/`LocalEnv` — the bound locations;
* **`Expr` — LOC-FREE since A4 (2026-09-04)**: the former `.locLit (l :
  Loc)` is `.global (gid : Nat)`, an index the machine resolves to an
  address at evaluation time (`Step.evalGlobal`'s premise `gid <
  s.heap.size` is what keeps the produced address bounded). The
  `Expr.locSup`/`Stmt.locSup`/`Func.locSup` carriers below are therefore
  identically zero and are kept only because the lemma network is stated
  over them — deleting them is the owed simplification recorded in the
  A-series design note (§A4).
* **`Func` bodies** (hence `Store.functions`) — a consequence of the
  historical `.locLit` finding: `enterFrame` moves `func.body` from the STATE into the
  configuration, so state well-formedness must cover stored function bodies
  or preservation fails at every call rule. `types`/`methods` carry no locs
  (`TypeDef`/`MethodSig`/`MethodInfo` are name/`Ty` data).
* `Cont`/`Config` — frame target/result loc lists, defer chains, evaluated
  operand values, environments, map-iteration snapshots, panic chains.
-/

namespace GoLean.GoCore.Machine

-- The preservation proofs below share broad `simp only` sets across many
-- match arms; an argument unused in one arm is load-bearing in another
-- (the same misfire the shared multi-goal combinators in `MachineSound`
-- suppress). Silenced file-wide for the same reason.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


open GoLean

-- B7 (2026-09-17): the program context is an IMPLICIT parameter of every
-- theorem below (`{ctx}`: lemma applications stay as they were); no
-- definition here reads it — `Store.locSup`/`StateWf`/`MachineWf` are
-- heap-only.
variable {ctx : ProgramCtx}

/-! ## The `locSup` family -/

/-- The root base address of a location: recurse through `.field`/`.index`
to the `.base` id. A location "exists" in the heap exactly when its root
base cell does — the allocator only ever hands out fresh `.base` ids. -/
def Loc.rootBase : Loc → Nat
  | .base a => a.id
  | .field b _ _ => Loc.rootBase b
  | .index b _ => Loc.rootBase b

/-- Strict sup of a single location: `rootBase + 1`, so `locSup ≤ b` says
`rootBase < b`. -/
def Loc.locSup (l : Loc) : Nat :=
  Loc.rootBase l + 1

/-- A location is bounded by `b` when its root base is strictly below it.
The Prop the whole module is about; kept as the mission-named checker. -/
def Loc.boundedBy (bound : Nat) (l : Loc) : Prop :=
  Loc.rootBase l < bound

theorem Loc.locSup_le_iff {bound : Nat} {l : Loc} :
    Loc.locSup l ≤ bound ↔ Loc.boundedBy bound l := by
  simp [Loc.locSup, Loc.boundedBy, Nat.succ_le_iff]

def optLocSup : Option Loc → Nat
  | none => 0
  | some l => Loc.locSup l

mutual

/-- Strict sup of every location root occurring in the value. Floats are
LOC-FREE scalars (a bit pattern plus a kind — no heap reference can hide
in one), so they sit in the zero arm with the other leaves. -/
def GoValue.locSup : GoValue → Nat
  | .unit | .bool _ | .int _ _ | .float _ _ | .string _ | .nil => 0
  | .addr l => Loc.locSup l
  | .interface _ v => GoValue.locSup v
  | .struct _ fields => goValueFieldsSup fields.toList
  | .array values => goValueListSup values.toList
  | .slice s => optLocSup s.base
  | .map m => optLocSup m.base
  | .chan c => optLocSup c.base
  | .funcVal _ captured => goValueListSup captured
  -- Sync primitive state is LOC-FREE (spec-parity slice 2: booleans
  -- and counters only — no heap reference can hide in one).
  | .syncData _ => 0

def goValueListSup : List GoValue → Nat
  | [] => 0
  | v :: vs => max (GoValue.locSup v) (goValueListSup vs)

def goValueFieldsSup : List (String × GoValue) → Nat
  | [] => 0
  | (_, v) :: vs => max (GoValue.locSup v) (goValueFieldsSup vs)

/-- Stamped map entries `(id, key, value)`: the id is a bare `Nat`
(entry identity, B1) and contributes nothing. -/
def goValueEntriesSup : List (Nat × GoValue × GoValue) → Nat
  | [] => 0
  | (_, k, v) :: vs =>
      max (max (GoValue.locSup k) (GoValue.locSup v)) (goValueEntriesSup vs)

end

/-- A heap cell: a value cell's value (the declared type carries no locs),
a map payload's entries, a channel payload's buffer (A3). -/
def HeapCell.locSup : HeapCell → Nat
  | .value _ v => GoValue.locSup v
  | .mapPayload entries _ => goValueEntriesSup entries.toList
  | .chanPayload buf _ _ => goValueListSup buf.toList

def heapCellsSup : List HeapCell → Nat
  | [] => 0
  | c :: rest => max (HeapCell.locSup c) (heapCellsSup rest)

/-- The heap: its cell values (addresses are indices — no keys to bound;
dense heap, A2). -/
def Heap.locSup (h : Heap) : Nat := heapCellsSup h.toList

/-- One lexical scope: every bound location. -/
def Scope.locSup : Scope → Nat
  | [] => 0
  | (_, l) :: rest => max (Loc.locSup l) (Scope.locSup rest)

/-- The scope stack. -/
def LocalEnv.locSup : LocalEnv → Nat
  | [] => 0
  | sc :: rest => max (Scope.locSup sc) (LocalEnv.locSup rest)

mutual

/-- Program-text locations: NONE since A4 (`.global gid` is an index, not
an address) — every arm is zero; the recursion covers every
`Expr`-carrying position and is kept for the lemma network stated over it
(owed deletion, design note §A4). -/
def Expr.locSup : Expr → Nat
  | .var _ | .nil _ | .intLit _ _ | .floatLit _ _ _ | .stringLit _
  | .boolLit _ | .ref _
  | .defaultValue _ | .recoverCall | .unsupported _ => 0
  | .global _ => 0
  | .convert _ e | .bytesFromString e | .stringFromByteSlice e
  | .stringFromRune e | .runesFromString e | .stringFromRuneSlice e
  | .floatBits _ e
  | .bitNeg e | .neg e | .not e | .deref e _
  | .addrOfDeref e
  | .fieldGet e _ _ | .fieldAddr e _ _ | .toInterface _ _ e
  | .typeAssert e _ _ | .length e _ | .capacity e _ =>
      Expr.locSup e
  | .add l r | .sub l r | .mul l r | .div l r | .mod l r
  | .shiftLeft l r | .shiftRight l r | .bitAnd l r | .bitOr l r
  | .bitXor l r | .bitClear l r | .eqCmp _ l r | .neqCmp _ l r
  | .atMostCmp l r | .atLeastCmp l r | .lessCmp l r | .greaterCmp l r
  | .and l r | .or l r | .indexGet l r | .indexAddr l r
  | .mapGet l r _ _ | .runeAt l r | .runeSizeAt l r =>
      max (Expr.locSup l) (Expr.locSup r)
  | .funcVal _ captured => exprListSup captured.toList
  | .structLit _ args => exprListSup args.toList
  | .arrayLit _ _ args => keyedExprListSup args.toList
  | .minOf args | .maxOf args => exprListSup args.toList
  | .slice b lo hi max? =>
      max (max (Expr.locSup b) (Expr.locSup lo))
        (max (Expr.locSup hi) (optExprSup max?))

def optExprSup : Option Expr → Nat
  | none => 0
  | some e => Expr.locSup e

def exprListSup : List Expr → Nat
  | [] => 0
  | e :: es => max (Expr.locSup e) (exprListSup es)

def keyedExprListSup : List (Int × Expr) → Nat
  | [] => 0
  | (_, e) :: es => max (Expr.locSup e) (keyedExprListSup es)

end

def Assignee.locSup : Assignee → Nat
  | .var _ | .unsupported _ => 0
  | .addr e => Expr.locSup e
  | .mapElem b k _ _ => max (Expr.locSup b) (Expr.locSup k)

def assigneeListSup : List Assignee → Nat
  | [] => 0
  | a :: as => max (Assignee.locSup a) (assigneeListSup as)

/-- A map literal's entries' loc positions (Stage E5 E5c). -/
def pairExprListSup : List (Expr × Expr) → Nat
  | [] => 0
  | (k, v) :: es => max (max (Expr.locSup k) (Expr.locSup v)) (pairExprListSup es)

/-- An allocation's loc positions (Stage E E4): its operand expressions. -/
def allocSpecSup : AllocSpec → Nat
  | .new v _ => Expr.locSup v
  | .makeSlice _ len cap => max (Expr.locSup len) (optExprSup cap)
  | .makeMap _ _ hint => optExprSup hint
  | .makeChan _ cap => optExprSup cap
  | .sliceLit _ _ elems => keyedExprListSup elems
  | .mapLit _ _ entries => pairExprListSup entries

/-- A wide statement's loc positions (Stage E5 E5a): its operand expressions. -/
def wideSpecSup : WideSpec → Nat
  | .append _ slice elems => max (Expr.locSup slice) (Expr.locSup elems)
  | .copy dst src => max (Expr.locSup dst) (Expr.locSup src)
  | .mapLookup base key _ _ => max (Expr.locSup base) (Expr.locSup key)
  | .typeAssert operand _ => Expr.locSup operand

/-- An `unseq` body's loc positions (Stage B): its head/operand expressions
and target assignee — program text, zero since A4 like `Expr.locSup`, kept
for the lemma network. -/
def unseqBodySup : UnseqBody → Nat
  | .eval _ head => Expr.locSup head
  | .load _ _ => 0
  | .invoke _ callee args => max (Expr.locSup callee) (exprListSup args)
  | .recv _ ch _ => Expr.locSup ch
  | .allocate _ spec => allocSpecSup spec
  | .wide _ spec => wideSpecSup spec
  | .target _ lhs => Assignee.locSup lhs
  | .guard _ _ _ => 0

def unseqOccsSup : List UnseqOcc → Nat
  | [] => 0
  | o :: os => max (unseqBodySup o.body) (unseqOccsSup os)

/-- A sweep graph's loc positions: its occurrences' bodies. -/
def UnseqGraph.locSup (g : UnseqGraph) : Nat := unseqOccsSup g.occs

mutual

def Stmt.locSup : Stmt → Nat
  | .returnStmt | .breakStmt | .continueStmt
  | .inertLabel _ | .breakTo _ | .continueTo _ | .unsupported _ => 0
  | .unseqProbe e => Expr.locSup e
  | .unseq g t => max (UnseqGraph.locSup g) (Stmt.locSup t)
  | .seqn ss => stmtListSup ss.toList
  | .block _ ss => stmtListSup ss.toList
  | .breakable body => Stmt.locSup body
  | .labeled _ body => Stmt.locSup body
  | .assign l r => max (Assignee.locSup l) (Expr.locSup r)
  | .assignMany ls rs =>
      max (assigneeListSup ls.toList) (exprListSup rs.toList)
  | .allocNew t v _ => max (Assignee.locSup t) (Expr.locSup v)
  | .makeSlice t _ len cap =>
      max (Assignee.locSup t) (max (Expr.locSup len) (optExprSup cap))
  | .makeMap t _ _ space =>
      max (Assignee.locSup t) (optExprSup space)
  | .mapAssign b i v _ _ =>
      max (Expr.locSup b) (max (Expr.locSup i) (Expr.locSup v))
  | .mapDelete b i _ => max (Expr.locSup b) (Expr.locSup i)
  | .clearMap b => Expr.locSup b
  | .clearSlice b _ => Expr.locSup b
  | .sortSlice b _ => Expr.locSup b
  | .mapLookup t okT b i _ _ =>
      max (max (Assignee.locSup t) (Assignee.locSup okT))
        (max (Expr.locSup b) (Expr.locSup i))
  | .typeAssert t okT e _ =>
      max (max (Assignee.locSup t) (Assignee.locSup okT)) (Expr.locSup e)
  | .appendSlice t _ sl els =>
      max (Assignee.locSup t) (max (Expr.locSup sl) (Expr.locSup els))
  | .randIntn (some t) n => max (Assignee.locSup t) (Expr.locSup n)
  | .randIntn none n => Expr.locSup n
  | .copySlice t dst src =>
      max (Assignee.locSup t) (max (Expr.locSup dst) (Expr.locSup src))
  | .call targets _ args =>
      max (assigneeListSup targets.toList) (exprListSup args.toList)
  | .callValue targets callee args =>
      max (assigneeListSup targets.toList)
        (max (Expr.locSup callee) (exprListSup args.toList))
  | .deferCall callee args =>
      max (Expr.locSup callee) (exprListSup args.toList)
  | .ifThenElse c t e =>
      max (Expr.locSup c) (max (Stmt.locSup t) (Stmt.locSup e))
  | .while c b => max (Expr.locSup c) (Stmt.locSup b)
  | .mapRange _ _ mapExpr _ _ body =>
      max (Expr.locSup mapExpr) (Stmt.locSup body)
  | .panicStmt payload => Expr.locSup payload
  -- Channel statements (channels arc slice 1).
  | .makeChan t _ capacity => max (Assignee.locSup t) (optExprSup capacity)
  | .chanSend ch v _ => max (Expr.locSup ch) (Expr.locSup v)
  | .chanRecv targets ch _ =>
      max (assigneeListSup targets.toList) (Expr.locSup ch)
  | .closeChan ch => Expr.locSup ch
  | .selectStmt clauses default? =>
      max (selectClausesSup clauses.toList) (optStmtSup default?)
  -- `go` statements (channels arc slice 2).
  | .goStmt callee args =>
      max (Expr.locSup callee) (exprListSup args.toList)
  -- Sync statements (spec-parity slice 2): heads are loc-free.
  | .syncStmt _ args targets =>
      max (exprListSup args.toList) (assigneeListSup targets.toList)
  -- sync/atomic statements (atomics arc wave 1): heads and kinds are
  -- loc-free.
  | .atomicStmt _ _ args targets =>
      max (exprListSup args.toList) (assigneeListSup targets.toList)
  -- print/println (stdlib slice 3): the head is loc-free.
  | .print _ args => exprListSup args.toList

def stmtListSup : List Stmt → Nat
  | [] => 0
  | s :: ss => max (Stmt.locSup s) (stmtListSup ss)

def selectClauseHeadSup : SelectClauseHead → Nat
  | .send ch v _ => max (Expr.locSup ch) (Expr.locSup v)
  | .recv targets ch _ =>
      max (assigneeListSup targets.toList) (Expr.locSup ch)

def selectClausesSup : List (SelectClauseHead × Stmt) → Nat
  | [] => 0
  | (h, b) :: rest =>
      max (max (selectClauseHeadSup h) (Stmt.locSup b)) (selectClausesSup rest)

def optStmtSup : Option Stmt → Nat
  | none => 0
  | some s => Stmt.locSup s

end

/-- A function's only loc-carrying position is its body (`args`/`results`
are `Param`s: name + `Ty`). -/
def Func.locSup (f : Func) : Nat :=
  Stmt.locSup f.body

def funcListSup : List Func → Nat
  | [] => 0
  | f :: fs => max (Func.locSup f) (funcListSup fs)

/-! ### Program text is loc-free (A4), as a THEOREM (B7)

Every `Expr`/`Stmt` sup above is identically zero — the carriers are kept
because the lemma network is stated over them (§A4's owed deletion), but
B7 needs the fact itself: the store no longer carries the function bodies,
so a frame's body bound (`enterFrame_tail`) is this lemma, not a
`StateWf` projection. -/

theorem Expr.locSup_eq_zero_all :
    (∀ e : Expr, Expr.locSup e = 0) ∧ (∀ o : Option Expr, optExprSup o = 0)
      ∧ (∀ l : List (Int × Expr), keyedExprListSup l = 0)
      ∧ (∀ l : List Expr, exprListSup l = 0) := by
  apply Expr.locSup.mutual_induct
  all_goals intros
  all_goals simp_all only [Expr.locSup, optExprSup, exprListSup, keyedExprListSup, Nat.max_self]

theorem Expr.locSup_eq_zero (e : Expr) : Expr.locSup e = 0 := Expr.locSup_eq_zero_all.1 e
theorem optExprSup_eq_zero (o : Option Expr) : optExprSup o = 0 := Expr.locSup_eq_zero_all.2.1 o
theorem keyedExprListSup_eq_zero (l : List (Int × Expr)) : keyedExprListSup l = 0 :=
  Expr.locSup_eq_zero_all.2.2.1 l
theorem exprListSup_eq_zero (l : List Expr) : exprListSup l = 0 := Expr.locSup_eq_zero_all.2.2.2 l

theorem Assignee.locSup_eq_zero (a : Assignee) : Assignee.locSup a = 0 := by
  cases a <;> simp [Assignee.locSup, Expr.locSup_eq_zero]
theorem assigneeListSup_eq_zero (l : List Assignee) : assigneeListSup l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [assigneeListSup, Assignee.locSup_eq_zero, ih]
theorem pairExprListSup_eq_zero (l : List (Expr × Expr)) : pairExprListSup l = 0 := by
  induction l with
  | nil => rfl
  | cons kv l ih => simp [pairExprListSup, Expr.locSup_eq_zero, ih]
theorem allocSpecSup_eq_zero (a : AllocSpec) : allocSpecSup a = 0 := by
  cases a <;> simp [allocSpecSup, Expr.locSup_eq_zero, optExprSup_eq_zero, keyedExprListSup_eq_zero,
    pairExprListSup_eq_zero]
theorem wideSpecSup_eq_zero (w : WideSpec) : wideSpecSup w = 0 := by
  cases w <;> simp [wideSpecSup, Expr.locSup_eq_zero]
theorem unseqBodySup_eq_zero (b : UnseqBody) : unseqBodySup b = 0 := by
  cases b <;> simp [unseqBodySup, Expr.locSup_eq_zero, exprListSup_eq_zero, Assignee.locSup_eq_zero,
    allocSpecSup_eq_zero, wideSpecSup_eq_zero]
theorem unseqOccsSup_eq_zero (os : List UnseqOcc) : unseqOccsSup os = 0 := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [unseqOccsSup, unseqBodySup_eq_zero, ih]
theorem UnseqGraph.locSup_eq_zero (g : UnseqGraph) : UnseqGraph.locSup g = 0 :=
  unseqOccsSup_eq_zero g.occs

theorem selectClauseHeadSup_eq_zero (h : SelectClauseHead) : selectClauseHeadSup h = 0 := by
  cases h <;> simp [selectClauseHeadSup, Expr.locSup_eq_zero, assigneeListSup_eq_zero]

theorem Stmt.locSup_eq_zero_all :
    (∀ st : Stmt, Stmt.locSup st = 0) ∧ (∀ o : Option Stmt, optStmtSup o = 0)
      ∧ (∀ l : List (SelectClauseHead × Stmt), selectClausesSup l = 0)
      ∧ (∀ l : List Stmt, stmtListSup l = 0) := by
  apply Stmt.locSup.mutual_induct
  all_goals intros
  all_goals simp_all only [Stmt.locSup, optStmtSup, selectClausesSup, stmtListSup,
    selectClauseHeadSup_eq_zero, Expr.locSup_eq_zero, optExprSup_eq_zero, exprListSup_eq_zero,
    Assignee.locSup_eq_zero, assigneeListSup_eq_zero, UnseqGraph.locSup_eq_zero, Nat.max_self]

theorem Stmt.locSup_eq_zero (st : Stmt) : Stmt.locSup st = 0 := Stmt.locSup_eq_zero_all.1 st
theorem Func.locSup_eq_zero (f : Func) : Func.locSup f = 0 := Stmt.locSup_eq_zero f.body
theorem funcListSup_eq_zero (l : List Func) : funcListSup l = 0 := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [funcListSup, Func.locSup_eq_zero, ih]

def locListSup : List Loc → Nat
  | [] => 0
  | l :: ls => max (Loc.locSup l) (locListSup ls)

/-- A pending deferred call: callee value plus evaluated argument values. -/
def deferListSup : List (GoValue × List GoValue) → Nat
  | [] => 0
  | (cv, args) :: ds =>
      max (max (GoValue.locSup cv) (goValueListSup args)) (deferListSup ds)

/-- A panic chain: every payload value. -/
def panicChainSup : List PanicEntry → Nat
  | [] => 0
  | e :: es => max (GoValue.locSup e.value) (panicChainSup es)

/-- A channel-op head's loc positions: a receive head carries its target
assignees (evaluated post-communication — BUG-022/BUG-029). -/
def chanStOpSup : ChanStOp → Nat
  | .send _ => 0
  | .recv targets _ => assigneeListSup targets
  | .close => 0

/-- A sync op head's loc positions: `onceBegin`'s delivery targets
(spec-parity slice 2) and the TRY heads' result targets (Q-TRYLOCK). -/
def syncOpSup : SyncOp → Nat
  | .onceBegin targets => assigneeListSup targets
  | .tryLock targets | .tryRLock targets | .tryWLock targets => assigneeListSup targets
  | _ => 0

/-- An atomic op's loc positions: its result target (atomics arc wave 1;
head and kind are loc-free). -/
def atomicOpSup (op : AtomicOp) : Nat := assigneeListSup op.targets

/-- A phase-1-resolved target's loc positions (its operand VALUES;
`TargetStep`s are loc-free). -/
def TargetRef.locSup : TargetRef → Nat
  | .chain anchor idxs _ => max (GoValue.locSup anchor) (goValueListSup idxs)
  | .mapElem b k _ _ => max (GoValue.locSup b) (GoValue.locSup k)

def targetRefListSup : List TargetRef → Nat
  | [] => 0
  | r :: rs => max (TargetRef.locSup r) (targetRefListSup rs)

/-- The `unseq` sweep frame's TARGET table: every frozen plan's operand
VALUES (Stage B). -/
def unseqTargetsSup : List (VarId × TargetRef) → Nat
  | [] => 0
  | (_, r) :: rs => max (TargetRef.locSup r) (unseqTargetsSup rs)

/-- Pending target plans (shape + operand expressions); shapes are
loc-free. -/
def targetPlansSup : List (TargetShape × List Expr) → Nat
  | [] => 0
  | (_, ops) :: rest => max (exprListSup ops) (targetPlansSup rest)

/-- Continuation sup: every loc position of every frame (loc lists,
evaluated operand values, environments, pending expressions/statements,
map-iteration snapshots, defer chains, suspended panic chains). -/
def Cont.locSup : Cont → Nat
  | .stop => 0
  | .probeK k => Cont.locSup k
  | .unseqK g thenB _ targets env _ k =>
      max (max (UnseqGraph.locSup g) (Stmt.locSup thenB))
        (max (unseqTargetsSup targets) (max (LocalEnv.locSup env) (Cont.locSup k)))
  -- The preprint frame (unit 6b): the suspended chain's three parts
  -- (`Rewrite.done`'s text is scalar — no location).
  | .preprintK older entry newer k =>
      max (max (panicChainSup older) (GoValue.locSup entry.value))
        (max (panicChainSup newer) (Cont.locSup k))
  | .seq rest env k =>
      max (max (stmtListSup rest) (LocalEnv.locSup env)) (Cont.locSup k)
  | .loop cond body env k =>
      max (max (Expr.locSup cond) (Stmt.locSup body))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .frame targets tenv results defers k _ =>
      max (max (targetPlansSup targets) (LocalEnv.locSup tenv))
        (max (max (locListSup results) (deferListSup defers)) (Cont.locSup k))
  | .deferCalleeK args env k =>
      max (max (exprListSup args) (LocalEnv.locSup env)) (Cont.locSup k)
  | .deferArgsK callee vals pending env k =>
      max (max (GoValue.locSup callee) (goValueListSup vals))
        (max (exprListSup pending) (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .breakableK k => Cont.locSup k
  | .labelK _ k => Cont.locSup k
  | .callValCalleeK targets args env k =>
      max (max (targetPlansSup targets) (exprListSup args))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .callValArgsK callee targets vals pending env k =>
      max (max (GoValue.locSup callee) (targetPlansSup targets))
        (max (max (goValueListSup vals) (exprListSup pending))
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .strictK _ done pending env k =>
      max (max (goValueListSup done) (exprListSup pending))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .andK r env k =>
      max (max (Expr.locSup r) (LocalEnv.locSup env)) (Cont.locSup k)
  | .orK r env k =>
      max (max (Expr.locSup r) (LocalEnv.locSup env)) (Cont.locSup k)
  | .boolK k => Cont.locSup k
  | .ifK t e env k =>
      max (max (Stmt.locSup t) (Stmt.locSup e))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .whileK c b env k =>
      max (max (Expr.locSup c) (Stmt.locSup b))
        (max (LocalEnv.locSup env) (Cont.locSup k))

  | .callArgsK _ targets vals pending env k =>
      max (max (targetPlansSup targets) (goValueListSup vals))
        (max (exprListSup pending) (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .stmtOpK _ _ done pending env k =>
      max (max (goValueListSup done) (exprListSup pending))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .mapRangeK _ _ _ _ body env k =>
      max (max (Stmt.locSup body) (LocalEnv.locSup env)) (Cont.locSup k)
  -- The `produced`/`start` ID sets are bare `Nat`s (B1 stamps): loc-free.
  | .mapIterK _ _ _ _ body base _ _ env k =>
      max (max (Stmt.locSup body) (optLocSup base))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .panicArgK k => Cont.locSup k
  | .panicResumeK chain k => max (panicChainSup chain) (Cont.locSup k)
  | .chanStK op done pending env k =>
      max (max (chanStOpSup op) (goValueListSup done))
        (max (exprListSup pending)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .selectOpsK clauses default? done pending env k =>
      max (max (selectClausesSup clauses) (optStmtSup default?))
        (max (max (goValueListSup done) (exprListSup pending))
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .tgtOpK _ ops pending refs targets _ rhs vals body env k =>
      max (max (goValueListSup ops) (exprListSup pending))
        (max (max (targetRefListSup refs) (targetPlansSup targets))
          (max (max (exprListSup rhs) (goValueListSup vals))
            (max (Stmt.locSup body)
              (max (LocalEnv.locSup env) (Cont.locSup k)))))
  | .rhsK _ refs done pending body env k =>
      max (max (targetRefListSup refs) (goValueListSup done))
        (max (exprListSup pending)
          (max (Stmt.locSup body)
            (max (LocalEnv.locSup env) (Cont.locSup k))))
  | .storeK refs vals body env k =>
      max (max (targetRefListSup refs) (goValueListSup vals))
        (max (Stmt.locSup body)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .goCalleeK args env k =>
      max (exprListSup args) (max (LocalEnv.locSup env) (Cont.locSup k))
  | .goArgsK callee vals pending env k =>
      max (max (GoValue.locSup callee) (goValueListSup vals))
        (max (exprListSup pending)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .syncStK op done pending env k =>
      max (max (syncOpSup op) (goValueListSup done))
        (max (exprListSup pending)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .atomicStK op done pending env k =>
      max (max (atomicOpSup op) (goValueListSup done))
        (max (exprListSup pending)
          (max (LocalEnv.locSup env) (Cont.locSup k)))

/-! ### The `Cont` algebra's sup laws (B3): a frame's sup is its own payload
joined with its tail's, so one lemma bounds every `Cont.rebuild` instance. -/

/-- The frame's OWN payload sup (its tail replaced by `.stop`). -/
def Cont.ownSup (k : Cont) : Nat := Cont.locSup (k.withTail .stop)

theorem Cont.locSup_withTail {k k₀ t : Cont} (h : k.tail = some k₀) :
    Cont.locSup (k.withTail t) = max (Cont.ownSup k) (Cont.locSup t) := by
  cases_cont k <;> simp [Cont.tail] at h <;> simp [Cont.withTail, Cont.ownSup, Cont.locSup] <;> omega

theorem Cont.locSup_eq_own_tail {k k₀ : Cont} (h : k.tail = some k₀) :
    Cont.locSup k = max (Cont.ownSup k) (Cont.locSup k₀) := by
  have := Cont.locSup_withTail (t := k₀) h
  rw [← this]; congr 1
  cases k <;> simp_all [Cont.tail, Cont.withTail]

/-- The sup as a LIST law (G-C3, packet C): the head frame's own payload
(`Cont.ownSup`, the frame over `[]`) joined with the tail's. -/
theorem Cont.locSup_cons (f : Frame) (k : Cont) :
    Cont.locSup (f :: k) = max (Cont.locSup [f]) (Cont.locSup k) :=
  Cont.locSup_eq_own_tail (k := f :: k) rfl

theorem Cont.locSup_nil : Cont.locSup [] = 0 := rfl

theorem Cont.ownSup_cons (f : Frame) (k : Cont) : Cont.ownSup (f :: k) = Cont.locSup [f] := rfl

theorem Cont.tail_locSup_le {k k₀ : Cont} (h : k.tail = some k₀) :
    Cont.locSup k₀ ≤ Cont.locSup k := by
  rw [Cont.locSup_eq_own_tail h]; omega

/-- **The one walk bound**: if the action never raises a frame's sup above
`bound ⊔ its input` and its payload above the input, neither does the
rebuilt continuation (strong induction on the frame's size). -/
theorem Cont.rebuild_locSup {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {bound : Nat} {μ : β → Nat}
    (hact : ∀ k b k', act k = some (b, k') →
      μ b ≤ Cont.locSup k ∧ Cont.locSup k' ≤ max bound (Cont.locSup k)) :
    ∀ k b k', Cont.rebuild descend act k = some (b, k') →
      μ b ≤ Cont.locSup k ∧ Cont.locSup k' ≤ max bound (Cont.locSup k) := by
  intro k
  induction k using WellFounded.induction (r := fun a b : Cont => sizeOf a < sizeOf b)
    (hwf := (measure sizeOf).wf) with
  | _ k ih =>
  intro b k' h
  by_cases hd : descend k = true
  · rw [Cont.rebuild_descend hd] at h
    cases ht : k.tail with
    | none => rw [ht] at h; exact hact _ _ _ h
    | some k₀ =>
      rw [ht] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨b₁, k₁⟩, h₁, h₂⟩ := h
      simp only [Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      rw [Cont.locSup_withTail ht, Cont.locSup_eq_own_tail ht]
      have := ih k₀ (Cont.sizeOf_tail_lt ht) b₁ k₁ h₁
      omega
  · rw [Cont.rebuild_act (Bool.eq_false_iff.mpr hd)] at h
    exact hact _ _ _ h

/-- One evaluated select clause's sup (`.blockedSelect` payloads). -/
def evClauseSup : EvClause → Nat
  | .sendEv chv v _ body =>
      max (max (GoValue.locSup chv) (GoValue.locSup v)) (Stmt.locSup body)
  | .recvEv chv targets _ body =>
      max (max (GoValue.locSup chv) (assigneeListSup targets)) (Stmt.locSup body)

def evClausesSup : List EvClause → Nat
  | [] => 0
  | c :: cs => max (evClauseSup c) (evClausesSup cs)

/-- Configuration sup. -/
def Config.locSup : Config → Nat
  | .exec stmt env k =>
      max (max (Stmt.locSup stmt) (LocalEnv.locSup env)) (Cont.locSup k)
  | .evalE e env k =>
      max (max (Expr.locSup e) (LocalEnv.locSup env)) (Cont.locSup k)
  | .retV v k => max (GoValue.locSup v) (Cont.locSup k)
  | .next k | .signal _ k => Cont.locSup k
  | .panicking chain k => max (panicChainSup chain) (Cont.locSup k)
  | .blockedSend ch v k =>
      max (optLocSup ch) (max (GoValue.locSup v) (Cont.locSup k))
  | .blockedRecv ch targets _ env k =>
      max (optLocSup ch)
        (max (assigneeListSup targets)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .blockedSelect clauses env k =>
      max (evClausesSup clauses) (max (LocalEnv.locSup env) (Cont.locSup k))
  | .blockedSync op loc env k =>
      max (max (syncOpSup op) (Loc.locSup loc))
        (max (LocalEnv.locSup env) (Cont.locSup k))

/-- The signal table never mints a location: every successor it produces
is built from the frame's own payload (B4). -/
theorem signalStep_locSup {sg : Signal} {k : Cont} {c' : Config}
    (h : signalStep sg k = some c') : Config.locSup c' ≤ Cont.locSup k := by
  cases_cont k <;> simp only [signalStep, Option.some.injEq, reduceCtorEq] at h
  all_goals try (subst h; simp only [Config.locSup, Cont.locSup]; omega)
  all_goals cases sg <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals try (subst h; simp only [Config.locSup, Cont.locSup, Stmt.locSup]; omega)
  all_goals split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h; simp only [Config.locSup, Cont.locSup, Stmt.locSup]; omega

/-- State sup: the heap's (keys are indices since A2, values and payloads
carry the locations). Since B7 the stored function bodies are NOT here:
they live in the `ProgramCtx`, and program text has been loc-free since
A4 (`Stmt.locSup_eq_zero` below), so the former `funcListSup σ.functions`
term was identically zero — the A4 debt, retired with the split. -/
def Store.locSup (σ : Store) : Nat :=
  Heap.locSup σ.heap

/-! ## The map-iteration typing component — DELETED (B7 fix round, 2026-09-17)

`Cont.itersNormalized`/`Config.itersNormalized` (sem-adequacy slice 3,
2026-08-04: «every in-flight `mapIterK` snapshot is self-normalized at
the state's type environment») and their vacuity certificates
`Cont.itersNormalized_true`/`Config.itersNormalized_true` are GONE. The
BUG-005 (L) surgery moved the check to `mapIterCandidates`' fail-closed
pick-time validation and left the predicate constantly `true` (no
constructor contributed a check; the `_true` lemmas proved it by
structural induction). D6 deleted its `MachineWf` conjunct; the fix round
deleted its `ThreadWf`/`MultiWf` twin ([USER] 2026-09-17, relayed: «We
should delete the vacuous conjunct right? that's just a strict
improvement») and, the predicates then being inert, the predicates and
every walk/transparency lemma about them (`seqCont_`, `pushDefer_`,
`panicPassthrough_`, `recoverThroughWrappers_`, `recoverResult_`,
`enterRecvTargets_`, `applyChanOp_`, `applySyncOp_`, `applyAtomicOp_`,
`commitClause_`, `applySelect_itersNormalized`; `spawnPlan_iters` in
`MultiWfSound.lean`). Tombstone record:
`docs/2026-09-17_b7-context-store-handoff.md` §4/§8. -/

/-! ## The Prop wrappers -/

variable (ctx) in
/-- State well-formedness: no location in the heap (values or payloads)
dangles at or beyond `nextAddr`. Heap-only since B7 (the context half of
the domain invariant is `Stmt.locSup_eq_zero`, a theorem, not a check). -/
def StateWf (σ : Store) : Prop :=
  Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ

/-- Configuration well-formedness at an allocator bound. -/
def ConfigWf (bound : Nat) (c : Config) : Prop :=
  Config.locSup c ≤ bound

variable (ctx) in
/-- The bundled invariant `Step` preserves: loc-boundedness of state and
configuration. B7 / D6 ([USER] 2026-09-16, relayed: «go ahead with the
D1-8 rulings as recommended»): the former third conjunct
`Config.itersNormalized σ.types c = true` — constantly `true` since the
BUG-005 (L) surgery (then certified by `Config.itersNormalized_true`;
predicate and certificate deleted in the B7 fix round, tombstone above),
retained until then only to bound that surgery's diff — is DELETED; the
map-iteration typing component's recorded ∀-choices obstruction is closed
by `mapIterCandidates`' fail-closed pick-time validation, not by an
invariant. A restatement, not a weakening: the deleted conjunct was a
theorem. -/
def MachineWf (σ : Store) (c : Config) : Prop :=
  StateWf ctx σ ∧ ConfigWf σ.nextAddr c

instance (ctx : ProgramCtx) (σ : Store) : Decidable (StateWf ctx σ) := by
  unfold StateWf; infer_instance
instance (bound : Nat) (c : Config) : Decidable (ConfigWf bound c) := by
  unfold ConfigWf; infer_instance
instance (ctx : ProgramCtx) (σ : Store) (c : Config) : Decidable (MachineWf ctx σ c) := by
  unfold MachineWf; infer_instance

/-- Monotonicity: every checker in the family lifts along a larger bound —
in `locSup` form this is transitivity, once, for all carriers. -/
theorem boundedBy_mono {s bound bound' : Nat} (h : s ≤ bound)
    (hbb : bound ≤ bound') : s ≤ bound' :=
  Nat.le_trans h hbb

@[inherit_doc boundedBy_mono]
theorem ConfigWf.mono {bound bound' : Nat} {c : Config} (h : ConfigWf bound c)
    (hbb : bound ≤ bound') : ConfigWf bound' c :=
  Nat.le_trans h hbb

/-! ## Generic list-sup machinery

Every list-shaped `locSup` above is an instance of one fold; the `_eq`
bridges let all membership/append/subset reasoning be proved once. -/

/-- Generic strict sup of `f` over a list. -/
def supBy {α : Type _} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => max (f x) (supBy f xs)

theorem supBy_le_iff {α : Type _} {f : α → Nat} {l : List α} {b : Nat} :
    supBy f l ≤ b ↔ ∀ a ∈ l, f a ≤ b := by
  induction l with
  | nil => simp [supBy]
  | cons x xs ih => simp [supBy, Nat.max_le, ih]

theorem supBy_mem {α : Type _} {f : α → Nat} {l : List α} {a : α}
    (h : a ∈ l) : f a ≤ supBy f l :=
  supBy_le_iff.mp (Nat.le_refl _) a h

theorem supBy_append {α : Type _} {f : α → Nat} {l₁ l₂ : List α} :
    supBy f (l₁ ++ l₂) = max (supBy f l₁) (supBy f l₂) := by
  induction l₁ with
  | nil => simp [supBy]
  | cons x xs ih => simp [supBy, ih, Nat.max_assoc]

/-- Sup over any pointwise-dominated sublist-like image. -/
theorem supBy_le_of_subset {α : Type _} {f : α → Nat} {l l' : List α}
    (h : ∀ a ∈ l', a ∈ l) : supBy f l' ≤ supBy f l :=
  supBy_le_iff.mpr fun a ha => supBy_mem (h a ha)

theorem supBy_reverse {α : Type _} {f : α → Nat} {l : List α} :
    supBy f l.reverse = supBy f l :=
  Nat.le_antisymm (supBy_le_of_subset fun a ha => List.mem_reverse.mp ha)
    (supBy_le_of_subset fun a ha => List.mem_reverse.mpr ha)

/-! The `_eq` bridges. -/

theorem goValueListSup_eq : ∀ l, goValueListSup l = supBy GoValue.locSup l
  | [] => rfl
  | _ :: vs => by simp [goValueListSup, supBy, goValueListSup_eq vs]

theorem goValueFieldsSup_eq :
    ∀ l, goValueFieldsSup l = supBy (fun p => GoValue.locSup p.2) l
  | [] => rfl
  | (_, _) :: vs => by simp [goValueFieldsSup, supBy, goValueFieldsSup_eq vs]

theorem goValueEntriesSup_eq :
    ∀ l, goValueEntriesSup l
      = supBy (fun p => max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) l
  | [] => rfl
  | (_, _, _) :: vs => by simp [goValueEntriesSup, supBy, goValueEntriesSup_eq vs]

theorem heapCellsSup_eq :
    ∀ l : List HeapCell, heapCellsSup l = supBy HeapCell.locSup l
  | [] => rfl
  | _ :: rest => by simp [heapCellsSup, supBy, heapCellsSup_eq rest]

theorem heapLocSup_eq (h : Heap) :
    Heap.locSup h = supBy HeapCell.locSup h.toList :=
  heapCellsSup_eq _

/-- Bounding the heap = bounding every cell (the dense heap's whole
ownership story: `Loc.rootBase < size` per cell value). -/
theorem Heap.locSup_le_iff {h : Heap} {b : Nat} :
    Heap.locSup h ≤ b ↔ ∀ c ∈ h, HeapCell.locSup c ≤ b := by
  rw [heapLocSup_eq, supBy_le_iff]
  simp only [Array.mem_toList_iff]

theorem scopeLocSup_eq :
    ∀ s : Scope, Scope.locSup s = supBy (fun p => Loc.locSup p.2) s
  | [] => rfl
  | (_, _) :: rest => by simp [Scope.locSup, supBy, scopeLocSup_eq rest]

theorem localEnvLocSup_eq :
    ∀ e : LocalEnv, LocalEnv.locSup e = supBy Scope.locSup e
  | [] => rfl
  | _ :: rest => by simp [LocalEnv.locSup, supBy, localEnvLocSup_eq rest]

theorem exprListSup_eq : ∀ l, exprListSup l = supBy Expr.locSup l
  | [] => rfl
  | _ :: es => by simp [exprListSup, supBy, exprListSup_eq es]

theorem keyedExprListSup_eq :
    ∀ l, keyedExprListSup l = supBy (fun p => Expr.locSup p.2) l
  | [] => rfl
  | (_, _) :: es => by simp [keyedExprListSup, supBy, keyedExprListSup_eq es]

theorem assigneeListSup_eq : ∀ l, assigneeListSup l = supBy Assignee.locSup l
  | [] => rfl
  | _ :: as => by simp [assigneeListSup, supBy, assigneeListSup_eq as]

theorem stmtListSup_eq : ∀ l, stmtListSup l = supBy Stmt.locSup l
  | [] => rfl
  | _ :: ss => by simp [stmtListSup, supBy, stmtListSup_eq ss]

theorem funcListSup_eq : ∀ l, funcListSup l = supBy Func.locSup l
  | [] => rfl
  | _ :: fs => by simp [funcListSup, supBy, funcListSup_eq fs]

theorem locListSup_eq : ∀ l, locListSup l = supBy Loc.locSup l
  | [] => rfl
  | _ :: ls => by simp [locListSup, supBy, locListSup_eq ls]

theorem deferListSup_eq :
    ∀ l, deferListSup l
      = supBy (fun p => max (GoValue.locSup p.1) (goValueListSup p.2)) l
  | [] => rfl
  | (_, _) :: ds => by simp [deferListSup, supBy, deferListSup_eq ds]

theorem panicChainSup_eq :
    ∀ l, panicChainSup l = supBy (fun e => GoValue.locSup e.value) l
  | [] => rfl
  | _ :: es => by simp [panicChainSup, supBy, panicChainSup_eq es]

/-! ## Fold/`forIn` machinery (Except-monad loops in the op tables) -/

/-- Projection of a `ForInStep`. -/
def forInStepVal {β : Type _} : ForInStep β → β
  | .done b => b
  | .yield b => b

/-! The Except-monad reduction helpers (the house idiom). They live here —
the most upstream metatheory module — and are re-exported to
`MachineSound` and the proof layer by import (moved from `MachineSound`,
sem-adequacy slice 3). -/

@[simp] theorem pure_eq_ok {ε α : Type} (a : α) :
    (pure a : Except ε α) = .ok a := rfl
@[simp] theorem stuck_def {α : Type} (m : String) :
    (GoCore.stuck m : Except Stop α) = .error (.stuck m) := rfl
@[simp] theorem panic_def {α : Type} (m : String) :
    (GoCore.panic m : Except Stop α) = .error (.panic m) := rfl
@[simp] theorem unsupported_def {α : Type} (m : String) :
    (GoCore.unsupported m : Except Stop α) = .error (.unsupported m) := rfl

theorem bind_eq_ok {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- Invariant transport along a successful `forIn` over a list in
`Except` — the loop shape of every op-table `for` loop. -/
theorem forIn_list_inv {α β : Type} {P : β → Prop} :
    ∀ {l : List α} {f : α → β → Except Stop (ForInStep β)} {b₀ bf : β},
    (∀ a ∈ l, ∀ b r, P b → f a b = .ok r → P (forInStepVal r)) →
    P b₀ → forIn l b₀ f = .ok bf → P bf := by
  intro l
  induction l with
  | nil =>
    intro f b₀ bf _ h0 hrun
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hrun
    exact hrun ▸ h0
  | cons a as ih =>
    intro f b₀ bf hstep h0 hrun
    rw [List.forIn_cons] at hrun
    rw [bind_eq_ok] at hrun
    obtain ⟨r, hr, hrest⟩ := hrun
    have hPr := hstep a (by simp) b₀ r h0 hr
    cases r with
    | done b =>
      simp only [pure, Except.pure, Except.ok.injEq] at hrest
      exact hrest ▸ hPr
    | yield b =>
      exact ih (fun a' ha' => hstep a' (by simp [ha'])) hPr hrest

/-! ## Environment and heap lemmas -/

theorem Scope.lookup_locSup {sc : Scope} {id : VarId} {l : Loc}
    (h : Scope.lookup sc id = some l) : Loc.locSup l ≤ Scope.locSup sc := by
  induction sc with
  | nil => simp [Scope.lookup] at h
  | cons p rest ih =>
    obtain ⟨name, loc⟩ := p
    simp only [Scope.lookup] at h
    split at h
    · cases h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem LocalEnv.lookup_locSup {env : LocalEnv} {id : VarId} {l : Loc}
    (h : LocalEnv.lookup env id = some l) : Loc.locSup l ≤ LocalEnv.locSup env := by
  induction env with
  | nil => simp [LocalEnv.lookup] at h
  | cons sc rest ih =>
    simp only [LocalEnv.lookup] at h
    split at h
    · rename_i heq
      cases h
      exact Nat.le_trans (Scope.lookup_locSup heq) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem LocalEnv.declare_locSup {env : LocalEnv} {id : VarId} {l : Loc} :
    LocalEnv.locSup (env.declare id l) ≤ max (LocalEnv.locSup env) (Loc.locSup l) := by
  cases env with
  | nil => simp [LocalEnv.declare, LocalEnv.locSup, Scope.locSup]
  | cons sc rest =>
    simp [LocalEnv.declare, LocalEnv.locSup, Scope.locSup]
    omega

theorem LocalEnv.pushScope_locSup {env : LocalEnv} :
    LocalEnv.locSup env.pushScope = LocalEnv.locSup env := by
  simp [LocalEnv.pushScope, LocalEnv.locSup, Scope.locSup]

/-- C4 D8 — FRESHNESS of an entry slot: no binding of a loc-bounded environment names it (an
entry slot's root is at or past the store's size, every bounded binding's root strictly below); with
`ConfigWf`'s sup bounds this is «no existing value, environment or label names the new cell». -/
theorem blockEntry_fresh {env : LocalEnv} {s : Store} (henv : LocalEnv.locSup env ≤ s.nextAddr)
    (id : VarId) (i : Nat) : LocalEnv.lookup env id ≠ some (entrySlot s i) := by
  intro h
  have hsup := LocalEnv.lookup_locSup h
  simp only [entrySlot, Loc.locSup, Loc.rootBase, Store.nextAddr] at hsup henv
  omega

theorem Heap.lookup_locSup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : HeapCell.locSup c ≤ Heap.locSup h := by
  cases l with
  | base a =>
    obtain ⟨i⟩ := a
    simp only [Heap.lookup] at hl
    exact Heap.locSup_le_iff.mp (Nat.le_refl _) c (Array.mem_of_getElem? hl)
  | field _ _ _ => simp [Heap.lookup] at hl
  | index _ _ => simp [Heap.lookup] at hl

/-- The KEY side: a mapped root address is below the heap's SIZE — on the
dense heap this is the array bound, not a sup over keys (keys no longer
contribute to `Heap.locSup`). -/
theorem Heap.lookup_key_locSup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : Loc.locSup l ≤ h.size := by
  cases l with
  | base a =>
    have := Heap.lookup_lt hl
    simp only [Loc.locSup, Loc.rootBase]
    omega
  | field _ _ _ => simp [Heap.lookup] at hl
  | index _ _ => simp [Heap.lookup] at hl

/-- Allocation (`push`) adds exactly the new cell's sup. -/
theorem Heap.push_locSup {h : Heap} {c : HeapCell} :
    Heap.locSup (h.push c) ≤ max (Heap.locSup h) (HeapCell.locSup c) := by
  rw [Heap.locSup_le_iff]
  intro x hx
  rcases Array.mem_push.mp hx with hx | rfl
  · exact Nat.le_trans (Heap.locSup_le_iff.mp (Nat.le_refl _) x hx) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-- An in-range overwrite is bounded by the old heap and the new cell. -/
theorem Heap.set_locSup {h : Heap} {i : Nat} {c : HeapCell} {hi : i < h.size} :
    Heap.locSup (h.set i c hi) ≤ max (Heap.locSup h) (HeapCell.locSup c) := by
  rw [Heap.locSup_le_iff]
  intro x hx
  rcases Array.mem_or_eq_of_mem_set hx with hx | rfl
  · exact Nat.le_trans (Heap.locSup_le_iff.mp (Nat.le_refl _) x hx) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-! ## Value-primitive lemmas -/

theorem StructFields.lookup_locSup {fields : Array (String × GoValue)}
    {needle : String} {v : GoValue}
    (h : StructFields.lookup fields needle = some v) :
    GoValue.locSup v ≤ goValueFieldsSup fields.toList := by
  simp only [StructFields.lookup] at h
  rw [← Array.foldl_toList] at h
  -- structure-eta defeq bridge to the projection form
  have h2 : fields.toList.foldl (fun found x =>
      match found with
      | some value => some value
      | none => if x.1 == needle then some x.2 else none) none = some v := h
  clear h
  rw [goValueFieldsSup_eq]
  suffices haux : ∀ (l : List (String × GoValue)) (acc : Option GoValue),
      (l.foldl (fun found x =>
        match found with
        | some value => some value
        | none => if x.1 == needle then some x.2 else none) acc = some v) →
      acc = some v ∨ GoValue.locSup v ≤ supBy (fun p => GoValue.locSup p.2) l by
    rcases haux fields.toList none h2 with h0 | hle
    · cases h0
    · exact hle
  intro l
  induction l with
  | nil => intro acc h; exact .inl h
  | cons p rest ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h0 | hle
    · cases acc with
      | some w => cases h0; exact .inl rfl
      | none =>
        simp only at h0
        split at h0
        · cases h0
          exact .inr (by simp [supBy]; omega)
        · cases h0
    · exact .inr (Nat.le_trans hle (by simp [supBy]; omega))

theorem findFunctionIn?_locSup {funcs : Array Func} {fid : FuncId} {f : Func}
    (h : findFunctionIn? funcs fid = some f) :
    Func.locSup f ≤ funcListSup funcs.toList := by
  simp only [findFunctionIn?] at h
  rw [← Array.foldl_toList] at h
  rw [funcListSup_eq]
  suffices haux : ∀ (l : List Func) (acc : Option Func),
      (l.foldl (fun found func =>
        match found with
        | some f => some f
        | none => if func.id == fid then some func else none) acc = some f) →
      acc = some f ∨ Func.locSup f ≤ supBy Func.locSup l by
    rcases haux funcs.toList none h with h0 | hle
    · cases h0
    · exact hle
  intro l
  induction l with
  | nil => intro acc h; exact .inl h
  | cons g rest ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h0 | hle
    · cases acc with
      | some w => cases h0; exact .inl rfl
      | none =>
        simp only at h0
        split at h0
        · cases h0
          exact .inr (by simp [supBy]; omega)
        · cases h0
    · exact .inr (Nat.le_trans hle (by simp [supBy]; omega))

theorem arrayGet_locSup {values : Array GoValue} {i : Int} {v : GoValue}
    (h : arrayGet values i = .ok v) :
    GoValue.locSup v ≤ goValueListSup values.toList := by
  unfold arrayGet arrayIndexNat at h
  try simp only [bind_eq_ok] at h
  obtain ⟨n, hn, h⟩ := h
  split at h
  · rename_i hv
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    rw [goValueListSup_eq]
    exact supBy_mem (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hv))
  · unfold indexOutOfRangePanic at h
    split at h <;> simp at h

/-- Strip a fail-closed guard (floats slice F2): an `ite` whose THEN
branch is an error can be `.ok` only through its ELSE branch. -/
theorem guard_ite_eq_ok {ε α : Type} {c : Prop} [Decidable c]
    {a b : Except ε α} {x : α} (ha : ∀ y, a ≠ .ok y)
    (h : (if c then a else b) = .ok x) : b = .ok x := by
  split at h
  · exact absurd h (ha x)
  · exact h

/-- `f <$> x` inversion, Except-side. -/
theorem map_eq_ok {ε α β : Type} {g : α → β} {x : Except ε α} {b : β} :
    g <$> x = .ok b ↔ ∃ a, x = .ok a ∧ g a = b := by
  cases x <;> simp [Functor.map, Except.map, eq_comm]

/-! ## Loc-path simp lemmas -/

@[simp] theorem Loc.rootBase_index {b : Loc} {i : Int} :
    Loc.rootBase (.index b i) = Loc.rootBase b := rfl
@[simp] theorem Loc.rootBase_field {b : Loc} {t : TypeId} {f : String} :
    Loc.rootBase (.field b t f) = Loc.rootBase b := rfl
theorem Loc.locSup_index {b : Loc} {i : Int} :
    Loc.locSup (.index b i) = Loc.locSup b := rfl
theorem Loc.locSup_field {b : Loc} {t : TypeId} {f : String} :
    Loc.locSup (.field b t f) = Loc.locSup b := rfl

/-! ## Type-directed value operations: outputs never invent locations -/

theorem goValueListSup_push {arr : Array GoValue} {x : GoValue} :
    goValueListSup (arr.push x).toList
      = max (goValueListSup arr.toList) (GoValue.locSup x) := by
  simp [goValueListSup_eq, Array.toList_push, supBy_append, supBy]

theorem goValueFieldsSup_push {arr : Array (String × GoValue)}
    {p : String × GoValue} :
    goValueFieldsSup (arr.push p).toList
      = max (goValueFieldsSup arr.toList) (GoValue.locSup p.2) := by
  simp [goValueFieldsSup_eq, Array.toList_push, supBy_append, supBy]

theorem normalizeListWithAux_locSup {f : GoValue → Except Stop GoValue}
    (hf : ∀ v r, f v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {l : List GoValue} {acc arr : Array GoValue},
      normalizeListWithAux f acc l = .ok arr →
      goValueListSup arr.toList ≤ max (goValueListSup acc.toList) (goValueListSup l) := by
  intro l
  induction l with
  | nil =>
    intro acc arr h
    simp only [normalizeListWithAux, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueListSup]
  | cons v vs ih =>
    intro acc arr h
    simp only [normalizeListWithAux, bind_eq_ok] at h
    obtain ⟨head, hhead, h⟩ := h
    have h1 := hf v head hhead
    have h2 := ih h
    rw [goValueListSup_push] at h2
    simp only [goValueListSup]
    omega

theorem normalizeListWith_locSup {f : GoValue → Except Stop GoValue}
    (hf : ∀ v r, f v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {l : List GoValue} {arr : Array GoValue},
      normalizeListWith f l = .ok arr →
      goValueListSup arr.toList ≤ goValueListSup l := by
  intro l arr h
  have := normalizeListWithAux_locSup hf h
  simpa [goValueListSup] using this

theorem normalizeFieldsWithAux_locSup {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ ty v r, f ty v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {fields : List FieldDef} {vals : List (String × GoValue)}
      {acc arr : Array (String × GoValue)},
      normalizeFieldsWithAux f acc fields vals = .ok arr →
      goValueFieldsSup arr.toList ≤ max (goValueFieldsSup acc.toList) (goValueFieldsSup vals) := by
  intro fields
  induction fields with
  | nil =>
    intro vals acc arr h
    simp only [normalizeFieldsWithAux, pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact Nat.le_max_left _ _
  | cons fd frest ih =>
    intro vals acc arr h
    cases vals with
    | nil =>
      simp only [normalizeFieldsWithAux, pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueFieldsSup]
    | cons p vrest =>
      obtain ⟨pn, pv⟩ := p
      simp only [normalizeFieldsWithAux] at h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · try simp only [bind_eq_ok] at h
        obtain ⟨head, hhead, h⟩ := h
        have h1 := hf _ _ _ hhead
        have h2 := ih h
        rw [goValueFieldsSup_push] at h2
        simp only [goValueFieldsSup] at *
        omega

theorem normalizeFieldsWith_locSup {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ ty v r, f ty v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {fields : List FieldDef} {vals : List (String × GoValue)}
      {arr : Array (String × GoValue)},
      normalizeFieldsWith f fields vals = .ok arr →
      goValueFieldsSup arr.toList ≤ goValueFieldsSup vals := by
  intro fields vals arr h
  have := normalizeFieldsWithAux_locSup hf h
  simpa [goValueFieldsSup] using this

theorem normalizeStructValueWith_locSup {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ ty v r, f ty v = .ok r → GoValue.locSup r ≤ GoValue.locSup v)
    {name : TypeId} {fields : Array FieldDef} {v r : GoValue}
    (h : normalizeStructValueWith f name fields v = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  cases v <;> try (simp [normalizeStructValueWith] at h; done)
  rename_i actual fieldsValue
  simp only [normalizeStructValueWith] at h
  split at h
  · -- tag mismatch: the empty-struct assignability escape yields the
    -- retagged EMPTY struct (locSup 0); the stuck arm is vacuous.
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [GoValue.locSup, goValueFieldsSup]
    · simp [Bind.bind, Except.bind] at h
  · split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [map_eq_ok] at h
      obtain ⟨arr, harr, rfl⟩ := h
      simpa [GoValue.locSup] using normalizeFieldsWith_locSup hf harr

/-- The TYPE layer of normalization is loc-bounded by its input, given the
same for the `.defined` callback. -/
theorem normalizeValueForTyTy_locSup {f : TypeIdx → GoValue → Except Stop GoValue}
    (hf : ∀ i v r, f i v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {ty : Ty} {v r : GoValue},
      normalizeValueForTyTy f ty v = .ok r →
      GoValue.locSup r ≤ GoValue.locSup v := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v r h
    cases v <;> try (simp [normalizeValueForTyTy] at h; done)
    rename_i values
    simp only [normalizeValueForTyTy] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, map_eq_ok] at h
      obtain ⟨arr, harr, rfl⟩ := h
      simpa [GoValue.locSup] using
        normalizeListWith_locSup (fun _ _ hr => ih hr) harr
  | leaf ty hne =>
    intro v r h
    cases ty
    case array => exact absurd rfl (hne _ _)
    case int kind =>
      cases v <;> simp [normalizeValueForTyTy] at h <;> subst h <;>
        simp [GoValue.locSup]
    case float kind =>
      cases v <;> try (simp [normalizeValueForTyTy] at h; done)
      rename_i bits k
      simp only [normalizeValueForTyTy] at h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        simp [GoValue.locSup]
      · simp [Bind.bind, Except.bind] at h
    case interface id =>
      simp only [normalizeValueForTyTy, pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
    case funcType ps rs _ =>
      cases v <;> simp [normalizeValueForTyTy] at h <;> subst h <;>
        exact Nat.le_refl _
    case defined i => exact hf _ _ _ h
    case unsupported f => simp [normalizeValueForTyTy] at h
    case chan d elem =>
      cases v <;>
        simp_all [normalizeValueForTyTy, GoValue.locSup, optLocSup] <;>
        subst h <;>
        simp [GoValue.locSup, optLocSup]
    case sync kind =>
      -- Sync arms (spec-parity slice 2): kind-matching state passes
      -- through unchanged; everything else is stuck.
      cases v <;> simp only [normalizeValueForTyTy] at h
      case syncData p =>
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq] at h
          subst h
          exact Nat.le_refl _
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    all_goals
      simp only [normalizeValueForTyTy, pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _

/-- The INDEX layer, by induction on the descent bound. -/
theorem normalizeValueForTyAt_locSup (types : TypeEnv) :
    ∀ (bound : Nat) {i : TypeIdx} {v r : GoValue},
      normalizeValueForTyAt types bound i v = .ok r →
      GoValue.locSup r ≤ GoValue.locSup v := by
  intro bound
  induction bound with
  | zero => intro i v r h; simp [normalizeValueForTyAt, typeIndexExhausted] at h
  | succ n ih =>
    intro i v r h
    simp only [normalizeValueForTyAt] at h
    split at h
    · exact normalizeStructValueWith_locSup
        (fun _ _ _ hr => normalizeValueForTyTy_locSup (fun _ _ _ hh => ih hh) hr) h
    · exact normalizeValueForTyTy_locSup (fun _ _ _ hh => ih hh) h
    · simp at h
    · simp at h
    · simp at h

theorem normalizeValueForTy_locSup {ty : Ty} {v r : GoValue}
    (h : normalizeValueForTy ctx ty v = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold normalizeValueForTy at h
  exact normalizeValueForTyTy_locSup (fun _ _ _ hh => normalizeValueForTyAt_locSup _ _ hh) h

theorem defaultFieldsWith_locSup {f : Ty → Except Stop GoValue}
    (hf : ∀ ty r, f ty = .ok r → GoValue.locSup r = 0) :
    ∀ {fields : List FieldDef} {arr : Array (String × GoValue)},
      defaultFieldsWith f fields = .ok arr →
      goValueFieldsSup arr.toList = 0 := by
  intro fields
  induction fields with
  | nil =>
    intro arr h
    simp only [defaultFieldsWith, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueFieldsSup]
  | cons fd rest ih =>
    intro arr h
    simp only [defaultFieldsWith, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    have h1 := hf _ _ hhead
    have h2 := ih htail
    have hl : (#[(fd.name, head)] ++ tail).toList
        = (fd.name, head) :: tail.toList := by simp
    rw [hl]
    simp only [goValueFieldsSup]
    omega

/-- The TYPE layer of the zero value is loc-free, given the same for the
`.defined` callback. -/
theorem defaultValueTy_locSup {f : TypeIdx → Except Stop GoValue}
    (hf : ∀ i r, f i = .ok r → GoValue.locSup r = 0) :
    ∀ {ty : Ty} {v : GoValue},
      defaultValueTy f ty = .ok v → GoValue.locSup v = 0 := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v h
    simp only [defaultValueTy] at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [GoValue.locSup, goValueListSup]
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨d, hd, hv⟩ := h
      subst hv
      have h0 := ih hd
      simp only [GoValue.locSup, goValueListSup_eq]
      refine Nat.le_zero.mp (supBy_le_iff.mpr fun x hx => ?_)
      rw [Array.toList_replicate] at hx
      rw [List.eq_of_mem_replicate hx, h0]
      exact Nat.le_refl _
  | leaf ty hne =>
    intro v h
    cases ty
    case array => exact absurd rfl (hne _ _)
    case defined i => exact hf _ _ h
    case unsupported f => simp [defaultValueTy] at h
    all_goals
      simp only [defaultValueTy, pure_eq_ok, Except.ok.injEq] at h
      subst h <;> simp [GoValue.locSup, optLocSup]

/-- The INDEX layer, by induction on the descent bound. -/
theorem defaultValueAt_locSup (types : TypeEnv) :
    ∀ (bound : Nat) {i : TypeIdx} {v : GoValue},
      defaultValueAt types bound i = .ok v → GoValue.locSup v = 0 := by
  intro bound
  induction bound with
  | zero => intro i v h; simp [defaultValueAt, typeIndexExhausted] at h
  | succ n ih =>
    intro i v h
    simp only [defaultValueAt] at h
    split at h
    · simp only [map_eq_ok] at h
      obtain ⟨arr, harr, rfl⟩ := h
      simpa [GoValue.locSup] using
        defaultFieldsWith_locSup
          (fun _ _ hr => defaultValueTy_locSup (fun _ _ hh => ih hh) hr) harr
    · exact defaultValueTy_locSup (fun _ _ hh => ih hh) h
    · simp at h
    · simp at h
    · simp at h

theorem defaultValue_locSup {ty : Ty} {v : GoValue}
    (h : defaultValue ctx ty = .ok v) : GoValue.locSup v = 0 := by
  unfold defaultValue at h
  exact defaultValueTy_locSup (fun _ _ hh => defaultValueAt_locSup _ _ hh) h

/-- Conversion is loc-bounded by its operand: every ok result is the
operand itself, a normalized array copy, a retagged copy of its fields,
or a loc-free scalar.
Cases on the RESOLVED target body (C2: the conversion is not recursive). -/
theorem convertValueToTy_locSup {ty : Ty} {v r : GoValue}
    (h : convertValueToTy ctx ty v = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold convertValueToTy at h
  generalize ctx.types.resolve ctx.types.size ty = body at h
  match body with
  | .error _ => simp at h
  | .ok (.interfaceDecl _) => simp at h
  | .ok (.opaque _ _) => simp at h
  | .ok (.struct name targetFields) =>
    -- struct conversion (stage 7): identity, or a retagged copy with
    -- the SAME fields — locSup is over the fields either way.
    cases v <;> try (simp at h; done)
    simp only at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
    · split at h
      · split at h
        · simp only [pure_eq_ok, Except.ok.injEq] at h
          subst h
          simp [GoValue.locSup]
        · simp at h
      · simp at h
  | .ok (.plain t) =>
    cases t <;> cases v <;>
      first
      | (simp at h; done)
      | (simp only [pure_eq_ok, Except.ok.injEq] at h;
         subst h; first | exact Nat.le_refl _ | simp [GoValue.locSup])
      | -- float arms (floats slice F2): nested kind/range dispatch, every
        -- ok result a loc-free scalar
        (simp only at h;
         split at h <;>
           first
           | (simp at h; done)
           | (split at h <;>
               first
               | (simp at h; done)
               | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
                  simp [GoValue.locSup]))
           | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
              simp [GoValue.locSup]))
      | skip
    case array.array n elem values =>
      exact normalizeValueForTy_locSup h
    -- pointer target × slice operand (triage L2a): the elem dispatch
    -- blocks the generic reduction; every branch is panic/unsupported,
    -- so no ok exists.
    case pointer.slice elem sl =>
      cases elem <;> simp only at h <;>
        first
        | (simp at h; done)
        | (split at h <;> simp at h)

/-- Every ok result of the IEEE
 `min`/`max` selection is one of the
`.float` operands — loc-free (triage L3). -/
theorem floatMinMax_locSup {isMin : Bool} {l r v : GoValue}
    (h : floatMinMax isMin l r = .ok v) : GoValue.locSup v = 0 := by
  cases l <;> cases r <;>
    first
    | (simp [floatMinMax] at h; done)
    | skip
  case float.float a ka b kb =>
    simp only [floatMinMax] at h
    (repeat' split at h) <;>
      first
      | (simp at h; done)
      | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
         simp [GoValue.locSup])

/-! ## Soundness of the self-normalization check

`isNormalForTyTy` (Ops.lean) mirrors the normalizer arm-for-arm; here
is the direction every theorem consumes: check true ⇒ the normalizer
returns the value UNCHANGED. Stated against an arbitrary state whose
`types` is the checker's environment. -/

theorem isNormalListWith_sound_aux {f : GoValue → Bool}
    {g : GoValue → Except Stop GoValue}
    (hfg : ∀ v, f v = true → g v = .ok v) :
    ∀ {l : List GoValue} (acc : Array GoValue), isNormalListWith f l = true →
      normalizeListWithAux g acc l = .ok (acc ++ l.toArray) := by
  intro l
  induction l with
  | nil => intro acc _; simp [normalizeListWithAux, pure, Except.pure]
  | cons v rest ih =>
    intro acc h
    simp only [isNormalListWith, Bool.and_eq_true] at h
    simp only [normalizeListWithAux, hfg v h.1, Bind.bind, Except.bind]
    rw [ih (acc.push v) h.2]
    congr 1
    apply Array.ext'
    simp

theorem isNormalListWith_sound {f : GoValue → Bool}
    {g : GoValue → Except Stop GoValue}
    (hfg : ∀ v, f v = true → g v = .ok v) :
    ∀ {l : List GoValue}, isNormalListWith f l = true →
      normalizeListWith g l = .ok l.toArray := by
  intro l h
  have := isNormalListWith_sound_aux hfg #[] h
  simpa [normalizeListWith] using this

theorem isNormalFieldsWith_sound_aux {f : Ty → GoValue → Bool}
    {g : Ty → GoValue → Except Stop GoValue}
    (hfg : ∀ ty v, f ty v = true → g ty v = .ok v) :
    ∀ {fds : List FieldDef} {vals : List (String × GoValue)} (acc : Array (String × GoValue)),
      isNormalFieldsWith f fds vals = true →
      normalizeFieldsWithAux g acc fds vals = .ok (acc ++ vals.toArray) := by
  intro fds
  induction fds with
  | nil =>
    intro vals acc h
    cases vals with
    | nil => simp [normalizeFieldsWithAux, pure, Except.pure]
    | cons _ _ => simp [isNormalFieldsWith] at h
  | cons fd fdRest ih =>
    intro vals acc h
    cases vals with
    | nil => simp [isNormalFieldsWith] at h
    | cons p valRest =>
      obtain ⟨actual, v⟩ := p
      simp only [isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hname, hv⟩, hrest⟩ := h
      subst hname
      simp only [normalizeFieldsWithAux, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        hfg _ _ hv, Bind.bind, Except.bind, pure, Except.pure]
      rw [ih (acc.push (fd.name, v)) hrest]
      congr 1
      apply Array.ext'
      simp

theorem isNormalFieldsWith_sound {f : Ty → GoValue → Bool}
    {g : Ty → GoValue → Except Stop GoValue}
    (hfg : ∀ ty v, f ty v = true → g ty v = .ok v) :
    ∀ {fds : List FieldDef} {vals : List (String × GoValue)},
      isNormalFieldsWith f fds vals = true →
      normalizeFieldsWith g fds vals = .ok vals.toArray := by
  intro fds vals h
  have := isNormalFieldsWith_sound_aux hfg #[] h
  simpa [normalizeFieldsWith] using this

/-- The TYPE layer: check true ⇒ the normalizer's type layer returns the
value unchanged, given the same for the two `.defined` callbacks. -/
theorem isNormalForTyTy_sound {f : TypeIdx → GoValue → Bool}
    {g : TypeIdx → GoValue → Except Stop GoValue}
    (hfg : ∀ i v, f i v = true → g i v = .ok v) :
    ∀ {ty : Ty} {v : GoValue},
      isNormalForTyTy f ty v = true →
      normalizeValueForTyTy g ty v = .ok v := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v h
    cases v
    case array values =>
      simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hsz, hels⟩ := h
      have hlist := isNormalListWith_sound (fun w hw => ih hw) hels
      simp [normalizeValueForTyTy, hsz, hlist, Bind.bind, Except.bind,
        Except.map, Functor.map, pure, Except.pure]
    all_goals exact absurd h (by simp [isNormalForTyTy])
  | leaf ty hne =>
    intro v h
    cases ty with
    | array => exact absurd rfl (hne _ _)
    | int kind =>
      cases v
      case int value k =>
        simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        simp [normalizeValueForTyTy, h1, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyTy])
    | float kind =>
      cases v
      case float bits k =>
        simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        simp only [normalizeValueForTyTy, h1, pure, Except.pure]
        have hbeq : (kind == kind) = true := by cases kind <;> rfl
        simp [hbeq, h1]
      all_goals exact absurd h (by simp [isNormalForTyTy])
    | interface _ => simp [normalizeValueForTyTy, pure, Except.pure]
    | funcType params results _ =>
      cases v
      case funcVal fid captured =>
        simp [normalizeValueForTyTy, pure, Except.pure]
      case nil => simp [normalizeValueForTyTy, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyTy])
    | defined i => exact hfg _ _ h
    | unsupported _ => simp [isNormalForTyTy] at h
    | bool => simp [normalizeValueForTyTy, pure, Except.pure]
    | string => simp [normalizeValueForTyTy, pure, Except.pure]
    | slice _ => simp [normalizeValueForTyTy, pure, Except.pure]
    | map _ _ => simp [normalizeValueForTyTy, pure, Except.pure]
    | chan _ _ =>
      cases v
      case chan cv => simp [normalizeValueForTyTy, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyTy])
    | sync kind =>
      cases v
      case syncData p =>
        simp only [isNormalForTyTy] at h
        simp [normalizeValueForTyTy, h, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyTy])
    | pointer _ => simp [normalizeValueForTyTy, pure, Except.pure]

/-- The INDEX layer, in lockstep: both descents at the same bound. -/
theorem isNormalForTyAt_sound (types : TypeEnv) :
    ∀ (bound : Nat) {i : TypeIdx} {v : GoValue},
      isNormalForTyAt types bound i v = true →
      normalizeValueForTyAt types bound i v = .ok v := by
  intro bound
  induction bound with
  | zero => intro i v h; simp [isNormalForTyAt] at h
  | succ n ih =>
    intro i v h
    simp only [isNormalForTyAt] at h
    cases hlook : types[i]? with
    | none => rw [hlook] at h; exact absurd h (by simp)
    | some e =>
      rw [hlook] at h
      obtain ⟨name, td⟩ := e
      cases td with
      | struct fields =>
        cases v
        case struct actual fieldsValue =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hname, hsz⟩, hflds⟩ := h
          subst hname
          have hf := isNormalFieldsWith_sound
            (fun t w hw => isNormalForTyTy_sound (fun _ _ hh => ih hh) hw) hflds
          simp [normalizeValueForTyAt, hlook, normalizeStructValueWith,
            hsz, hf, Bind.bind, Except.bind, Except.map, Functor.map,
            pure, Except.pure]
        all_goals exact absurd h (by simp)
      | defined target =>
        simpa [normalizeValueForTyAt, hlook] using
          isNormalForTyTy_sound (fun _ _ hh => ih hh) h
      | opaqueDecl _ => exact absurd h (by simp)
      | interfaceDef _ => exact absurd h (by simp)

/-- The wrapper form: check at `ctx.types` ⇒ `normalizeValueForTy` is the
identity (in `.ok`) at `σ`. -/
theorem isNormalForTy_sound {ty : Ty} {v : GoValue}
    (h : isNormalForTy ctx.types ty v = true) :
    normalizeValueForTy ctx ty v = .ok v := by
  unfold normalizeValueForTy
  unfold isNormalForTy at h
  exact isNormalForTyTy_sound (fun _ _ hh => isNormalForTyAt_sound _ _ hh) h

/-! #### The list/field normalizers' old equations (C1 S1)

`normalizeListWith`/`normalizeFieldsWith` are LINEAR since C1 S1 (accumulator
form, `Ops.lean`); the lemmas below recover the former recursive equations, so
every proof that unfolded them arm by arm keeps its shape. -/

theorem normalizeListWithAux_acc {f : GoValue → Except Stop GoValue} :
    ∀ (l : List GoValue) (acc : Array GoValue),
      normalizeListWithAux f acc l = (normalizeListWithAux f #[] l).map (acc ++ ·) := by
  intro l
  induction l with
  | nil => intro acc; simp [normalizeListWithAux, pure, Except.pure, Except.map]
  | cons v rest ih =>
    intro acc
    simp only [normalizeListWithAux]
    cases f v with
    | error e => simp [Bind.bind, Except.bind, Except.map]
    | ok h =>
      simp only [Bind.bind, Except.bind]
      rw [ih (acc.push h), ih (#[].push h)]
      cases normalizeListWithAux f #[] rest with
      | error e => simp [Except.map]
      | ok tail =>
        simp only [Except.map, Except.ok.injEq]
        apply Array.ext'
        simp

theorem normalizeListWith_nil {f : GoValue → Except Stop GoValue} :
    normalizeListWith f [] = pure #[] := rfl

theorem normalizeListWith_cons {f : GoValue → Except Stop GoValue} {v : GoValue}
    {rest : List GoValue} :
    normalizeListWith f (v :: rest) = do
      let head ← f v
      let tail ← normalizeListWith f rest
      return #[head] ++ tail := by
  simp only [normalizeListWith, normalizeListWithAux]
  cases f v with
  | error e => simp [Bind.bind, Except.bind]
  | ok h =>
    simp only [Bind.bind, Except.bind]
    rw [normalizeListWithAux_acc rest (#[].push h)]
    cases normalizeListWithAux f #[] rest with
    | error e => simp [Except.map]
    | ok tail =>
      simp only [Except.map, pure, Except.pure, Except.ok.injEq]
      apply Array.ext'
      simp

theorem normalizeFieldsWithAux_acc {f : Ty → GoValue → Except Stop GoValue} :
    ∀ (defs : List FieldDef) (vals : List (String × GoValue)) (acc : Array (String × GoValue)),
      normalizeFieldsWithAux f acc defs vals
        = (normalizeFieldsWithAux f #[] defs vals).map (acc ++ ·) := by
  intro defs
  induction defs with
  | nil =>
    intro vals acc
    simp [normalizeFieldsWithAux, pure, Except.pure, Except.map]
  | cons fd rest ih =>
    intro vals acc
    cases vals with
    | nil => simp [normalizeFieldsWithAux, pure, Except.pure, Except.map]
    | cons p valRest =>
      obtain ⟨actual, v⟩ := p
      simp only [normalizeFieldsWithAux]
      split
      · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw,
          Except.map]
      · simp only [Bind.bind, Except.bind]
        cases f fd.typ v with
        | error e => simp [Except.map]
        | ok h =>
          simp only
          rw [ih valRest (acc.push (fd.name, h)), ih valRest (#[].push (fd.name, h))]
          cases normalizeFieldsWithAux f #[] rest valRest with
          | error e => simp [Except.map]
          | ok tail =>
            simp only [Except.map, Except.ok.injEq]
            apply Array.ext'
            simp

theorem normalizeFieldsWith_nil_left {f : Ty → GoValue → Except Stop GoValue}
    {vals : List (String × GoValue)} : normalizeFieldsWith f [] vals = pure #[] := by
  cases vals <;> rfl

theorem normalizeFieldsWith_nil_right {f : Ty → GoValue → Except Stop GoValue}
    {defs : List FieldDef} : normalizeFieldsWith f defs [] = pure #[] := by
  cases defs <;> rfl

theorem normalizeFieldsWith_cons {f : Ty → GoValue → Except Stop GoValue} {fd : FieldDef}
    {defs : List FieldDef} {actual : String} {v : GoValue} {vals : List (String × GoValue)} :
    normalizeFieldsWith f (fd :: defs) ((actual, v) :: vals) = do
      if actual != fd.name then
        stuck s!"struct value field mismatch: expected {fd.name}, got {actual}"
      let head ← f fd.typ v
      let tail ← normalizeFieldsWith f defs vals
      return #[(fd.name, head)] ++ tail := by
  simp only [normalizeFieldsWith, normalizeFieldsWithAux]
  split
  · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
  · simp only [Bind.bind, Except.bind, pure, Except.pure]
    cases f fd.typ v with
    | error e => rfl
    | ok h =>
      simp only
      rw [normalizeFieldsWithAux_acc defs vals (#[].push (fd.name, h))]
      cases normalizeFieldsWithAux f #[] defs vals with
      | error e => simp [Except.map]
      | ok tail =>
        simp only [Except.map, Except.ok.injEq]
        apply Array.ext'
        simp


/-! #### Idempotence: the normalizer's output is self-normal (C1 S1) -/

theorem isNormalListWith_iff {f : GoValue → Bool} :
    ∀ l : List GoValue, isNormalListWith f l = true ↔ ∀ x ∈ l, f x = true := by
  intro l
  induction l with
  | nil => simp [isNormalListWith]
  | cons x rest ih => simp [isNormalListWith, ih]

theorem IntKind.normalize_idem (kind : IntKind) (v : Int) :
    kind.normalize (kind.normalize v) = kind.normalize v := by
  unfold IntKind.normalize
  cases hb : kind.bits? with
  | none => rfl
  | some bits =>
    simp only
    have hm : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
    have hw0 : 0 ≤ v % 2 ^ bits := Int.emod_nonneg v (Int.ne_of_gt hm)
    have hwlt : v % 2 ^ bits < 2 ^ bits := Int.emod_lt_of_pos v hm
    have hself : v % 2 ^ bits % 2 ^ bits = v % 2 ^ bits := Int.emod_eq_of_lt hw0 hwlt
    cases kind.signed with
    | false => simp [hself]
    | true =>
      simp only [ite_true]
      split
      · rename_i hge
        rw [Int.sub_emod_right, hself]
        simp [hge]
      · rename_i hlt
        rw [hself]
        simp [hlt]

theorem FloatKind.normalizeBits_idem (kind : FloatKind) (b : Nat) :
    kind.normalizeBits (kind.normalizeBits b) = kind.normalizeBits b := by
  unfold FloatKind.normalizeBits
  exact Nat.mod_mod _ _

/-- Pointwise relation on two lists of equal length (core has no `Forall₂`). -/
inductive Pointwise {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pointwise R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} :
      R a b → Pointwise R l l' → Pointwise R (a :: l) (b :: l')

theorem Pointwise.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Pointwise R l l' → l.length = l'.length := by
  intro l l' h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- `normalizeListWith`'s output, characterized pointwise. -/
theorem normalizeListWith_ok {f : GoValue → Except Stop GoValue} :
    ∀ {l : List GoValue} {r : Array GoValue},
      normalizeListWith f l = .ok r →
      ∃ ws : List GoValue, r = ws.toArray ∧ Pointwise (fun v w => f v = .ok w) l ws := by
  intro l
  induction l with
  | nil =>
    intro r h
    rw [normalizeListWith_nil] at h
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, Pointwise.nil⟩
  | cons v rest ih =>
    intro r h
    rw [normalizeListWith_cons] at h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨w, hw, tail, htail, hr⟩ := h
    obtain ⟨ws, rfl, hall⟩ := ih htail
    exact ⟨w :: ws, by simp [← hr], Pointwise.cons hw hall⟩

theorem isNormalListWith_of_pointwise {g : GoValue → Bool} {f : GoValue → Except Stop GoValue}
    (hfg : ∀ v w, f v = .ok w → g w = true) :
    ∀ {l ws : List GoValue}, Pointwise (fun v w => f v = .ok w) l ws →
      isNormalListWith g ws = true := by
  intro l ws h
  induction h with
  | nil => rfl
  | cons hvw _ ih =>
    simp only [isNormalListWith, Bool.and_eq_true]
    exact ⟨hfg _ _ hvw, ih⟩

/-- The field normalizer's output: same names in order, each value the
normalizer's output at the declared field type; length = the shorter list. -/
theorem normalizeFieldsWith_isNormal {f : Ty → GoValue → Except Stop GoValue}
    {g : Ty → GoValue → Bool} (hfg : ∀ ty v w, f ty v = .ok w → g ty w = true) :
    ∀ {defs : List FieldDef} {vals : List (String × GoValue)} {r : Array (String × GoValue)},
      normalizeFieldsWith f defs vals = .ok r → defs.length = vals.length →
      isNormalFieldsWith g defs r.toList = true ∧ r.size = defs.length := by
  intro defs
  induction defs with
  | nil =>
    intro vals r h hlen
    cases vals with
    | nil =>
      rw [normalizeFieldsWith_nil_left] at h
      simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hlen
  | cons fd rest ih =>
    intro vals r h hlen
    cases vals with
    | nil => simp at hlen
    | cons p valRest =>
      obtain ⟨actual, v⟩ := p
      rw [normalizeFieldsWith_cons] at h
      split at h
      · simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      · rename_i hname
        simp only [Bind.bind, Except.bind] at h
        cases hv : f fd.typ v with
        | error e => rw [hv] at h; simp at h
        | ok w =>
          rw [hv] at h
          simp only at h
          cases htail : normalizeFieldsWith f rest valRest with
          | error e => rw [htail] at h; simp at h
          | ok tail =>
            rw [htail] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            obtain ⟨hnorm, hsize⟩ := ih htail (by simpa using hlen)
            refine ⟨?_, by simp [hsize, Nat.add_comm]⟩
            simp only [Array.toList_append, List.singleton_append,
              isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨trivial, hfg _ _ _ hv⟩, hnorm⟩

/-- THE TYPE LAYER: the normalizer's output is self-normal, given the same
for the two `.defined` callbacks. -/
theorem normalizeValueForTyTy_isNormal {f : TypeIdx → GoValue → Except Stop GoValue}
    {g : TypeIdx → GoValue → Bool}
    (hfg : ∀ i v w, f i v = .ok w → g i w = true) :
    ∀ {ty : Ty} {v w : GoValue},
      normalizeValueForTyTy f ty v = .ok w → isNormalForTyTy g ty w = true := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v w h
    cases v
    case array values =>
      simp only [normalizeValueForTyTy] at h
      by_cases hsz : values.size = length
      · simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
        cases hl : normalizeListWith (normalizeValueForTyTy f elem) values.toList with
        | error e => rw [hl] at h; simp [Functor.map, Except.map] at h
        | ok arr =>
          rw [hl] at h
          simp only [Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          obtain ⟨ws, rfl, hall⟩ := normalizeListWith_ok hl
          simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨?_, ?_⟩
          · have := hall.length_eq
            simp only [Array.length_toList] at this
            simp [← this, hsz]
          · simpa using isNormalListWith_of_pointwise (fun v w hvw => ih hvw) hall
      · have hne : (values.size != length) = true := by simpa using hsz
        simp [hne, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
      MonadExceptOf.throw])
  | leaf ty hne =>
    intro v w h
    cases ty with
    | array => exact absurd rfl (hne _ _)
    | int kind =>
      cases v
      case int value k =>
        simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [isNormalForTyTy, IntKind.normalize_idem]
      all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
        MonadExceptOf.throw])
    | float kind =>
      cases v
      case float bits k =>
        simp only [normalizeValueForTyTy] at h
        split at h
        · rename_i hk
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hkk : kind = k := by
            cases kind <;> cases k <;> first | rfl | exact absurd hk (by decide)
          subst hkk
          simp [isNormalForTyTy, FloatKind.normalizeBits_idem]
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
        MonadExceptOf.throw])
    | interface _ =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]
    | funcType params results _ =>
      cases v
      case funcVal fid captured =>
        simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [isNormalForTyTy]
      case nil =>
        simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [isNormalForTyTy]
      all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
        MonadExceptOf.throw])
    | defined i => exact hfg _ _ _ h
    | unsupported _ =>
      exact absurd h (by simp [normalizeValueForTyTy, unsupported, throw, throwThe,
        MonadExceptOf.throw])
    | bool =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]
    | string =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]
    | slice _ =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]
    | map _ _ =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]
    | chan _ _ =>
      cases v
      case chan cv =>
        simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [isNormalForTyTy]
      case nil =>
        simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [isNormalForTyTy]
      all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
        MonadExceptOf.throw])
    | sync kind =>
      cases v
      case syncData p =>
        simp only [normalizeValueForTyTy] at h
        split at h
        · rename_i hk
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simpa [isNormalForTyTy] using hk
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      all_goals exact absurd h (by simp [normalizeValueForTyTy, stuck, throw, throwThe,
        MonadExceptOf.throw])
    | pointer _ =>
      simp only [normalizeValueForTyTy, pure, Except.pure, Except.ok.injEq] at h
      simp [isNormalForTyTy]

/-- THE INDEX LAYER, in lockstep: the output of the index descent at
`bound` is normal at the same `bound`. -/
theorem normalizeValueForTyAt_isNormal (types : TypeEnv) :
    ∀ (bound : Nat) {i : TypeIdx} {v w : GoValue},
      normalizeValueForTyAt types bound i v = .ok w →
      isNormalForTyAt types bound i w = true := by
  intro bound
  induction bound with
  | zero =>
    intro i v w h
    exact absurd h (by simp [normalizeValueForTyAt, typeIndexExhausted, unsupported, throw,
      throwThe, MonadExceptOf.throw])
  | succ n ih =>
    intro i v w h
    simp only [normalizeValueForTyAt] at h
    cases hlook : types[i]? with
    | none =>
      rw [hlook] at h
      exact absurd h (by simp [unsupported, throw, throwThe, MonadExceptOf.throw])
    | some e =>
      rw [hlook] at h
      obtain ⟨name, td⟩ := e
      cases td with
      | struct fields =>
        simp only [normalizeStructValueWith] at h
        cases v
        case struct actual fieldsValue =>
          simp only [isNormalForTyAt, hlook]
          by_cases hact : actual = name
          · subst hact
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind,
              Except.bind] at h
            by_cases hsz : fieldsValue.size = fields.size
            · simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
              cases hf : normalizeFieldsWith (normalizeValueForTyTy (normalizeValueForTyAt types n))
                  fields.toList fieldsValue.toList with
              | error e => rw [hf] at h; simp [Functor.map, Except.map] at h
              | ok arr =>
                rw [hf] at h
                simp only [Functor.map, Except.map, Except.ok.injEq] at h
                subst h
                obtain ⟨hnorm, hsize⟩ := normalizeFieldsWith_isNormal
                  (f := normalizeValueForTyTy (normalizeValueForTyAt types n))
                  (g := isNormalForTyTy (isNormalForTyAt types n))
                  (fun ty v w hvw => normalizeValueForTyTy_isNormal
                    (f := normalizeValueForTyAt types n) (g := isNormalForTyAt types n)
                    (fun _ _ _ hh => ih hh) hvw)
                  hf (by simp [hsz])
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨trivial, by simpa using hsize⟩, hnorm⟩
            · have hne : (fieldsValue.size != fields.size) = true := by simpa using hsz
              simp [hne, stuck, throw, throwThe, MonadExceptOf.throw] at h
          · -- tag mismatch: the empty-struct escape yields `.struct name #[]`, else stuck
            have hne : (actual != name) = true := by simpa using hact
            simp only [hne, ↓reduceIte] at h
            split at h
            · rename_i hesc
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hfe : fields.isEmpty = true := by
                simp only [emptyStructAssignable, Bool.and_eq_true] at hesc
                exact hesc.1.2
              have hsz0 : fields.size = 0 := by simpa [Array.isEmpty] using hfe
              have hnil : fields.toList = [] :=
                List.eq_nil_of_length_eq_zero (by simpa using hsz0)
              simp [hsz0, hnil, isNormalFieldsWith]
            · simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
        all_goals exact absurd h (by simp [stuck, throw, throwThe, MonadExceptOf.throw])
      | defined target =>
        try dsimp only at h
        simp only [isNormalForTyAt, hlook]
        exact normalizeValueForTyTy_isNormal (f := normalizeValueForTyAt types n)
          (g := isNormalForTyAt types n) (fun _ _ _ hh => ih hh) h
      | opaqueDecl _ =>
        exact absurd h (by simp [unsupported, throw, throwThe, MonadExceptOf.throw])
      | interfaceDef _ =>
        exact absurd h (by simp [unsupported, throw, throwThe, MonadExceptOf.throw])

/-- The wrapper: `normalizeValueForTy` is self-normal at `ctx.types`. -/
theorem normalizeValueForTy_isNormal (ctx : ProgramCtx) {ty : Ty} {v w : GoValue}
    (h : normalizeValueForTy ctx ty v = .ok w) : isNormalForTy ctx.types ty w = true := by
  unfold normalizeValueForTy at h
  unfold isNormalForTy
  exact normalizeValueForTyTy_isNormal (f := normalizeValueForTyAt ctx.types ctx.types.size)
    (g := isNormalForTyAt ctx.types ctx.types.size)
    (fun _ _ _ hh => normalizeValueForTyAt_isNormal _ _ hh) h



/-- What the structural search finds: in range, the name matches, no
earlier position (from the start index) does. -/
theorem fieldIdxFrom_spec (fields : Array (String × GoValue)) (f : String) :
    ∀ (fuel i k : Nat), fieldIdxFrom fields f fuel i = some k →
      i ≤ k ∧ ∃ hk : k < fields.size, fields[k].1 = f ∧
        ∀ j (hj : j < k), i ≤ j → (fields[j]'(Nat.lt_trans hj hk)).1 ≠ f := by
  intro fuel
  induction fuel with
  | zero => intro i k h; simp [fieldIdxFrom] at h
  | succ n ih =>
    intro i k h
    simp only [fieldIdxFrom] at h
    cases hget : fields[i]? with
    | none => simp [hget] at h
    | some p =>
      obtain ⟨name, x⟩ := p
      simp only [hget] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        subst h
        have hlt := (Array.getElem?_eq_some_iff.mp hget).1
        refine ⟨Nat.le_refl _, hlt, ?_, fun j hj hij => absurd hj (Nat.not_lt.mpr hij)⟩
        have : fields[i] = (name, x) := (Array.getElem?_eq_some_iff.mp hget).2
        rw [this]
        simpa using heq
      · rename_i hne
        obtain ⟨hle, hk, hname, hbefore⟩ := ih (i + 1) k h
        refine ⟨by omega, hk, hname, fun j hj hij => ?_⟩
        by_cases hji : j = i
        · subst hji
          have : fields[j] = (name, x) := (Array.getElem?_eq_some_iff.mp hget).2
          rw [this]
          simpa using hne
        · exact hbefore j hj (by omega)

theorem fieldIdx?_spec (fields : Array (String × GoValue)) (f : String) (k : Nat)
    (h : fieldIdx? fields f = some k) :
    ∃ hk : k < fields.size, fields[k].1 = f ∧
      ∀ j (hj : j < k), (fields[j]'(Nat.lt_trans hj hk)).1 ≠ f := by
  obtain ⟨_, hk, hname, hbefore⟩ := fieldIdxFrom_spec fields f _ _ _ h
  exact ⟨hk, hname, fun j hj => hbefore j hj (Nat.zero_le _)⟩


/-! ## StateWf projections -/

theorem StateWf.heap_le {σ : Store} (h : StateWf ctx σ) :
    Heap.locSup σ.heap ≤ σ.nextAddr := h.1

/-- The normal-form half (C1 S1, D3). -/
theorem StateWf.normal {σ : Store} (h : StateWf ctx σ) : HeapNormal ctx σ := h.2

-- `StateWf.funcs_le` (the stored-function-body half of the old bound) is
-- RETIRED with B7: the store carries no functions; `Func.locSup_eq_zero`
-- is what every former consumer needs.

theorem StateWf.mk' {σ : Store} (h1 : Heap.locSup σ.heap ≤ σ.nextAddr)
    (h2 : HeapNormal ctx σ) : StateWf ctx σ := ⟨h1, h2⟩

/-! ## Value coercion inversions -/

theorem valueAsLoc_locSup {v : GoValue} {l : Loc} (h : valueAsLoc v = .ok l) :
    Loc.locSup l ≤ GoValue.locSup v := by
  cases v <;> simp_all [valueAsLoc, GoValue.locSup]

theorem valueAsSlice_locSup {v : GoValue} {sl : SliceValue}
    (h : valueAsSlice v = .ok sl) : optLocSup sl.base ≤ GoValue.locSup v := by
  cases v <;> simp_all [valueAsSlice, GoValue.locSup]

theorem valueAsMap_locSup {v : GoValue} {m : MapValue}
    (h : valueAsMap v = .ok m) : optLocSup m.base ≤ GoValue.locSup v := by
  cases v <;> simp_all [valueAsMap, GoValue.locSup]

/-! ## Slice-shape operations -/

theorem sliceIndexLoc_locSup {sl : SliceValue} {i : Int} {l : Loc}
    (h : sliceIndexLoc sl i = .ok l) : Loc.locSup l ≤ optLocSup sl.base := by
  unfold sliceIndexLoc at h
  try simp only [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  obtain ⟨n, hn, h⟩ := h
  split at h
  · split at h
    · rename_i base heq
      simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [Loc.locSup, optLocSup, heq]
    · simp at h
  · unfold indexOutOfRangePanic at h
    split at h <;> simp at h

theorem sliceFromSlice_locSup {sl : SliceValue} {lo hi : Int} {m : Option Int}
    {v : GoValue} (h : sliceFromSlice sl lo hi m = .ok v) :
    GoValue.locSup v ≤ optLocSup sl.base := by
  unfold sliceFromSlice at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨d, -, hv⟩ := h
    subst hv
    simp [GoValue.locSup]
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨mx, -, d, -, hv⟩ := h
    subst hv
    simp [GoValue.locSup]

theorem sliceFromArray_locSup {base : Loc} {length : Nat} {lo hi : Int}
    {m : Option Int} {v : GoValue} (h : sliceFromArray base length lo hi m = .ok v) :
    GoValue.locSup v ≤ Loc.locSup base := by
  unfold sliceFromArray at h
  split at h
  · try simp only [bind_eq_ok] at h
    obtain ⟨⟨lo', hi'⟩, -, hv⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq] at hv
    subst hv
    simp [GoValue.locSup, optLocSup]
  · try simp only [bind_eq_ok] at h
    obtain ⟨mx, -, ⟨lo', hi'⟩, -, hv⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq] at hv
    subst hv
    simp [GoValue.locSup, optLocSup]

theorem stringSlice_locSup {gs : GoString} {lo hi : Int} {m : Option Int}
    {v : GoValue} (h : stringSlice gs lo hi m = .ok v) :
    GoValue.locSup v = 0 := by
  unfold stringSlice at h
  split at h
  · simp [Bind.bind, Except.bind] at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨p, _, hv⟩ := h
    subst hv
    rfl

/-! ## Heap access -/

theorem loadLoc_locSup {s : Store} :
    ∀ {l : Loc} {v : GoValue}, loadLoc ctx s l = .ok v →
      GoValue.locSup v ≤ Heap.locSup s.heap := by
  intro l
  induction l with
  | base a =>
    intro v h
    unfold loadLoc at h
    split at h
    · rename_i ty v₀ hcell
      simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Heap.lookup_locSup hcell
    all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  | field b tid fname ih =>
    intro v h
    unfold loadLoc at h
    try simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · rename_i actual fields
      split at h
      · simp [Bind.bind, Except.bind] at h
      · split at h
        · rename_i w hw
          simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq] at h
          subst h
          refine Nat.le_trans (StructFields.lookup_locSup hw) ?_
          simpa [GoValue.locSup] using ih hbv
        · simp [Bind.bind, Except.bind] at h
    · simp at h
  | index b i ih =>
    intro v h
    unfold loadLoc at h
    try simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · rename_i values
      refine Nat.le_trans (arrayGet_locSup h) ?_
      simpa [GoValue.locSup] using ih hbv
    · simp at h

/-! ## Array-update sup lemmas -/

/-- An index-target location is bounded by its base value and the heap
(the pointer-to-array/slice arms read a cell). Shared by the
`indexAddr` strict-op WF case and `storeTarget`'s preservation. -/
theorem indexTargetLoc_locSup {s : Store} {b i : GoValue} {l : Loc}
    (h : indexTargetLoc ctx s b i = .ok l) :
    Loc.locSup l ≤ max (GoValue.locSup b) (Heap.locSup s.heap) := by
  unfold indexTargetLoc at h
  try simp only [bind_eq_ok] at h
  obtain ⟨iv, hiv, h⟩ := h
  split at h
  · -- slice base
    rename_i sl
    have h2 := sliceIndexLoc_locSup h
    have h3 : GoValue.locSup (GoValue.slice sl) = optLocSup sl.base := rfl
    omega
  · -- nil base: the BUG-038 panic arm — no `.ok` result
    simp [GoCore.panic, throw, throwThe, MonadExceptOf.throw] at h
  · -- addr base
    rename_i baseLoc
    try simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · -- array element
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      have h3 : GoValue.locSup (GoValue.addr baseLoc) = Loc.locSup baseLoc := rfl
      have h4 : Loc.locSup (Loc.index baseLoc iv) = Loc.locSup baseLoc := rfl
      omega
    · -- slice cell
      rename_i sl
      have h2 := sliceIndexLoc_locSup h
      have h4 := loadLoc_locSup hbv
      have h5 : GoValue.locSup (GoValue.slice sl) = optLocSup sl.base := rfl
      omega
    · simp [Bind.bind, Except.bind] at h
  · simp at h


theorem goValueEntriesSup_push {arr : Array (Nat × GoValue × GoValue)}
    {p : Nat × GoValue × GoValue} :
    goValueEntriesSup (arr.push p).toList
      = max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) := by
  simp [goValueEntriesSup_eq, Array.toList_push, supBy_append, supBy]

theorem goValueEntriesSup_mem {arr : List (Nat × GoValue × GoValue)}
    {p : Nat × GoValue × GoValue} (h : p ∈ arr) :
    max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2) ≤ goValueEntriesSup arr := by
  rw [goValueEntriesSup_eq]
  exact supBy_mem (f := fun p => max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) h

theorem goValueEntriesSup_setIfInBounds {arr : Array (Nat × GoValue × GoValue)} {i : Nat}
    {p : Nat × GoValue × GoValue} :
    goValueEntriesSup (arr.setIfInBounds i p).toList
      ≤ max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) := by
  simp only [goValueEntriesSup_eq]
  rw [Array.toList_setIfInBounds]
  refine supBy_le_iff.mpr fun a ha => ?_
  rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
  · exact Nat.le_trans
      (supBy_mem (f := fun p => max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) hmem)
      (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem goValueEntriesSup_eraseIdx! {arr : Array (Nat × GoValue × GoValue)} {i : Nat} :
    goValueEntriesSup (arr.eraseIdx! i).toList
      ≤ goValueEntriesSup arr.toList := by
  simp only [goValueEntriesSup_eq]
  unfold Array.eraseIdx!
  split
  · rw [Array.toList_eraseIdx]
    exact supBy_le_of_subset fun a ha => List.mem_of_mem_eraseIdx ha
  · -- out of range: `panic!` computes to `default = #[]`
    rw [show (panicWithPosWithDecl "Init.Data.Array.Basic" "Array.eraseIdx!" 1820 47
        "invalid index" : Array (Nat × GoValue × GoValue)) = #[] from rfl]
    simp [supBy]

theorem goValueEntriesSup_eraseIdx {arr : Array (Nat × GoValue × GoValue)} {i : Nat}
    {h : i < arr.size} :
    goValueEntriesSup ((arr.eraseIdx i h).toList)
      ≤ goValueEntriesSup arr.toList := by
  simp only [goValueEntriesSup_eq]
  rw [Array.toList_eraseIdx]
  exact supBy_le_of_subset fun a ha => List.mem_of_mem_eraseIdx ha

theorem goValueListSup_setIfInBounds {arr : Array GoValue} {i : Nat} {x : GoValue} :
    goValueListSup (arr.setIfInBounds i x).toList
      ≤ max (goValueListSup arr.toList) (GoValue.locSup x) := by
  simp only [goValueListSup_eq]
  rw [Array.toList_setIfInBounds]
  refine supBy_le_iff.mpr fun a ha => ?_
  rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
  · exact Nat.le_trans (supBy_mem hmem) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-! ## `set!` bounds for entry and value arrays (the map payload's RMW) -/

theorem goValueEntriesSup_set! {arr : Array (Nat × GoValue × GoValue)} {i : Nat}
    {p : Nat × GoValue × GoValue} :
    goValueEntriesSup (arr.set! i p).toList
      ≤ max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.2.1) (GoValue.locSup p.2.2)) := by
  rw [Array.set!]
  exact goValueEntriesSup_setIfInBounds

theorem goValueListSup_set! {arr : Array GoValue} {i : Nat} {x : GoValue} :
    goValueListSup (arr.set! i x).toList
      ≤ max (goValueListSup arr.toList) (GoValue.locSup x) := by
  rw [Array.set!]
  exact goValueListSup_setIfInBounds

/-! ## `Store.updateCell`: the one root-cell write (A3) -/

theorem Store.updateCell_shape {σ σ' : Store} {a : Addr}
    {f : HeapCell → Except Stop HeapCell} (h : σ.updateCell a f = .ok σ') :
    σ'.nextAddr = σ.nextAddr
      ∧ ∃ cell cell', Heap.lookup σ.heap (.base a) = some cell ∧ f cell = .ok cell'
          ∧ Heap.locSup σ'.heap ≤ max (Heap.locSup σ.heap) (HeapCell.locSup cell') := by
  obtain ⟨i⟩ := a
  unfold Store.updateCell at h
  split at h
  · rename_i hi
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨cell', hf, hσ⟩ := h
    subst hσ
    refine ⟨by simp [Store.nextAddr], σ.heap[i], cell', ?_, hf,
      Heap.set_locSup (hi := hi)⟩
    simp [Heap.lookup, Array.getElem?_eq_getElem hi]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `storeLoc`: shape and preservation (C1 S1: the root-first in-place write) -/

/-- `Array.modifyM` in `Except`, unfolded once (the reference body of the
`implemented_by` primitive): a success at an in-range index is `set` of the
callback's output. -/
theorem Array.modifyM_ok_iff {α : Type} (xs : Array α) (i : Nat) (hi : i < xs.size)
    (f : α → Except Stop α) (ys : Array α) :
    xs.modifyM i f = .ok ys ↔ ∃ v, f xs[i] = .ok v ∧ ys = xs.set i v hi := by
  unfold Array.modifyM
  rw [dif_pos hi]
  constructor
  · intro h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨v, hv, h⟩ := h
    exact ⟨v, hv, h.symm⟩
  · rintro ⟨v, hv, rfl⟩
    dsimp only
    rw [hv]
    rfl

theorem fieldIdxFrom_lt (fields : Array (String × GoValue)) (f : String) :
    ∀ (fuel i k : Nat), fieldIdxFrom fields f fuel i = some k → k < fields.size := by
  intro fuel
  induction fuel with
  | zero => intro i k h; simp [fieldIdxFrom] at h
  | succ n ih =>
    intro i k h
    simp only [fieldIdxFrom] at h
    cases hget : fields[i]? with
    | none => simp [hget] at h
    | some p =>
      obtain ⟨n, x⟩ := p
      simp only [hget] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact (Array.getElem?_eq_some_iff.mp hget).1
      · exact ih (i + 1) k h

theorem fieldIdx?_lt {fields : Array (String × GoValue)} {f : String} {k : Nat}
    (h : fieldIdx? fields f = some k) : k < fields.size :=
  fieldIdxFrom_lt fields f _ _ _ h

theorem goValueListSup_set {arr : Array GoValue} {k : Nat} (hk : k < arr.size) {x : GoValue} :
    goValueListSup (arr.set k x hk).toList ≤ max (goValueListSup arr.toList) (GoValue.locSup x) := by
  rw [goValueListSup_eq, goValueListSup_eq, supBy_le_iff]
  intro a ha
  rw [Array.toList_set] at ha
  rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
  · exact Nat.le_trans (supBy_mem hmem) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem goValueFieldsSup_set {arr : Array (String × GoValue)} {k : Nat} (hk : k < arr.size)
    {p : String × GoValue} :
    goValueFieldsSup (arr.set k p hk).toList
      ≤ max (goValueFieldsSup arr.toList) (GoValue.locSup p.2) := by
  rw [goValueFieldsSup_eq, goValueFieldsSup_eq, supBy_le_iff]
  intro a ha
  rw [Array.toList_set] at ha
  rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
  · exact Nat.le_trans (supBy_mem (f := fun q : String × GoValue => GoValue.locSup q.2) hmem)
      (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem goValueListSup_getElem {arr : Array GoValue} {k : Nat} (hk : k < arr.size) :
    GoValue.locSup arr[k] ≤ goValueListSup arr.toList := by
  rw [goValueListSup_eq]
  have hmem : arr[k] ∈ arr.toList := by
    rw [← Array.getElem_toList hk]; exact List.getElem_mem _
  exact supBy_mem hmem

theorem goValueFieldsSup_getElem {arr : Array (String × GoValue)} {k : Nat} (hk : k < arr.size) :
    GoValue.locSup arr[k].2 ≤ goValueFieldsSup arr.toList := by
  rw [goValueFieldsSup_eq]
  have hmem : arr[k] ∈ arr.toList := by
    rw [← Array.getElem_toList hk]; exact List.getElem_mem _
  exact supBy_mem (f := fun q : String × GoValue => GoValue.locSup q.2) hmem

/-- The write path's index re-check (`arrayIndexNatFormed`, C1 S3): the same
three facts on success as `arrayIndexNat_spec` below; its failure is `.internal`. -/
theorem arrayIndexNatFormed_spec {values : Array GoValue} {i : Int} {k : Nat}
    (h : arrayIndexNatFormed values i = .ok k) : 0 ≤ i ∧ k = i.toNat ∧ k < values.size := by
  unfold arrayIndexNatFormed at h
  split at h
  · rename_i hc
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact ⟨hc.1, rfl, hc.2⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The root-first write never invents locations: the new root is bounded
by the old root and the incoming leaf. -/
theorem writeAt_locSup :
    ∀ {path : List PathStep} {b : Nat} {ty : Ty} {root v root' : GoValue},
      writeAt ctx b ty root path v = .ok root' →
      GoValue.locSup root' ≤ max (GoValue.locSup root) (GoValue.locSup v) := by
  intro path
  induction path with
  | nil =>
    intro b ty root v root' h
    simp only [writeAt] at h
    exact Nat.le_trans
      (normalizeValueForTyTy_locSup (fun _ _ _ hh => normalizeValueForTyAt_locSup _ _ hh) h)
      (Nat.le_max_right _ _)
  | cons step rest ih =>
    intro b ty root v root' h
    cases step with
    | field tid f =>
      cases root with
      | struct actual fields =>
        simp only [writeAt] at h
        by_cases hc : (actual != tid && !structTagCompatible ctx actual tid) = true
        · simp [hc, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
        · have hc' : (actual != tid && !structTagCompatible ctx actual tid) = false := by
            simpa using hc
          simp only [hc', Bool.false_eq_true, ↓reduceIte, pure_bind] at h
          split at h
          · rename_i k hk
            have hklt := fieldIdx?_lt hk
            try simp only [bind_eq_ok] at h
            obtain ⟨⟨fty, b'⟩, _, h⟩ := h
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
            obtain ⟨fields', hmod, rfl⟩ := h
            obtain ⟨q, hq, rfl⟩ := (Array.modifyM_ok_iff fields k hklt _ fields').mp hmod
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hq
            obtain ⟨old', hold', rfl⟩ := hq
            have h1 := ih hold'
            have h2 := goValueFieldsSup_set (arr := fields) hklt (p := (fields[k].1, old'))
            have h3 := goValueFieldsSup_getElem (arr := fields) hklt
            simp only [GoValue.locSup] at h2 ⊢
            omega
          · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      | _ =>
        simp only [writeAt] at h
        split at h <;> simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    | index i =>
      cases root with
      | array values =>
        simp only [writeAt, bind_eq_ok] at h
        obtain ⟨k, hk, ⟨ety, b'⟩, _, values', hmod, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        have hklt : k < values.size := (arrayIndexNatFormed_spec hk).2.2
        obtain ⟨old', hold', rfl⟩ := (Array.modifyM_ok_iff values k hklt _ values').mp hmod
        have h1 := ih hold'
        have h2 := goValueListSup_set (arr := values) hklt (x := old')
        have h3 := goValueListSup_getElem (arr := values) hklt
        simp only [GoValue.locSup] at h2 ⊢
        omega
      | _ =>
        simp only [writeAt] at h
        split at h <;> simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem storeLoc_shape {σ : Store} :
    ∀ {l : Loc} {v : GoValue} {σ' : Store}, storeLoc ctx σ l v = .ok σ' →
      σ'.nextAddr = σ.nextAddr
        ∧ Heap.locSup σ'.heap
            ≤ max (Heap.locSup σ.heap) (max (Loc.locSup l) (GoValue.locSup v)) := by
  intro l v σ' h
  unfold storeLoc at h
  -- ONE root write (A3): the root cell is rewritten in place at its
  -- declared type; payload cells refuse; out of range refuses (BUG-085).
  obtain ⟨h4, cell, cell', hcell, hf, hsup⟩ := Store.updateCell_shape h
  refine ⟨h4, ?_⟩
  have hcb := Heap.lookup_locSup hcell
  cases cell with
  | value ty root =>
    simp only [map_eq_ok] at hf
    obtain ⟨root', hw, rfl⟩ := hf
    have hb := writeAt_locSup hw
    have hc : HeapCell.locSup (.value ty root') = GoValue.locSup root' := rfl
    have hc0 : HeapCell.locSup (.value ty root) = GoValue.locSup root := rfl
    omega
  | mapPayload _ _ =>
    revert hf
    cases (Loc.rootPath l).2 <;> simp [stuck, throw, throwThe, MonadExceptOf.throw]
  | chanPayload _ _ _ =>
    revert hf
    cases (Loc.rootPath l).2 <;> simp [stuck, throw, throwThe, MonadExceptOf.throw]

/-! ## `HeapNormal` preservation (C1 S1, D3) -/

theorem HeapNormal.cell_of {σ : Store} (h : HeapNormal ctx σ) {i : Nat} (hi : i < σ.heap.size) :
    HeapCell.normal ctx.types σ.heap[i] = true := by
  unfold HeapNormal Heap.normalB at h
  rw [List.all_eq_true] at h
  exact h _ (by rw [← Array.getElem_toList hi]; exact List.getElem_mem _)

theorem HeapNormal.lookup_of {σ : Store} (h : HeapNormal ctx σ) {a : Addr} {c : HeapCell}
    (hl : Heap.lookup σ.heap (.base a) = some c) : HeapCell.normal ctx.types c = true := by
  obtain ⟨i⟩ := a
  simp only [Heap.lookup] at hl
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hl
  exact HeapNormal.cell_of h hi

/-- A root-cell update by a normal-preserving cell function keeps the heap normal. -/
theorem HeapNormal.of_updateCell {σ σ' : Store} {a : Addr} {f : HeapCell → Except Stop HeapCell}
    (h : HeapNormal ctx σ) (hst : σ.updateCell a f = .ok σ')
    (hf : ∀ cell cell', Heap.lookup σ.heap (.base a) = some cell → f cell = .ok cell' →
      HeapCell.normal ctx.types cell' = true) :
    HeapNormal ctx σ' := by
  obtain ⟨i⟩ := a
  unfold Store.updateCell at hst
  split at hst
  · rename_i hi
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hst
    obtain ⟨cell', hcell', rfl⟩ := hst
    have hnew : HeapCell.normal ctx.types cell' = true :=
      hf σ.heap[i] cell' (by simp [Heap.lookup, Array.getElem?_eq_getElem hi]) hcell'
    unfold HeapNormal Heap.normalB
    rw [List.all_eq_true]
    intro c hc
    simp only [Array.toList_set] at hc
    rcases List.mem_or_eq_of_mem_set hc with hmem | rfl
    · unfold HeapNormal Heap.normalB at h
      rw [List.all_eq_true] at h
      exact h c hmem
    · exact hnew
  · simp [throw, throwThe, MonadExceptOf.throw] at hst

theorem HeapNormal.of_allocCell {σ σ' : Store} {c : HeapCell} {l : Loc}
    (h : HeapNormal ctx σ) (hc : HeapCell.normal ctx.types c = true)
    (hal : σ.allocCell c = (l, σ')) : HeapNormal ctx σ' := by
  have h2 : ({ heap := σ.heap.push c } : Store) = σ' := congrArg Prod.snd hal
  subst h2
  unfold HeapNormal Heap.normalB
  rw [List.all_eq_true]
  intro x hx
  simp only [Array.toList_push] at hx
  rcases List.mem_append.mp hx with hx | hx
  · unfold HeapNormal Heap.normalB at h
    rw [List.all_eq_true] at h
    exact h x hx
  · rw [List.mem_singleton.mp hx]; exact hc

theorem HeapNormal.of_alloc {σ σ' : Store} {v : GoValue} {ty : Ty} {l : Loc}
    (h : HeapNormal ctx σ) (hal : Store.alloc ctx σ v ty = .ok (l, σ')) : HeapNormal ctx σ' := by
  unfold Store.alloc at hal
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hal
  obtain ⟨v', hv', hal⟩ := hal
  exact HeapNormal.of_allocCell h (c := .value ty v') (by
    simpa [HeapCell.normal] using normalizeValueForTy_isNormal ctx hv') hal

theorem HeapNormal.of_storeMapPayload {σ σ' : Store} {l : Loc}
    {entries : Array (Nat × GoValue × GoValue)} {nextId : Nat}
    (h : HeapNormal ctx σ) (hst : storeMapPayload σ l entries nextId = .ok σ') :
    HeapNormal ctx σ' := by
  unfold storeMapPayload at hst
  split at hst
  · exact HeapNormal.of_updateCell h hst fun cell cell' _ hf => by
      cases cell <;> simp [stuck, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hf
      subst hf; rfl
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at hst

theorem HeapNormal.of_storeChanPayload {σ σ' : Store} {l : Loc} {buf : Array GoValue}
    {capacity : Nat} {closed : Bool}
    (h : HeapNormal ctx σ) (hst : storeChanPayload σ l buf capacity closed = .ok σ') :
    HeapNormal ctx σ' := by
  unfold storeChanPayload at hst
  split at hst
  · exact HeapNormal.of_updateCell h hst fun cell cell' _ hf => by
      cases cell <;> simp [stuck, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hf
      subst hf; rfl
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at hst

/-! ## The leaf congruence for the real write -/

theorem arrayIndexNat_spec {values : Array GoValue} {i : Int} {k : Nat}
    (h : arrayIndexNat values i = .ok k) : 0 ≤ i ∧ k = i.toNat ∧ k < values.size := by
  unfold arrayIndexNat at h
  by_cases hneg : i < 0
  · simp [hneg, indexOutOfRangePanic, GoLean.GoCore.panic, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind] at h
  · by_cases hlt : i.toNat < values.size
    · simp [hneg, hlt, Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      exact ⟨Int.not_lt.mp hneg, rfl, hlt⟩
    · simp [hneg, hlt, indexOutOfRangePanic, GoLean.GoCore.panic, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at h

/-- Field names of a normal struct value align with its declaration. -/
theorem isNormalFieldsWith_names {g : Ty → GoValue → Bool} :
    ∀ {defs : List FieldDef} {vals : List (String × GoValue)},
      isNormalFieldsWith g defs vals = true →
      defs.length = vals.length ∧
        ∀ k (hk : k < defs.length) (hk' : k < vals.length), vals[k].1 = defs[k].name ∧
          g defs[k].typ vals[k].2 = true := by
  intro defs
  induction defs with
  | nil =>
    intro vals h
    cases vals with
    | nil => exact ⟨rfl, fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩
    | cons _ _ => simp [isNormalFieldsWith] at h
  | cons fd rest ih =>
    intro vals h
    cases vals with
    | nil => simp [isNormalFieldsWith] at h
    | cons p prest =>
      obtain ⟨n, v⟩ := p
      simp only [isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hn, hv⟩, hrest⟩ := h
      obtain ⟨hlen, hk⟩ := ih hrest
      refine ⟨by simp [hlen], fun k hk' hk'' => ?_⟩
      cases k with
      | zero => exact ⟨hn, hv⟩
      | succ k => exact hk k (by simpa using hk') (by simpa using hk'')

/-- The first field named `f` in an aligned struct sits at the same position
in the declaration: `FieldDef.find?` answers `defs[k]`. -/
theorem FieldDef.find?_of_first (f : String) :
    ∀ (defs : List FieldDef) (k : Nat) (hk : k < defs.length),
      defs[k].name = f → (∀ j (hj : j < k), (defs[j]'(Nat.lt_trans hj hk)).name ≠ f) →
      FieldDef.find? f defs = some defs[k] := by
  intro defs
  induction defs with
  | nil => intro k hk; simp at hk
  | cons fd rest ih =>
    intro k hk hname hbefore
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hname
      simp [FieldDef.find?, hname]
    | succ k =>
      have h0 : fd.name ≠ f := hbefore 0 (Nat.zero_lt_succ _)
      simp only [List.getElem_cons_succ] at hname
      simp only [FieldDef.find?, beq_iff_eq, h0, ↓reduceIte, List.getElem_cons_succ]
      exact ih k (by simpa using hk) hname (fun j hj => hbefore (j + 1) (Nat.succ_lt_succ hj))

theorem isNormalFieldsWith_set {f : Ty → GoValue → Bool} :
    ∀ (defs : List FieldDef) (fields : List (String × GoValue)) (k : Nat)
      (name : String) (old v : GoValue),
      fields[k]? = some (name, old) →
      isNormalFieldsWith f defs fields = true →
      (∀ fd, defs[k]? = some fd → f fd.typ v = true) →
        isNormalFieldsWith f defs (fields.set k (name, v)) = true := by
  intro defs
  induction defs with
  | nil =>
    intro fields k name old v _ h _
    cases fields with
    | nil => simp [isNormalFieldsWith]
    | cons _ _ => simp [isNormalFieldsWith] at h
  | cons fd rest ih =>
    intro fields k name old v hk h hv
    cases fields with
    | nil => simp [isNormalFieldsWith] at h
    | cons fv fvs =>
      obtain ⟨fname, fval⟩ := fv
      simp only [isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hname, hval⟩, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [List.set, isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hname, hv fd rfl⟩, hrest⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [List.set, isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hname, hval⟩, ih fvs k name old v hk hrest (fun fd' h' => hv fd' h')⟩

/-- The array component: `stepDown` through `.defined` hops reaches the
`.array` head at the bound the normality check reached it. -/
theorem writeAt_isNormal_array {rest : List PathStep} {v : GoValue} :
    ∀ {b : Nat} {ty : Ty} {values : Array GoValue} {ety : Ty} {b' : Nat} {i : Int}
      {old' : GoValue} (hklt : i.toNat < values.size),
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty (.array values) = true →
      Ty.stepDown ctx.types b ty (.index i) = .ok (ety, b') →
      writeAt ctx b' ety values[i.toNat] rest v = .ok old' →
      (∀ {b : Nat} {ty : Ty} {root v root' : GoValue},
        isNormalForTyTy (isNormalForTyAt ctx.types b) ty root = true →
        writeAt ctx b ty root rest v = .ok root' →
        isNormalForTyTy (isNormalForTyAt ctx.types b) ty root' = true) →
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty (.array (values.set i.toNat old' hklt)) = true := by
  intro b
  induction b with
  | zero =>
    intro ty values ety b' i old' hklt hn hstep hold' ih
    cases ty with
    | array length elem =>
      -- `.array n elem` at bound 0: no hop
      simp only [Ty.stepDown, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at hn ⊢
      obtain ⟨hsz, hlist⟩ := hn
      refine ⟨by simpa using hsz, ?_⟩
      rw [isNormalListWith_iff] at hlist ⊢
      intro x hx
      rw [Array.toList_set] at hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hlist x hx
      · exact ih (hlist _ (by rw [← Array.getElem_toList hklt]; exact List.getElem_mem _)) hold'
    -- The identity-normalized types (audit fix round F3): the descent returns
    -- the type itself and every value is normal there — the catch-all arm.
    | interface _ | bool | string | slice _ | map _ _ | pointer _ => simp [isNormalForTyTy]
    | _ =>
      simp [Ty.stepDown, typeIndexExhausted, unsupported, throw, throwThe,
        MonadExceptOf.throw, stuck, pure, Except.pure] at hstep
  | succ n ihb =>
    intro ty values ety b' i old' hklt hn hstep hold' ih
    cases ty with
    | array length elem =>
      simp only [Ty.stepDown, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at hn ⊢
      obtain ⟨hsz, hlist⟩ := hn
      refine ⟨by simpa using hsz, ?_⟩
      rw [isNormalListWith_iff] at hlist ⊢
      intro x hx
      rw [Array.toList_set] at hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hlist x hx
      · exact ih (hlist _ (by rw [← Array.getElem_toList hklt]; exact List.getElem_mem _)) hold'
    | defined j =>
      simp only [Ty.stepDown] at hstep
      simp only [isNormalForTyTy, isNormalForTyAt] at hn ⊢
      cases hlook : ctx.types[j]? with
      | none => rw [hlook] at hstep; simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
      | some e =>
        (try rw [hlook] at hstep); (try rw [hlook] at hn); (try rw [hlook])
        obtain ⟨name, td⟩ := e
        cases td with
        | struct fields => simp [stuck, throw, throwThe, MonadExceptOf.throw] at hstep
        | defined target =>
          dsimp only at hstep hn ⊢
          exact ihb (ty := target) hklt hn hstep hold' ih
        | opaqueDecl _ => simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
        | interfaceDef _ => simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
    | interface _ | bool | string | slice _ | map _ _ | pointer _ => simp [isNormalForTyTy]
    | _ =>
      simp [Ty.stepDown, stuck, throw, throwThe, MonadExceptOf.throw] at hstep
/-- The struct component, at the index layer where the struct arm lives. -/
theorem writeAt_isNormal_struct {rest : List PathStep} {v : GoValue} :
    ∀ {b : Nat} {ty : Ty} {actual : TypeId} {fields : Array (String × GoValue)} {tid : TypeId}
      {f : String} {fty : Ty} {b' : Nat} {k : Nat} {old' : GoValue},
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty (.struct actual fields) = true →
      Ty.stepDown ctx.types b ty (.field tid f) = .ok (fty, b') →
      (hklt : k < fields.size) → writeAt ctx b' fty fields[k].2 rest v = .ok old' →
      fields[k].1 = f →
      (∀ j (hj : j < k), (fields[j]'(Nat.lt_trans hj hklt)).1 ≠ f) →
      (∀ {b : Nat} {ty : Ty} {root v root' : GoValue},
        isNormalForTyTy (isNormalForTyAt ctx.types b) ty root = true →
        writeAt ctx b ty root rest v = .ok root' →
        isNormalForTyTy (isNormalForTyAt ctx.types b) ty root' = true) →
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty
        (.struct actual (fields.set k (fields[k].1, old') hklt)) = true := by
  intro b
  induction b with
  | zero =>
    intro ty actual fields tid f fty b' k old' hn hstep hklt hold' hname hbefore ih
    cases ty with
    | interface _ | bool | string | slice _ | map _ _ | pointer _ => simp [isNormalForTyTy]
    | _ =>
      simp [Ty.stepDown, typeIndexExhausted, unsupported, throw, throwThe,
        MonadExceptOf.throw, stuck, pure, Except.pure] at hstep
  | succ n ihb =>
    intro ty actual fields tid f fty b' k old' hn hstep hklt hold' hname hbefore ih
    cases ty with
    | defined j =>
      simp only [Ty.stepDown] at hstep
      simp only [isNormalForTyTy, isNormalForTyAt] at hn ⊢
      cases hlook : ctx.types[j]? with
      | none => rw [hlook] at hstep; simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
      | some e =>
        (try rw [hlook] at hstep); (try rw [hlook] at hn); (try rw [hlook])
        obtain ⟨name, td⟩ := e
        cases td with
        | struct defs =>
          dsimp only at hstep hn ⊢
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hn ⊢
          obtain ⟨⟨hact, hsz⟩, hflds⟩ := hn
          obtain ⟨hlen, halign⟩ := isNormalFieldsWith_names hflds
          have hkf : k < fields.toList.length := by simpa using hklt
          have hkd : k < defs.toList.length := by simpa [hlen] using hkf
          have hdname : defs.toList[k].name = f := by
            have := (halign k hkd hkf).1
            simpa [Array.getElem_toList, hname] using this.symm
          have hdbefore : ∀ j (hj : j < k), (defs.toList[j]'(Nat.lt_trans hj hkd)).name ≠ f := by
            intro j hj heq
            have := (halign j (Nat.lt_trans hj hkd) (Nat.lt_trans hj hkf)).1
            exact hbefore j hj (by simpa [Array.getElem_toList] using this.trans heq)
          rw [FieldDef.find?_of_first f defs.toList k hkd hdname hdbefore] at hstep
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          have hval := (halign k hkd hkf).2
          have hold : isNormalForTyTy (isNormalForTyAt ctx.types n) defs.toList[k].typ old' = true :=
            ih (by simpa [Array.getElem_toList] using hval) hold'
          refine ⟨⟨hact, by simpa using hsz⟩, ?_⟩
          have hk' : fields.toList[k]? = some (fields[k].1, fields[k].2) := by
            simp [List.getElem?_eq_getElem (show k < fields.toList.length by simpa using hklt)]
          have := isNormalFieldsWith_set (f := isNormalForTyTy (isNormalForTyAt ctx.types n))
            defs.toList fields.toList k fields[k].1 fields[k].2 old' hk' hflds
            (fun fd hfd => by
              have : fd = defs.toList[k] := by
                rw [List.getElem?_eq_getElem hkd] at hfd; exact (Option.some.inj hfd).symm
              rw [this]; exact hold)
          simpa [Array.toList_set] using this
        | defined target =>
          dsimp only at hstep hn ⊢
          exact ihb (ty := target) hn hstep hklt hold' hname hbefore ih
        | opaqueDecl _ => simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
        | interfaceDef _ => simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hstep
    | interface _ | bool | string | slice _ | map _ _ | pointer _ => simp [isNormalForTyTy]
    | _ =>
      simp [Ty.stepDown, stuck, throw, throwThe, MonadExceptOf.throw] at hstep


/-- THE CONGRUENCE: a root normal at `(ty, b)` written along `path` with a
leaf that `writeAt` normalizes at the descended type stays normal. -/
theorem writeAt_isNormal :
    ∀ {path : List PathStep} {b : Nat} {ty : Ty} {root v root' : GoValue},
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty root = true →
      writeAt ctx b ty root path v = .ok root' →
      isNormalForTyTy (isNormalForTyAt ctx.types b) ty root' = true := by
  intro path
  induction path with
  | nil =>
    intro b ty root v root' _ h
    simp only [writeAt] at h
    exact normalizeValueForTyTy_isNormal (f := normalizeValueForTyAt ctx.types b)
      (g := isNormalForTyAt ctx.types b) (fun _ _ _ hh => normalizeValueForTyAt_isNormal _ _ hh) h
  | cons step rest ih =>
    intro b ty root v root' hn h
    cases step with
    | field tid f =>
      cases root with
      | struct actual fields =>
        simp only [writeAt] at h
        by_cases hc : (actual != tid && !structTagCompatible ctx actual tid) = true
        · simp [hc, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
        · have hc' : (actual != tid && !structTagCompatible ctx actual tid) = false := by
            simpa using hc
          simp only [hc', Bool.false_eq_true, ↓reduceIte, pure_bind] at h
          split at h
          · rename_i k hidx
            have hklt := fieldIdx?_lt hidx
            try simp only [bind_eq_ok] at h
            obtain ⟨⟨fty, b'⟩, hstep, h⟩ := h
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
            obtain ⟨fields', hmod, rfl⟩ := h
            obtain ⟨q, hq, rfl⟩ := (Array.modifyM_ok_iff fields k hklt _ fields').mp hmod
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hq
            obtain ⟨old', hold', rfl⟩ := hq
            -- The declared type: a struct value is normal at a `.defined`
            -- struct declaration, or at an identity-normalized slot
            -- (`.interface` and the catch-all kinds), where the descent
            -- returns the slot's own type and normality is the `true` arm.
            obtain ⟨hk, hname, hbefore⟩ := fieldIdx?_spec fields f k hidx
            exact writeAt_isNormal_struct hn hstep hk hold' hname hbefore ih
          · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      | _ =>
        simp only [writeAt] at h
        split at h <;> simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    | index i =>
      cases root with
      | array values =>
        simp only [writeAt, bind_eq_ok] at h
        obtain ⟨k, hk, ⟨ety, b'⟩, hstep, values', hmod, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        obtain ⟨_, rfl, hklt⟩ := arrayIndexNatFormed_spec hk
        obtain ⟨old', hold', rfl⟩ := (Array.modifyM_ok_iff values i.toNat hklt _ values').mp hmod
        exact writeAt_isNormal_array hklt hn hstep hold' ih
      | _ =>
        simp only [writeAt] at h
        split at h <;> simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
/-- `storeLoc` preserves `HeapNormal`: the one root-cell update writes a
root normal at its declared type. -/
theorem HeapNormal.of_storeLoc {σ σ' : Store} {l : Loc} {v : GoValue}
    (h : HeapNormal ctx σ) (hst : storeLoc ctx σ l v = .ok σ') : HeapNormal ctx σ' := by
  unfold storeLoc at hst
  dsimp only at hst
  refine HeapNormal.of_updateCell h hst fun cell cell' hcell hf => ?_
  have hcn := HeapNormal.lookup_of h hcell
  cases cell with
  | value ty root =>
    simp only [map_eq_ok] at hf
    obtain ⟨root', hw, rfl⟩ := hf
    simp only [HeapCell.normal, isNormalForTy] at hcn ⊢
    exact writeAt_isNormal hcn hw
  | mapPayload _ _ =>
    dsimp only at hf
    revert hf
    cases (Loc.rootPath l).2 <;> simp [stuck, throw, throwThe, MonadExceptOf.throw]
  | chanPayload _ _ _ =>
    dsimp only at hf
    revert hf
    cases (Loc.rootPath l).2 <;> simp [stuck, throw, throwThe, MonadExceptOf.throw]

-- DELETED (C1 S3): `HeapNormal.of_storeMany` — its subject `storeMany` (dead since
-- the tgtOpK spine took the caller-target stores) left Machine.lean with S3.

theorem storeLoc_wf {σ : Store} {l : Loc} {v : GoValue} {σ' : Store}
    (hw : StateWf ctx σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) (h : storeLoc ctx σ l v = .ok σ') :
    StateWf ctx σ' ∧ σ'.nextAddr = σ.nextAddr := by
  obtain ⟨h4, h5⟩ := storeLoc_shape h
  have hh := hw.heap_le
  refine ⟨StateWf.mk' ?_ (HeapNormal.of_storeLoc hw.normal h), h4⟩
  rw [h4]; omega

/-! ## Allocation -/

theorem allocCell_shape {σ : Store} {c : HeapCell} {l : Loc}
    {σ' : Store} (h : σ.allocCell c = (l, σ')) :
    l = .base ⟨σ.nextAddr⟩ ∧ σ'.nextAddr = σ.nextAddr + 1
      ∧ Heap.locSup σ'.heap
          ≤ max (Heap.locSup σ.heap) (max (σ.nextAddr + 1) (HeapCell.locSup c)) := by
  -- definitional bridge to the explicit record form (dense heap: `push`)
  have h1 : Loc.base ⟨σ.heap.size⟩ = l := congrArg Prod.fst h
  have h2 : ({ σ with heap := σ.heap.push c } : Store) = σ' := congrArg Prod.snd h
  subst h1
  subst h2
  refine ⟨rfl, by simp [Store.nextAddr], ?_⟩
  refine Nat.le_trans Heap.push_locSup ?_
  simp only [Store.nextAddr]
  omega

/-- `Store.alloc` normalizes (C1 S1, D3) — the shape is `allocCell`'s at
the normalized value, which never invents locations. -/
theorem alloc_shape {σ : Store} {v : GoValue} {ty : Ty} {l : Loc}
    {σ' : Store} (h : Store.alloc ctx σ v ty = .ok (l, σ')) :
    l = .base ⟨σ.nextAddr⟩ ∧ σ'.nextAddr = σ.nextAddr + 1
      ∧ Heap.locSup σ'.heap
          ≤ max (Heap.locSup σ.heap) (max (σ.nextAddr + 1) (GoValue.locSup v)) := by
  unfold Store.alloc at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨v', hv', h⟩ := h
  have hb := normalizeValueForTy_locSup hv'
  obtain ⟨h1, h2, h3⟩ := allocCell_shape (c := .value ty v') h
  refine ⟨h1, h2, ?_⟩
  have hc : HeapCell.locSup (.value ty v') = GoValue.locSup v' := rfl
  omega

theorem allocCell_wf {σ : Store} {c : HeapCell} {l : Loc}
    {σ' : Store} (hw : StateWf ctx σ) (hc : HeapCell.locSup c ≤ σ.nextAddr)
    (h : σ.allocCell c = (l, σ')) (hn : HeapCell.normal ctx.types c = true) :
    StateWf ctx σ' ∧ Loc.locSup l ≤ σ'.nextAddr ∧ σ'.nextAddr = σ.nextAddr + 1 := by
  obtain ⟨hl, h2, h6⟩ := allocCell_shape h
  have hh := hw.heap_le
  refine ⟨StateWf.mk' ?_ (HeapNormal.of_allocCell hw.normal hn h), ?_, h2⟩
  · rw [h2]; omega
  · rw [h2, hl]
    simp [Loc.locSup, Loc.rootBase]

theorem alloc_wf {σ : Store} {v : GoValue} {ty : Ty} {l : Loc}
    {σ' : Store} (hw : StateWf ctx σ) (hv : GoValue.locSup v ≤ σ.nextAddr)
    (h : Store.alloc ctx σ v ty = .ok (l, σ')) :
    StateWf ctx σ' ∧ Loc.locSup l ≤ σ'.nextAddr ∧ σ'.nextAddr = σ.nextAddr + 1 := by
  obtain ⟨hl, h2, h6⟩ := alloc_shape h
  have hh := hw.heap_le
  refine ⟨StateWf.mk' ?_ (HeapNormal.of_alloc hw.normal h), ?_, h2⟩
  · rw [h2]; omega
  · rw [h2, hl]
    simp [Loc.locSup, Loc.rootBase]

/-! ## List-op threading lemmas (call protocol) -/

theorem loadMany_locSup {σ : Store} :
    ∀ {locs : List Loc} {vs : List GoValue}, loadMany ctx σ locs = .ok vs →
      goValueListSup vs ≤ Heap.locSup σ.heap := by
  intro locs
  induction locs with
  | nil =>
    intro vs h
    simp only [loadMany, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueListSup]
  | cons l rest ih =>
    intro vs h
    simp only [loadMany, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨v, hv, tail, htail, rfl⟩ := h
    have h1 := loadLoc_locSup hv
    have h2 := ih htail
    simp only [goValueListSup]
    omega

-- DELETED (C1 S3): `storeMany_shape` (with `storeMany`).

theorem pinResultLocs_locSup {env : LocalEnv} :
    ∀ {ps : List Param} {locs : List Loc}, pinResultLocs env ps = .ok locs →
      locListSup locs ≤ LocalEnv.locSup env := by
  intro ps
  induction ps with
  | nil =>
    intro locs h
    simp only [pinResultLocs, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [locListSup]
  | cons p rest ih =>
    intro locs h
    simp only [pinResultLocs] at h
    split at h
    · rename_i loc hloc
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨tail, htail, rfl⟩ := h
      have h1 := LocalEnv.lookup_locSup hloc
      have h2 := ih htail
      simp only [locListSup]
      omega
    · simp at h

theorem allocDecls_wf :
    ∀ {ps : List Param} {env : LocalEnv} {σ : Store} {env' : LocalEnv}
      {σ' : Store},
      allocDecls ctx env σ ps = .ok (env', σ') → StateWf ctx σ →
      LocalEnv.locSup env ≤ σ.nextAddr →
      StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr
        ∧ LocalEnv.locSup env' ≤ σ'.nextAddr := by
  intro ps
  induction ps with
  | nil =>
    intro env σ env' σ' h hw henv
    simp only [allocDecls, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, Nat.le_refl _, henv⟩
  | cons p rest ih =>
    intro env σ env' σ' h hw henv
    simp only [allocDecls, bind_eq_ok] at h
    obtain ⟨v, hv, h⟩ := h
    have hv0 := defaultValue_locSup hv
    obtain ⟨⟨loc, σ₁⟩, halloc, h⟩ := h
    try dsimp only at h
    obtain ⟨hw₁, hloc, hna⟩ := alloc_wf hw (by omega) halloc
    obtain ⟨d1, d2, _⟩ := alloc_shape halloc
    try dsimp only at hw₁ hloc hna d1 d2
    obtain ⟨c1, c2, c6⟩ := ih h hw₁ (by
      refine Nat.le_trans LocalEnv.declare_locSup ?_
      rw [hna]
      refine Nat.max_le.mpr ⟨by omega, ?_⟩
      rw [← hna]; exact hloc)
    refine ⟨c1, by omega, c6⟩

theorem bindParams_wf :
    ∀ {ps : List Param} {vals : List GoValue} {env : LocalEnv} {σ : Store}
      {env' : LocalEnv} {σ' : Store},
      bindParams ctx env σ ps vals = .ok (env', σ') → StateWf ctx σ →
      LocalEnv.locSup env ≤ σ.nextAddr → goValueListSup vals ≤ σ.nextAddr →
      StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr
        ∧ LocalEnv.locSup env' ≤ σ'.nextAddr := by
  intro ps
  induction ps with
  | nil =>
    intro vals env σ env' σ' h hw henv hvals
    cases vals with
    | nil =>
      simp only [bindParams, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, Nat.le_refl _, henv⟩
    | cons v rest => simp [bindParams] at h
  | cons p rest ih =>
    intro vals env σ env' σ' h hw henv hvals
    cases vals with
    | nil => simp [bindParams] at h
    | cons v vrest =>
      simp only [bindParams, bind_eq_ok] at h
      obtain ⟨v', hv', h⟩ := h
      have hvb : GoValue.locSup v' ≤ σ.nextAddr := by
        have := normalizeValueForTy_locSup hv'
        simp only [goValueListSup] at hvals
        omega
      obtain ⟨⟨loc, σ₁⟩, halloc, h⟩ := h
      try dsimp only at h
      obtain ⟨hw₁, hloc, hna⟩ := alloc_wf hw hvb halloc
      obtain ⟨d1, d2, _⟩ := alloc_shape halloc
      try dsimp only at hw₁ hloc hna d1 d2
      obtain ⟨c1, c2, c6⟩ := ih h hw₁ (by
        refine Nat.le_trans LocalEnv.declare_locSup ?_
        rw [hna]
        exact Nat.max_le.mpr ⟨by omega, by rw [← hna]; exact hloc⟩) (by
        simp only [goValueListSup] at hvals
        omega)
      exact ⟨c1, by omega, c6⟩

/-! ## Map/assert helpers -/

/-- A map payload read is bounded by the heap (A3). -/
theorem mapPayload?_locSup {σ : Store} {l : Loc}
    {es : Array (Nat × GoValue × GoValue)} {n : Nat}
    (h : mapPayload? σ l = .ok (es, n)) :
    goValueEntriesSup es.toList ≤ Heap.locSup σ.heap := by
  unfold mapPayload? at h
  split at h
  · rename_i entries nextId hcell
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Heap.lookup_locSup hcell
  all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- A channel payload read is bounded by the heap (A3). -/
theorem chanPayload?_locSup {σ : Store} {l : Loc} {buf : Array GoValue}
    {capacity : Nat} {closed : Bool}
    (h : chanPayload? σ l = .ok (buf, capacity, closed)) :
    goValueListSup buf.toList ≤ Heap.locSup σ.heap := by
  unfold chanPayload? at h
  split at h
  · rename_i b c k hcell
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Heap.lookup_locSup hcell
  all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem mapEntries_locSup {σ : Store} {m : MapValue}
    {out : Option (Loc × Array (Nat × GoValue × GoValue) × Nat)}
    (h : mapEntries σ m = .ok out) :
    ∀ {baseLoc entries nextId}, out = some (baseLoc, entries, nextId) →
      Loc.locSup baseLoc ≤ optLocSup m.base
        ∧ goValueEntriesSup entries.toList ≤ Heap.locSup σ.heap := by
  intro baseLoc entries nextId hout
  subst hout
  unfold mapEntries at h
  split at h
  · simp at h
  · rename_i base heq
    try simp only [bind_eq_ok] at h
    obtain ⟨⟨es, n⟩, hp, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    constructor
    · rw [heq]; exact Nat.le_refl _
    · exact mapPayload?_locSup hp

theorem mapEntryIndex?_ok_entries {kt : Ty}
    {entries : Array (Nat × GoValue × GoValue)} {key : GoValue} {i : Nat}
    {isInsert : Bool}
    (h : mapEntryIndex? ctx kt entries key isInsert = .ok (some i)) :
    True := trivial

/-! ## The emitting operations (C1 S2a): each is its primitive plus a fixed emission -/

theorem Mem.load_eq {σ : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.load ctx σ l = .ok (v, tr)) :
    loadLoc ctx σ l = .ok v ∧ tr = [.access .read (.data l.canon)] := by
  simp only [Mem.load, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨v', hv, rfl, rfl⟩ := h
  exact ⟨hv, rfl⟩

theorem Mem.loadFor_eq {σ : Store} {root leaf : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.loadFor ctx σ root leaf = .ok (v, tr)) :
    loadLoc ctx σ root = .ok v ∧ tr = [.access .read (.data leaf.canon)] := by
  simp only [Mem.loadFor, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨v', hv, rfl, rfl⟩ := h
  exact ⟨hv, rfl⟩

theorem Mem.store_eq {σ σ' : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.store ctx σ l v = .ok (σ', tr)) :
    storeLoc ctx σ l v = .ok σ' ∧ tr = [.access .write (.data l.canon)] := by
  simp only [Mem.store, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨s', hs, rfl, rfl⟩ := h
  exact ⟨hs, rfl⟩

theorem Mem.mapRead_eq {σ : Store} {l : Loc} {p : Array (Nat × GoValue × GoValue) × Nat}
    {tr : AccessTrace} (h : Mem.mapRead σ l = .ok (p, tr)) :
    mapPayload? σ l = .ok p ∧ tr = [.access .read (.data l.canon)] := by
  simp only [Mem.mapRead, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨p', hp, rfl, rfl⟩ := h
  exact ⟨hp, rfl⟩

theorem Mem.mapWrite_eq {σ σ' : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)}
    {n : Nat} {tr : AccessTrace} (h : Mem.mapWrite σ l es n = .ok (σ', tr)) :
    storeMapPayload σ l es n = .ok σ' ∧ tr = [.access .write (.data l.canon)] := by
  simp only [Mem.mapWrite, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨s', hs, rfl, rfl⟩ := h
  exact ⟨hs, rfl⟩

theorem Mem.loadElems_locSup {σ : Store} {base : Loc} :
    ∀ {n start : Nat} {vs : List GoValue} {tr : AccessTrace},
      Mem.loadElems ctx σ base start n = .ok (vs, tr) →
      goValueListSup vs ≤ Heap.locSup σ.heap ∧ vs.length = n := by
  intro n
  induction n with
  | zero =>
    intro start vs tr h
    simp only [Mem.loadElems, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [goValueListSup]
  | succ n ih =>
    intro start vs tr h
    simp only [Mem.loadElems, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨v, t⟩, hv, ⟨rest, ts⟩, hrest, rfl, rfl⟩ := h
    have h1 := loadLoc_locSup (Mem.load_eq hv).1
    obtain ⟨h2, h3⟩ := ih hrest
    simp only [goValueListSup, List.length_cons]
    omega

theorem Mem.loadSlice_locSup {σ : Store} {slice : SliceValue} {vs : Array GoValue}
    {tr : AccessTrace} (h : Mem.loadSlice ctx σ slice = .ok (vs, tr)) :
    goValueListSup vs.toList ≤ Heap.locSup σ.heap := by
  simp only [Mem.loadSlice, bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, t⟩, hl, rfl, rfl⟩ := h
    simp only [List.toList_toArray]
    exact (Mem.loadElems_locSup hl).1
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [goValueListSup]

theorem loadResults_locSup {σ : Store} :
    ∀ {locs : List Loc} {vs : List GoValue} {tr : AccessTrace},
      loadResults ctx σ locs = .ok (vs, tr) →
      goValueListSup vs ≤ Heap.locSup σ.heap := by
  intro locs
  induction locs with
  | nil =>
    intro vs tr h
    simp only [loadResults, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [goValueListSup]
  | cons l rest ih =>
    intro vs tr h
    simp only [loadResults, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨v, t⟩, hv, ⟨tail, ts⟩, htail, rfl, rfl⟩ := h
    have h1 := loadLoc_locSup (Mem.load_eq (loadBinding_ok ctx hv)).1
    have h2 := ih htail
    simp only [goValueListSup]
    omega

theorem mapLookupValue_locSup {σ : Store} {m : MapValue} {key : GoValue}
    {kt vt : Ty} {rv : GoValue} {b : Bool} {tr : AccessTrace}
    (h : mapLookupValue ctx σ m key kt vt = .ok ((rv, b), tr)) :
    GoValue.locSup rv ≤ Heap.locSup σ.heap := by
  unfold mapLookupValue at h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, d, hd, ⟨rfl, rfl⟩, rfl⟩ := h
    rw [defaultValue_locSup hd]
    exact Nat.zero_le _
  · rename_i baseLoc hbase
    try simp only [bind_eq_ok] at h
    obtain ⟨⟨⟨entries, n⟩, tr'⟩, hread, h⟩ := h
    obtain ⟨hp, rfl⟩ := Mem.mapRead_eq hread
    try dsimp only at h
    try simp only [bind_eq_ok] at h
    obtain ⟨idx, hidx, h⟩ := h
    split at h
    · rename_i i
      split at h
      · rename_i id' k' v' hp'
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        have hmem : (id', k', v') ∈ entries.toList :=
          List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp')
        have h2 := mapPayload?_locSup hp
        have h3 := goValueEntriesSup_mem hmem
        simp only at h3
        omega
      · simp at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨d, hd, ⟨rfl, rfl⟩, rfl⟩ := h
      rw [defaultValue_locSup hd]
      exact Nat.zero_le _

theorem typeAssertValue_locSup {v : GoValue} {ty : Ty}
    {r : GoValue} {b : Bool} (h : typeAssertValue ctx v ty = .ok (r, b)) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold typeAssertValue at h
  try simp only [bind_eq_ok] at h
  obtain ⟨failed, hfailed, h⟩ := h
  have h0 := defaultValue_locSup hfailed
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    omega
  · rename_i dynTy inner
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨tst, htst, h⟩ := h
      split at h <;>
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        first
          | exact Nat.le_refl _
          | omega
    · split at h <;>
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        first
          | exact Nat.le_refl _
          | (simp only [GoValue.locSup]; omega)
          | omega
  · simp at h

/-! ## Frame entry -/

theorem goValueListSup_getElem? {arr : Array GoValue} {i : Nat} {x : GoValue}
    (h : arr[i]? = some x) : GoValue.locSup x ≤ goValueListSup arr.toList := by
  rw [goValueListSup_eq]
  exact supBy_mem (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h))

theorem structFieldValue_locSup {v : GoValue} {tid : TypeId} {f : String} {w : GoValue}
    (h : structFieldValue ctx v tid f = .ok w) : GoValue.locSup w ≤ GoValue.locSup v := by
  unfold structFieldValue at h
  split at h
  · rename_i actualType fields
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · rename_i value hv
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simpa [GoValue.locSup] using StructFields.lookup_locSup hv
      · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- The walk cursor's loc bound: the value in hand, or the cell's root. -/
def WalkCursor.locSup : WalkCursor → Nat
  | .val v => GoValue.locSup v
  | .cell l => Loc.locSup l

/-- One promotion hop stays within the cursor's bound and the heap's (G-P
S2, `receiverAt`): a projection keeps the root, a pointer-field read is a
heap value. -/
theorem promotionHop_locSup {σ : Store} {cur : WalkCursor} {hop : PromotionHop}
    {cur' : WalkCursor} {tr : AccessTrace}
    (h : promotionHop ctx σ cur hop = .ok (cur', tr)) :
    WalkCursor.locSup cur' ≤ max (WalkCursor.locSup cur) (Heap.locSup σ.heap) := by
  unfold promotionHop at h
  simp only at h
  split at h
  · -- the struct in hand
    rename_i tid fields
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    have := structFieldValue_locSup hw
    simp only [WalkCursor.locSup] at this ⊢
    omega
  all_goals try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done)
  all_goals
    -- `.val (.addr loc)` / `.cell loc`: the field under `loc`
    rename_i loc
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨pv, trv⟩, hload, h⟩ := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := loadLoc_locSup (Mem.load_eq hload).1
      simp only [WalkCursor.locSup]
      omega
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [WalkCursor.locSup, GoValue.locSup, Loc.locSup_field]
      omega

theorem promotionWalk_locSup {σ : Store} :
    ∀ {cur : WalkCursor} {hops : List PromotionHop} {cur' : WalkCursor} {tr : AccessTrace},
      promotionWalk ctx σ cur hops = .ok (cur', tr) →
      WalkCursor.locSup cur' ≤ max (WalkCursor.locSup cur) (Heap.locSup σ.heap)
  | cur, [], cur', tr, h => by
      simp only [promotionWalk, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_max_left _ _
  | cur, hop :: hops, cur', tr, h => by
      simp only [promotionWalk, bind_eq_ok] at h
      obtain ⟨⟨c₁, t₁⟩, h1, ⟨c₂, t₂⟩, h2, h3⟩ := h
      (try dsimp only at h1); (try dsimp only at h2)
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have a := promotionHop_locSup h1
      have b := promotionWalk_locSup h2
      omega

/-- The receiver at the end of a path is bounded by the root and the heap
(G-P S2): every value it can be is the root, a projection of it, or a
heap read. -/
theorem receiverAt_locSup {σ : Store} {root : GoValue} {path : Array PromotionHop}
    {adjust : PromotionAdjust} {v : GoValue} {tr : AccessTrace}
    (h : receiverAt ctx σ root path adjust = .ok (v, tr)) :
    GoValue.locSup v ≤ max (GoValue.locSup root) (Heap.locSup σ.heap) := by
  unfold receiverAt at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨cur, tr₀⟩, hwalk, h⟩ := h
  (try dsimp only at h)
  have hw := promotionWalk_locSup hwalk
  simp only [WalkCursor.locSup] at hw
  split at h
  all_goals try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done)
  · -- asIs, the value in hand
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [WalkCursor.locSup] using hw
  · -- asIs, the cell read
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨v', tr'⟩, hload, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := loadLoc_locSup (Mem.load_eq hload).1
    omega
  · -- deref, the pointee read
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨v', tr'⟩, hload, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := loadLoc_locSup (Mem.load_eq hload).1
    omega
  · -- addr, the cell's address
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [WalkCursor.locSup, GoValue.locSup] using hw

/-- The preprint call's RESOLUTION (unit 6b, `preprintDispatch`): the
adjusted receiver is bounded by the payload and the heap (`receiverAt_locSup`
on the boxed inner value). -/
theorem preprintDispatch_locSup {σ : Store} {e : PanicEntry} {fid : FuncId} {recv : GoValue}
    {tr : AccessTrace} (h : preprintDispatch ctx σ e = .ok (fid, recv, tr)) :
    GoValue.locSup recv ≤ max (GoValue.locSup e.value) (Heap.locSup σ.heap) := by
  unfold preprintDispatch at h
  split at h
  · split at h
    · rename_i dynTy inner heq
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨recv', tr'⟩, hrecv, rfl, rfl, rfl⟩ := h
          have := receiverAt_locSup hrecv
          rw [heq]
          simp only [GoValue.locSup]
          exact this
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A dispatch's arguments are bounded by the entry's and the heap, and a
`.target`'s `Func` is one of the program's (G-P S2: the receiver is
`receiverAt`'s, the other arguments the entry's). -/
theorem dynamicDispatch?_locSup {σ : Store} {func : Func}
    {args : Array GoValue} {out : Option Dispatched} {tr : AccessTrace}
    (h : dynamicDispatch? ctx σ func args = .ok (out, tr)) :
    ∀ {d : Dispatched}, out = some d →
      goValueListSup d.args.toList
          ≤ max (goValueListSup args.toList) (Heap.locSup σ.heap)
        ∧ ∀ {tf : Func} {a : Array GoValue}, d = .target tf a →
            Func.locSup tf ≤ funcListSup ctx.functions.toList := by
  intro d hout
  subst hout
  unfold dynamicDispatch? at h
  simp only [Bind.bind, Except.bind, pure, Except.pure, GoCore.stuck,
    throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i dynTy inner heq
        have hinner : GoValue.locSup inner ≤ goValueListSup args.toList := by
          have := goValueListSup_getElem? heq
          simpa [GoValue.locSup] using this
        split at h
        · rename_i r hr
          split at h
          · split at h <;> (try split at h) <;> simp at h
          · split at h
            · split at h
              · rename_i f
                split at h
                · rename_i tf htf
                  split at h
                  · simp at h
                  · rename_i p hp
                    obtain ⟨rv, tr'⟩ := p
                    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                    refine ⟨?_, ?_⟩
                    · simp only [Dispatched.args]
                      try rw [Array.set!]
                      refine Nat.le_trans goValueListSup_setIfInBounds ?_
                      have := receiverAt_locSup hp
                      omega
                    · intro tf' a' hd
                      simp only [Dispatched.target.injEq] at hd
                      obtain ⟨rfl, rfl⟩ := hd
                      exact findFunctionIn?_locSup htf
                · simp at h
              · simp at h
            · split at h
              · simp at h
              · rename_i p hp
                obtain ⟨rv, tr'⟩ := p
                have hrv := receiverAt_locSup hp
                split at h
                · rename_i f
                  split at h
                  · rename_i tf htf
                    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                    refine ⟨?_, ?_⟩
                    · simp only [Dispatched.args]
                      try rw [Array.set!]
                      refine Nat.le_trans goValueListSup_setIfInBounds ?_
                      omega
                    · intro tf' a' hd
                      simp only [Dispatched.target.injEq] at hd
                      obtain ⟨rfl, rfl⟩ := hd
                      exact findFunctionIn?_locSup htf
                  · simp at h
                · rename_i i
                  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                  refine ⟨?_, ?_⟩
                  · simp only [Dispatched.args]
                    try rw [Array.set!]
                    refine Nat.le_trans goValueListSup_setIfInBounds ?_
                    omega
                  · intro tf' a' hd
                    cases hd
        · simp at h
      · simp at h
      · simp at h


/-- A promoted method expression's callee (S7) is bounded like a dispatch. -/
theorem promotedCallee_locSup {σ : Store} {fid : FuncId} {p : Promotion}
    {argVals : List GoValue} {d : Dispatched} {tr : AccessTrace}
    (h : promotedCallee ctx σ fid p argVals = .ok (d, tr)) :
    goValueListSup d.args.toList ≤ max (goValueListSup argVals) (Heap.locSup σ.heap)
      ∧ ∀ {tf : Func} {a : Array GoValue}, d = .target tf a →
          Func.locSup tf ≤ funcListSup ctx.functions.toList := by
  unfold promotedCallee at h
  simp only [Bind.bind, Except.bind, pure, Except.pure, GoCore.stuck,
    throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp at h
  · split at h
    · rename_i f
      split at h
      · simp at h
      · rename_i tf htf
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i root rest
            split at h
            · simp at h
            · rename_i q hq
              obtain ⟨rv, tr'⟩ := q
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrv := receiverAt_locSup hq
              refine ⟨?_, ?_⟩
              · simp only [Dispatched.args, List.toList_toArray, goValueListSup]
                omega
              · intro tf' a' hd
                simp only [Dispatched.target.injEq] at hd
                obtain ⟨rfl, rfl⟩ := hd
                exact findFunctionIn?_locSup htf
    · rename_i i
      split at h
      · simp at h
      · rename_i anchor hanchor
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i root rest
            split at h
            · simp at h
            · rename_i q hq
              obtain ⟨rv, tr'⟩ := q
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrv := receiverAt_locSup hq
              refine ⟨?_, ?_⟩
              · simp only [Dispatched.args, List.toList_toArray, goValueListSup]
                omega
              · intro tf' a' hd
                cases hd


theorem enterFrame_tail {σ : Store} {func₁ : Func} {argVals₁ : List GoValue}
    {argsEnv : LocalEnv} {s₁ : Store} {frameEnv₁ : LocalEnv} {s₂ : Store}
    {locs : List Loc}
    (hw : StateWf ctx σ)
    (hargs₁ : goValueListSup argVals₁ ≤ σ.nextAddr)
    (hbp : bindParams ctx [] σ func₁.args.toList argVals₁ = .ok (argsEnv, s₁))
    (had : allocDecls ctx argsEnv s₁ func₁.results.toList = .ok (frameEnv₁, s₂))
    (hpin : pinResultLocs frameEnv₁ func₁.results.toList = .ok locs) :
    StateWf ctx s₂ ∧ σ.nextAddr ≤ s₂.nextAddr
      ∧ Stmt.locSup func₁.body ≤ s₂.nextAddr
      ∧ LocalEnv.locSup frameEnv₁ ≤ s₂.nextAddr
      ∧ locListSup locs ≤ s₂.nextAddr := by
  obtain ⟨b1, b2, b6⟩ := bindParams_wf hbp hw
    (by simp [LocalEnv.locSup]) hargs₁
  obtain ⟨c1, c2, c6⟩ := allocDecls_wf had b1 b6
  have hpinb := pinResultLocs_locSup hpin
  -- B7: the body bound is the A4 fact itself (program text is loc-free),
  -- no longer a projection of a stored-function-body half of `StateWf`.
  have hbody : Stmt.locSup func₁.body = 0 := Stmt.locSup_eq_zero _
  exact ⟨c1, by omega, by omega, c6, by omega⟩

/-- What a frame entry delivers, loc-wise (G-P S2): a RUN's body, frame
environment and pinned result cells, or a RE-DISPATCH's arguments. -/
def Entry.locSup : Entry → Nat
  | .run func frameEnv resultLocs =>
      max (Stmt.locSup func.body) (max (LocalEnv.locSup frameEnv) (locListSup resultLocs))
  | .again _ args => goValueListSup args

/-- Close an `enterFrame_wf` arm whose plan is the RUN commit (G-P S2): the
commit's bind/declare/pin run on the entry store (`h`), bounded by
`enterFrame_tail`. Expects `hplan : Except.ok (fun s => …) = Except.ok c`
and `h : c σ = .ok (e, σ', tr)`; `func`/`args` are the callee and its
arguments as they appear in the commit. -/
macro "enterFrame_run_arm " hplan:ident h:ident hw:term:max hargs:term:max σ:term:max func:term:max args:term:max : tactic =>
  `(tactic| (
    simp only [Except.ok.injEq] at $hplan:ident
    subst $hplan:ident
    (try simp only [Bind.bind, Except.bind, pure, Except.pure] at $h:ident)
    cases hbp : bindParams ctx [] $σ ($func).args.toList $args with
    | error e => rw [hbp] at $h:ident; simp at $h:ident
    | ok p₁ =>
    rw [hbp] at $h:ident
    obtain ⟨argsEnv, s₁⟩ := p₁
    try dsimp only at $h:ident
    cases had : allocDecls ctx argsEnv s₁ ($func).results.toList with
    | error e => rw [had] at $h:ident; simp at $h:ident
    | ok p₂ =>
    rw [had] at $h:ident
    obtain ⟨frameEnv₁, s₂⟩ := p₂
    try dsimp only at $h:ident
    cases hpin : pinResultLocs frameEnv₁ ($func).results.toList with
    | error e => rw [hpin] at $h:ident; simp at $h:ident
    | ok locs =>
    rw [hpin] at $h:ident
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at $h:ident
    obtain ⟨h1, h2, h3⟩ := $h:ident
    subst h1; subst h2; subst h3
    obtain ⟨t1, t2, t3, t4, t5⟩ := enterFrame_tail $hw $hargs hbp had hpin
    refine ⟨t1, t2, ?_⟩
    simp only [Entry.locSup, Nat.max_le]
    omega))

/-- Close an `enterFrame_wf` arm whose plan is the RE-DISPATCH (nothing
committed). Expects `hplan : Except.ok (fun s => Except.ok (.again …, s, tr₀)) = Except.ok c`,
`h : c σ = .ok (e, σ', tr)`, `hd1 : goValueListSup (Dispatched.again fid' args').args.toList ≤ …`. -/
macro "enterFrame_again_arm " hplan:ident h:ident hw:term:max hd1:ident : tactic =>
  `(tactic| (
    simp only [Except.ok.injEq] at $hplan:ident
    subst $hplan:ident
    simp only [Except.ok.injEq, Prod.mk.injEq] at $h:ident
    obtain ⟨h1, h2, h3⟩ := $h:ident
    subst h1; subst h2; subst h3
    refine ⟨$hw, Nat.le_refl _, ?_⟩
    simp only [Dispatched.args] at $hd1:ident
    simp only [Entry.locSup]
    omega))

theorem enterFrame_wf {σ : Store} {fid : FuncId} {argVals : List GoValue}
    {e : Entry} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hargs : goValueListSup argVals ≤ σ.nextAddr)
    (h : enterFrame ctx σ fid argVals = .ok (e, σ', tr)) :
    StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ Entry.locSup e ≤ σ'.nextAddr := by
  unfold enterFrame at h
  simp only [bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  unfold enterFrame.plan at hplan
  simp only [Bind.bind, Except.bind, pure, Except.pure, GoCore.stuck,
    throw, throwThe, MonadExceptOf.throw] at hplan
  have hh := hw.heap_le
  have harr : goValueListSup argVals.toArray.toList = goValueListSup argVals := by simp
  split at hplan
  · simp at hplan
  · -- a declared callee: arity, then dispatch
    rename_i func₀ hfunc₀
    split at hplan
    · simp at hplan
    · split at hplan
      · simp at hplan
      · rename_i q hdd
        obtain ⟨dOut, tr₀⟩ := q
        (try dsimp only at hplan)
        split at hplan
        · rename_i d tr₁ hdq
          simp only [Prod.mk.injEq] at hdq
          obtain ⟨rfl, rfl⟩ := hdq
          (try dsimp only at hplan)
          obtain ⟨hd1, hd2⟩ := dynamicDispatch?_locSup hdd rfl
          split at hplan
          · enterFrame_again_arm hplan h hw hd1
          · rename_i func args
            split at hplan
            · simp at hplan
            · have hargs' : goValueListSup args.toList ≤ σ.nextAddr := by
                simp only [Dispatched.args] at hd1
                omega
              enterFrame_run_arm hplan h hw hargs' σ func args.toList
        · (try dsimp only at hplan)
          split at hplan
          · simp at hplan
          · have hargs' : goValueListSup argVals.toArray.toList ≤ σ.nextAddr := by omega
            enterFrame_run_arm hplan h hw hargs' σ func₀ argVals.toArray.toList
  · -- a promotion record callee (a method expression, S7)
    rename_i p hp
    split at hplan
    · simp at hplan
    · rename_i q hpc
      obtain ⟨d, tr₀⟩ := q
      (try dsimp only at hplan)
      obtain ⟨hd1, hd2⟩ := promotedCallee_locSup hpc
      split at hplan
      · enterFrame_again_arm hplan h hw hd1
      · rename_i func args
        split at hplan
        · simp at hplan
        · have hargs' : goValueListSup args.toList ≤ σ.nextAddr := by
            simp only [Dispatched.args] at hd1
            omega
          enterFrame_run_arm hplan h hw hargs' σ func args.toList


theorem bindIterVars_wf {env : LocalEnv} {σ : Store}
    {kv vv : Option VarId} {kt vt : Ty} {key value : GoValue}
    {env' : LocalEnv} {σ' : Store}
    (hw : StateWf ctx σ) (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : GoValue.locSup key ≤ σ.nextAddr)
    (hv : GoValue.locSup value ≤ σ.nextAddr)
    (h : bindIterVars ctx env σ kv vv kt vt key value = .ok (env', σ')) :
    StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr
      ∧ LocalEnv.locSup env' ≤ σ'.nextAddr := by
  unfold bindIterVars at h
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- key bound
    rename_i name
    split at h
    all_goals try (simp at h; done)
    rename_i kv' hkv'
    have hkb : GoValue.locSup kv' ≤ σ.nextAddr := by
      have := normalizeValueForTy_locSup hkv'
      omega
    cases halloc : Store.alloc ctx σ kv' kt with
    | error e => rw [halloc] at h; simp at h
    | ok pr =>
    obtain ⟨loc, σa⟩ := pr
    rw [halloc] at h
    try dsimp only at h
    obtain ⟨w1, w2, w3⟩ := alloc_wf hw hkb halloc
    obtain ⟨d1, d2, _⟩ := alloc_shape halloc
    have henva : LocalEnv.locSup (env.declare name loc) ≤ σa.nextAddr := by
      refine Nat.le_trans LocalEnv.declare_locSup ?_
      exact Nat.max_le.mpr ⟨by omega, w2⟩
    split at h
    · -- value bound too
      rename_i name₂
      split at h
      all_goals try (simp at h; done)
      rename_i vv' hvv'
      have hvb : GoValue.locSup vv' ≤ σa.nextAddr := by
        have := normalizeValueForTy_locSup hvv'
        omega
      cases halloc₂ : Store.alloc ctx σa vv' vt with
      | error e => rw [halloc₂] at h; simp at h
      | ok pr₂ =>
        obtain ⟨loc₂, σb⟩ := pr₂
        rw [halloc₂] at h
        try dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨y1, y2, y3⟩ := alloc_wf w1 hvb halloc₂
        obtain ⟨e1, e2, _⟩ := alloc_shape halloc₂
        refine ⟨y1, by omega, ?_⟩
        refine Nat.le_trans LocalEnv.declare_locSup ?_
        exact Nat.max_le.mpr ⟨by omega, y2⟩
    · -- value unbound
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨w1, by omega, henva⟩
  · -- key unbound
    split at h
    · -- value bound
      rename_i name₂
      split at h
      all_goals try (simp at h; done)
      rename_i vv' hvv'
      have hvb : GoValue.locSup vv' ≤ σ.nextAddr := by
        have := normalizeValueForTy_locSup hvv'
        omega
      cases halloc : Store.alloc ctx σ vv' vt with
      | error e => rw [halloc] at h; simp at h
      | ok pr =>
      obtain ⟨loc, σa⟩ := pr
      rw [halloc] at h
      try dsimp only at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨w1, w2, w3⟩ := alloc_wf hw hvb halloc
      obtain ⟨d1, d2, _⟩ := alloc_shape halloc
      refine ⟨w1, by omega, ?_⟩
      refine Nat.le_trans LocalEnv.declare_locSup ?_
      exact Nat.max_le.mpr ⟨by omega, w2⟩
    · -- neither bound
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, Nat.le_refl _, henv⟩

/-- Range-start bound (BUG-005 (L) surgery; B1 stamps): the recorded
base loc is bounded by the ranged map VALUE's sup (the start set is a
set of entry IDS — loc-free, nothing to bound). -/
theorem mapRangeStartSets_locSup {σ : Store} {v : GoValue}
    {base : Option Loc} {start : Array Nat} {tr : AccessTrace}
    (h : mapRangeStartSets σ v = .ok (base, start, tr)) :
    optLocSup base ≤ GoValue.locSup v := by
  unfold mapRangeStartSets at h
  try simp only [bind_eq_ok] at h
  obtain ⟨m, hm, h⟩ := h
  have hmv : optLocSup m.base ≤ GoValue.locSup v := by
    unfold valueAsMap at hm
    split at hm <;> simp_all [GoValue.locSup, pure, Except.pure]
  split at h
  · rename_i hbase
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [optLocSup]
  · rename_i base' hbase
    try simp only [bind_eq_ok] at h
    obtain ⟨⟨⟨es, n⟩, tr'⟩, hp, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simpa [hbase] using hmv

/-- The pick-time filter only drops entries (it is a `List.filter`). -/
theorem filterCandidateList_sup {produced : Array Nat}
    {es : List (Nat × GoValue × GoValue)} :
    goValueEntriesSup (filterCandidateList produced es) ≤ goValueEntriesSup es := by
  simp only [goValueEntriesSup_eq, filterCandidateList]
  exact supBy_le_of_subset fun a ha => (List.mem_filter.mp ha).1

/-- Every candidate list is drawn from the live cell: the pick-time
candidates are heap-bounded (BUG-005 (L) surgery — the mapIterNext wf
case's bound, replacing the retired snapshot bound). -/
theorem mapIterCandidates_locSup {σ : Store} {keyTy valTy : Ty}
    {base : Option Loc} {produced : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace}
    (h : mapIterCandidates ctx σ keyTy valTy base produced = .ok (cands, tr)) :
    goValueEntriesSup cands.toList ≤ Heap.locSup σ.heap := by
  unfold mapIterCandidates at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨es, tr₀⟩, hes, h⟩ := h
  have hlive : goValueEntriesSup es.toList ≤ Heap.locSup σ.heap := by
    cases base with
    | none =>
        simp only [mapIterLiveEntries, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hes
        obtain ⟨rfl, rfl⟩ := hes
        simp [goValueEntriesSup]
    | some l =>
        simp only [mapIterLiveEntries, bind_eq_ok] at hes
        obtain ⟨⟨⟨es', n⟩, tr₁⟩, hp, hes⟩ := hes
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hes
        obtain ⟨rfl, rfl⟩ := hes
        exact mapPayload?_locSup (Mem.mapRead_eq hp).1
  try dsimp only at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.toList_toArray]
    exact Nat.le_trans filterCandidateList_sup hlive
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Literal/aggregate builders -/

theorem buildStructFields_locSup :
    ∀ {fds : List FieldDef} {vals : List GoValue}
      {arr : Array (String × GoValue)},
      buildStructFields ctx fds vals = .ok arr →
      goValueFieldsSup arr.toList ≤ goValueListSup vals := by
  intro fds
  induction fds with
  | nil =>
    intro vals arr h
    rw [buildStructFields.eq_def] at h
    split at h
    · simp_all
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueFieldsSup]
  | cons fd frest ih =>
    intro vals arr h
    cases vals with
    | nil =>
      simp only [buildStructFields, pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueFieldsSup]
    | cons v vrest =>
      simp only [buildStructFields, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      have h1 := normalizeValueForTy_locSup hhead
      have h2 := ih htail
      have hl : (#[(fd.name, head)] ++ tail).toList
          = (fd.name, head) :: tail.toList := by simp
      rw [hl]
      simp only [goValueFieldsSup, goValueListSup] at *
      omega

/-- A struct literal's value is loc-bounded by its arguments. Cases on the
RESOLVED type body (C2: the literal is not recursive). -/
theorem buildStructValue_locSup {ty : Ty} {args : Array GoValue}
    {r : GoValue} (h : buildStructValue ctx ty args = .ok r) :
    GoValue.locSup r ≤ goValueListSup args.toList := by
  unfold buildStructValue at h
  generalize ctx.types.resolve ctx.types.size ty = body at h
  match body with
  | .error _ => simp at h
  | .ok (.interfaceDecl _) => simp at h
  | .ok (.opaque _ _) => simp at h
  | .ok (.plain t) => cases t <;> simp at h
  | .ok (.struct name fields) =>
    simp only at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      rw [map_eq_ok] at h
      obtain ⟨fs, hfs, rfl⟩ := h
      simpa [GoValue.locSup] using buildStructFields_locSup hfs

theorem buildArrayValue_locSup {len : Nat} {elem : Ty}
    {args : Array (Int × GoValue)} {r : GoValue}
    (h : buildArrayValue ctx len elem args = .ok r) :
    GoValue.locSup r ≤ supBy (fun p => GoValue.locSup p.2) args.toList := by
  unfold buildArrayValue at h
  try simp only [bind_eq_ok] at h
  obtain ⟨vs₁, hvs₁, h⟩ := h
  have hb₁ : goValueListSup vs₁.toList ≤ 0 := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hvs₁
    refine forIn_list_inv (P := fun vs : Array GoValue =>
      goValueListSup vs.toList ≤ 0) ?_ (Nat.zero_le _) hvs₁
    intro a _ b rr hbb hr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨d, hd, hrr⟩ := hr
    subst hrr
    have h0 := defaultValue_locSup hd
    simp only [forInStepVal, goValueListSup_push]
    omega
  obtain ⟨st, hloop, h⟩ := h
  rw [← Array.forIn_toList] at hloop
  -- 4.32.2: loop state is now `(values, seenKeys) : Array GoValue × Array Int`
  -- (was `MProd (Array Int) (Array GoValue)`); the values live in `.1`.
  have hP : goValueListSup st.1.toList
      ≤ supBy (fun p => GoValue.locSup p.2) args.toList := by
    refine forIn_list_inv (P := fun st : Array GoValue × Array Int =>
      goValueListSup st.1.toList ≤ supBy (fun p => GoValue.locSup p.2) args.toList)
      ?_ (Nat.le_trans hb₁ (Nat.zero_le _)) hloop
    intro a ha b rr hbb hr
    obtain ⟨key, value⟩ := a
    have hmem : GoValue.locSup value
        ≤ supBy (fun p => GoValue.locSup p.2) args.toList :=
      supBy_mem (f := fun p => GoValue.locSup p.2) ha
    split at hr
    · simp [Bind.bind, Except.bind] at hr
    · split at hr
      · simp [Bind.bind, Except.bind] at hr
      · split at hr
        · rename_i old hold
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
          obtain ⟨nv, hnv, hrr⟩ := hr
          subst hrr
          have h1 := normalizeValueForTy_locSup hnv
          simp only [forInStepVal]
          refine Nat.le_trans goValueListSup_set! ?_
          omega
        · simp [Bind.bind, Except.bind] at hr
  simp only [pure_eq_ok, Except.ok.injEq] at h
  subst h
  simpa [GoValue.locSup] using hP

theorem buildDefaultArrayValue_locSup {len : Nat} {elem : Ty}
    {r : GoValue} (h : buildDefaultArrayValue ctx len elem = .ok r) :
    GoValue.locSup r = 0 := by
  unfold buildDefaultArrayValue at h
  have hb := buildArrayValue_locSup h
  have h0 : supBy (fun p => GoValue.locSup p.2)
      (#[] : Array (Int × GoValue)).toList = 0 := rfl
  omega

theorem sliceVisibleValues_locSup {σ : Store} {slice : SliceValue}
    {values : Array GoValue} (h : sliceVisibleValues ctx σ slice = .ok values) :
    goValueListSup values.toList ≤ Heap.locSup σ.heap := by
  unfold sliceVisibleValues at h
  rw [map_eq_ok] at h
  obtain ⟨⟨vs, tr⟩, hl, hv⟩ := h
  simp only at hv
  subst hv
  exact Mem.loadSlice_locSup hl

theorem buildAppendBackingValue_locSup {elem : Ty}
    {oldValues elemValues : Array GoValue} {newCap : Nat} {r : GoValue}
    (h : buildAppendBackingValue ctx elem oldValues elemValues newCap = .ok r) :
    GoValue.locSup r
      ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
  unfold buildAppendBackingValue at h
  try simp only [bind_eq_ok] at h
  obtain ⟨vs₁, hloop, h⟩ := h
  rw [← Array.forIn_toList] at hloop
  have hb₁ : goValueListSup vs₁.toList
      ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
    refine forIn_list_inv (P := fun vs : Array GoValue =>
      goValueListSup vs.toList
        ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList))
      ?_ (Nat.zero_le _) hloop
    intro a ha b rr hbb hr
    have hmem : GoValue.locSup a
        ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
      rw [Array.toList_append] at ha
      rcases List.mem_append.mp ha with hm | hm
      · exact Nat.le_trans (by rw [goValueListSup_eq]; exact supBy_mem hm)
          (Nat.le_max_left _ _)
      · exact Nat.le_trans (by rw [goValueListSup_eq]; exact supBy_mem hm)
          (Nat.le_max_right _ _)
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨nv, hnv, hrr⟩ := hr
    subst hrr
    have h1 := normalizeValueForTy_locSup hnv
    simp only [forInStepVal, goValueListSup_push]
    omega
  split at h
  · simp [Bind.bind, Except.bind] at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨vs₂, hloop₂, hr⟩ := h
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop₂
    have hb₂ : goValueListSup vs₂.toList
        ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
      refine forIn_list_inv (P := fun vs : Array GoValue =>
        goValueListSup vs.toList
          ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList))
        ?_ hb₁ hloop₂
      intro a _ b rr hbb hr
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨d, hd, hrr⟩ := hr
      subst hrr
      have h0 := defaultValue_locSup hd
      simp only [forInStepVal, goValueListSup_push]
      omega
    subst hr
    simpa [GoValue.locSup] using hb₂

theorem applySlice_locSup {σ : Store} {b : GoValue} {lo hi : Int}
    {m : Option Int} {v : GoValue} {σ' : Store}
    (h : applySlice ctx σ b lo hi m = .ok (v, σ')) :
    σ' = σ ∧ GoValue.locSup v ≤ max (GoValue.locSup b) (Heap.locSup σ.heap) := by
  unfold applySlice at h
  split at h
  · -- string
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sv, hsv, rfl, rfl⟩ := h
    exact ⟨rfl, by rw [stringSlice_locSup hsv]; omega⟩
  · -- slice value
    rename_i sl
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sv, hsv, rfl, rfl⟩ := h
    have := sliceFromSlice_locSup hsv
    refine ⟨rfl, ?_⟩
    have : GoValue.locSup (GoValue.slice sl) = optLocSup sl.base := rfl
    have h2 := sliceFromSlice_locSup hsv
    omega
  · -- addr base
    rename_i baseLoc
    try simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨sv, hsv, rfl, rfl⟩ := h
      have h2 := sliceFromArray_locSup hsv
      have h3 : GoValue.locSup (GoValue.addr baseLoc) = Loc.locSup baseLoc := rfl
      exact ⟨rfl, by omega⟩
    · rename_i sl
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨sv, hsv, rfl, rfl⟩ := h
      have h2 := sliceFromSlice_locSup hsv
      have h3 : GoValue.locSup (GoValue.slice sl) = optLocSup sl.base := rfl
      have h4 := loadLoc_locSup hbv
      rw [h3] at h4
      exact ⟨rfl, by omega⟩
    · simp at h
  · simp at h
  · simp at h

/-! ## Integer-result operators: no locations in, none out -/

theorem intBinaryResult_locSup {nm : String} {op : Int → Int → Int}
    {l r v : GoValue} (h : intBinaryResult nm op l r = .ok v) :
    GoValue.locSup v = 0 := by
  unfold intBinaryResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  obtain ⟨⟨rv, rk⟩, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨k, hk, rfl⟩ := h
    rfl
  · simp [Bind.bind, Except.bind] at h

theorem floatBinaryResult_locSup {nm : String} {op64 op32 : Nat → Nat → Nat}
    {l r v : GoValue} (h : floatBinaryResult nm op64 op32 l r = .ok v) :
    GoValue.locSup v = 0 := by
  unfold floatBinaryResult at h
  split at h
  · split at h
    · split at h <;>
        (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h; rfl)
    · simp [Bind.bind, Except.bind] at h
  · simp [Bind.bind, Except.bind] at h

theorem intBitwiseBinaryResult_locSup {nm : String} {op : Nat → Nat → Nat}
    {l r v : GoValue} (h : intBitwiseBinaryResult nm op l r = .ok v) :
    GoValue.locSup v = 0 := by
  unfold intBitwiseBinaryResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  obtain ⟨⟨rv, rk⟩, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨k, hk, lb, hlb, rb, hrb, rfl⟩ := h
    rfl
  · simp [Bind.bind, Except.bind] at h

theorem intBitClearResult_locSup {l r v : GoValue}
    (h : intBitClearResult l r = .ok v) : GoValue.locSup v = 0 := by
  unfold intBitClearResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  obtain ⟨⟨rv, rk⟩, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨k, hk, bits, hbits, lb, hlb, rb, hrb, rfl⟩ := h
    rfl
  · simp [Bind.bind, Except.bind] at h

theorem intBitNegResult_locSup {x v : GoValue}
    (h : intBitNegResult x = .ok v) : GoValue.locSup v = 0 := by
  unfold intBitNegResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨xv, xk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨bits, hbits, vb, hvb, rfl⟩ := h
  rfl

theorem intShiftLeftResult_locSup {l r v : GoValue}
    (h : intShiftLeftResult l r = .ok v) : GoValue.locSup v = 0 := by
  unfold intShiftLeftResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨c, hc, bits, hbits, h⟩ := h
  -- BUG-096: the width-saturation branch and the in-width branch both
  -- produce a plain `.int`, whose locSup is 0.
  split at h <;> simp only [pure_eq_ok, Except.ok.injEq] at h <;> subst h <;> rfl

theorem intShiftRightResult_locSup {l r v : GoValue}
    (h : intShiftRightResult l r = .ok v) : GoValue.locSup v = 0 := by
  unfold intShiftRightResult at h
  try simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨c, hc, bits, hbits, h⟩ := h
  split at h <;> simp only [pure_eq_ok, Except.ok.injEq] at h <;> subst h <;> rfl

/-! ## `applyStrictOp` preserves well-formedness -/

/-- The state-unchanged conclusion shape shared by every non-allocating
strict-op arm. -/
theorem strictWfSame {σ : Store} {v : GoValue} (hw : StateWf ctx σ)
    (hv : GoValue.locSup v ≤ σ.nextAddr) :
    StateWf ctx σ ∧ σ.nextAddr ≤ σ.nextAddr
      ∧ GoValue.locSup v ≤ σ.nextAddr :=
  ⟨hw, Nat.le_refl _, hv⟩

theorem zip_snd_sup_le {keys : List Int} {vs : List GoValue} :
    supBy (fun p => GoValue.locSup p.2) ((keys.zip vs).toArray.toList)
      ≤ goValueListSup vs := by
  rw [goValueListSup_eq]
  refine supBy_le_iff.mpr fun p hp => ?_
  have hp' : p ∈ keys.zip vs := by simpa using hp
  exact supBy_mem (List.of_mem_zip hp').2

/-- The `float-bits` primitive yields a scalar: no location in the result. -/
theorem floatBitsApply_locSup {op : FloatBitsOp} {v r : GoValue}
    (h : floatBitsApply op v = .ok r) : GoValue.locSup r = 0 := by
  unfold floatBitsApply at h
  split at h <;> (try split at h) <;>
    first
    | (simp [unsupported, stuck, throw, throwThe, MonadExceptOf.throw] at h; done)
    | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h; simp [GoValue.locSup]; done)

set_option maxHeartbeats 1600000 in
theorem applyStrictOp_wf {σ : Store} {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue}
    {v : GoValue} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStrictOp ctx σ leafOf op vs = .ok (v, σ', tr)) :
    StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr
      ∧ GoValue.locSup v ≤ σ'.nextAddr := by
  have hheap := hw.heap_le
  rw [applyStrictOp.eq_def] at h
  split at h
  · -- add
    split at h
    · -- int + int
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
    · -- float + float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · -- string + string
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- sub
    split at h
    · -- float - float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- mul
    split at h
    · -- float * float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- div
    split at h
    · -- float / float (dispatches BEFORE the int zero check; never panics)
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨d, hd, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- mod
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨d, hd, h⟩ := h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- shiftLeft
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intShiftLeftResult_locSup hiv]; omega)
  · -- shiftRight
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intShiftRightResult_locSup hiv]; omega)
  · -- bitAnd
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitOr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitXor
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitClear
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitClearResult_locSup hiv]; omega)
  · -- bitNeg
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitNegResult_locSup hiv]; omega)
  · -- neg (value-directed unary minus): int/float scalars out
    split at h <;>
      first
      | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h;
         obtain ⟨rfl, rfl, rfl⟩ := h;
         exact strictWfSame hw (by simp [GoValue.locSup]))
      | simp [Bind.bind, Except.bind] at h
  · -- floatLit (nullary; the rational kernel's scalar out)
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
  · -- not
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- eqCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- neqCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- atMostCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- atLeastCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- lessCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- greaterCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- convert
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨cv, hcv, rfl, rfl, rfl⟩ := h
    have := convertValueToTy_locSup hcv
    simp only [goValueListSup] at hvs
    exact strictWfSame hw (by omega)
  · -- bytesFromString: the ONE allocating arm
    split at h
    · rename_i bytes
      try dsimp only at h
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨base, σa⟩, halloc, h⟩ := h
      · try dsimp only at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hvb : GoValue.locSup (.array (bytes.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) IntKind.uint8)) ≤ σ.nextAddr := by
          simp only [GoValue.locSup, goValueListSup_eq]
          refine Nat.le_trans (supBy_le_iff.mpr fun x hx => ?_) (Nat.zero_le _)
          rw [Array.toList_map] at hx
          obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
          exact Nat.le_refl _
        obtain ⟨w1, w2, w3⟩ := alloc_wf hw hvb halloc
        obtain ⟨d1, d2, d6⟩ := alloc_shape halloc
        refine ⟨w1, by omega, ?_⟩
        show Loc.locSup base ≤ σa.nextAddr
        omega
    · simp at h
  · -- stringFromByteSlice
    try dsimp only at h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sl, hsl, ⟨vals, trS⟩, hvals, h⟩ := h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨r, hr, rfl, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- stringFromRune
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- deref: the narrowed pointee read
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, ⟨lv, trL⟩, hlv, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have := loadLoc_locSup (Mem.loadFor_eq hlv).1
    exact strictWfSame hw (by omega)
  · -- addrOfDeref (BUG-056): nil-assert on the pointer VALUE, no load
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := h
    have := valueAsLoc_locSup hl
    simp only [goValueListSup] at hvs
    refine strictWfSame hw ?_
    show Loc.locSup l ≤ σ.nextAddr
    omega
  · -- fieldGet
    split at h
    · -- struct value
      split at h
      · -- field found
        rename_i fv hfv
        try dsimp only at h
        split at h
        · simp [Bind.bind, Except.bind] at h
        · simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have := StructFields.lookup_locSup hfv
          simp only [goValueListSup, GoValue.locSup] at hvs
          exact strictWfSame hw (by omega)
      · -- unknown field: stuck on both ite branches
        try dsimp only at h
        split at h <;> simp [Bind.bind, Except.bind] at h
    · simp at h
  · -- fieldAddr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := h
    have := valueAsLoc_locSup hl
    simp only [goValueListSup] at hvs
    refine strictWfSame hw ?_
    show Loc.locSup l ≤ σ.nextAddr
    omega
  · -- structLit
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sv, hsv, rfl, rfl, rfl⟩ := h
    have := buildStructValue_locSup hsv
    refine strictWfSame hw ?_
    have h2 : goValueListSup vs.toArray.toList = goValueListSup vs := by simp
    omega
  · -- arrayLit
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨av, hav, rfl, rfl, rfl⟩ := h
      have := buildArrayValue_locSup hav
      exact strictWfSame hw (Nat.le_trans this (Nat.le_trans zip_snd_sup_le hvs))
  · -- toInterface
    rename_i tgt dynm v0
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨dynTy, hdt, h⟩ := h
    simp only [goValueListSup] at hvs
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by omega)
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine strictWfSame hw ?_
      show GoValue.locSup v0 ≤ σ.nextAddr
      omega
  · -- typeAssert
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨res, hres, h⟩ := h
    obtain ⟨rv, rb⟩ := res
    have hb := typeAssertValue_locSup hres
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by omega)
    · exfalso
      revert h
      split <;> intro h
      · try simp only [bind_eq_ok] at h
        obtain ⟨m, hm, hc⟩ := h
        -- `typeAssertPanicMessage` is `Except Stop String` (audit fix
        -- round R1/R3, 2026-09-05): whichever way it goes, the result is
        -- an `.error` (a refusal, or the panic), never `.ok`.
        simp [Bind.bind, Except.bind, GoCore.panic, throw, throwThe, MonadExceptOf.throw] at hc
      · simp_all [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
        split at h <;> simp_all
  · -- indexGet
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, h⟩ := h
    simp only [goValueListSup] at hvs
    split at h
    · rename_i values
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨gv, hgv, rfl, rfl, rfl⟩ := h
      have hb := arrayGet_locSup hgv
      have h3 : GoValue.locSup (GoValue.array values)
          = goValueListSup values.toList := rfl
      exact strictWfSame hw (by omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨gv, hgv, rfl, rfl, rfl⟩ := h
      unfold stringByteGet at hgv
      simp only [letFun, Bind.bind, Except.bind, indexOutOfRangePanic] at hgv
      repeat' split at hgv
      all_goals
        first
          | (simp_all [GoCore.panic, throw, throwThe, MonadExceptOf.throw]; done)
          | (simp only [pure_eq_ok, Except.ok.injEq] at hgv
             subst hgv
             exact strictWfSame hw (by simp [GoValue.locSup]))
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨l, hl, ⟨lv, trL⟩, hlv, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have := loadLoc_locSup (Mem.load_eq hlv).1
      have h2 := sliceIndexLoc_locSup hl
      exact strictWfSame hw (by omega)
    · -- pointer-to-array read (triage L5): the element-narrowed load, then the projection
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨bv, trB⟩, hbv, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i values
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨gv, hgv, rfl, rfl, rfl, rfl⟩ := h
        have hb := arrayGet_locSup hgv
        have hload := loadLoc_locSup (Mem.loadFor_eq hbv).1
        have h3 : GoValue.locSup (GoValue.array values)
            = goValueListSup values.toList := rfl
        exact strictWfSame hw (by omega)
      · simp at h
    · -- nil pointer-to-array base (triage L6): the panic is never ok
      simp at h
    · simp at h
  · -- indexAddr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := h
    simp only [goValueListSup] at hvs
    have h2 := indexTargetLoc_locSup hl
    refine strictWfSame hw ?_
    show Loc.locSup l ≤ σ.nextAddr
    omega
  · -- mapGet
    try simp only [bind_eq_ok] at h
    obtain ⟨m, hm, key, hkey, h⟩ := h
    split at h
    · -- nil map
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, d, hd, rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
    · rename_i baseLoc
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨⟨entries, nextId⟩, trM⟩, hp, h⟩ := h
      try dsimp only at h
      try simp only [bind_eq_ok] at h
      obtain ⟨idx, hidx, h⟩ := h
      split at h
      · split at h
        · rename_i id' k' v' hp'
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have hmem : (id', k', v') ∈ entries.toList :=
            List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp')
          have h2 := mapPayload?_locSup (Mem.mapRead_eq hp).1
          have h3 := goValueEntriesSup_mem hmem
          simp only at h3
          exact strictWfSame hw (by omega)
        · simp at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
  · -- sliceExpr false
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨lo, hlo, hi, hhi, h⟩ := h
    cases hsl : applySlice ctx σ _ lo hi none with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sv, σs⟩ := p
      rw [hsl] at h
      simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨w, hw', rfl, rfl, rfl⟩ := h
      subst hw'
      obtain ⟨rfl, hb⟩ := applySlice_locSup hsl
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by dsimp only; omega)
  · -- sliceExpr true
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨lo, hlo, hi, hhi, mx, hmx, h⟩ := h
    cases hsl : applySlice ctx σ _ lo hi (some mx) with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sv, σs⟩ := p
      rw [hsl] at h
      simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨w, hw', rfl, rfl, rfl⟩ := h
      subst hw'
      obtain ⟨rfl, hb⟩ := applySlice_locSup hsl
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by dsimp only; omega)
  · -- lengthOf
    split at h
    · -- the type-static pointer-to-array arm: a pointer operand (C1 S2b fail-closed check)
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨bv, hbv, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [SeqRight.seqRight, Seq.seq, Function.const, Bind.bind,
          Except.bind, Functor.map, Except.map] at h
        split at h
        · simp at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨bv, trM⟩, hbv, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · -- chan: len(ch) — nil → 0; else the cell's buffer size
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨bv, hbv, h⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
  · -- capacityOf
    split at h
    · -- the type-static pointer-to-array arm: a pointer operand (C1 S2b fail-closed check)
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨bv, hbv, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp at h
      · simp only [SeqRight.seqRight, Seq.seq, Function.const, Bind.bind,
          Except.bind, Functor.map, Except.map] at h
        split at h
        · simp at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · -- chan: cap(ch) — nil → 0; else the cell's capacity
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨bv, hbv, h⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
  · -- funcValOf
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine strictWfSame hw ?_
    show goValueListSup vs ≤ σ.nextAddr
    omega
  · -- minOf
    rename_i v₀ rest
    simp only [goValueListSup] at hvs
    -- float-vs-ordered dispatch (triage L3): the IEEE fold's every ok
    -- step is one of the .float operands (locSup 0); the ordered fold
    -- keeps the pre-float invariant proof verbatim.
    split at h
    · -- IEEE float fold
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨best, hbest, rfl, rfl, rfl⟩ := h
      have hP := forIn_list_inv
        (P := fun b : GoValue => GoValue.locSup b ≤ σ.nextAddr)
        ?_ (by omega) hbest
      · exact strictWfSame hw hP
      · intro a ha b rr hbb hr
        rw [bind_eq_ok] at hr
        obtain ⟨c, hc, hr2⟩ := hr
        simp only [Bind.bind, Except.bind, Except.ok.injEq] at hr2
        subst hr2
        simp [forInStepVal, floatMinMax_locSup hc]
    · -- ordered fold
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨best, hbest, rfl, rfl, rfl⟩ := h
      have hP := forIn_list_inv
        (P := fun b : GoValue => GoValue.locSup b ≤ σ.nextAddr)
        ?_ (by omega) hbest
      · exact strictWfSame hw hP
      · intro a ha b rr hbb hr
        have hmem : GoValue.locSup a ≤ goValueListSup rest := by
          rw [goValueListSup_eq]; exact supBy_mem ha
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
        obtain ⟨c, hc, hr⟩ := hr
        split at hr <;>
          (simp_all only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq]
           try subst rr
           first
             | (show GoValue.locSup a ≤ σ.nextAddr
                omega)
             | (show GoValue.locSup b ≤ σ.nextAddr
                omega))
  · -- maxOf
    rename_i v₀ rest
    simp only [goValueListSup] at hvs
    split at h
    · -- IEEE float fold (as in minOf)
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨best, hbest, rfl, rfl, rfl⟩ := h
      have hP := forIn_list_inv
        (P := fun b : GoValue => GoValue.locSup b ≤ σ.nextAddr)
        ?_ (by omega) hbest
      · exact strictWfSame hw hP
      · intro a ha b rr hbb hr
        rw [bind_eq_ok] at hr
        obtain ⟨c, hc, hr2⟩ := hr
        simp only [Bind.bind, Except.bind, Except.ok.injEq] at hr2
        subst hr2
        simp [forInStepVal, floatMinMax_locSup hc]
    · -- ordered fold
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨best, hbest, rfl, rfl, rfl⟩ := h
      have hP := forIn_list_inv
        (P := fun b : GoValue => GoValue.locSup b ≤ σ.nextAddr)
        ?_ (by omega) hbest
      · exact strictWfSame hw hP
      · intro a ha b rr hbb hr
        have hmem : GoValue.locSup a ≤ goValueListSup rest := by
          rw [goValueListSup_eq]; exact supBy_mem ha
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
        obtain ⟨c, hc, hr⟩ := hr
        split at hr <;>
          (simp_all only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq]
           try subst rr
           first
             | (show GoValue.locSup a ≤ σ.nextAddr
                omega)
             | (show GoValue.locSup b ≤ σ.nextAddr
                omega))
  · -- runeAt
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨off, hoff, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · obtain ⟨_, _, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- runeSizeAt
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨off, hoff, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · obtain ⟨_, _, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- defaultValueOf
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
  · -- nilLit
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · -- chan: typed nil literal → the nil-channel default value
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · -- interface: typed nil literal → the nil interface (BUG-077)
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · -- funcType: typed nil literal → the nil func value (BUG-077)
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
      · simp at h
  · -- runesFromString: the second allocating arm (triage L1, mirrors
    -- bytesFromString's proof with the rune-decode map)
    split at h
    · rename_i str
      try dsimp only at h
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨base, σa⟩, halloc, h⟩ := h
      · try dsimp only at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hvb : GoValue.locSup (.array ((runesOfString str).map fun r =>
            GoValue.int r IntKind.int32)) ≤ σ.nextAddr := by
          simp only [GoValue.locSup, goValueListSup_eq]
          refine Nat.le_trans (supBy_le_iff.mpr fun x hx => ?_) (Nat.zero_le _)
          rw [Array.toList_map] at hx
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
          exact Nat.le_refl _
        obtain ⟨w1, w2, w3⟩ := alloc_wf hw hvb halloc
        obtain ⟨d1, d2, d6⟩ := alloc_shape halloc
        refine ⟨w1, by omega, ?_⟩
        show Loc.locSup base ≤ σa.nextAddr
        omega
    · simp at h
  · -- stringFromRuneSlice
    try dsimp only at h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sl, hsl, ⟨vals, trS⟩, hvals, h⟩ := h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨r, hr, rfl, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- floatBits (stdlib slice 3): a pure bit reinterpretation, loc-free result
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [floatBitsApply_locSup hr]; exact Nat.zero_le _)
  · -- catch-all
    simp at h

/-! ## `applyStmtOpCore` / `applyStmtOp` preserve well-formedness -/

theorem goValueListSup_take {vs : List GoValue} {n : Nat} :
    goValueListSup (vs.take n) ≤ goValueListSup vs := by
  simp only [goValueListSup_eq]
  exact supBy_le_of_subset fun a ha => List.take_subset _ _ ha

theorem goValueListSup_drop {vs : List GoValue} {n : Nat} :
    goValueListSup (vs.drop n) ≤ goValueListSup vs := by
  simp only [goValueListSup_eq]
  exact supBy_le_of_subset fun a ha => List.drop_subset _ _ ha

variable (ctx) in
/-- The conclusion shape of the wide-op preservation lemmas. -/
def StmtOpPres (σ σ' : Store) : Prop :=
  StateWf ctx σ' ∧ σ.nextAddr ≤ σ'.nextAddr

theorem stmtOpPres_refl {σ : Store} (hw : StateWf ctx σ) : StmtOpPres ctx σ σ :=
  ⟨hw, Nat.le_refl _⟩

theorem storeLoc_pres {σ : Store} {l : Loc} {v : GoValue} {σ' : Store}
    (hw : StateWf ctx σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) (h : storeLoc ctx σ l v = .ok σ') :
    StmtOpPres ctx σ σ' := by
  obtain ⟨h4, h5⟩ := storeLoc_shape h
  have hh := hw.heap_le
  exact ⟨StateWf.mk' (by omega) (HeapNormal.of_storeLoc hw.normal h), by omega⟩

/-- A whole-payload map store preserves the invariant (A3; the map-op
cases' `storeLoc_pres` replacement). `hl` is unused on the dense heap (a
root address is bounded by construction) and kept for call-site parity. -/
theorem storeMapPayload_pres {σ σ' : Store} {l : Loc}
    {entries : Array (Nat × GoValue × GoValue)} {nextId : Nat}
    (hw : StateWf ctx σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (he : goValueEntriesSup entries.toList ≤ σ.nextAddr)
    (h : storeMapPayload σ l entries nextId = .ok σ') : StmtOpPres ctx σ σ' := by
  have hn := HeapNormal.of_storeMapPayload hw.normal h
  unfold storeMapPayload at h
  split at h
  · obtain ⟨h4, cell, cell', hcell, hf, hsup⟩ :=
      Store.updateCell_shape h
    have hc : HeapCell.locSup cell' = goValueEntriesSup entries.toList := by
      cases cell with
      | mapPayload _ _ =>
        simp only [pure_eq_ok, Except.ok.injEq] at hf
        subst hf; rfl
      | value _ _ => simp [stuck, throw, throwThe, MonadExceptOf.throw] at hf
      | chanPayload _ _ _ => simp [stuck, throw, throwThe, MonadExceptOf.throw] at hf
    have hh := hw.heap_le
    exact ⟨StateWf.mk' (by omega) hn, by omega⟩
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- A whole-payload channel store preserves the invariant (A3). -/
theorem storeChanPayload_pres {σ σ' : Store} {l : Loc} {buf : Array GoValue}
    {capacity : Nat} {closed : Bool}
    (hw : StateWf ctx σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hb : goValueListSup buf.toList ≤ σ.nextAddr)
    (h : storeChanPayload σ l buf capacity closed = .ok σ') : StmtOpPres ctx σ σ' := by
  have hn := HeapNormal.of_storeChanPayload hw.normal h
  unfold storeChanPayload at h
  split at h
  · obtain ⟨h4, cell, cell', hcell, hf, hsup⟩ :=
      Store.updateCell_shape h
    have hc : HeapCell.locSup cell' = goValueListSup buf.toList := by
      cases cell with
      | chanPayload _ _ _ =>
        simp only [pure_eq_ok, Except.ok.injEq] at hf
        subst hf; rfl
      | value _ _ => simp [stuck, throw, throwThe, MonadExceptOf.throw] at hf
      | mapPayload _ _ => simp [stuck, throw, throwThe, MonadExceptOf.throw] at hf
    have hh := hw.heap_le
    exact ⟨StateWf.mk' (by omega) hn, by omega⟩
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem StmtOpPres.trans {σ₁ σ₂ σ₃ : Store} (a : StmtOpPres ctx σ₁ σ₂)
    (b : StmtOpPres ctx σ₂ σ₃) : StmtOpPres ctx σ₁ σ₃ := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  exact ⟨b1, by omega⟩

theorem Mem.store_pres {σ σ' : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) (h : Mem.store ctx σ l v = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' :=
  storeLoc_pres hw hl hv (Mem.store_eq h).1

theorem Mem.store_shape {σ σ' : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.store ctx σ l v = .ok (σ', tr)) : σ'.nextAddr = σ.nextAddr :=
  (storeLoc_shape (Mem.store_eq h).1).1

/-- A run of element writes preserves the invariant (the structural twin of
the former `forIn` loops of append/copy/clear). -/
theorem Mem.storeElems_pres {σ : Store} {base : Loc} :
    ∀ {vs : List GoValue} {start : Nat} {σ' : Store} {tr : AccessTrace},
      StateWf ctx σ → Loc.locSup base ≤ σ.nextAddr → goValueListSup vs ≤ σ.nextAddr →
      Mem.storeElems ctx σ base start vs = .ok (σ', tr) → StmtOpPres ctx σ σ' := by
  intro vs
  induction vs generalizing σ with
  | nil =>
    intro start σ' tr hw _ _ h
    simp only [Mem.storeElems, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact stmtOpPres_refl hw
  | cons v rest ih =>
    intro start σ' tr hw hb hvs h
    simp only [Mem.storeElems, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨s₁, t⟩, h1, ⟨s₂, ts⟩, h2, rfl, rfl⟩ := h
    simp only [goValueListSup] at hvs
    have p1 := Mem.store_pres hw (by rw [Loc.locSup_index]; exact hb) (by omega) h1
    have hn := Mem.store_shape h1
    obtain ⟨w1, w2⟩ := p1
    exact StmtOpPres.trans ⟨w1, w2⟩ (ih w1 (by omega) (by omega) h2)

theorem Mem.loadRun_locSup {σ : Store} {sl : SliceValue} {n : Nat} {vs : List GoValue}
    {tr : AccessTrace} (h : Mem.loadRun ctx σ sl n = .ok (vs, tr)) :
    goValueListSup vs ≤ Heap.locSup σ.heap := by
  unfold Mem.loadRun at h
  split at h
  · exact (Mem.loadElems_locSup h).1
  · split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [goValueListSup]
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem Mem.storeRun_pres {σ σ' : Store} {sl : SliceValue} {start : Nat} {vs : List GoValue}
    {tr : AccessTrace} (hw : StateWf ctx σ) (hb : optLocSup sl.base ≤ σ.nextAddr)
    (hvs : goValueListSup vs ≤ σ.nextAddr) (h : Mem.storeRun ctx σ sl start vs = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' := by
  unfold Mem.storeRun at h
  split at h
  · rename_i b hbase
    refine Mem.storeElems_pres hw ?_ hvs h
    simpa [hbase, optLocSup] using hb
  · split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact stmtOpPres_refl hw
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem goValueListSup_replicate {v : GoValue} : ∀ {n : Nat},
    goValueListSup (List.replicate n v) ≤ GoValue.locSup v
  | 0 => by simp [goValueListSup]
  | n + 1 => by
      simp only [List.replicate, goValueListSup]
      have := goValueListSup_replicate (v := v) (n := n)
      omega

theorem goValueListSup_eq_zero_of_ints : ∀ {l : List GoValue},
    (∀ v ∈ l, ∃ i k, v = .int i k) → goValueListSup l = 0
  | [], _ => rfl
  | v :: rest, h => by
      obtain ⟨i, k, rfl⟩ := h v List.mem_cons_self
      simp only [goValueListSup, GoValue.locSup]
      exact goValueListSup_eq_zero_of_ints fun w hw => h w (List.mem_cons_of_mem _ hw)

-- DELETED (C1 S3): `storeMany_pres` (with `storeMany`).


set_option maxHeartbeats 1600000 in
/-- `mapAssignValue` preserves the loc invariant (verbatim the old
`mapAssign` wide-op case; shared with `storeTarget`'s map-element arm,
convergence round BUG-030). -/
theorem mapAssignValue_pres {σ : Store} {keyTy valueTy : Ty}
    {baseV keyV valueV : GoValue} {σ' : Store}
    (hw : StateWf ctx σ)
    (hb : GoValue.locSup baseV ≤ σ.nextAddr)
    (hk : GoValue.locSup keyV ≤ σ.nextAddr)
    (hv : GoValue.locSup valueV ≤ σ.nextAddr) {tr : AccessTrace}
    (h : mapAssignValue ctx σ keyTy valueTy baseV keyV valueV = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' := by
  have hheap := hw.heap_le
  -- C1 S3: the VALIDATE phase (the RMW's peek, the key hash — `hplan`) yields
  -- the COMMIT (the one map write), which runs on `σ` (`h`).
  unfold mapAssignValue at h
  simp only [bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  unfold mapAssignValue.plan at hplan
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
  obtain ⟨m, hm, key, hkey, value, hvalue, hplan⟩ := hplan
  have hkb : GoValue.locSup key ≤ σ.nextAddr := by
    have := normalizeValueForTy_locSup hkey
    omega
  have hvb : GoValue.locSup value ≤ σ.nextAddr := by
    have := normalizeValueForTy_locSup hvalue
    omega
  obtain ⟨entriesOut, hentries, hplan⟩ := hplan
  split at hplan
  · simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hplan
  · rename_i baseLoc entries nextId
    obtain ⟨hbl, hent⟩ := mapEntries_locSup hentries rfl
    have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
      have := valueAsMap_locSup hm
      omega
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
    obtain ⟨idx, hidx, hplan⟩ := hplan
    split at hplan
    · rename_i i
      -- present key: same id, new key/value (E10 always-replace). The
      -- do-block's `let (entries, nextId) ← match …` lifts the
      -- continuation into the match arms, so split first.
      split at hplan
      · rename_i id k₀ v₀ hget
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨y, hy, hplan⟩ := hplan
        subst hy
        simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        refine storeMapPayload_pres hw hblb ?_ (Mem.mapWrite_eq h).1
        show goValueEntriesSup (entries.set! i (id, key, value)).toList ≤ σ.nextAddr
        refine Nat.le_trans goValueEntriesSup_set! ?_
        simp only at *
        omega
      · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw] at hplan
    · -- absent key: a fresh stamped entry
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨y, hy, hplan⟩ := hplan
      subst hy
      simp only [pure_eq_ok, Except.ok.injEq] at hplan
      subst hplan
      try dsimp only at h
      refine storeMapPayload_pres hw hblb ?_ (Mem.mapWrite_eq h).1
      show goValueEntriesSup (entries.push (nextId, key, value)).toList ≤ σ.nextAddr
      rw [goValueEntriesSup_push]
      simp only at *
      omega

/-- `resolveChain` output bound (round 4, BUG-033): the replayed
chain's cursor value stays bounded by the inputs and the heap (index
steps may read cells). The chain never allocates. -/
theorem resolveChain_locSup {σ : Store} :
    ∀ {steps : List TargetStep} {cur : GoValue} {idxs : List GoValue}
      {out : GoValue}, resolveChain ctx σ cur steps idxs = .ok out →
      GoValue.locSup out ≤
        max (max (GoValue.locSup cur) (goValueListSup idxs))
          (Heap.locSup σ.heap) := by
  intro steps
  induction steps with
  | nil =>
    intro cur idxs out h
    unfold resolveChain at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      omega
    · simp_all
    · simp_all
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  | cons st rest ih =>
    intro cur idxs out h
    unfold resolveChain at h
    cases st with
    | index =>
      cases idxs with
      | nil => simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      | cons i irest =>
        try simp only [bind_eq_ok] at h
        obtain ⟨l, hl, h⟩ := h
        have h2 := indexTargetLoc_locSup hl
        have h3 := ih h
        have h4 : GoValue.locSup (GoValue.addr l) = Loc.locSup l := rfl
        simp only [goValueListSup] at *
        omega
    | field tid f =>
      try simp only [bind_eq_ok] at h
      obtain ⟨l, hl, h⟩ := h
      have h2 := valueAsLoc_locSup hl
      have h3 := ih h
      have h4 : GoValue.locSup (GoValue.addr (Loc.field l tid f))
          = Loc.locSup l := rfl
      omega

/-- `applyRhsOp` output bound (round 4, BUG-034): the value source's
results are bounded by its operands and the heap (a lookup reads the
map cell); the state is untouched. -/
theorem applyRhsOp_locSup {σ : Store} {rop : RhsOp}
    {vs vals : List GoValue} {tr : AccessTrace} (h : applyRhsOp ctx σ rop vs = .ok (vals, tr)) :
    goValueListSup vals ≤ max (goValueListSup vs) (Heap.locSup σ.heap) := by
  unfold applyRhsOp at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    omega
  · -- mapLookup
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨m, hm, key, hkey, ⟨⟨rv, rb⟩, trM⟩, hpair, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 := mapLookupValue_locSup hpair
    simp only [goValueListSup, GoValue.locSup]
    omega
  · -- typeAssert
    rename_i targetTy value
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rv, rb⟩, hres, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 := typeAssertValue_locSup hres
    simp only [goValueListSup, GoValue.locSup]
    omega
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `storeTarget` preservation (convergence round, BUG-029; chain form
round 4, BUG-033): one phase-2 store keeps the loc invariant. -/
theorem storeTarget_pres {σ : Store} {r : TargetRef} {v : GoValue}
    {σ' : Store}
    (hw : StateWf ctx σ) (hr : TargetRef.locSup r ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) {tr : AccessTrace}
    (h : storeTarget ctx σ r v = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' := by
  have hheap := hw.heap_le
  -- C1 S3: the VALIDATE phase (chain resolution) yields the COMMIT (the write).
  unfold storeTarget at h
  simp only [bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  cases r with
  | chain anchor idxs steps =>
    simp only [storeTarget.plan, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
    obtain ⟨cur, hres, l, hl, rfl⟩ := hplan
    try dsimp only at h
    have h2 := resolveChain_locSup hres
    have h3 := valueAsLoc_locSup hl
    simp only [TargetRef.locSup, Nat.max_le] at hr
    exact Mem.store_pres hw (by omega) hv h
  | mapElem b k kt vt =>
    simp only [TargetRef.locSup, Nat.max_le] at hr
    simp only [storeTarget.plan] at hplan
    refine mapAssignValue_pres (keyTy := kt) (valueTy := vt) (tr := tr) hw hr.1 hr.2 hv ?_
    simp only [mapAssignValue, bind_eq_ok]
    exact ⟨c, hplan, h⟩

theorem applyStmtOpCore_wf {σ : Store} {op : StmtOp}
    {vs : List GoValue} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOpCore ctx σ op vs = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' := by
  have hheap := hw.heap_le
  -- C1 S3: the composed apply is its VALIDATE phase's COMMIT run on `σ`
  -- (`bind_eq_ok`); each arm decomposes the phase (`hplan`), then the
  -- commit (`h`, beta-reduced), and closes as it did before the split.
  unfold applyStmtOpCore at h
  simp only [bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  rw [applyStmtOpCore.plan.eq_def] at hplan
  split at hplan
  · -- allocNew
    rename_i typ
    split at hplan
    · rename_i tv value
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨loc, hloc, rfl⟩ := hplan
      have hlocb := valueAsLoc_locSup hloc
      try dsimp only at h
      simp only [bind_eq_ok] at h
      obtain ⟨⟨nloc, σa⟩, halloc, h⟩ := h
      try dsimp only at h
      obtain ⟨w1, w2, w3⟩ := alloc_wf hw (by omega) halloc
      obtain ⟨d1, d2, _⟩ := alloc_shape halloc
      refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
      refine Mem.store_pres w1 (by omega) ?_ h
      show Loc.locSup nloc ≤ σa.nextAddr
      exact w2
    · simp at hplan
  · -- makeSlice
    rename_i elem hasCap
    split at hplan
    all_goals try (simp [Bind.bind, Except.bind] at hplan; done)
    · -- no explicit cap
      rename_i tv lenV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨lenValue, hlenV, elemSize, hsz, hplan⟩ := hplan
      -- The R16 refusal (makeslice len/cap out of range) precedes the
      -- allocation: both panic branches are errors, never `.ok`.
      split at hplan
      · split at hplan <;> simp [Bind.bind, Except.bind] at hplan
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨backing, hbacking, loc, hloc, rfl⟩ := hplan
        have hb0 := buildDefaultArrayValue_locSup hbacking
        have hlocb := valueAsLoc_locSup hloc
        try dsimp only at h
        simp only [bind_eq_ok] at h
        obtain ⟨⟨base, σa⟩, halloc, h⟩ := h
        try dsimp only at h
        obtain ⟨w1, w2, w3⟩ := alloc_wf hw (by omega) halloc
        obtain ⟨d1, d2, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
    · -- explicit cap
      rename_i tv lenV capV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨lenValue, hlenV, capValue, hcapV, elemSize, hsz, hplan⟩ := hplan
      split at hplan
      · split at hplan <;> simp [Bind.bind, Except.bind] at hplan
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨backing, hbacking, loc, hloc, rfl⟩ := hplan
        have hb0 := buildDefaultArrayValue_locSup hbacking
        have hlocb := valueAsLoc_locSup hloc
        try dsimp only at h
        simp only [bind_eq_ok] at h
        obtain ⟨⟨base, σa⟩, halloc, h⟩ := h
        try dsimp only at h
        obtain ⟨w1, w2, w3⟩ := alloc_wf hw (by omega) halloc
        obtain ⟨d1, d2, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
  · -- makeMap
    rename_i hasSpace
    split at hplan
    all_goals try (simp [Bind.bind, Except.bind] at hplan; done)
    · -- no space hint
      rename_i tv
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨loc, hloc, rfl⟩ := hplan
      have hlocb := valueAsLoc_locSup hloc
      try dsimp only at h
      cases halloc : σ.allocCell (.mapPayload #[] 0) with
      | mk base s₁ =>
        rw [halloc] at h
        try dsimp only at h
        obtain ⟨w1, w2, w3⟩ := allocCell_wf hw
          (by simp [HeapCell.locSup, goValueEntriesSup]) halloc rfl
        obtain ⟨d1, d2, _⟩ := allocCell_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ s₁.nextAddr
        exact w2
    · -- with space hint
      rename_i tv spaceV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨sz, hsz, loc, hloc, rfl⟩ := hplan
      have hlocb := valueAsLoc_locSup hloc
      try dsimp only at h
      cases halloc : σ.allocCell (.mapPayload #[] 0) with
      | mk base s₁ =>
        rw [halloc] at h
        try dsimp only at h
        obtain ⟨w1, w2, w3⟩ := allocCell_wf hw
          (by simp [HeapCell.locSup, goValueEntriesSup]) halloc rfl
        obtain ⟨d1, d2, _⟩ := allocCell_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ s₁.nextAddr
        exact w2
  · -- makeChan
    rename_i elem hasCap
    split at hplan
    · -- no cap: capacity 0
      rename_i tv
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨loc, hloc, rfl⟩ := hplan
      have hlocb := valueAsLoc_locSup hloc
      try dsimp only at h
      cases halloc : σ.allocCell (.chanPayload #[] 0 false) with
      | mk base σa =>
        rw [halloc] at h
        try dsimp only at h
        obtain ⟨w1, w2, w3⟩ := allocCell_wf hw
          (by simp [HeapCell.locSup, goValueListSup]) halloc rfl
        obtain ⟨d1, d2, _⟩ := allocCell_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
    · -- explicit cap
      rename_i tv capV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at hplan
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨size, hsize, elemSize, hsz, hplan⟩ := hplan
      -- The R16 refusal (makechan size out of range) precedes the
      -- allocation; the surviving branch stores capacity `size.toNat`.
      split at hplan
      · simp [Bind.bind, Except.bind] at hplan
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨loc, hloc, rfl⟩ := hplan
        have hlocb := valueAsLoc_locSup hloc
        try dsimp only at h
        cases halloc : σ.allocCell (.chanPayload #[] size.toNat false) with
        | mk base σa =>
          rw [halloc] at h
          try dsimp only at h
          obtain ⟨w1, w2, w3⟩ := allocCell_wf hw
            (by simp [HeapCell.locSup, goValueListSup]) halloc rfl
          obtain ⟨d1, d2, _⟩ := allocCell_shape halloc
          refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
          refine Mem.store_pres w1 (by omega) ?_ h
          show optLocSup (some base) ≤ σa.nextAddr
          exact w2
    · simp [Bind.bind, Except.bind] at hplan
  · -- mapAssign
    rename_i keyTy valueTy
    split at hplan
    · rename_i baseV keyV valueV
      simp only [goValueListSup] at hvs
      refine mapAssignValue_pres (keyTy := keyTy) (valueTy := valueTy) (baseV := baseV)
        (keyV := keyV) (valueV := valueV) (tr := tr) hw (by omega) (by omega) (by omega) ?_
      simp only [mapAssignValue, bind_eq_ok]
      exact ⟨c, hplan, h⟩
    · simp at hplan
  · -- mapDelete
    rename_i keyTy
    split at hplan
    · rename_i baseV keyV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨m, hm, key, hkey, es, hes, hplan⟩ := hplan
      split at hplan
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨_, _, rfl⟩ := hplan
        try dsimp only at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact stmtOpPres_refl hw
      · rename_i baseLoc entries nextId
        obtain ⟨hbl, hent⟩ := mapEntries_locSup hes rfl
        have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
          have := valueAsMap_locSup hm
          omega
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
        obtain ⟨idx, hidx, hplan⟩ := hplan
        split at hplan
        · simp only [pure_eq_ok, Except.ok.injEq] at hplan
          subst hplan
          try dsimp only at h
          refine storeMapPayload_pres hw hblb ?_ (Mem.mapWrite_eq h).1
          show goValueEntriesSup _ ≤ σ.nextAddr
          refine Nat.le_trans goValueEntriesSup_eraseIdx! ?_
          omega
        · -- absent key: the unchanged payload is rewritten (the emitted write)
          simp only [pure_eq_ok, Except.ok.injEq] at hplan
          subst hplan
          try dsimp only at h
          refine storeMapPayload_pres hw hblb ?_ (Mem.mapWrite_eq h).1
          show goValueEntriesSup entries.toList ≤ σ.nextAddr
          omega
    · simp at hplan
  · -- clearMap
    split at hplan
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨m, hm, es, hes, hplan⟩ := hplan
      split at hplan
      · simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact stmtOpPres_refl hw
      · rename_i baseLoc entries nextId
        obtain ⟨hbl, hent⟩ := mapEntries_locSup hes rfl
        have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
          have := valueAsMap_locSup hm
          omega
        simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        refine storeMapPayload_pres hw hblb ?_ (Mem.mapWrite_eq h).1
        show goValueEntriesSup (#[] : Array (Nat × GoValue × GoValue)).toList ≤ σ.nextAddr
        simp [goValueEntriesSup]
    · simp at hplan
  · -- clearSlice: one emitting write per visible element (`Mem.storeRun`)
    rename_i elem
    split at hplan
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨sl, hsl, _, _, zero, hzero, rfl⟩ := hplan
      try dsimp only at h
      have hz := defaultValue_locSup hzero
      have hslb : optLocSup sl.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hsl
        omega
      refine Mem.storeRun_pres hw hslb ?_ h
      have := goValueListSup_replicate (v := zero) (n := sl.len)
      omega
    · simp at hplan
  · -- sortSlice (dead op): the visible elements read (`Mem.loadSlice`), the
    -- sorted ints written back (`Mem.storeRun`; ints are loc-free)
    rename_i elem
    split at hplan
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨sl, hsl, ⟨values, trR⟩, hvals, loaded, hloop, rfl⟩ := hplan
      have hslb : optLocSup sl.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hsl
        omega
      try dsimp only at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨s₁, trW⟩, hst, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Mem.storeRun_pres hw hslb ?_ hst
      rw [goValueListSup_eq_zero_of_ints]
      · exact Nat.zero_le _
      · intro w hw'
        simp only [List.mem_map] at hw'
        obtain ⟨⟨i, k⟩, -, rfl⟩ := hw'
        exact ⟨i, k, rfl⟩
    · simp at hplan
  · -- copySlice: the source run read, the destination run written, the count stored
    split at hplan
    · rename_i tv dstV srcV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨dst, hdst, src, hsrc, _, _, _, _, ⟨values, trR⟩, hread, tloc, htloc, rfl⟩ := hplan
      try dsimp only at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨current, trW⟩, hwrite, ⟨s', trT⟩, hst, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hdstb : optLocSup dst.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hdst
        omega
      have hvalsb : goValueListSup values ≤ σ.nextAddr :=
        Nat.le_trans (Mem.loadRun_locSup hread) hheap
      have hpres := Mem.storeRun_pres hw hdstb hvalsb hwrite
      refine StmtOpPres.trans hpres ?_
      obtain ⟨b1, b2⟩ := hpres
      refine Mem.store_pres b1 ?_ (by simp [GoValue.locSup]) hst
      have := valueAsLoc_locSup htloc
      omega
    · simp at hplan
  · -- print (stdlib slice 3): validates the operands, state unchanged
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
    obtain ⟨_, _, rfl⟩ := hplan
    try dsimp only at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact stmtOpPres_refl hw
  · -- appendSlice: dispatches through applyStmtOp
    simp only [throw, throwThe, MonadExceptOf.throw] at hplan
    cases hplan
  · -- randIntn (unit 5b): dispatches through applyStmtOp
    simp only [throw, throwThe, MonadExceptOf.throw] at hplan
    cases hplan

set_option maxHeartbeats 1600000 in
theorem applyStmtOp_wf {σ : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {σ' : Store} {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOp ctx σ ch op nt vs = .ok (σ', ch', ps, tr)) :
    StmtOpPres ctx σ σ' := by
  have hheap := hw.heap_le
  -- C1 S3: the VALIDATE phase (`hplan`), then its COMMIT on `σ` (`h`).
  unfold applyStmtOp at h
  simp only [bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  rw [applyStmtOp.plan.eq_def] at hplan
  split at hplan
  · -- appendSlice
    rename_i elem
    split at hplan
    · rename_i tv sliceV elemsV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
      obtain ⟨slice, hslice, elems, helems, _, _, _, _, ⟨elemValues, trE⟩, helemValues, hplan⟩ := hplan
      have hsliceb : optLocSup slice.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hslice
        omega
      have hvalsb : goValueListSup elemValues.toList ≤ σ.nextAddr := by
        have := Mem.loadSlice_locSup helemValues
        omega
      try dsimp only at hplan
      try simp only [bind_eq_ok] at hplan
      obtain ⟨tloc, htloc, hplan⟩ := hplan
      have htlocb : Loc.locSup tloc ≤ σ.nextAddr := by
        have := valueAsLoc_locSup htloc
        omega
      split at hplan
      · -- in-place path: the element writes (`Mem.storeRun`), then the header write
        simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        simp only [Commit.withStream, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨sp, trp⟩, ⟨⟨current, trW⟩, hwrite, ⟨s₂, trT⟩, hst, rfl, rfl⟩, hσ, hch, htr⟩ := h
        try dsimp only at hσ hch htr
        subst hσ
        have hpres : StmtOpPres ctx σ current := Mem.storeRun_pres hw hsliceb hvalsb hwrite
        refine StmtOpPres.trans hpres ?_
        obtain ⟨b1, b2⟩ := hpres
        refine Mem.store_pres b1 ?_ ?_ hst
        · omega
        · show optLocSup slice.base ≤ current.nextAddr
          omega
      · -- spill path
        simp only [Choices.consumeAt_appendSpill, bind_eq_ok, pure_eq_ok,
          Except.ok.injEq, Prod.mk.injEq] at hplan
        obtain ⟨elemSize, hsz, hplan⟩ := hplan
        -- The R16 growslice refusal precedes the choice consumption and
        -- the allocation (decided on newLen — choice-free).
        split at hplan
        · simp [Bind.bind, Except.bind] at hplan
        simp only [Choices.consumeAt_appendSpill, bind_eq_ok, pure_eq_ok,
          Except.ok.injEq, Prod.mk.injEq] at hplan
        obtain ⟨⟨oldValues, trO⟩, holdValues, backing, hbacking, hplan⟩ := hplan
        try dsimp only at hbacking hplan
        subst hplan
        try dsimp only at h
        simp only [Commit.withStream, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨sp, trp⟩, ⟨⟨base, σa⟩, halloc, ⟨σ₂, trT⟩, h, rfl, rfl⟩, hσ, hch, htr⟩ := h
        try dsimp only at halloc h hσ hch htr
        subst hσ
        have holdb : goValueListSup oldValues.toList ≤ σ.nextAddr := by
          have := Mem.loadSlice_locSup holdValues
          omega
        have hbb := buildAppendBackingValue_locSup hbacking
        obtain ⟨w1, w2, w3⟩ := alloc_wf hw (by omega) halloc
        obtain ⟨d1, d2, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega⟩ ?_
        refine Mem.store_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
    · simp at hplan
  · -- the `[0, n)` draw (unit 5b): the consult, then ONE `int` store into the
    -- validated target address (a loc-free value into a bounded loc), or — in
    -- the discarded-result shape — no store at all
    split at hplan
    · rename_i tv n
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok] at hplan
      obtain ⟨tloc, htloc, hplan⟩ := hplan
      have htlocb : Loc.locSup tloc ≤ σ.nextAddr := by
        have := valueAsLoc_locSup htloc
        omega
      split at hplan
      · simp at hplan
      · rcases hc : Choices.consumeAtE .intn n.toNat ch with ⟨pick, ch₁, ps₁⟩
        rw [hc] at hplan
        simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        simp only [Commit.withStream, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨sp, trp⟩, ⟨⟨s₂, trT⟩, hst, rfl, rfl⟩, hσ, hch, htr⟩ := h
        try dsimp only at hσ hch htr
        subst hσ
        exact Mem.store_pres hw htlocb (by simp [GoValue.locSup]) hst
    · rename_i n
      split at hplan
      · simp at hplan
      · rcases hc : Choices.consumeAtE .intn n.toNat ch with ⟨pick, ch₁, ps₁⟩
        rw [hc] at hplan
        simp only [pure_eq_ok, Except.ok.injEq] at hplan
        subst hplan
        try dsimp only at h
        simp only [Commit.withStream, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨sp, trp⟩, ⟨rfl, rfl⟩, hσ, hch, htr⟩ := h
        try dsimp only at hσ hch htr
        subst hσ
        exact stmtOpPres_refl hw
    · simp at hplan
  · -- every other arm dispatches to applyStmtOpCore
    rename_i op' hne
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
    obtain ⟨c₀, hcore, rfl⟩ := hplan
    try dsimp only at h
    simp only [Commit.withStream, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨σ₂, tr₂⟩, hc₀, hσ, hch, htr⟩ := h
    try dsimp only at hσ hch htr
    subst hσ
    refine applyStmtOpCore_wf (op := op) (tr := tr₂) hw hvs ?_
    simp only [applyStmtOpCore, bind_eq_ok]
    exact ⟨c₀, hcore, hc₀⟩


/-! ## Plan lemmas: operand lists of classified forms are bounded by the form -/

theorem assigneeExpr_locSup {a : Assignee} {e : Expr}
    (h : assigneeExpr a = some e) : Expr.locSup e ≤ Assignee.locSup a := by
  cases a with
  | var id =>
    simp only [assigneeExpr, Option.some.injEq] at h
    subst h
    simp [Assignee.locSup, Expr.locSup]
  | addr e' =>
    simp only [assigneeExpr, Option.some.injEq] at h
    subst h
    exact Nat.le_refl _
  | mapElem b k kt vt => simp [assigneeExpr] at h
  | unsupported f => simp [assigneeExpr] at h

theorem exprListSup_append {a b : List Expr} :
    exprListSup (a ++ b) = max (exprListSup a) (exprListSup b) := by
  simp [exprListSup_eq, supBy_append]

/-- The spine's operand expressions are bounded by the target
expression (round 4, BUG-033). -/
theorem targetSpine_locSup : ∀ (e : Expr),
    exprListSup (targetSpine e).2 ≤ Expr.locSup e := by
  intro e
  fun_induction targetSpine e with
  | case1 b i st ops heq ih =>
    rw [heq] at ih
    simp only [exprListSup_append, exprListSup, Expr.locSup, Nat.max_le] at ih ⊢
    omega
  | case2 b tid f st ops heq ih =>
    rw [heq] at ih
    simp only [exprListSup_append, exprListSup, Expr.locSup, Nat.max_le] at ih ⊢
    omega
  | case3 e _ _ =>
    simp only [exprListSup]
    omega

/-- One target plan's operand expressions are bounded by the assignee
(convergence round, BUG-029: phase-1 operand lists). -/
theorem targetPlan_locSup {a : Assignee} {sh : TargetShape} {ops : List Expr}
    (h : targetPlan a = some (sh, ops)) :
    exprListSup ops ≤ Assignee.locSup a := by
  cases a with
  | var id =>
    simp only [targetPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h⟩ := h
    subst h
    simp [Assignee.locSup, exprListSup, Expr.locSup]
  | addr e' =>
    simp only [targetPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h⟩ := h
    subst h
    exact targetSpine_locSup e'
  | mapElem b k kt vt =>
    simp only [targetPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h⟩ := h
    subst h
    simp only [Assignee.locSup, exprListSup]
    omega
  | unsupported f => simp [targetPlan] at h

theorem targetsPlan_locSup :
    ∀ {targets : List Assignee} {tps : List (TargetShape × List Expr)},
      targetsPlan targets = some tps →
      targetPlansSup tps ≤ assigneeListSup targets := by
  intro targets
  induction targets with
  | nil =>
    intro tps h
    simp only [targetsPlan, List.mapM_nil, Option.pure_def,
      Option.some.injEq] at h
    subst h
    simp [targetPlansSup]
  | cons a rest ih =>
    intro tps h
    rw [targetsPlan, List.mapM_cons] at h
    obtain ⟨⟨sh, ops⟩, he, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, htail, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    have h1 := targetPlan_locSup he
    have h2 := ih (show targetsPlan rest = some tail from htail)
    simp only [targetPlansSup, assigneeListSup]
    omega

theorem targetRefListSup_append {a b : List TargetRef} :
    targetRefListSup (a ++ b) = max (targetRefListSup a) (targetRefListSup b) := by
  induction a with
  | nil => simp [targetRefListSup]
  | cons x xs ih => simp [targetRefListSup, ih, Nat.max_assoc]

/-- A completed target reference is bounded by its operand values
(convergence round, BUG-029). -/
theorem completeTargetRef_locSup {sh : TargetShape} {ops : List GoValue}
    {r : TargetRef} (h : completeTargetRef sh ops = some r) :
    TargetRef.locSup r ≤ goValueListSup ops := by
  unfold completeTargetRef at h
  split at h
  · -- chain: the arity-checked if
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [TargetRef.locSup, goValueListSup]
      omega
    · simp at h
  · -- mapElem
    simp only [Option.some.injEq] at h
    subst h
    simp only [TargetRef.locSup, goValueListSup]
    omega
  · simp at h

theorem optExprSup_toList {e : Option Expr} :
    exprListSup e.toList ≤ optExprSup e := by
  cases e <;> simp [exprListSup, optExprSup]

set_option maxHeartbeats 800000 in
theorem strictPlan_locSup {e : Expr} {op : StrictOp} {args : List Expr}
    (h : strictPlan e = some (op, args)) :
    exprListSup args ≤ Expr.locSup e := by
  cases e <;>
    first
    | (simp_all [strictPlan]; done)
    | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp_all [exprListSup, Expr.locSup, optExprSup, Nat.max_le]
       done)
    | skip
  case arrayLit n elem pairs =>
    simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.locSup, exprListSup_eq, keyedExprListSup_eq]
    refine supBy_le_iff.mpr fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact supBy_mem (f := fun p : Int × Expr => Expr.locSup p.2) hp
  case slice b lo hi m =>
    cases m <;>
    · simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [exprListSup, Expr.locSup, optExprSup, Nat.max_le]
      try omega

set_option maxHeartbeats 800000 in
theorem stmtPlan_locSup {stmt : Stmt} {op : StmtOp} {nt : Nat} {es : List Expr}
    (h : stmtPlan stmt = some (op, nt, es)) :
    exprListSup es ≤ Stmt.locSup stmt := by
  cases stmt <;>
    first
    | (simp [stmtPlan] at h; done)
    | skip
  case print newline args =>
    simp only [stmtPlan] at h
    split at h
    · simp at h
    · rename_i e rest heq
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      simp only [Stmt.locSup, heq]
      exact Nat.le_refl _
  case allocNew target value typ =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case makeSlice target elem len cap =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    have h2 : exprListSup cap.toList ≤ optExprSup cap := optExprSup_toList
    simp only [Stmt.locSup, exprListSup_append, exprListSup, Nat.max_le]
    omega
  case makeMap target kt vt space =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    have h2 : exprListSup space.toList ≤ optExprSup space := optExprSup_toList
    simp only [Stmt.locSup, exprListSup_append, exprListSup, Nat.max_le]
    omega
  case makeChan target elem capacity =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    have h2 : exprListSup capacity.toList ≤ optExprSup capacity := optExprSup_toList
    simp only [Stmt.locSup, exprListSup_append, exprListSup, Nat.max_le]
    omega
  case mapAssign b i v kt vt =>
    simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case mapDelete b i kt =>
    simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case clearMap b =>
    simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case clearSlice b elem =>
    simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case sortSlice b elem =>
    simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case randIntn target n =>
    -- unit 5b: the target's address (when there is one), then the bound
    cases target with
    | none =>
      simp only [stmtPlan, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      simp only [Stmt.locSup, exprListSup, Nat.max_le]
      omega
    | some t =>
      simp only [stmtPlan] at h
      obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      have h1 := assigneeExpr_locSup hte
      simp only [Stmt.locSup, exprListSup, Nat.max_le]
      omega
  case appendSlice target elem sl els =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case copySlice target dst src =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega


/-! ## Continuation-operation lemmas -/

theorem stmtListSup_append {a b : List Stmt} :
    stmtListSup (a ++ b) = max (stmtListSup a) (stmtListSup b) := by
  simp [stmtListSup_eq, supBy_append]

theorem seqCont_locSup {ss : List Stmt} {env : LocalEnv} {k : Cont} :
    Cont.locSup (seqCont ss env k)
      ≤ max (stmtListSup ss) (max (LocalEnv.locSup env) (Cont.locSup k)) := by
  cases_cont k <;>
    simp [seqCont, Cont.locSup, stmtListSup_append, Nat.max_le] <;>
    first
      | omega
      | (split <;> simp [Cont.locSup, stmtListSup_append, Nat.max_le] <;> omega)

theorem pushDefer_locSup {d : GoValue × List GoValue} :
    ∀ {k k' : Cont}, pushDefer d k = some k' →
      Cont.locSup k'
        ≤ max (max (GoValue.locSup d.1) (goValueListSup d.2)) (Cont.locSup k) := by
  intro k k' h
  simp only [pushDefer, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, k₁⟩, hr, rfl⟩ := h
  refine (Cont.rebuild_locSup (μ := fun _ => 0) ?_ k u k₁ hr).2
  intro k b k' ha
  split at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    simp only [Cont.locSup, deferListSup, Nat.max_le]
    omega
  · cases ha

theorem panicPassthrough_locSup {k k' : Cont}
    (h : panicPassthrough k = some k') : Cont.locSup k' ≤ Cont.locSup k := by
  unfold panicPassthrough at h
  split at h
  · exact Cont.tail_locSup_le h
  · cases h

theorem markNewestRecovered_locSup :
    ∀ {chain : List PanicEntry} {v : GoValue} {chain' : List PanicEntry},
      markNewestRecovered chain = some (v, chain') →
      GoValue.locSup v ≤ panicChainSup chain
        ∧ panicChainSup chain' ≤ panicChainSup chain := by
  intro chain
  induction chain with
  | nil => intro v chain' h; simp [markNewestRecovered] at h
  | cons e rest ih =>
    intro v chain' h
    cases rest with
    | nil =>
      simp only [markNewestRecovered] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        constructor
        · simp [panicChainSup]
        · simp [panicChainSup]
    | cons e₂ rest₂ =>
      simp only [markNewestRecovered, Option.map_eq_some_iff] at h
      obtain ⟨⟨v₀, rest'⟩, hrec, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ih hrec
      simp only [panicChainSup] at ih1 ih2 ⊢
      omega

/-- Below the deferred frame (G-P S2 `recoverAtDeferred`, replacing
`recoverThroughWrappers_locSup`): the payload and the marked marker are
bounded by the marker. -/
theorem recoverAtDeferred_locSup {k : Cont} {v : GoValue} {k' : Cont}
    (h : recoverAtDeferred k = some (v, k')) :
    GoValue.locSup v ≤ Cont.locSup k ∧ Cont.locSup k' ≤ Cont.locSup k := by
  cases_cont k <;> try (simp [recoverAtDeferred] at h; done)
  rename_i k₀ chain
  simp only [recoverAtDeferred, Option.map_eq_some_iff] at h
  obtain ⟨⟨v₀, chain'⟩, hmark, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨m1, m2⟩ := markNewestRecovered_locSup hmark
  constructor <;> (simp only [Cont.locSup, Nat.max_le] at m1 m2 ⊢; omega)

theorem recoverResult_locSup :
    ∀ {k : Cont} {v : GoValue} {k' : Cont}, recoverResult k = (v, k') →
      GoValue.locSup v ≤ Cont.locSup k ∧ Cont.locSup k' ≤ Cont.locSup k := by
  intro k v k' h
  unfold recoverResult at h
  cases hr : Cont.rebuild Cont.isGlue _ k with
  | none =>
    rw [hr] at h
    simp only [Option.getD_none, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  | some p =>
    obtain ⟨v₁, k₁⟩ := p
    rw [hr] at h
    simp only [Option.getD_some, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := Cont.rebuild_locSup (μ := GoValue.locSup) (bound := 0) ?_ k v₁ k₁ hr
    · simpa using this
    intro k b k' ha
    split at ha
    · rename_i t te r ds f k₀
      simp only [Option.some.injEq] at ha
      cases hin : recoverAtDeferred k₀ with
      | none =>
        rw [hin] at ha
        simp only [Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        simp [GoValue.locSup]
      | some q =>
        obtain ⟨v₀, k₁⟩ := q
        rw [hin] at ha
        simp only [Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        obtain ⟨m1, m2⟩ := recoverAtDeferred_locSup hin
        constructor <;> (simp only [Cont.locSup, Nat.max_le] at m1 m2 ⊢; omega)
    · simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      simp [GoValue.locSup]

/-- The configuration a CALL position delivers is bounded by its entry, the
plans, the environment and the continuation (G-P S2, both `Entry` arms). -/
theorem Entry.callConfig_bounded {plans : List (TargetShape × List Expr)} {env : LocalEnv}
    {k : Cont} {e : Entry} {bound : Nat}
    (he : Entry.locSup e ≤ bound) (hp : targetPlansSup plans ≤ bound)
    (henv : LocalEnv.locSup env ≤ bound) (hk : Cont.locSup k ≤ bound) :
    Config.locSup (e.callConfig plans env k) ≤ bound := by
  cases e with
  | run func frameEnv resultLocs =>
    simp only [Entry.locSup, Nat.max_le] at he
    simp only [Entry.callConfig, Config.locSup, Cont.locSup, deferListSup, Nat.max_le]
    omega
  | again fid args =>
    simp only [Entry.locSup] at he
    simp only [Entry.callConfig, Config.locSup, Cont.locSup, GoValue.locSup, exprListSup, Nat.max_le]
    omega

/-- The configuration a DRAIN (or the spawn) delivers is bounded by its
entry, the barrier and the re-queue's bound (G-P S2, both `Entry` arms). -/
theorem Entry.drainConfig_bounded {barrier : Cont} {requeue : GoValue → Config} {e : Entry}
    {bound : Nat}
    (he : Entry.locSup e ≤ bound) (hb : Cont.locSup barrier ≤ bound)
    (hreq : ∀ cv, GoValue.locSup cv ≤ bound → Config.locSup (requeue cv) ≤ bound) :
    Config.locSup (e.drainConfig barrier requeue) ≤ bound := by
  cases e with
  | run func frameEnv resultLocs =>
    simp only [Entry.locSup, Nat.max_le] at he
    simp only [Entry.drainConfig, Config.locSup, Cont.locSup, deferListSup, locListSup,
      targetPlansSup, LocalEnv.locSup, Scope.locSup, Nat.max_le]
    omega
  | again fid args =>
    simp only [Entry.locSup] at he
    exact hreq (.funcVal fid args) (by simpa [GoValue.locSup] using he)

/-! ## Small append/list bridges for the preservation closers -/

theorem goValueListSup_append {a b : List GoValue} :
    goValueListSup (a ++ b) = max (goValueListSup a) (goValueListSup b) := by
  simp [goValueListSup_eq, supBy_append]

theorem locListSup_append {a b : List Loc} :
    locListSup (a ++ b) = max (locListSup a) (locListSup b) := by
  simp [locListSup_eq, supBy_append]

theorem panicChainSup_append {a b : List PanicEntry} :
    panicChainSup (a ++ b) = max (panicChainSup a) (panicChainSup b) := by
  simp [panicChainSup_eq, supBy_append]

/-- The preprint phase's collapse mark touches no payload (unit 6b). -/
theorem panicChainSup_markLastRepanicked :
    ∀ {l : List PanicEntry}, panicChainSup (markLastRepanicked l) = panicChainSup l
  | [] => rfl
  | [e] => by simp [markLastRepanicked, panicChainSup]
  | e :: e' :: rest => by
    simp only [markLastRepanicked, panicChainSup]
    rw [panicChainSup_markLastRepanicked (l := e' :: rest)]
    rfl

/-- The phase's collapse drops an entry and marks another: never a new location. -/
theorem panicChainSup_preprintDrop {older newer : List PanicEntry} :
    panicChainSup (preprintDrop older newer) = max (panicChainSup older) (panicChainSup newer) := by
  simp [preprintDrop, panicChainSup_append, panicChainSup_markLastRepanicked]

theorem goValueListSup_reverse {a : List GoValue} :
    goValueListSup a.reverse = goValueListSup a := by
  simp [goValueListSup_eq, supBy_reverse]

theorem goValueEntriesSup_eraseIdxA {arr : Array (Nat × GoValue × GoValue)} {i : Nat}
    {hlt : i < arr.size} :
    goValueEntriesSup ((arr.eraseIdx i hlt).toList) ≤ goValueEntriesSup arr.toList :=
  goValueEntriesSup_eraseIdx

theorem runtimeErrorValue_locSup {msg : String} :
    GoValue.locSup (runtimeErrorValue msg) = 0 := rfl

/-- A fresh runtime-panic chain entry (B2's `panicEntry`) is loc-free. -/
@[simp] theorem panicEntry_locSup {msg : String} :
    GoValue.locSup (panicEntry msg).value = 0 := rfl

@[simp] theorem panicChainSup_panicEntry {msg : String} :
    panicChainSup [panicEntry msg] = 0 := rfl

theorem stringPanicValue_locSup {msg : String} :
    GoValue.locSup (stringPanicValue msg) = 0 := rfl

/-- `panicPayload` never introduces locations: the nil arm's runtime
error is loc-free, every other payload passes through (modern
`panic(nil)` semantics, arc-final audit F21 2026-08-06). -/
theorem panicPayload_locSup {v : GoValue} :
    GoValue.locSup (panicPayload v) ≤ GoValue.locSup v := by
  cases v <;> simp [panicPayload, runtimeErrorValue_locSup, panicEntry_locSup, GoValue.locSup]


/-! ## Channel-step preservation lemmas (channels arc slice 1) -/

theorem valueAsChan_locSup {v : GoValue} {ch : ChanValue}
    (h : valueAsChan v = .ok ch) : optLocSup ch.base ≤ GoValue.locSup v := by
  cases v <;> simp_all [valueAsChan, GoValue.locSup]

theorem goValueListSup_mem {l : List GoValue} {v : GoValue} (h : v ∈ l) :
    GoValue.locSup v ≤ goValueListSup l := by
  rw [goValueListSup_eq]; exact supBy_mem h

theorem goValueListSup_eraseIdx! {arr : Array GoValue} {i : Nat} :
    goValueListSup (arr.eraseIdx! i).toList ≤ goValueListSup arr.toList := by
  simp only [goValueListSup_eq]
  unfold Array.eraseIdx!
  split
  · rw [Array.toList_eraseIdx]
    exact supBy_le_of_subset fun a ha => List.mem_of_mem_eraseIdx ha
  · rw [show (panicWithPosWithDecl "Init.Data.Array.Basic" "Array.eraseIdx!" 1820 47
        "invalid index" : Array GoValue) = #[] from rfl]
    simp [supBy]

theorem recvStores_locSup {v : GoValue} {ok : Bool} :
    ∀ n, goValueListSup (recvStores v ok n) ≤ GoValue.locSup v
  | 0 => by simp [recvStores, goValueListSup]
  | 1 => by simp [recvStores, goValueListSup]
  | 2 => by simp [recvStores, goValueListSup, GoValue.locSup]
  | n + 3 => by simp [recvStores, goValueListSup]

theorem chanCell_locSup {σ : Store} {loc : Loc} {buf : Array GoValue}
    {capacity : Nat} {closed : Bool}
    (h : chanCell σ loc = .ok (buf, capacity, closed)) :
    goValueListSup buf.toList ≤ Heap.locSup σ.heap :=
  chanPayload?_locSup h

theorem chanPlan_locSup {stmt : Stmt} {op : ChanStOp}
    {es : List Expr} (h : chanPlan stmt = some (op, es)) :
    exprListSup es ≤ Stmt.locSup stmt
      ∧ chanStOpSup op ≤ Stmt.locSup stmt := by
  cases stmt <;>
    first
    | (simp [chanPlan] at h; done)
    | skip
  case chanSend ch v elem =>
    simp only [chanPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Stmt.locSup, chanStOpSup, exprListSup, Nat.max_le]
    omega
  case chanRecv targets ch elem =>
    simp only [chanPlan] at h
    split at h
    · simp at h
    · obtain ⟨tes, htes, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Stmt.locSup, chanStOpSup, exprListSup, Nat.max_le]
      omega
  case closeChan ch =>
    simp only [chanPlan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Stmt.locSup, chanStOpSup, exprListSup, Nat.max_le]
    omega

theorem selectOperands_locSup : ∀ {clauses : List (SelectClauseHead × Stmt)},
    exprListSup (selectOperands clauses) ≤ selectClausesSup clauses := by
  intro clauses
  induction clauses with
  | nil => simp [selectOperands, exprListSup, selectClausesSup]
  | cons c rest ih =>
    obtain ⟨hd, b⟩ := c
    cases hd <;>
      (simp only [selectOperands, exprListSup, selectClausesSup,
        selectClauseHeadSup, Nat.max_le] at ih ⊢) <;>
      omega

theorem evClausesSup_mem {l : List EvClause} {c : EvClause} (h : c ∈ l) :
    evClauseSup c ≤ evClausesSup l := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
    rcases h with _ | h
    · simp only [evClausesSup]
      exact Nat.le_max_left _ _
    · simp only [evClausesSup]
      exact Nat.le_trans (ih ‹_›) (Nat.le_max_right _ _)

theorem evalClauses_sup :
    ∀ {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
      {evs : List EvClause}, evalClauses clauses vs = .ok evs →
      evClausesSup evs ≤ max (selectClausesSup clauses) (goValueListSup vs) := by
  intro clauses
  induction clauses with
  | nil =>
    intro vs evs h
    cases vs <;> simp_all [evalClauses, evClausesSup]
    all_goals simp_all [stuck, throw, throwThe, MonadExceptOf.throw]
  | cons c rest ih =>
    intro vs evs h
    obtain ⟨hd, b⟩ := c
    cases hd with
    | send ch v elem =>
      cases vs with
      | nil => simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
      | cons chv vs' =>
        cases vs' with
        | nil => simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
        | cons vv vs'' =>
          simp only [evalClauses, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨tail, htail, rfl⟩ := h
          have := ih htail
          simp only [evClausesSup, evClauseSup, selectClausesSup,
            selectClauseHeadSup, goValueListSup, Nat.max_le] at this ⊢
          omega
    | recv targets ch elem =>
      cases vs with
      | nil => simp [evalClauses, stuck, throw, throwThe, MonadExceptOf.throw] at h
      | cons chv vs' =>
        simp only [evalClauses] at h
        split at h
        · rename_i tes htes
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨tail, htail, rfl⟩ := h
          have := ih htail
          simp only [evClausesSup, evClauseSup, selectClausesSup,
            selectClauseHeadSup, goValueListSup, Nat.max_le] at this ⊢
          omega
        · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem readyClauses_subset {σ : Store} :
    ∀ {l rc : List EvClause}, readyClauses σ l = .ok rc → ∀ c ∈ rc, c ∈ l := by
  intro l
  induction l with
  | nil =>
    intro rc h c hc
    simp only [readyClauses, pure_eq_ok, Except.ok.injEq] at h
    subst h
    cases hc
  | cons a rest ih =>
    intro rc h c hc
    simp only [readyClauses, bind_eq_ok] at h
    obtain ⟨tail, htail, h⟩ := h
    obtain ⟨rdy, hrdy, h⟩ := h
    split at h <;> simp only [pure_eq_ok, Except.ok.injEq] at h <;> rw [← h] at hc
    · cases hc with
      | head => exact List.mem_cons_self ..
      | tail _ hmem => exact List.mem_cons_of_mem _ (ih htail _ hmem)
    · exact List.mem_cons_of_mem _ (ih htail _ hc)

/-- `enterRecvTargets` preservation (convergence round, BUG-029): the
phase-1 entry configuration is bounded; the state is untouched. -/
theorem enterRecvTargets_wf {σ : Store} {targets : List Assignee}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c' : Config} {σ' : Store}
    (hw : StateWf ctx σ)
    (ht : assigneeListSup targets ≤ σ.nextAddr)
    (hvals : goValueListSup vals ≤ σ.nextAddr)
    (hbody : Stmt.locSup body ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : enterRecvTargets σ targets vals body env k = .ok (c', σ')) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  unfold enterRecvTargets at h
  split at h
  · rename_i sh e ops rest hplan
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hw, ?_, Nat.le_refl _⟩
    have hplans := targetsPlan_locSup hplan
    simp only [targetPlansSup, exprListSup, Nat.max_le] at hplans
    simp only [Config.locSup, Cont.locSup, goValueListSup, exprListSup,
      targetRefListSup, targetPlansSup, Nat.max_le]
    omega
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `commitClause` preservation: state stays wf (allocator monotone,
types unchanged) and the successor configuration is bounded. -/
theorem commitClause_wf {σ : Store} {env : LocalEnv} {k : Cont}
    {cl : EvClause} {c' : Config} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hcl : evClauseSup cl ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : commitClause ctx σ env k cl = .ok (c', σ', tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  have hheap := hw.heap_le
  rw [commitClause.eq_def] at h
  split at h
  · -- sendEv
    rename_i chv vv elem body
    simp only [evClauseSup, Nat.max_le] at hcl
    try simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i loc hbase
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
          Nat.max_le]
        omega
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨v', hv', σ₂, hst, h⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hv'b : GoValue.locSup v' ≤ σ.nextAddr := by
            have := normalizeValueForTy_locSup hv'
            omega
          obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
            (by rw [goValueListSup_push]
                omega) hst
          refine ⟨w1, ?_, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · -- recvEv
    rename_i chv targets elem body
    simp only [evClauseSup, Nat.max_le] at hcl
    try simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i loc hbase
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      -- The `let (v, ok, s₁) ← match …` prelude inlines its continuation
      -- into each branch: split on the dequeue-or-zero match first.
      split at h
      · -- dequeue
        rename_i v₀ hv₀
        have hv0b : GoValue.locSup v₀ ≤ σ.nextAddr := by
          have := goValueListSup_mem (l := buf.toList) (v := v₀)
            (List.mem_of_getElem? (by simpa using hv₀))
          omega
        simp only [pure_bind, bind_eq_ok] at h
        obtain ⟨σ₁, hst, h⟩ := h
        obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
          (by
              exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨w1, ?_, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · rename_i t ts
          try simp only [bind_eq_ok] at h
          obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf w1
            (by omega)
            (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
            (by omega) (by omega) (by omega) hent
          exact ⟨q1, by simpa using q2, Nat.le_trans w2 q4⟩
      · -- closed-and-drained or unready
        split at h
        · simp only [pure_bind, bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          have hzb : GoValue.locSup z ≤ σ.nextAddr := by
            rw [defaultValue_locSup hz]; omega
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨hw, ?_, Nat.le_refl _⟩
            simp only [Config.locSup, Nat.max_le]
            omega
          · rename_i t ts
            try simp only [bind_eq_ok] at h
            obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf hw
              (by omega)
              (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
              (by omega) (by omega) (by omega) hent
            exact ⟨q1, by simpa using q2, q4⟩
        · simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind,
            Except.bind] at h

set_option maxHeartbeats 1600000 in
/-- `applyChanOp` preservation: wf state out, bounded successor
configuration, types unchanged, allocator monotone. (The
`σ.nextAddr ≤ σ'.nextAddr` conjunct is the MultiWf discharge route's
step-level monotonicity — the slice-3 build log's recorded plan: extend
the existing `*_wf` conclusions rather than build a parallel
premise-free family.) -/
theorem applyChanOp_wf {σ : Store} {op : ChanStOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (hop : chanStOpSup op ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applyChanOp ctx σ op vs env k = .ok (c', σ', tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  have hheap := hw.heap_le
  rw [applyChanOp.eq_def] at h
  split at h
  · -- send
    rename_i elem chv vv
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    obtain ⟨v', hv', h⟩ := h
    have hchb := valueAsChan_locSup hch
    have hv'b : GoValue.locSup v' ≤ σ.nextAddr := by
      have := normalizeValueForTy_locSup hv'
      omega
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, Nat.le_refl _⟩
      simp only [Config.locSup, optLocSup, Nat.max_le]
      omega
    · rename_i loc hbase
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
          Nat.max_le]
        omega
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
          obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
            (by rw [goValueListSup_push]
                omega) hst
          refine ⟨w1, ?_, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hw, ?_, Nat.le_refl _⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · -- recv (audit response BUG-022: communication FIRST, then targets)
    rename_i targets elem chv
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [chanStOpSup] at hop
    try simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, Nat.le_refl _⟩
      simp only [Config.locSup, optLocSup, Nat.max_le]
      omega
    · rename_i loc hbase
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · -- dequeue, then deliver (targets post-communication)
        rename_i v hv
        have hvb : GoValue.locSup v ≤ σ.nextAddr := by
          have := goValueListSup_mem (l := buf.toList) (v := v)
            (List.mem_of_getElem? (by simpa using hv))
          omega
        try simp only [bind_eq_ok] at h
        obtain ⟨σ₁, hst, h⟩ := h
        obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
          (by
              exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨w1, ?_, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · rename_i t ts
          try simp only [bind_eq_ok] at h
          obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf w1
            (by omega)
            (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
            (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
          exact ⟨q1, by simpa using q2, Nat.le_trans w2 q4⟩
      · split at h
        · -- closed-and-drained: zero value, then deliver
          try simp only [bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          have hzb : GoValue.locSup z ≤ σ.nextAddr := by
            rw [defaultValue_locSup hz]; omega
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨hw, by simp only [Config.locSup, Nat.max_le]; omega, Nat.le_refl _⟩
          · rename_i t ts
            try simp only [bind_eq_ok] at h
            obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf hw
              (by omega)
              (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
              (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
            exact ⟨q1, by simpa using q2, q4⟩
        · -- open-and-empty: block
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hw, ?_, Nat.le_refl _⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · -- close
    rename_i chv
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, Nat.le_refl _⟩
      simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
        Nat.max_le]
      omega
    · rename_i loc hbase
      try simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
          Nat.max_le]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeChanPayload_pres hw hlocb
          (by
              omega) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup, Nat.max_le]
        omega
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `syncPlan` extraction is loc-bounded by the statement (the
`chanPlan_locSup` twin, spec-parity slice 2). -/
theorem syncPlan_locSup {stmt : Stmt} {op : SyncOp}
    {es : List Expr} (h : syncPlan stmt = some (op, es)) :
    exprListSup es ≤ Stmt.locSup stmt
      ∧ syncOpSup op ≤ Stmt.locSup stmt := by
  cases stmt <;>
    first
    | (simp [syncPlan] at h; done)
    | skip
  case syncStmt sop args targets =>
    cases sop <;> simp only [syncPlan, syncPlan.tryPlan] at h <;> repeat' split at h
    all_goals try (simp at h; done)
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
    all_goals
      refine ⟨?_, ?_⟩
      · simpa [Stmt.locSup] using Nat.le_max_left _ _
      · simp only [Stmt.locSup, syncOpSup]
        first
        | exact Nat.zero_le _
        | exact Nat.le_max_right _ _
        | (simp only [assigneeListSup]; exact Nat.zero_le _)
        -- The TRY heads' one-target plan: `targets.toList = [t]` is the
        -- split's equation; the target list's sup IS the statement's.
        | (rename_i ht _ _ _; rw [ht]; exact Nat.le_max_right _ _)

/-- The lock/counter cells store LOC-FREE values, so a sync cell store
never raises any sup. -/
theorem syncData_locSup (p : SyncPrim) : GoValue.locSup (.syncData p) = 0 := rfl

/-- `atomicPlan` extraction is loc-bounded by the statement (the
`syncPlan_locSup` twin, atomics arc wave 1). -/
theorem atomicPlan_locSup {stmt : Stmt} {op : AtomicOp}
    {es : List Expr} (h : atomicPlan stmt = some (op, es)) :
    exprListSup es ≤ Stmt.locSup stmt
      ∧ atomicOpSup op ≤ Stmt.locSup stmt := by
  cases stmt <;>
    first
    | (simp [atomicPlan] at h; done)
    | skip
  case atomicStmt aop kind args targets =>
    simp only [atomicPlan] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Stmt.locSup, atomicOpSup]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
    · simp at h

/-- `atomicCompute`'s result value is LOC-FREE (an integer, a bool, or
unit), so a delivery never raises any sup. -/
theorem atomicCompute_locSup {head : AtomicStmtOp} {kind : IntKind} {cur : Int}
    {ops : List GoValue} {new? : Option Int} {r : GoValue}
    (h : atomicCompute head kind cur ops = .ok (new?, r)) :
    GoValue.locSup r = 0 := by
  unfold atomicCompute at h
  split at h
  all_goals
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq,
      stuck, throw, throwThe, MonadExceptOf.throw] at h
  all_goals
    first
    | (obtain ⟨rfl, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, rfl, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, h⟩ := h
       split at h
       all_goals
         simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       all_goals
         first
         | (obtain ⟨rfl, rfl⟩ := h; rfl)
         | (obtain ⟨_, _, rfl, rfl⟩ := h; rfl))
    | (cases h)

set_option maxHeartbeats 1600000 in
/-- `applySyncOpCore` preservation (spec-parity slice 2, the
`applyChanOp_wf` twin): wf state out, bounded successor configuration,
types unchanged, allocator monotone. Sync stores are loc-free
(`syncData_locSup`), so every arm is either state-invariant or a
`storeLoc_pres` of a loc-free value. -/
theorem applySyncOpCore_wf {σ : Store} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (hop : syncOpSup op ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applySyncOpCore ctx σ op vs env k = .ok (c', σ', tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  -- Closers shared by every arm's outcomes.
  rw [applySyncOpCore.eq_def] at h
  split at h
  case _ av =>  -- lock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, syncOpSup, Nat.max_le]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- unlock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- rlock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, syncOpSup, Nat.max_le]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- runlock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- wlock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup, syncOpSup, Nat.max_le]
        omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- wunlock
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av dv =>  -- wgAdd
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨delta, hdelta, h⟩ := h
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · try simp only [bind_eq_ok] at h
      obtain ⟨σ₂, hst, h⟩ := h
      obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
        (by simp [syncData_locSup]) hst
      split at h <;>
        (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h;
         obtain ⟨rfl, rfl, rfl⟩ := h;
         refine ⟨w1, ?_, w2⟩;
         simp only [Config.locSup, panicChainSup, stringPanicValue_locSup,
           goValueListSup, Nat.max_le];
         omega)
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- wgWait
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup, syncOpSup, Nat.max_le]
        omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ targets av =>  -- onceBegin
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [syncOpSup] at hop
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · try simp only [bind_eq_ok] at h
        obtain ⟨σ₂, hst, h⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf w1
          (by omega) (by simp [goValueListSup, GoValue.locSup])
          (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
        exact ⟨q1, by simpa using q2, Nat.le_trans w2 q4⟩
      · split at h
        · try simp only [bind_eq_ok] at h
          obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf hw
            (by omega) (by simp [goValueListSup, GoValue.locSup])
            (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
          exact ⟨q1, by simpa using q2, q4⟩
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨hw, ?_, Nat.le_refl _⟩
          simp only [Config.locSup, syncOpSup, Nat.max_le]
          omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  case _ av =>  -- onceComplete
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨p, hcell, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl, rfl⟩ := h
        obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
          (by simp [syncData_locSup]) hst
        refine ⟨w1, ?_, w2⟩
        simp only [Config.locSup]
        omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  -- The TRY heads (`.internal` — they apply through `applySyncOp`) and
  -- the malformed-arity catch-all (`stuck`): no successor.
  all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `tryDeliver` preservation: the plain continuation is state-invariant;
the target entry is `enterRecvTargets_wf` over a loc-free Bool. -/
theorem tryDeliver_wf {σ : Store} {b : Bool} {targets : List Assignee}
    {env : LocalEnv} {k : Cont} {c' : Config} {σ' : Store}
    (hw : StateWf ctx σ) (ht : assigneeListSup targets ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : tryDeliver b σ targets env k = .ok (c', σ')) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  unfold tryDeliver at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hw, ?_, Nat.le_refl _⟩
    simp only [Config.locSup]
    omega
  · try simp only [bind_eq_ok] at h
    obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf hw
      (by omega) (by simp [goValueListSup, GoValue.locSup])
      (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
    exact ⟨q1, by simpa using q2, q4⟩

/-- `applyTryLock` preservation (Q-TRYLOCK): the pre-committed acquire
is a `storeLoc_pres` of a loc-free sync value; the delivery is
`tryDeliver_wf` at either state. -/
theorem applyTryLock_wf {σ : Store} {op : SyncOp} {loc : Loc}
    {pre : SyncPrim} {spurious : Bool} {targets : List Assignee}
    {env : LocalEnv} {k : Cont} {c' : Config} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hloc : Loc.locSup loc ≤ σ.nextAddr)
    (ht : assigneeListSup targets ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applyTryLock ctx σ op loc pre spurious targets env k = .ok (c', σ', tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  rw [applyTryLock.eq_def] at h
  try simp only [bind_eq_ok] at h
  obtain ⟨acq, hacq, h⟩ := h
  split at h
  · try simp only [bind_eq_ok] at h
    obtain ⟨⟨c₀, σ₀⟩, hdel, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact tryDeliver_wf hw ht henv hk hdel
  · try simp only [bind_eq_ok] at h
    obtain ⟨σ₂, hst, h⟩ := h
    obtain ⟨w1, w2⟩ := storeLoc_pres hw hloc
      (by simp [syncData_locSup]) hst
    split at h
    · try simp only [bind_eq_ok] at h
      obtain ⟨⟨c₀, σ₀⟩, hdel, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact tryDeliver_wf hw ht henv hk hdel
    · try simp only [bind_eq_ok] at h
      obtain ⟨⟨c₀, σ₀⟩, hdel, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨q1, q2, q4⟩ := tryDeliver_wf w1 (by omega) (by omega) (by omega) hdel
      exact ⟨q1, q2, Nat.le_trans w2 q4⟩

/-- A TRY head's result-target sup is its `syncOpSup`. -/
theorem syncOpSup_of_tryTargets {op : SyncOp} {ts : List Assignee}
    (h : op.tryTargets? = some ts) : syncOpSup op = assigneeListSup ts := by
  cases op <;> simp_all [SyncOp.tryTargets?, syncOpSup]

/-- `applySyncOp` preservation (the choice-taking entry): the TRY heads
through `applyTryLock_wf`, everything else through
`applySyncOpCore_wf`. The stream plays no part in the state claims. -/
theorem applySyncOp_wf {σ : Store} {ch : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (hop : syncOpSup op ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applySyncOp ctx σ ch op vs env k = .ok (c', σ', ch', ps, tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  rw [applySyncOp.eq_def] at h
  split at h
  · rename_i targets av htry
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨pre, hcell, h⟩ := h
    obtain ⟨⟨c₀, σ₀, tr₀⟩, happ, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rw [syncOpSup_of_tryTargets htry] at hop
    exact applyTryLock_wf hw hlocb hop henv hk happ
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · try simp only [bind_eq_ok] at h
    obtain ⟨⟨c₀, σ₀, tr₀⟩, hcore, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact applySyncOpCore_wf hw hvs hop henv hk hcore

set_option maxHeartbeats 1600000 in
/-- Extract the source element behind one `mapM` output position (the
multi-ready select arm's commit list). -/
theorem mapM_getElem?_mem {α β : Type} {f : α → Except Stop β}
    {xs : List α} {ys : List β} {i : Nat} {b : β}
    (h : xs.mapM f = .ok ys) (hb : ys[i]? = some b) :
    ∃ a ∈ xs, f a = .ok b := by
  induction xs generalizing ys i with
  | nil =>
      simp only [List.mapM_nil, pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp at hb
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨y, hy, ys', hys', rfl⟩ := h
      match i, hb with
      | 0, hb =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
          subst hb
          exact ⟨x, by simp, hy⟩
      | i + 1, hb =>
          simp only [List.getElem?_cons_succ] at hb
          obtain ⟨a, ha, hfa⟩ := ih hys' hb
          exact ⟨a, by simp [ha], hfa⟩

/-- `applySelect` preservation (readiness/commit step; slice 4: the
stream threads through — the L2 pick never touches locs, so the
bounds argument is per committed clause, membership-generalized). -/
theorem applySelect_wf {σ : Store}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {ch ch' : Choices} {ps : List PickRecord} {cl? : Option EvClause}
    {tr : AccessTrace}
    (hw : StateWf ctx σ) (hcl : selectClausesSup clauses ≤ σ.nextAddr)
    (hd : optStmtSup default? ≤ σ.nextAddr)
    (hvs : goValueListSup vs ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applySelect ctx σ clauses default? vs env k ch = .ok (c', σ', ch', ps, cl?, tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  rw [applySelect.eq_def] at h
  try simp only [bind_eq_ok] at h
  obtain ⟨outc, hcore, h⟩ := h
  rw [applySelectCore.eq_def] at hcore
  simp only [bind_eq_ok] at hcore
  obtain ⟨evs, hevs, hcore⟩ := hcore
  obtain ⟨rc, hrc, hcore⟩ := hcore
  have hevsb : evClausesSup evs ≤ σ.nextAddr := by
    have := evalClauses_sup hevs
    omega
  have hcommit : ∀ c ∈ rc, ∀ {c₂ : Config} {σ₂ : Store} {tr₂ : AccessTrace},
      commitClause ctx σ env k c = .ok (c₂, σ₂, tr₂) →
      StateWf ctx σ₂ ∧ Config.locSup c₂ ≤ σ₂.nextAddr
        ∧ σ.nextAddr ≤ σ₂.nextAddr := by
    intro c hmem c₂ σ₂ tr₂ hcom
    have hcb : evClauseSup c ≤ σ.nextAddr := by
      have hmem' := readyClauses_subset hrc c hmem
      exact Nat.le_trans (evClausesSup_mem hmem') hevsb
    exact commitClause_wf hw hcb henv hk hcom
  split at h
  · -- outc = .done c₂ σ₂ clq tr₂: no pick was consumed
    rename_i c₂ σ₂ clq tr₂
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    split at hcore
    · split at hcore <;>
        (simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore;
         obtain ⟨rfl, rfl, rfl, rfl⟩ := hcore)
      · rename_i d
        refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [optStmtSup] at hd
        simp only [Config.locSup, Nat.max_le]
        omega
      · refine ⟨hw, ?_, Nat.le_refl _⟩
        simp only [Config.locSup, Nat.max_le]
        omega
    · rename_i c
      simp only [bind_eq_ok] at hcore
      obtain ⟨⟨c₃, σ₃, tr₃⟩, hcom, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcore
      exact hcommit c (List.mem_cons_self ..) hcom
    · simp only [bind_eq_ok] at hcore
      obtain ⟨commits, hcommits, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq] at hcore
      cases hcore
  · -- outc = .picks poll commits: the L2 pick indexes the pre-committed list
    rename_i poll commits
    split at h
    · rename_i clp r₂c r₂σ r₂tr hget
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      split at hcore
      · split at hcore <;>
          (simp only [pure_eq_ok, Except.ok.injEq] at hcore; cases hcore)
      · simp only [bind_eq_ok] at hcore
        obtain ⟨⟨c₃, σ₃, tr₃⟩, hcom, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq] at hcore
        cases hcore
      · simp only [bind_eq_ok] at hcore
        obtain ⟨commits₂, hcommits, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.picks.injEq] at hcore
        obtain ⟨rfl, rfl⟩ := hcore
        obtain ⟨cl, hmem, hf⟩ := mapM_getElem?_mem hcommits hget
        have hcom : commitClause ctx σ env k cl = .ok (r₂c, r₂σ, r₂tr) := by
          cases hcc : commitClause ctx σ env k cl with
          | ok r => rw [hcc] at hf; simp_all
          | error e =>
              rw [hcc] at hf
              -- A1 stop grammar: the terminal class needs its own split.
              rcases e with _ | t | _
              · simp_all
              · cases t <;> simp_all
              · simp_all
        exact hcommit cl hmem hcom
    · -- defensive `.inr` (unreachable today): the picked panic as a
      -- `.panicking` configuration over the input state
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, Nat.le_refl _⟩
      simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup, panicEntry_locSup,
        Nat.max_le]
      omega
    · simp [throw, throwThe, MonadExceptOf.throw] at h

set_option maxHeartbeats 1600000 in
/-- `applyAtomicOp` preservation (atomics arc wave 1, the
`applySyncOp_wf` twin): wf state out, bounded successor configuration,
types unchanged, allocator monotone. The op stores a LOC-FREE integer
(`GoValue.locSup (.int _ _) = 0`) and delivers a loc-free result
(`atomicCompute_locSup`), so every arm is state-invariant, a
`storeLoc_pres`, and/or an `enterRecvTargets_wf`. -/
theorem applyAtomicOp_wf {σ : Store} {op : AtomicOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (hop : atomicOpSup op ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applyAtomicOp ctx σ op vs env k = .ok (c', σ', tr)) :
    StateWf ctx σ' ∧ Config.locSup c' ≤ σ'.nextAddr
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  obtain ⟨head, kind, targets⟩ := op
  simp only [atomicOpSup] at hop
  rw [applyAtomicOp.eq_def] at h
  split at h
  · rename_i av operands
    simp only [goValueListSup, Nat.max_le] at hvs
    try simp only [bind_eq_ok] at h
    obtain ⟨loc, hloc, h⟩ := h
    have hlocb : Loc.locSup loc ≤ σ.nextAddr :=
      Nat.le_trans (valueAsLoc_locSup hloc) (by omega)
    obtain ⟨cur, hcell, h⟩ := h
    split at h
    · rename_i curv ck
      split at h
      · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      · try simp only [bind_eq_ok] at h
        obtain ⟨p, hcomp, h⟩ := h
        obtain ⟨new?, result⟩ := p
        try dsimp only at h
        obtain ⟨σ₂, hst, h⟩ := h
        have hres : GoValue.locSup result = 0 := atomicCompute_locSup hcomp
        -- The optional store: a loc-free value, or no store at all.
        have hσ₂ : StateWf ctx σ₂ ∧ σ.nextAddr ≤ σ₂.nextAddr := by
          cases new? with
          | some nv =>
              simp only [atomicStore] at hst
              obtain ⟨w1, w2⟩ := storeLoc_pres hw hlocb
                (by simp [GoValue.locSup]) hst
              exact ⟨w1, w2⟩
          | none =>
              simp only [atomicStore, pure_eq_ok, Except.ok.injEq] at hst
              subst hst
              exact ⟨hw, Nat.le_refl _⟩
        obtain ⟨w1, w2⟩ := hσ₂
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨w1, ?_, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · try simp only [bind_eq_ok] at h
          obtain ⟨⟨c₀, σ₀⟩, hent, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨q1, q2, q4⟩ := enterRecvTargets_wf w1
            (by omega)
            (by simp [goValueListSup, hres])
            (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) hent
          exact ⟨q1, by simpa using q2, Nat.le_trans w2 q4⟩
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-! ## The `unseq` construct's loc lemmas (Stage B, 2026-09-16) -/

theorem unseqCellLoc_locSup {env : LocalEnv} {bind : VarId} {loc : Loc}
    (h : unseqCellLoc env bind = .ok loc) : Loc.locSup loc ≤ LocalEnv.locSup env := by
  unfold unseqCellLoc at h
  split at h
  · rename_i hl
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact LocalEnv.lookup_locSup hl
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem unseqLookupTarget_locSup :
    ∀ {tg : List (VarId × TargetRef)} {t : VarId} {r : TargetRef},
      unseqLookupTarget tg t = .ok r → TargetRef.locSup r ≤ unseqTargetsSup tg
  | [], _, _, h => by simp [unseqLookupTarget, stuck, throw, throwThe, MonadExceptOf.throw] at h
  | (n, r') :: rest, t, r, h => by
      simp only [unseqLookupTarget] at h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        simp only [unseqTargetsSup]
        omega
      · have := unseqLookupTarget_locSup h
        simp only [unseqTargetsSup]
        omega

theorem unseqAtom_locSup {env : LocalEnv} {s : Store} {e : Expr} {v : GoValue} {tr : AccessTrace}
    (h : unseqAtom ctx env s e = .ok (v, tr)) :
    GoValue.locSup v ≤ max (LocalEnv.locSup env) (Heap.locSup s.heap) := by
  cases e <;> simp only [unseqAtom] at h
  all_goals try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done)
  · -- `.var`
    split at h
    · have := loadLoc_locSup (Mem.load_eq (loadBinding_ok ctx h)).1
      omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · -- `.intLit`
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  · -- `.boolLit`
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  · -- `.stringLit` (Stage E E2)
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  · -- `.ref`
    split at h
    · rename_i hl
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := LocalEnv.lookup_locSup hl
      simp only [GoValue.locSup]
      omega
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem unseqAtoms_locSup {env : LocalEnv} {s : Store} :
    ∀ {ops : List Expr} {vals : List GoValue} {tr : AccessTrace},
      unseqAtoms ctx env s ops = .ok (vals, tr) →
      goValueListSup vals ≤ max (LocalEnv.locSup env) (Heap.locSup s.heap)
  | [], vals, tr, h => by
      simp only [unseqAtoms, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [goValueListSup]
  | e :: es, vals, tr, h => by
      simp only [unseqAtoms, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨v, t⟩, hv, ⟨vs, ts⟩, hvs, rfl, rfl⟩ := h
      have h1 := unseqAtom_locSup hv
      have h2 := unseqAtoms_locSup hvs
      simp only [goValueListSup]
      omega

theorem unseqTargetPlan_locSup {s : Store} {env : LocalEnv} {lhs : Assignee} {r : TargetRef}
    {tr : AccessTrace} (h : unseqTargetPlan ctx s env lhs = .ok (r, tr)) :
    TargetRef.locSup r ≤ max (LocalEnv.locSup env) (Heap.locSup s.heap) := by
  unfold unseqTargetPlan at h
  split at h
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · try simp only [bind_eq_ok] at h
    obtain ⟨⟨vals, trA⟩, hvals, h⟩ := h
    try dsimp only at h
    split at h
    · rename_i hcomp
      -- The frozen-anchor check (audit F2) only refuses; a pass returns
      -- the completed plan unchanged.
      split at h
      · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Nat.le_trans (completeTargetRef_locSup hcomp) (unseqAtoms_locSup hvals)
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem unseqReadTarget_locSup {s : Store} {r : TargetRef} {v : GoValue} {tr : AccessTrace}
    (h : unseqReadTarget ctx s r = .ok (v, tr)) : GoValue.locSup v ≤ Heap.locSup s.heap := by
  cases r with
  | chain anchor idxs steps =>
      simp only [unseqReadTarget, bind_eq_ok] at h
      obtain ⟨cur, -, loc, -, hload⟩ := h
      exact loadLoc_locSup (Mem.load_eq hload).1
  | mapElem b k kt vt =>
      -- Stage E E2: the frozen map-element read is `mapLookupValue`'s bound.
      simp only [unseqReadTarget, bind_eq_ok] at h
      obtain ⟨map, -, key, -, ⟨⟨rv, b'⟩, tr'⟩, hlook, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact mapLookupValue_locSup hlook

theorem unseqLoad_pres {σ : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)}
    {bind tgt : VarId} {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (h : unseqLoad ctx σ env tg bind tgt = .ok (σ', tr)) :
    StmtOpPres ctx σ σ' ∧ σ'.nextAddr = σ.nextAddr := by
  -- C1 S3: the checked read is the VALIDATE phase; the binder write the COMMIT.
  simp only [unseqLoad, bind_eq_ok] at h
  obtain ⟨c, hplan, h⟩ := h
  simp only [unseqLoad.plan, bind_eq_ok] at hplan
  obtain ⟨r, -, ⟨v, t₁⟩, hv, hplan⟩ := hplan
  try dsimp only at hplan
  try simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hplan
  obtain ⟨loc, hloc, rfl⟩ := hplan
  try dsimp only at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨s', t₂⟩, hst, h⟩ := h
  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h1 := unseqCellLoc_locSup hloc
  have h2 := unseqReadTarget_locSup hv
  have hh := hw.heap_le
  exact ⟨Mem.store_pres hw (by omega) (by omega) hst, Mem.store_shape hst⟩

theorem unseqGuard_pres {σ : Store} {g : UnseqGraph} {env : LocalEnv}
    {st st' : List UnseqStatus} {i : Nat} {test : VarId} {w : Bool} {out : VarId}
    {σ' : Store} {tr : AccessTrace}
    (hw : StateWf ctx σ) (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (h : unseqGuard ctx σ g env st i test w out = .ok (st', σ', tr)) :
    StmtOpPres ctx σ σ' ∧ σ'.nextAddr = σ.nextAddr := by
  simp only [unseqGuard, bind_eq_ok] at h
  obtain ⟨tloc, -, ⟨tv, t₁⟩, -, h⟩ := h
  try dsimp only at h
  try simp only [bind_eq_ok] at h
  obtain ⟨b, -, h⟩ := h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨stmtOpPres_refl hw, rfl⟩
  · try simp only [bind_eq_ok] at h
    obtain ⟨oloc, holoc, ⟨s₁, t₂⟩, hst, h⟩ := h
    try dsimp only at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      have h1 := unseqCellLoc_locSup holoc
      exact ⟨Mem.store_pres hw (by omega) (by simp [GoValue.locSup]) hst, Mem.store_shape hst⟩
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

theorem unseqStorePlan_locSup {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)} :
    ∀ {stores : List (VarId × VarId)} {refs : List TargetRef} {vals : List GoValue},
      unseqStorePlan ctx s env tg stores = .ok (refs, vals) →
      targetRefListSup refs ≤ unseqTargetsSup tg ∧ goValueListSup vals ≤ Heap.locSup s.heap
  | [], refs, vals, h => by
      simp only [unseqStorePlan, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [targetRefListSup, goValueListSup]
  | (t, v) :: rest, refs, vals, h => by
      simp only [unseqStorePlan, bind_eq_ok] at h
      obtain ⟨r, hr, loc, -, val, hval, ⟨rs, vs⟩, hrest, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h0 := unseqStorePlan_locSup hrest
      have h1 := unseqLookupTarget_locSup hr
      have h2 := loadLoc_locSup (loadRoot_ok ctx hval)
      simp only [targetRefListSup, goValueListSup]
      omega

theorem unseqBodySup_of_get :
    ∀ {occs : List UnseqOcc} {i : Nat} {o : UnseqOcc}, occs[i]? = some o →
      unseqBodySup o.body ≤ unseqOccsSup occs
  | [], _, _, h => by simp at h
  | o' :: os, 0, o, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [unseqOccsSup]
      omega
  | o' :: os, i + 1, o, h => by
      simp only [List.getElem?_cons_succ] at h
      have := unseqBodySup_of_get h
      simp only [unseqOccsSup]
      omega

theorem assigneeListSup_vars : ∀ (binds : List VarId),
    assigneeListSup (binds.map Assignee.var) = 0
  | [] => rfl
  | _ :: bs => by simp [assigneeListSup, Assignee.locSup, assigneeListSup_vars bs]

theorem unseqInvokeStmt_locSup {binds : List VarId} {callee : Expr} {args : List Expr} :
    Stmt.locSup (unseqInvokeStmt binds callee args)
      ≤ unseqBodySup (.invoke binds callee args) := by
  simp only [unseqInvokeStmt, Stmt.locSup, unseqBodySup, List.toList_toArray,
    assigneeListSup_vars]
  omega

/-- Stage E E3: the receive statement's loc bound is its body's (the binder
targets are `var`s, bound 0). -/
theorem unseqRecvStmt_locSup {binds : List VarId} {ch : Expr} {elem : Ty} :
    Stmt.locSup (unseqRecvStmt binds ch elem) ≤ unseqBodySup (.recv binds ch elem) := by
  simp only [unseqRecvStmt, Stmt.locSup, unseqBodySup, List.toList_toArray,
    assigneeListSup_vars]
  omega

/-- Stage E E4: the allocation statement's loc bound is its body's (program text is
loc-free since A4 — `Stmt.locSup_eq_zero`). -/
theorem unseqAllocStmt_locSup {bind : VarId} {spec : AllocSpec} :
    Stmt.locSup (unseqAllocStmt bind spec) ≤ unseqBodySup (.allocate bind spec) := by
  simp [Stmt.locSup_eq_zero]

/-- Stage E5 E5a: the wide statement's loc bound is its body's (program text is
loc-free since A4 — `Stmt.locSup_eq_zero`). -/
theorem unseqWideStmt_locSup {binds : List VarId} {spec : WideSpec} :
    Stmt.locSup (unseqWideStmt binds spec) ≤ unseqBodySup (.wide binds spec) := by
  simp [Stmt.locSup_eq_zero]

/-- Close a `step_preserves_wf_loc` goal whose step DELIVERED A PANIC
(B2): the successor is `.panicking (chain ++ [panicEntry msg]) k` over
the unchanged state, loc-bounded by the source configuration's bound. -/
macro "wf_loc_panic " hs:term:max hc:term:max hdel:term:max : tactic =>
  `(tactic| (
    obtain ⟨hc', hs', -⟩ := deliver_panic_eq $hdel
    subst hc'
    subst hs'
    refine ⟨$hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at $hc:term ⊢
    omega))

set_option maxHeartbeats 4000000 in
/-- The LOC half of the preservation theorem: one machine step keeps the
state and the configuration loc-bounded (every location root strictly
below `nextAddr`), and never mutates the type environment. The combined
`step_preserves_wf` below adds the map-iteration typing component. -/
theorem step_preserves_wf_loc {c : Config} {σ : Store} {c' : Config}
    {σ' : Store} {l : StepLabel} (h : Step ctx c σ c' σ' l)
    (hs : StateWf ctx σ) (hc : ConfigWf σ.nextAddr c) :
    StateWf ctx σ' ∧ ConfigWf σ'.nextAddr c'
      ∧ σ.nextAddr ≤ σ'.nextAddr := by

  have hheap := hs.heap_le
  cases h
  all_goals try (
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega)
  case signal sg k hstep =>
    -- B4: the table's successors are built from the frame's own payload.
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have hle := signalStep_locSup hstep
    simp only [ConfigWf, Config.locSup] at hc
    exact Nat.le_trans hle hc
  case evalGlobal =>
    -- A4: the produced address is the global's index; the rule's premise
    -- (the cell exists) is exactly its bound.
    rename_i gid env k hgid
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Expr.locSup, Nat.max_le] at hc ⊢
    have hna : σ.nextAddr = σ.heap.size := rfl
    simp only [GoValue.locSup, Loc.locSup, Loc.rootBase]
    omega
  case panicArgValue v k =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have hp := panicPayload_locSup (v := v)
    simp only [ConfigWf, Config.locSup, Cont.locSup, Expr.locSup,
      GoValue.locSup, panicChainSup, panicEntryOf, Nat.max_le] at hc ⊢
    omega
  -- The preprint phase (unit 6b): the chain is re-arranged, never extended
  -- with a location; the resolution's receiver is bounded by the payload
  -- and the heap; the delivered result is a cell's value.
  case preprintCollapse chain older entry newer hsplit hcol =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    rw [splitNewestPending?_eq hsplit] at hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, panicChainSup_preprintDrop,
      panicChainSup_append, panicChainSup, Nat.max_le] at hc ⊢
    omega
  case preprintDistinct chain older entry newer hsplit hcol =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    rw [splitNewestPending?_eq hsplit] at hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, panicChainSup_append, panicChainSup,
      Nat.max_le] at hc ⊢
    omega
  case preprintSelect chain older entry newer hsplit hcol =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    rw [splitNewestPending?_eq hsplit] at hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, panicChainSup_append, panicChainSup,
      Nat.max_le] at hc ⊢
    omega
  case preprintResolve older entry newer k r hres hdel =>
    rcases toResult_cases hres with ⟨⟨fid, recv, tr₀⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      refine ⟨hs, ?_, Nat.le_refl _⟩
      have hrecv := preprintDispatch_locSup hX
      simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup, goValueListSup,
        targetPlansSup, exprListSup, LocalEnv.locSup, Nat.max_le] at hc hrecv ⊢
      omega
    · simp only [deliver_panic, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      refine ⟨hs, ?_, Nat.le_refl _⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, panicChainSup, panicEntry_locSup,
        List.nil_append, Nat.max_le] at hc ⊢
      omega
  case preprintReturn tenv rl older entry newer k fr v tr₀ hload =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := loadLoc_locSup (Mem.load_eq (loadBinding_ok ctx hload)).1
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup, locListSup, deferListSup,
      targetPlansSup, LocalEnv.locSup, Nat.max_le] at hc h1 ⊢
    omega
  case preprintFall tenv rl older entry newer k fr v tr₀ hload =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := loadLoc_locSup (Mem.load_eq (loadBinding_ok ctx hload)).1
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup, locListSup, deferListSup,
      targetPlansSup, LocalEnv.locSup, Nat.max_le] at hc h1 ⊢
    omega
  case evalRef id loc env k hlook =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := LocalEnv.lookup_locSup hlook
    simp only [ConfigWf, Config.locSup, Cont.locSup, Expr.locSup,
      GoValue.locSup, Nat.max_le] at hc ⊢
    omega
  case evalVar id loc v env k hlook hload =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := loadLoc_locSup (Mem.loadFor_eq (loadBindingFor_ok ctx hload)).1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case evalStrict e op e₁ rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := strictPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case evalStrictNullary e op r env k hplan hres hdel =>
    rcases toResult_cases hres with ⟨⟨v, s₂, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      obtain ⟨w1, w2, w6⟩ := applyStrictOp_wf hs
        (by simp [goValueListSup]) happly
      refine ⟨w1, ?_, w2⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel
  case evalRecover env k v k' hrec =>
    obtain ⟨r1, r2⟩ := recoverResult_locSup hrec
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case strictApply op done v r env k hres hdel =>
    rcases toResult_cases hres with ⟨⟨out, s₂, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨w1, w2, w6⟩ := applyStrictOp_wf hs hop happly
      refine ⟨w1, ?_, w2⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel
  case seqn ss env k =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := seqCont_locSup (ss := ss.toList) (env := env) (k := k)
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case block decls ss env env' k hdecls =>
    obtain ⟨w1, w2, w6⟩ := allocDecls_wf hdecls hs (by
      rw [LocalEnv.pushScope_locSup]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega)
    refine ⟨w1, ?_, w2⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callStart targets fid args plans a rest env k hplan hargs =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := targetsPlan_locSup hplan
    have h2 : exprListSup (a :: rest) = exprListSup args.toList := by rw [hargs]
    simp only [exprListSup] at h2
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 h2 ⊢
    omega
  case callImmediate targets fid args plans r env k ch ch' ps hplan hargs hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have h1 := targetsPlan_locSup hplan
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs
        (by simp [goValueListSup]) henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.callConfig_bounded w6 ?_ ?_ ?_ <;>
        (simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc h1 ⊢; omega)
    · wf_loc_panic hs hc hdel
  case callArgsDoneEnter v fid plans vals r env k ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup (vals ++ [v]) ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.callConfig_bounded w6 ?_ ?_ ?_ <;>
        (simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢; omega)
    · wf_loc_panic hs hc hdel
  case stmtOpFirst stmt op nt e rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := stmtPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case stmtOpShiftTarget op nt done v r e rest env k hlt hres hdel =>
    rcases toResult_cases hres with ⟨loc, rfl, -⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      refine ⟨hs, ?_, Nat.le_refl _⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel
  case stmtOpApply op nt done v r env k ch hres hdel =>
    rcases toResult_cases hres with ⟨⟨s₂, ch', tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨w1, w2⟩ := applyStmtOp_wf hs hop happly
      refine ⟨w1, ?_, w2⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel
  case mapRangeStart v base start keyVar valVar keyTy valTy body env k hstart =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have hb := mapRangeStartSets_locSup hstart
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      List.toList_toArray,
      Nat.max_le] at hc hb ⊢
    omega
  -- (The label-bearing premise is moved after the others by `cases`'
  -- substitution of the label index, hence the name order `hbind hcands`.)
  case mapIterNext keyVar valVar keyTy valTy body base produced start cands idx env env' k
 tr hidx hcands hbind =>
    have hentb : goValueEntriesSup cands.toList ≤ σ.nextAddr :=
      Nat.le_trans (mapIterCandidates_locSup hcands) hheap
    have hkb : max (GoValue.locSup cands[idx].2.1)
        (GoValue.locSup cands[idx].2.2) ≤ σ.nextAddr := by
      refine Nat.le_trans (goValueEntriesSup_mem ?_) hentb
      exact List.mem_of_getElem? (by
        rw [Array.getElem?_toList]
        exact Array.getElem?_eq_getElem hidx)
    obtain ⟨w1, w2, w6⟩ := bindIterVars_wf hs
      (by rw [LocalEnv.pushScope_locSup]; simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc; omega)
      (by omega) (by omega) hbind
    refine ⟨w1, ?_, w2⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callValueStart targets callee args plans env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := targetsPlan_locSup hplan
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case callValCalleeEnter fid captured plans r env k ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup captured ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.callConfig_bounded w6 ?_ ?_ ?_ <;>
        (simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢; omega)
    · wf_loc_panic hs hc hdel
  case callValArgsEnter v fid captured plans vals r env k ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup (captured ++ vals ++ [v]) ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.callConfig_bounded w6 ?_ ?_ ?_ <;>
        (simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢; omega)
    · wf_loc_panic hs hc hdel
  case frameReturnTargets sh e ops rest tenv results k w vs hload =>
    have h1 := loadResults_locSup hload
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le, LocalEnv.locSup] at hc h1 ⊢
    omega
  case frameFallTargets sh e ops rest tenv results k w vs hload =>
    have h1 := loadResults_locSup hload
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le, LocalEnv.locSup] at hc h1 ⊢
    omega
  case frameDeferFall targets tenv results fid captured args ds k w r ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.drainConfig_bounded w6 ?_ ?_
      · simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
      · intro cv hcv
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
    · wf_loc_panic hs hc hdel
  case frameDeferReturn targets tenv results fid captured args ds k w r ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.drainConfig_bounded w6 ?_ ?_
      · simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
      · intro cv hcv
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
    · wf_loc_panic hs hc hdel
  case deferCalleeNoArgs cv env k k' hdc hpush =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := pushDefer_locSup hpush
    simp only [Nat.max_le] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    simp only [goValueListSup] at h1
    omega
  case deferArgsDone v cv vals env k k' hpush =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := pushDefer_locSup hpush
    simp only [Nat.max_le, goValueListSup_append, goValueListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case panicUnwind chain k k' hpass =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 := panicPassthrough_locSup hpass
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case panicFrameDefer chain targets tenv results fid captured args ds k w r ch ch' ps hres hdel =>
    rcases enterFramePick_cases hres with ⟨e, s₂, tr₂, rfl, henter, rfl, rfl⟩ | ⟨msg, rfl, -, rfl, rfl⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
        (try rw [goValueListSup_append]); (try rw [goValueListSup_append])
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc
        (try simp only [goValueListSup])
        omega
      obtain ⟨w1, w2, w6⟩ := enterFrame_wf hs hargb henter
      refine ⟨w1, ?_, w2⟩
      refine Entry.drainConfig_bounded w6 ?_ ?_
      · simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
      · intro cv hcv
        simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
        GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
        stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
        goValueListSup_append, exprListSup_append, stmtListSup_append,
        locListSup_append, panicChainSup_append, goValueListSup_reverse,
        targetRefListSup, targetPlansSup, targetRefListSup_append,
        LocalEnv.locSup, Scope.locSup,
        runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
        Nat.max_le] at hc ⊢
        omega
    · wf_loc_panic hs hc hdel
  case chanStFirst stmt op e rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    obtain ⟨h1, h2⟩ := chanPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      targetRefListSup, targetPlansSup, targetRefListSup_append,
      LocalEnv.locSup, Scope.locSup,
      runtimeErrorValue_locSup, panicEntry_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 h2 ⊢
    omega
  case chanStApply op done v r env k hres hdel =>
    rcases toResult_cases hres with ⟨⟨c₂, s₂, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr
          ∧ chanStOpSup op ≤ σ.nextAddr
          ∧ LocalEnv.locSup env ≤ σ.nextAddr
          ∧ Cont.locSup k ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
          exprListSup, Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨h1, h2, h3, h4⟩ := hop
      obtain ⟨w1, w2, w4⟩ := applyChanOp_wf hs h1 h2 h3 h4 happly
      exact ⟨w1, w2, w4⟩
    · wf_loc_panic hs hc hdel
  case syncStFirst stmt op e rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    obtain ⟨h1, h2⟩ := syncPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      Nat.max_le] at hc h1 h2 ⊢
    omega
  case syncStApply op done v r env k ch hres hdel =>
    rcases toResult_cases hres with ⟨⟨c₂, s₂, ch', tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr
          ∧ syncOpSup op ≤ σ.nextAddr
          ∧ LocalEnv.locSup env ≤ σ.nextAddr
          ∧ Cont.locSup k ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
          exprListSup, Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨h1, h2, h3, h4⟩ := hop
      exact applySyncOp_wf hs h1 h2 h3 h4 happly
    · wf_loc_panic hs hc hdel
  case atomicStFirst stmt op e rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    obtain ⟨h1, h2⟩ := atomicPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      Nat.max_le] at hc h1 h2 ⊢
    omega
  case atomicStApply op done v r env k hres hdel =>
    rcases toResult_cases hres with ⟨⟨c₂, s₂, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr
          ∧ atomicOpSup op ≤ σ.nextAddr
          ∧ LocalEnv.locSup env ≤ σ.nextAddr
          ∧ Cont.locSup k ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
          exprListSup, Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨h1, h2, h3, h4⟩ := hop
      exact applyAtomicOp_wf hs h1 h2 h3 h4 happly
    · wf_loc_panic hs hc hdel
  case selectFirst clauses default? e rest env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have h1 : exprListSup (e :: rest) ≤ selectClausesSup clauses.toList := by
      rw [← hplan]; exact selectOperands_locSup
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case selectNoClausesDefault clauses d env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, optStmtSup,
      Nat.max_le] at hc ⊢
    omega
  case selectNoClausesBlock clauses env k hplan =>
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, evClausesSup,
      Nat.max_le] at hc ⊢
    omega
  case selectApply clauses default? done v r env k ch hres hdel =>
    rcases toResult_cases hres with ⟨⟨c₂, s₂, ch', cl?, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hcomp : selectClausesSup clauses ≤ σ.nextAddr
          ∧ optStmtSup default? ≤ σ.nextAddr
          ∧ goValueListSup (v :: done).reverse ≤ σ.nextAddr
          ∧ LocalEnv.locSup env ≤ σ.nextAddr
          ∧ Cont.locSup k ≤ σ.nextAddr := by
        rw [goValueListSup_reverse]
        simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
          exprListSup, Nat.max_le] at hc
        simp only [goValueListSup]
        omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := hcomp
      obtain ⟨w1, w2, w4⟩ := applySelect_wf hs h1 h2 h3 h4 h5 happly
      exact ⟨w1, w2, w4⟩
    · wf_loc_panic hs hc hdel
  case tgtOpNext sh ops v r sh' e ops' targets refs vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case tgtOpStores sh ops v r refs vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case tgtOpRhs sh ops v r refs e rest vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case assignManyFirst left right sh e ops rest env k hsz hplan =>
    have hplans := targetsPlan_locSup hplan
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [targetPlansSup, exprListSup, Nat.max_le] at hplans
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      stmtListSup, Nat.max_le] at hc ⊢
    omega
  case rhsStores rop refs done v r body env k hres hdel =>
    rcases toResult_cases hres with ⟨⟨vals, tr₂⟩, rfl, happly⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hv := applyRhsOp_locSup happly
      rw [goValueListSup_reverse] at hv
      refine ⟨hs, ?_, Nat.le_refl _⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
        goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
        Stmt.locSup, Nat.max_le] at hc hv ⊢
      omega
    · wf_loc_panic hs hc hdel
  case assignFirst lhs rhs sh e ops env k hplan =>
    have hp := targetPlan_locSup hplan
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [exprListSup, Nat.max_le] at hp
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      stmtListSup, Nat.max_le] at hc ⊢
    omega
  case mapLookupFirst t okT base index keyTy valueTy sh e ops rest env k hplan =>
    have hp := targetsPlan_locSup hplan
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [targetPlansSup, exprListSup, assigneeListSup, Nat.max_le] at hp
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      stmtListSup, assigneeListSup, Nat.max_le] at hc ⊢
    omega
  case typeAssertFirst t okT expr targetTy sh e ops rest env k hplan =>
    have hp := targetsPlan_locSup hplan
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [targetPlansSup, exprListSup, assigneeListSup, Nat.max_le] at hp
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      stmtListSup, assigneeListSup, Nat.max_le] at hc ⊢
    omega
  -- The `unseq` construct (Stage B): the frame's sup is its graph, its
  -- completion statement, its target table, its scope and its tail; the
  -- state changes only through `allocDecls` (ENTER), `storeLoc` (a value
  -- delivered into a cell; a guard's completion constant) and `unseqLoad`.
  case unseqEnter g thenB rest env env' k hwf hentry hdecls =>
    have hc' := hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Nat.max_le] at hc'
    -- C4 D3 (b): the cells go into a pushed scope — same sup as the source environment
    obtain ⟨w1, w2, w6⟩ := allocDecls_wf hdecls hs (by rw [LocalEnv.pushScope_locSup]; omega)
    refine ⟨w1, ?_, w2⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, unseqTargetsSup,
      Nat.max_le] at hc ⊢
    omega
  case unseqComplete g thenB st tg env k refs vals hdep hall hprod hplan =>
    have hp := unseqStorePlan_locSup hplan
    have hh := hs.heap_le
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc ⊢
    omega
  case unseqRunEval g thenB st tg env k o bind head i hget hbody =>
    have hb := unseqBodySup_of_get hget
    rw [hbody] at hb
    simp only [unseqBodySup] at hb
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, UnseqGraph.locSup, Nat.max_le] at hc hb ⊢
    omega
  case unseqRunInvoke g thenB st tg env k o binds callee args i hget hbody =>
    have hb := unseqBodySup_of_get hget
    rw [hbody] at hb
    have hst := unseqInvokeStmt_locSup (binds := binds) (callee := callee) (args := args)
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, UnseqGraph.locSup, Nat.max_le] at hc hb hst ⊢
    omega
  case unseqRunRecv g thenB st tg env k o binds ch elem i hget hbody =>
    have hb := unseqBodySup_of_get hget
    rw [hbody] at hb
    have hst := unseqRecvStmt_locSup (binds := binds) (ch := ch) (elem := elem)
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, UnseqGraph.locSup, Nat.max_le] at hc hb hst ⊢
    omega
  case unseqRunAlloc g thenB st tg env k o bind spec i hget hbody =>
    have hb := unseqBodySup_of_get hget
    rw [hbody] at hb
    have hst := unseqAllocStmt_locSup (bind := bind) (spec := spec)
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, UnseqGraph.locSup, Nat.max_le] at hc hb hst ⊢
    omega
  case unseqRunWide g thenB st tg env k o binds spec i hget hbody =>
    have hb := unseqBodySup_of_get hget
    rw [hbody] at hb
    have hst := unseqWideStmt_locSup (binds := binds) (spec := spec)
    refine ⟨hs, ?_, Nat.le_refl _⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, UnseqGraph.locSup, Nat.max_le] at hc hb hst ⊢
    omega
  case unseqRunLoad g thenB st tg env k o bind tgt r i hget hbody hres hdel =>
    rcases toResult_cases hres with ⟨⟨s₂, tr₂⟩, rfl, hload⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel
      have hc' := hc
      simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc'
      obtain ⟨⟨w1, w2⟩, hn⟩ := unseqLoad_pres hs (by omega) hload
      refine ⟨w1, ?_, w2⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel
  case unseqRunTarget g thenB st tg env k o bind lhs r tr i hget hbody hplan =>
    have hr := unseqTargetPlan_locSup hplan
    have hh := hs.heap_le
    refine ⟨hs, ?_, Nat.le_refl _⟩
    have hc' := hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc' hc ⊢
    have htg : unseqTargetsSup (tg ++ [(bind, r)]) ≤ σ.nextAddr := by
      clear hc' hplan hget hbody
      induction tg with
      | nil => simp only [List.nil_append, unseqTargetsSup]; omega
      | cons p rest ih =>
          obtain ⟨n, r'⟩ := p
          simp only [unseqTargetsSup, List.cons_append] at hc ⊢
          have := ih (by omega)
          omega
    omega
  case unseqRunGuard g thenB st tg env k o test w out st' i hget hbody hguard =>
    have hc' := hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc'
    obtain ⟨⟨w1, w2⟩, hn⟩ := unseqGuard_pres hs (by omega) hguard
    refine ⟨w1, ?_, w2⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc ⊢
    omega
  case unseqValue g thenB st tg env k o bind head v loc i hget hbody hloc hst =>
    have hc' := hc
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup, Nat.max_le] at hc'
    have hl := unseqCellLoc_locSup hloc
    obtain ⟨w1, w2⟩ := Mem.store_pres hs (by omega) (by omega) hst
    have hn := Mem.store_shape hst
    refine ⟨w1, ?_, w2⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Nat.max_le] at hc ⊢
    omega
  case storeStep ref rs val vals r body env k hres hdel =>
    rcases toResult_cases hres with ⟨⟨s₂, tr₂⟩, rfl, hst⟩ | ⟨msg, rfl, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl, rfl⟩ := hdel

      have hbounds : TargetRef.locSup ref ≤ σ.nextAddr
          ∧ GoValue.locSup val ≤ σ.nextAddr := by
        simp only [ConfigWf, Config.locSup, Cont.locSup, targetRefListSup,
          goValueListSup, Nat.max_le] at hc
        omega
      obtain ⟨w1, w2⟩ := storeTarget_pres hs hbounds.1 hbounds.2 hst
      refine ⟨w1, ?_, w2⟩
      simp only [ConfigWf, Config.locSup, Cont.locSup, targetRefListSup,
        goValueListSup, Stmt.locSup, Nat.max_le] at hc ⊢
      omega
    · wf_loc_panic hs hc hdel



/-- C4 D8 — the heap never shrinks along a step (the `σ.nextAddr ≤ σ'.nextAddr` conjunct of
`step_preserves_wf_loc`, named): an entry slot of an earlier store stays below every later store's
size — the lifetime half of `frameEntry_fresh`. -/
theorem heap_size_mono {c : Config} {σ : Store} {c' : Config} {σ' : Store} {l : StepLabel}
    (h : Step ctx c σ c' σ' l) (hs : StateWf ctx σ) (hc : ConfigWf σ.nextAddr c) :
    σ.heap.size ≤ σ'.heap.size :=
  (step_preserves_wf_loc h hs hc).2.2

/-! ## Preservation of the map-iteration typing component -/

theorem snapshotEntriesSelfNormalizedList_mem {types : TypeEnv} {kt vt : Ty} :
    ∀ {l : List (Nat × GoValue × GoValue)},
      snapshotEntriesSelfNormalizedList types kt vt l = true →
      ∀ {e : Nat × GoValue × GoValue}, e ∈ l →
        isNormalForTy types kt e.2.1 = true ∧ isNormalForTy types vt e.2.2 = true := by
  intro l
  induction l with
  | nil => intro _ e he; cases he
  | cons p rest ih =>
    intro h e he
    obtain ⟨i, k, v⟩ := p
    simp only [snapshotEntriesSelfNormalizedList, Bool.and_eq_true] at h
    cases he with
    | head => exact ⟨h.1.1, h.1.2⟩
    | tail _ ht => exact ih h.2 ht

theorem snapshotEntriesSelfNormalizedList_of_mem {types : TypeEnv} {kt vt : Ty} :
    ∀ {l : List (Nat × GoValue × GoValue)},
      (∀ e ∈ l, isNormalForTy types kt e.2.1 = true
        ∧ isNormalForTy types vt e.2.2 = true) →
      snapshotEntriesSelfNormalizedList types kt vt l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    obtain ⟨i, k, v⟩ := p
    have hp := h (i, k, v) List.mem_cons_self
    simp only [snapshotEntriesSelfNormalizedList, Bool.and_eq_true]
    exact ⟨⟨hp.1, hp.2⟩, ih fun e he => h e (List.mem_cons_of_mem _ he)⟩

/-- Snapshot shrinkage preserves the typing check (`mapIterNext`'s
`eraseIdx` keeps a sub-multiset of the entries). -/
theorem snapshotEntriesSelfNormalized_eraseIdx {types : TypeEnv} {kt vt : Ty}
    {arr : Array (Nat × GoValue × GoValue)} {i : Nat} {h : i < arr.size}
    (hall : snapshotEntriesSelfNormalized types kt vt arr = true) :
    snapshotEntriesSelfNormalized types kt vt (arr.eraseIdx i h) = true := by
  unfold snapshotEntriesSelfNormalized at hall ⊢
  rw [Array.toList_eraseIdx]
  exact snapshotEntriesSelfNormalizedList_of_mem fun e he =>
    snapshotEntriesSelfNormalizedList_mem hall (List.mem_of_mem_eraseIdx he)

-- `step_preserves_iters` (the TYPING half: `Config.itersNormalized` along a
-- step) is RETIRED with B7 / D6: `MachineWf` no longer carries the
-- conjunct, and the statement was `Config.itersNormalized_true` restated
-- (constantly `true` since the BUG-005 (L) surgery). The predicate, its
-- certificate and the walk lemmas that once lived here (`seqCont_`,
-- `pushDefer_`, `panicPassthrough_`, `recoverThroughWrappers_`,
-- `recoverResult_itersNormalized`) followed in the B7 fix round (the
-- `ThreadWf` twin deleted, [USER] 2026-09-17 relayed). Tombstones in
-- `docs/2026-09-17_b7-context-store-handoff.md`.

/-- **The preservation theorem**: one machine step keeps the joint
invariant — loc-boundedness of state and configuration (B7 / D6: the
former map-iteration typing conjunct is gone from `MachineWf`). -/
theorem step_preserves_wf {c : Config} {σ : Store} {c' : Config}
    {σ' : Store} {l : StepLabel} (h : Step ctx c σ c' σ' l) (hwf : MachineWf ctx σ c) :
    MachineWf ctx σ' c' := by
  obtain ⟨hs, hc⟩ := hwf
  obtain ⟨hs', hc', _⟩ := step_preserves_wf_loc h hs hc
  exact ⟨hs', hc'⟩

-- (S5 audit response: the standalone `step_nextAddr_mono` projection
-- that briefly lived here was DELETED as born-unused — the `MultiWf`
-- discharge consumes the `σ.nextAddr ≤ σ'.nextAddr` conjunct of
-- `step_preserves_wf_loc` directly, and the no-inert-scaffolding rule
-- forbids an unconsumed twin whose docstring claimed the role.)

end GoLean.GoCore.Machine
