import GoLean.GoCore.Machine

/-!
# State/configuration well-formedness (sem-adequacy arc slice 3, 2026-08-04)

**The invariant**: every location occurring anywhere in the machine state or
control configuration has its ROOT BASE address strictly below the
allocator's `nextAddr`. The machine manufactures locations only through
`ExecState.alloc` (which hands out `nextAddr` and bumps it), so this holds
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
* `GoValue` — `.addr`, `.slice` (base), `.map` (base), and recursion
  through `.interface`/`.struct`/`.array`/`.mapData`/`.funcVal`;
* `HeapCell`/`Heap` — cell values AND keys (`declaredTy` is a `Ty`: no locs);
* `Scope`/`LocalEnv` — the bound locations;
* **`Expr` — `.locLit` carries a `Loc`** (contra the slice plan's "program
  text carries no locs" assumption; found by the `Syntax.lean` scan this
  module's plan mandated). `Stmt`/`Assignee` recurse into `Expr`. Every
  other `Expr`/`Stmt` field is loc-free (`Ty`/`TypeId`/`FuncId`/literals).
* **`Func` bodies** (hence `ExecState.functions`) — a consequence of the
  `.locLit` finding: `enterFrame` moves `func.body` from the STATE into the
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
  | .mapData entries => goValueEntriesSup entries.toList
  | .chan c => optLocSup c.base
  | .chanData buf _ _ => goValueListSup buf.toList
  | .funcVal _ captured => goValueListSup captured

def goValueListSup : List GoValue → Nat
  | [] => 0
  | v :: vs => max (GoValue.locSup v) (goValueListSup vs)

def goValueFieldsSup : List (String × GoValue) → Nat
  | [] => 0
  | (_, v) :: vs => max (GoValue.locSup v) (goValueFieldsSup vs)

def goValueEntriesSup : List (GoValue × GoValue) → Nat
  | [] => 0
  | (k, v) :: vs =>
      max (max (GoValue.locSup k) (GoValue.locSup v)) (goValueEntriesSup vs)

end

/-- A heap cell: the stored value (the declared type carries no locs). -/
def HeapCell.locSup (c : HeapCell) : Nat :=
  GoValue.locSup c.value

/-- The heap: KEYS and cell values both. -/
def Heap.locSup : Heap → Nat
  | [] => 0
  | (l, c) :: rest =>
      max (max (Loc.locSup l) (HeapCell.locSup c)) (Heap.locSup rest)

/-- One lexical scope: every bound location. -/
def Scope.locSup : Scope → Nat
  | [] => 0
  | (_, l) :: rest => max (Loc.locSup l) (Scope.locSup rest)

/-- The scope stack. -/
def LocalEnv.locSup : LocalEnv → Nat
  | [] => 0
  | sc :: rest => max (Scope.locSup sc) (LocalEnv.locSup rest)

mutual

/-- Program-text locations: only `.locLit` carries one (proof-facing;
never frontend-emitted) — every other field is loc-free; the recursion
covers every `Expr`-carrying position. -/
def Expr.locSup : Expr → Nat
  | .var _ | .nil _ | .intLit _ _ | .floatLit _ _ _ | .stringLit _
  | .boolLit _ | .ref _
  | .defaultValue _ | .recoverCall | .unsupported _ => 0
  | .locLit l => Loc.locSup l
  | .convert _ e | .bytesFromString e | .stringFromByteSlice e
  | .stringFromRune e | .bitNeg e | .neg e | .not e | .deref e _
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

mutual

def Stmt.locSup : Stmt → Nat
  | .initialization _ | .returnStmt | .breakStmt | .continueStmt
  | .label _ | .breakTo _ | .continueTo _ | .unsupported _ => 0
  | .seqn ss => stmtListSup ss.toList
  | .block _ ss => stmtListSup ss.toList
  | .breakable body => Stmt.locSup body
  | .labeled _ body => Stmt.locSup body
  | .assign l r => max (Assignee.locSup l) (Expr.locSup r)
  | .assignMany ls rs =>
      max (assigneeListSup ls.toList) (exprListSup rs.toList)
  | .newValue t v _ => max (Assignee.locSup t) (Expr.locSup v)
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

/-- A phase-1-resolved target's loc positions (its operand VALUES;
`TargetStep`s are loc-free). -/
def TargetRef.locSup : TargetRef → Nat
  | .chain anchor idxs _ => max (GoValue.locSup anchor) (goValueListSup idxs)
  | .mapElem b k _ _ => max (GoValue.locSup b) (GoValue.locSup k)

def targetRefListSup : List TargetRef → Nat
  | [] => 0
  | r :: rs => max (TargetRef.locSup r) (targetRefListSup rs)

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
  | .seq rest env k =>
      max (max (stmtListSup rest) (LocalEnv.locSup env)) (Cont.locSup k)
  | .loop cond body env k =>
      max (max (Expr.locSup cond) (Stmt.locSup body))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .frame targets results defers k _ =>
      max (max (locListSup targets) (locListSup results))
        (max (deferListSup defers) (Cont.locSup k))
  | .deferCalleeK args env k =>
      max (max (exprListSup args) (LocalEnv.locSup env)) (Cont.locSup k)
  | .deferArgsK callee vals pending env k =>
      max (max (GoValue.locSup callee) (goValueListSup vals))
        (max (exprListSup pending) (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .breakableK k => Cont.locSup k
  | .labelK _ k => Cont.locSup k
  | .callValTargetsK callee locs pending args env k =>
      max (max (Expr.locSup callee) (locListSup locs))
        (max (max (exprListSup pending) (exprListSup args))
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .callValCalleeK locs args env k =>
      max (max (locListSup locs) (exprListSup args))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .callValArgsK callee locs vals pending env k =>
      max (max (GoValue.locSup callee) (locListSup locs))
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
  | .assignTargetK rhs env k =>
      max (max (Expr.locSup rhs) (LocalEnv.locSup env)) (Cont.locSup k)
  | .assignStoreK l k => max (Loc.locSup l) (Cont.locSup k)
  | .callTargetsK _ locs pending args env k =>
      max (max (locListSup locs) (exprListSup pending))
        (max (exprListSup args) (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .callArgsK _ locs vals pending env k =>
      max (max (locListSup locs) (goValueListSup vals))
        (max (exprListSup pending) (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .stmtOpK _ _ done pending env k =>
      max (max (goValueListSup done) (exprListSup pending))
        (max (LocalEnv.locSup env) (Cont.locSup k))
  | .mapRangeK _ _ _ _ body env k =>
      max (max (Stmt.locSup body) (LocalEnv.locSup env)) (Cont.locSup k)
  | .mapIterK _ _ _ _ body remaining env k =>
      max (max (Stmt.locSup body) (goValueEntriesSup remaining.toList))
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
  | .tgtOpK _ ops pending refs targets rhs vals body env k =>
      max (max (goValueListSup ops) (exprListSup pending))
        (max (max (targetRefListSup refs) (targetPlansSup targets))
          (max (max (exprListSup rhs) (goValueListSup vals))
            (max (Stmt.locSup body)
              (max (LocalEnv.locSup env) (Cont.locSup k)))))
  | .rhsK refs done pending body env k =>
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

/-- One evaluated select clause's sup (`.blockedSelect` payloads). -/
def evClauseSup : EvClause → Nat
  | .sendEv chv v _ body =>
      max (max (GoValue.locSup chv) (GoValue.locSup v)) (Stmt.locSup body)
  | .recvEv chv targets _ body =>
      max (max (GoValue.locSup chv) (assigneeListSup targets)) (Stmt.locSup body)

def evClausesSup : List EvClause → Nat
  | [] => 0
  | c :: cs => max (evClauseSup c) (evClausesSup cs)

/-- Configuration sup. `.panicked` carries only the rendered message. -/
def Config.locSup : Config → Nat
  | .exec stmt env k =>
      max (max (Stmt.locSup stmt) (LocalEnv.locSup env)) (Cont.locSup k)
  | .evalE e env k =>
      max (max (Expr.locSup e) (LocalEnv.locSup env)) (Cont.locSup k)
  | .retV v k => max (GoValue.locSup v) (Cont.locSup k)
  | .next k | .breaking k | .continuing k | .returning k => Cont.locSup k
  | .breakingTo _ k | .continuingTo _ k => Cont.locSup k
  | .panicking chain k => max (panicChainSup chain) (Cont.locSup k)
  | .panicked _ => 0
  | .blockedSend ch v k =>
      max (optLocSup ch) (max (GoValue.locSup v) (Cont.locSup k))
  | .blockedRecv ch targets _ env k =>
      max (optLocSup ch)
        (max (assigneeListSup targets)
          (max (LocalEnv.locSup env) (Cont.locSup k)))
  | .blockedSelect clauses env k =>
      max (evClausesSup clauses) (max (LocalEnv.locSup env) (Cont.locSup k))
  | .spawned k => Cont.locSup k

/-- State sup: heap keys+values, and every stored function body
(bodies enter the configuration at `enterFrame`). -/
def ExecState.locSup (σ : ExecState) : Nat :=
  max (Heap.locSup σ.heap) (funcListSup σ.functions.toList)

/-! ## The map-iteration typing component (sem-adequacy slice 3, 2026-08-04)

Loc-boundedness alone cannot exclude the second recorded ∀-choices
obstruction (`.tmp/probe_mapiter.lean`): a `mapIterK` snapshot whose
entries are not self-normalized at the range key/value types is loc-free
(trivially bounded) yet makes `mapIterNext`'s success depend on the pick.
The joint invariant therefore also carries: every in-flight `mapIterK`
continuation's snapshot passes `snapshotEntriesSelfNormalized` at the
state's type environment. Established by the (now fail-closed) snapshot
step, preserved by shrinkage (`eraseIdx`), and invariant along every
other rule because no rule mutates `σ.types` and continuations are only
ever decomposed structurally. Parameterized by the `TypeEnv` directly so
types-preservation is a rewrite, never a congruence induction. -/

/-- Every `mapIterK` snapshot along the continuation is self-normalized
at its own key/value types under `types`. Each constructor forwards to
its (unique) continuation tail; only `mapIterK` contributes a check. -/
def Cont.itersNormalized (types : TypeEnv) : Cont → Bool
  | .stop => true
  | .seq _ _ k => Cont.itersNormalized types k
  | .loop _ _ _ k => Cont.itersNormalized types k
  | .frame _ _ _ k _ => Cont.itersNormalized types k
  | .deferCalleeK _ _ k => Cont.itersNormalized types k
  | .deferArgsK _ _ _ _ k => Cont.itersNormalized types k
  | .breakableK k => Cont.itersNormalized types k
  | .labelK _ k => Cont.itersNormalized types k
  | .callValTargetsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .callValCalleeK _ _ _ k => Cont.itersNormalized types k
  | .callValArgsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .strictK _ _ _ _ k => Cont.itersNormalized types k
  | .andK _ _ k => Cont.itersNormalized types k
  | .orK _ _ k => Cont.itersNormalized types k
  | .boolK k => Cont.itersNormalized types k
  | .ifK _ _ _ k => Cont.itersNormalized types k
  | .whileK _ _ _ k => Cont.itersNormalized types k
  | .assignTargetK _ _ k => Cont.itersNormalized types k
  | .assignStoreK _ k => Cont.itersNormalized types k
  | .callTargetsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .callArgsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .stmtOpK _ _ _ _ _ k => Cont.itersNormalized types k
  | .mapRangeK _ _ _ _ _ _ k => Cont.itersNormalized types k
  | .mapIterK _ _ keyTy valTy _ remaining _ k =>
      snapshotEntriesSelfNormalized types keyTy valTy remaining
        && Cont.itersNormalized types k
  | .panicArgK k => Cont.itersNormalized types k
  | .panicResumeK _ k => Cont.itersNormalized types k
  | .chanStK _ _ _ _ k => Cont.itersNormalized types k
  | .selectOpsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .tgtOpK _ _ _ _ _ _ _ _ _ k => Cont.itersNormalized types k
  | .rhsK _ _ _ _ _ k => Cont.itersNormalized types k
  | .storeK _ _ _ _ k => Cont.itersNormalized types k
  | .goCalleeK _ _ k => Cont.itersNormalized types k
  | .goArgsK _ _ _ _ k => Cont.itersNormalized types k

@[inherit_doc Cont.itersNormalized]
def Config.itersNormalized (types : TypeEnv) : Config → Bool
  | .exec _ _ k => Cont.itersNormalized types k
  | .evalE _ _ k => Cont.itersNormalized types k
  | .retV _ k => Cont.itersNormalized types k
  | .next k => Cont.itersNormalized types k
  | .breaking k => Cont.itersNormalized types k
  | .continuing k => Cont.itersNormalized types k
  | .returning k => Cont.itersNormalized types k
  | .breakingTo _ k => Cont.itersNormalized types k
  | .continuingTo _ k => Cont.itersNormalized types k
  | .panicking _ k => Cont.itersNormalized types k
  | .blockedSend _ _ k => Cont.itersNormalized types k
  | .blockedRecv _ _ _ _ k => Cont.itersNormalized types k
  | .blockedSelect _ _ k => Cont.itersNormalized types k
  | .spawned k => Cont.itersNormalized types k
  | .panicked _ => true

/-! ## The Prop wrappers -/

/-- State well-formedness: no location in the heap (keys or values) or in
a stored function body dangles at or beyond `nextAddr`. -/
def StateWf (σ : ExecState) : Prop :=
  ExecState.locSup σ ≤ σ.nextAddr

/-- Configuration well-formedness at an allocator bound. -/
def ConfigWf (bound : Nat) (c : Config) : Prop :=
  Config.locSup c ≤ bound

/-- The bundled invariant `Step` preserves: loc-boundedness of state and
configuration, plus the map-iteration typing component (the two recorded
∀-choices obstructions, in order). -/
def MachineWf (σ : ExecState) (c : Config) : Prop :=
  StateWf σ ∧ ConfigWf σ.nextAddr c
    ∧ Config.itersNormalized σ.types c = true

instance (σ : ExecState) : Decidable (StateWf σ) := by unfold StateWf; infer_instance
instance (bound : Nat) (c : Config) : Decidable (ConfigWf bound c) := by
  unfold ConfigWf; infer_instance
instance (σ : ExecState) (c : Config) : Decidable (MachineWf σ c) := by
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
      = supBy (fun p => max (GoValue.locSup p.1) (GoValue.locSup p.2)) l
  | [] => rfl
  | (_, _) :: vs => by simp [goValueEntriesSup, supBy, goValueEntriesSup_eq vs]

theorem heapLocSup_eq :
    ∀ h : Heap, Heap.locSup h
      = supBy (fun p => max (Loc.locSup p.1) (HeapCell.locSup p.2)) h
  | [] => rfl
  | (_, _) :: rest => by simp [Heap.locSup, supBy, heapLocSup_eq rest]

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
    (GoCore.stuck m : Except GoError α) = .error (.stuck m) := rfl
@[simp] theorem panic_def {α : Type} (m : String) :
    (GoCore.panic m : Except GoError α) = .error (.panic m) := rfl
@[simp] theorem unsupported_def {α : Type} (m : String) :
    (GoCore.unsupported m : Except GoError α) = .error (.unsupported m) := rfl

theorem bind_eq_ok {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- Invariant transport along a successful `forIn` over a list in
`Except` — the loop shape of every op-table `for` loop. -/
theorem forIn_list_inv {α β : Type} {P : β → Prop} :
    ∀ {l : List α} {f : α → β → Except GoError (ForInStep β)} {b₀ bf : β},
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

theorem Scope.lookup_locSup {sc : Scope} {id : String} {l : Loc}
    (h : Scope.lookup sc id = some l) : Loc.locSup l ≤ Scope.locSup sc := by
  induction sc with
  | nil => simp [Scope.lookup] at h
  | cons p rest ih =>
    obtain ⟨name, loc⟩ := p
    simp only [Scope.lookup] at h
    split at h
    · cases h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem LocalEnv.lookup_locSup {env : LocalEnv} {id : String} {l : Loc}
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

theorem LocalEnv.declare_locSup {env : LocalEnv} {id : String} {l : Loc} :
    LocalEnv.locSup (env.declare id l) ≤ max (LocalEnv.locSup env) (Loc.locSup l) := by
  cases env with
  | nil => simp [LocalEnv.declare, LocalEnv.locSup, Scope.locSup]
  | cons sc rest =>
    simp [LocalEnv.declare, LocalEnv.locSup, Scope.locSup]
    omega

theorem LocalEnv.pushScope_locSup {env : LocalEnv} :
    LocalEnv.locSup env.pushScope = LocalEnv.locSup env := by
  simp [LocalEnv.pushScope, LocalEnv.locSup, Scope.locSup]

theorem Heap.lookup_locSup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : HeapCell.locSup c ≤ Heap.locSup h := by
  induction h with
  | nil => simp [Heap.lookup] at hl
  | cons p rest ih =>
    obtain ⟨l', c'⟩ := p
    simp only [Heap.lookup] at hl
    split at hl
    · cases hl
      simp only [Heap.locSup]
      omega
    · refine Nat.le_trans (ih hl) ?_
      simp only [Heap.locSup]
      omega

/-- The KEY side of `Heap.lookup_locSup`: a mapped location's own root
base is bounded by the heap's sup (keys contribute to `Heap.locSup`
alongside cell values). Feeds `InitialSplit.heapBounded` — the derivation
that made the old `bounded` field redundant (sem-adequacy slice 5). -/
theorem Heap.lookup_key_locSup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : Loc.locSup l ≤ Heap.locSup h := by
  induction h with
  | nil => simp [Heap.lookup] at hl
  | cons p rest ih =>
    obtain ⟨l', c'⟩ := p
    simp only [Heap.lookup] at hl
    split at hl
    · rename_i hbeq
      obtain rfl := eq_of_beq hbeq
      simp only [Heap.locSup]
      omega
    · refine Nat.le_trans (ih hl) ?_
      simp only [Heap.locSup]
      omega

theorem Heap.set_locSup {h : Heap} {l : Loc} {c : HeapCell} :
    Heap.locSup (Heap.set h l c)
      ≤ max (Heap.locSup h) (max (Loc.locSup l) (HeapCell.locSup c)) := by
  induction h with
  | nil => simp [Heap.set, Heap.locSup]
  | cons p rest ih =>
    obtain ⟨l', c'⟩ := p
    simp only [Heap.set]
    split
    · simp only [Heap.locSup]; omega
    · simp only [Heap.locSup] at *; omega

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
  simp only [bind_eq_ok] at h
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

theorem coerceStoredValue_locSup' :
    ∀ old new : GoValue, ∀ r : GoValue, coerceStoredValue old new = .ok r →
      GoValue.locSup r ≤ GoValue.locSup new := by
  refine fun old new => coerceStoredValue.induct
    (motive_1 := fun old new => ∀ r, coerceStoredValue old new = .ok r →
      GoValue.locSup r ≤ GoValue.locSup new)
    (motive_2 := fun oldFs newFs => ∀ r, coerceStruct oldFs newFs = .ok r →
      goValueFieldsSup r.toList ≤ goValueFieldsSup newFs)
    (motive_3 := fun oldL newL => ∀ r, coerceArray oldL newL = .ok r →
      goValueListSup r.toList ≤ goValueListSup newL)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ old new
  · -- int / int
    intro v k v' k' r h
    simp only [coerceStoredValue, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [GoValue.locSup]
  · -- float / float, kinds equal (loc-free scalar out)
    intro ob kind bits k hk r h
    simp only [coerceStoredValue] at h
    split at h <;>
      first
      | (simp [Bind.bind, Except.bind] at h; done)
      | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
         simp [GoValue.locSup])
      | (subst h; simp [GoValue.locSup])
  · -- float / float, kind mismatch: stuck
    intro ob kind bits k hk r h
    simp only [coerceStoredValue] at h
    split at h <;>
      first
      | (simp [Bind.bind, Except.bind] at h; done)
      | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
         simp [GoValue.locSup])
      | (subst h; simp [GoValue.locSup])
  · -- array size mismatch: stuck
    intro o n hne r h
    simp only [coerceStoredValue] at h
    split at h <;> simp_all
  · -- array / array
    intro o n hne ih r h
    simp only [coerceStoredValue] at h
    split at h
    · simp_all
    · rw [map_eq_ok] at h
      obtain ⟨arr, harr, rfl⟩ := h
      simpa [GoValue.locSup] using ih arr harr
  · -- struct type mismatch
    intro ot ofs nt nfs hne r h
    simp only [coerceStoredValue] at h
    split at h <;> simp_all
  · -- struct field-count mismatch
    intro ot ofs nt nfs hne hsz r h
    simp only [coerceStoredValue] at h
    split at h <;> simp_all
  · -- struct / struct
    intro ot ofs nt nfs hne hsz ih r h
    simp only [coerceStoredValue] at h
    split at h
    · simp_all
    · rw [map_eq_ok] at h
      obtain ⟨fs, hfs, rfl⟩ := h
      simpa [GoValue.locSup] using ih fs hfs
  · -- catch-all: pass the new value through
    intro t v hint hfloat harr hstruct r h
    rw [coerceStoredValue.eq_def] at h
    split at h
    · exact (hint _ _ _ _ rfl rfl).elim
    · exact (hfloat _ _ _ _ rfl rfl).elim
    · exact (harr _ _ rfl rfl).elim
    · exact (hstruct _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
  · -- coerceArray cons
    intro ov orest nv nrest ih1 ih3 r h
    simp only [coerceArray, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    have h1 := ih1 head hhead
    have h3 := ih3 tail htail
    have hl : (#[head] ++ tail).toList = head :: tail.toList := by simp
    rw [hl]
    simp only [goValueListSup]
    omega
  · -- coerceArray catch-all
    intro t x hnc r h
    rw [coerceArray.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueListSup]
  · -- coerceStruct cons, name mismatch: stuck
    intro on ov orest nn nv nrest hname _ih1 _ih2 r h
    simp only [coerceStruct] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · rename_i hcond
      exact absurd hname hcond
  · -- coerceStruct cons, names equal
    intro on ov orest nn nv nrest hname ih1 ih2 r h
    simp only [coerceStruct] at h
    split at h
    · rename_i hcond
      exact absurd hcond hname
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨_, _, hv, hcv, arr, harr, hr⟩ := h
      subst hr
      have h1 := ih1 hv hcv
      have h2 := ih2 arr harr
      have hl : (#[(on, hv)] ++ arr).toList = (on, hv) :: arr.toList := by simp
      rw [hl]
      simp only [goValueFieldsSup]
      omega
  · -- coerceStruct catch-all
    intro t x hnc r h
    rw [coerceStruct.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueFieldsSup]

theorem coerceStoredValue_locSup {old new r : GoValue}
    (h : coerceStoredValue old new = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup new := coerceStoredValue_locSup' _ _ _ h

theorem arraySet_locSup {values : Array GoValue} {i : Int} {v : GoValue}
    {out : Array GoValue} (h : arraySet values i v = .ok out) :
    goValueListSup out.toList
      ≤ max (goValueListSup values.toList) (GoValue.locSup v) := by
  unfold arraySet arrayIndexNat at h
  simp only [bind_eq_ok] at h
  obtain ⟨n, hn, h⟩ := h
  split at h
  · rename_i old hold
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨c, hc, h⟩ := h
    subst h
    have hcv := coerceStoredValue_locSup hc
    simp only [goValueListSup_eq]
    rw [Array.set!, Array.toList_setIfInBounds]
    refine supBy_le_iff.mpr fun a ha => ?_
    rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
    · exact Nat.le_trans (supBy_mem hmem) (Nat.le_max_left _ _)
    · exact Nat.le_trans hcv (Nat.le_max_right _ _)
  · unfold indexOutOfRangePanic at h
    split at h <;> simp at h

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

theorem normalizeListWith_locSup {f : GoValue → Except GoError GoValue}
    (hf : ∀ v r, f v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {l : List GoValue} {arr : Array GoValue},
      normalizeListWith f l = .ok arr →
      goValueListSup arr.toList ≤ goValueListSup l := by
  intro l
  induction l with
  | nil =>
    intro arr h
    simp only [normalizeListWith, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueListSup]
  | cons v vs ih =>
    intro arr h
    simp only [normalizeListWith, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    have h1 := hf v head hhead
    have h2 := ih htail
    have hl : (#[head] ++ tail).toList = head :: tail.toList := by simp
    rw [hl]
    simp only [goValueListSup]
    omega

theorem normalizeFieldsWith_locSup {f : Ty → GoValue → Except GoError GoValue}
    (hf : ∀ ty v r, f ty v = .ok r → GoValue.locSup r ≤ GoValue.locSup v) :
    ∀ {fields : List FieldDef} {vals : List (String × GoValue)}
      {arr : Array (String × GoValue)},
      normalizeFieldsWith f fields vals = .ok arr →
      goValueFieldsSup arr.toList ≤ goValueFieldsSup vals := by
  intro fields
  induction fields with
  | nil =>
    intro vals arr h
    simp only [normalizeFieldsWith, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueFieldsSup]
  | cons fd frest ih =>
    intro vals arr h
    cases vals with
    | nil =>
      simp only [normalizeFieldsWith, pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [goValueFieldsSup]
    | cons p vrest =>
      obtain ⟨pn, pv⟩ := p
      simp only [normalizeFieldsWith] at h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨_, _, head, hhead, tail, htail, hr⟩ := h
        subst hr
        have h1 := hf _ _ _ hhead
        have h2 := ih htail
        have hl : (#[(fd.name, head)] ++ tail).toList
            = (fd.name, head) :: tail.toList := by simp
        rw [hl]
        simp only [goValueFieldsSup] at *
        omega

theorem normalizeStructValueWith_locSup {f : Ty → GoValue → Except GoError GoValue}
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
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, map_eq_ok] at h
      obtain ⟨_, _, arr, harr, rfl⟩ := h
      simpa [GoValue.locSup] using normalizeFieldsWith_locSup hf harr

theorem normalizeValueForTyFuel_locSup :
    ∀ (fuel : Nat) {s : ExecState} {ty : Ty} {v r : GoValue},
      normalizeValueForTyFuel fuel s ty v = .ok r →
      GoValue.locSup r ≤ GoValue.locSup v := by
  intro fuel
  induction fuel with
  | zero => intro s ty v r h; simp [normalizeValueForTyFuel] at h
  | succ n ih =>
    intro s ty v r h
    cases ty
    case int kind =>
      cases v <;> simp [normalizeValueForTyFuel] at h <;> subst h <;>
        simp [GoValue.locSup]
    case float kind =>
      cases v <;> try (simp [normalizeValueForTyFuel] at h; done)
      rename_i bits k
      simp only [normalizeValueForTyFuel] at h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        simp [GoValue.locSup]
      · simp [Bind.bind, Except.bind] at h
    case array length elem =>
      cases v <;> try (simp [normalizeValueForTyFuel] at h; done)
      rename_i values
      simp only [normalizeValueForTyFuel] at h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, map_eq_ok] at h
        obtain ⟨_, _, arr, harr, rfl⟩ := h
        simpa [GoValue.locSup] using
          normalizeListWith_locSup (fun _ _ hr => ih hr) harr
    case interface id =>
      simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _
    case funcType ps rs =>
      cases v <;> simp [normalizeValueForTyFuel] at h <;> subst h <;>
        exact Nat.le_refl _
    case defined name =>
      simp only [normalizeValueForTyFuel] at h
      split at h
      · exact ih h
      · exact ih h
      · exact normalizeStructValueWith_locSup (fun _ _ _ hr => ih hr) h
      · simp at h
      · simp at h
      · simp at h
    case unsupported f => simp [normalizeValueForTyFuel] at h
    case chan d elem =>
      cases v <;>
        simp_all [normalizeValueForTyFuel, GoValue.locSup, optLocSup] <;>
        subst h <;>
        simp [GoValue.locSup, optLocSup]
    all_goals
      simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Nat.le_refl _

theorem normalizeValueForTy_locSup {s : ExecState} {ty : Ty} {v r : GoValue}
    (h : normalizeValueForTy s ty v = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold normalizeValueForTy at h
  exact normalizeValueForTyFuel_locSup _ h

theorem defaultFieldsWith_locSup {f : Ty → Except GoError GoValue}
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

theorem defaultValueFuel_locSup :
    ∀ (fuel : Nat) {s : ExecState} {ty : Ty} {v : GoValue},
      defaultValueFuel fuel s ty = .ok v → GoValue.locSup v = 0 := by
  intro fuel
  induction fuel with
  | zero => intro s ty v h; simp [defaultValueFuel] at h
  | succ n ih =>
    intro s ty v h
    cases ty
    case array length elem =>
      simp only [defaultValueFuel] at h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        simp [GoValue.locSup, goValueListSup]
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨_, _, d, hd, hv⟩ := h
        subst hv
        have h0 := ih hd
        simp only [GoValue.locSup, goValueListSup_eq]
        refine Nat.le_zero.mp (supBy_le_iff.mpr fun x hx => ?_)
        rw [Array.toList_replicate] at hx
        rw [List.eq_of_mem_replicate hx, h0]
        exact Nat.le_refl _
    case defined name =>
      simp only [defaultValueFuel] at h
      split at h
      · simp only [map_eq_ok] at h
        obtain ⟨arr, harr, rfl⟩ := h
        simpa [GoValue.locSup] using
          defaultFieldsWith_locSup (fun _ _ hr => ih hr) harr
      · exact ih h
      · exact ih h
      · simp at h
      · simp at h
      · simp at h
    case unsupported f => simp [defaultValueFuel] at h
    all_goals
      simp only [defaultValueFuel, pure_eq_ok, Except.ok.injEq] at h
      subst h <;> simp [GoValue.locSup, optLocSup]

theorem defaultValue_locSup {s : ExecState} {ty : Ty} {v : GoValue}
    (h : defaultValue s ty = .ok v) : GoValue.locSup v = 0 := by
  unfold defaultValue at h
  exact defaultValueFuel_locSup _ h

theorem convertValueToTyFuel_locSup :
    ∀ (fuel : Nat) {s : ExecState} {ty : Ty} {v r : GoValue},
      convertValueToTyFuel fuel s ty v = .ok r →
      GoValue.locSup r ≤ GoValue.locSup v := by
  intro fuel
  induction fuel with
  | zero =>
    intro s ty v r h
    cases ty <;> cases v <;>
      first
      | (simp [convertValueToTyFuel] at h; done)
      | (simp only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] at h;
         subst h; first | exact Nat.le_refl _ | simp [GoValue.locSup])
      | -- float arms (floats slice F2): nested kind/range dispatch, every
        -- ok result a loc-free scalar
        (simp only [convertValueToTyFuel] at h;
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
  | succ n ih =>
    intro s ty v r h
    cases ty
    case defined name =>
      simp only [convertValueToTyFuel] at h
      split at h
      · exact ih h
      · exact ih h
      · -- struct conversion (stage 7): identity, or a retagged copy with
        -- the SAME fields — locSup is over the fields either way.
        split at h
        · split at h
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
        · simp at h
      · simp at h
      · simp at h
      · simp at h
    all_goals
      cases v <;>
        first
        | (simp [convertValueToTyFuel] at h; done)
        | (simp only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] at h;
           subst h; first | exact Nat.le_refl _ | simp [GoValue.locSup])
        | -- float arms (floats slice F2), as in the zero case
          (simp only [convertValueToTyFuel] at h;
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

/-! ## Soundness of the self-normalization check

`isNormalForTyFuel` (Ops.lean) mirrors the normalizer arm-for-arm; here
is the direction every theorem consumes: check true ⇒ the normalizer
returns the value UNCHANGED. Stated against an arbitrary state whose
`types` is the checker's environment. -/

theorem isNormalListWith_sound {f : GoValue → Bool}
    {g : GoValue → Except GoError GoValue}
    (hfg : ∀ v, f v = true → g v = .ok v) :
    ∀ {l : List GoValue}, isNormalListWith f l = true →
      normalizeListWith g l = .ok l.toArray := by
  intro l
  induction l with
  | nil => intro _; simp [normalizeListWith, pure, Except.pure]
  | cons v rest ih =>
    intro h
    simp only [isNormalListWith, Bool.and_eq_true] at h
    simp [normalizeListWith, hfg v h.1, ih h.2, Bind.bind, Except.bind,
      pure, Except.pure]

theorem isNormalFieldsWith_sound {f : Ty → GoValue → Bool}
    {g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v, f ty v = true → g ty v = .ok v) :
    ∀ {fds : List FieldDef} {vals : List (String × GoValue)},
      isNormalFieldsWith f fds vals = true →
      normalizeFieldsWith g fds vals = .ok vals.toArray := by
  intro fds
  induction fds with
  | nil =>
    intro vals h
    cases vals with
    | nil => simp [normalizeFieldsWith, pure, Except.pure]
    | cons _ _ => simp [isNormalFieldsWith] at h
  | cons fd fdRest ih =>
    intro vals h
    cases vals with
    | nil => simp [isNormalFieldsWith] at h
    | cons p valRest =>
      obtain ⟨actual, v⟩ := p
      simp only [isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hname, hv⟩, hrest⟩ := h
      subst hname
      simp [normalizeFieldsWith, hfg _ _ hv, ih hrest, Bind.bind, Except.bind,
        pure, Except.pure]

theorem isNormalForTyFuel_sound {σ : ExecState} :
    ∀ (fuel : Nat) (ty : Ty) (v : GoValue),
      isNormalForTyFuel fuel σ.types ty v = true →
      normalizeValueForTyFuel fuel σ ty v = .ok v := by
  intro fuel
  induction fuel with
  | zero => intro ty v h; simp [isNormalForTyFuel] at h
  | succ f ih =>
    intro ty v h
    cases ty with
    | int kind =>
      cases v
      case int value k =>
        simp only [isNormalForTyFuel, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        simp [normalizeValueForTyFuel, h1, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyFuel])
    | float kind =>
      cases v
      case float bits k =>
        simp only [isNormalForTyFuel, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        simp only [normalizeValueForTyFuel, h1, pure, Except.pure]
        have hbeq : (kind == kind) = true := by cases kind <;> rfl
        simp [hbeq, h1]
      all_goals exact absurd h (by simp [isNormalForTyFuel])
    | array length elem =>
      cases v
      case array values =>
        simp only [isNormalForTyFuel, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hels⟩ := h
        have hlist := isNormalListWith_sound (fun w hw => ih elem w hw) hels
        simp [normalizeValueForTyFuel, hsz, hlist, Bind.bind, Except.bind,
          Except.map, Functor.map, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyFuel])
    | interface _ => simp [normalizeValueForTyFuel, pure, Except.pure]
    | funcType params results =>
      cases v
      case funcVal fid captured =>
        simp [normalizeValueForTyFuel, pure, Except.pure]
      case nil => simp [normalizeValueForTyFuel, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyFuel])
    | defined name =>
      simp only [isNormalForTyFuel] at h
      cases hlook : TypeEnv.lookup σ.types name with
      | none => rw [hlook] at h; exact absurd h (by simp)
      | some td =>
        rw [hlook] at h
        cases td with
        | alias target =>
          simpa [normalizeValueForTyFuel, hlook] using ih target v h
        | defined target =>
          simpa [normalizeValueForTyFuel, hlook] using ih target v h
        | struct fields =>
          cases v
          case struct actual fieldsValue =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hname, hsz⟩, hflds⟩ := h
            subst hname
            have hf := isNormalFieldsWith_sound
              (fun t w hw => ih t w hw) hflds
            simp [normalizeValueForTyFuel, hlook, normalizeStructValueWith,
              hsz, hf, Bind.bind, Except.bind, Except.map, Functor.map,
              pure, Except.pure]
          all_goals exact absurd h (by simp)
        | unsupported _ => exact absurd h (by simp)
        | interfaceDef _ => exact absurd h (by simp)
    | unsupported _ => simp [isNormalForTyFuel] at h
    | bool => simp [normalizeValueForTyFuel, pure, Except.pure]
    | string => simp [normalizeValueForTyFuel, pure, Except.pure]
    | slice _ => simp [normalizeValueForTyFuel, pure, Except.pure]
    | map _ _ => simp [normalizeValueForTyFuel, pure, Except.pure]
    | chan _ _ =>
      cases v
      case chan cv => simp [normalizeValueForTyFuel, pure, Except.pure]
      all_goals exact absurd h (by simp [isNormalForTyFuel])
    | pointer _ => simp [normalizeValueForTyFuel, pure, Except.pure]

/-- The wrapper form: check at `σ.types` ⇒ `normalizeValueForTy` is the
identity (in `.ok`) at `σ`. -/
theorem isNormalForTy_sound {σ : ExecState} {ty : Ty} {v : GoValue}
    (h : isNormalForTy σ.types ty v = true) :
    normalizeValueForTy σ ty v = .ok v := by
  unfold normalizeValueForTy
  unfold isNormalForTy at h
  exact isNormalForTyFuel_sound _ _ _ h

theorem convertValueToTy_locSup {s : ExecState} {ty : Ty} {v r : GoValue}
    (h : convertValueToTy s ty v = .ok r) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold convertValueToTy at h
  exact convertValueToTyFuel_locSup _ h

/-! ## StateWf projections -/

theorem StateWf.heap_le {σ : ExecState} (h : StateWf σ) :
    Heap.locSup σ.heap ≤ σ.nextAddr := by
  unfold StateWf ExecState.locSup at h
  omega

theorem StateWf.funcs_le {σ : ExecState} (h : StateWf σ) :
    funcListSup σ.functions.toList ≤ σ.nextAddr := by
  unfold StateWf ExecState.locSup at h
  omega

theorem StateWf.mk' {σ : ExecState} (h1 : Heap.locSup σ.heap ≤ σ.nextAddr)
    (h2 : funcListSup σ.functions.toList ≤ σ.nextAddr) : StateWf σ := by
  unfold StateWf ExecState.locSup
  omega

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
  simp only [bind_eq_ok] at h
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
  · simp only [bind_eq_ok] at h
    obtain ⟨⟨lo', hi'⟩, -, hv⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq] at hv
    subst hv
    simp [GoValue.locSup, optLocSup]
  · simp only [bind_eq_ok] at h
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
    obtain ⟨_, _, p, _, hv⟩ := h
    subst hv
    rfl

/-! ## Heap access -/

theorem loadLoc_locSup {s : ExecState} :
    ∀ {l : Loc} {v : GoValue}, loadLoc s l = .ok v →
      GoValue.locSup v ≤ Heap.locSup s.heap := by
  intro l
  induction l with
  | base a =>
    intro v h
    unfold loadLoc at h
    split at h
    · rename_i cell hcell
      simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact Heap.lookup_locSup hcell
    · simp at h
  | field b tid fname ih =>
    intro v h
    unfold loadLoc at h
    simp only [bind_eq_ok] at h
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
    simp only [bind_eq_ok] at h
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
theorem indexTargetLoc_locSup {s : ExecState} {b i : GoValue} {l : Loc}
    (h : indexTargetLoc s b i = .ok l) :
    Loc.locSup l ≤ max (GoValue.locSup b) (Heap.locSup s.heap) := by
  unfold indexTargetLoc at h
  simp only [bind_eq_ok] at h
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
    simp only [bind_eq_ok] at h
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

theorem goValueListSup_push {arr : Array GoValue} {x : GoValue} :
    goValueListSup (arr.push x).toList
      = max (goValueListSup arr.toList) (GoValue.locSup x) := by
  simp [goValueListSup_eq, Array.toList_push, supBy_append, supBy]

theorem goValueFieldsSup_push {arr : Array (String × GoValue)}
    {p : String × GoValue} :
    goValueFieldsSup (arr.push p).toList
      = max (goValueFieldsSup arr.toList) (GoValue.locSup p.2) := by
  simp [goValueFieldsSup_eq, Array.toList_push, supBy_append, supBy]

theorem goValueEntriesSup_push {arr : Array (GoValue × GoValue)}
    {p : GoValue × GoValue} :
    goValueEntriesSup (arr.push p).toList
      = max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.1) (GoValue.locSup p.2)) := by
  simp [goValueEntriesSup_eq, Array.toList_push, supBy_append, supBy]

theorem goValueEntriesSup_mem {arr : List (GoValue × GoValue)}
    {p : GoValue × GoValue} (h : p ∈ arr) :
    max (GoValue.locSup p.1) (GoValue.locSup p.2) ≤ goValueEntriesSup arr := by
  rw [goValueEntriesSup_eq]
  exact supBy_mem (f := fun p => max (GoValue.locSup p.1) (GoValue.locSup p.2)) h

theorem goValueEntriesSup_setIfInBounds {arr : Array (GoValue × GoValue)} {i : Nat}
    {p : GoValue × GoValue} :
    goValueEntriesSup (arr.setIfInBounds i p).toList
      ≤ max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.1) (GoValue.locSup p.2)) := by
  simp only [goValueEntriesSup_eq]
  rw [Array.toList_setIfInBounds]
  refine supBy_le_iff.mpr fun a ha => ?_
  rcases List.mem_or_eq_of_mem_set ha with hmem | rfl
  · exact Nat.le_trans
      (supBy_mem (f := fun p => max (GoValue.locSup p.1) (GoValue.locSup p.2)) hmem)
      (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

theorem goValueEntriesSup_eraseIdx! {arr : Array (GoValue × GoValue)} {i : Nat} :
    goValueEntriesSup (arr.eraseIdx! i).toList
      ≤ goValueEntriesSup arr.toList := by
  simp only [goValueEntriesSup_eq]
  unfold Array.eraseIdx!
  split
  · rw [Array.toList_eraseIdx]
    exact supBy_le_of_subset fun a ha => List.mem_of_mem_eraseIdx ha
  · -- out of range: `panic!` computes to `default = #[]`
    rw [show (panicWithPosWithDecl "Init.Data.Array.Basic" "Array.eraseIdx!" 1820 47
        "invalid index" : Array (GoValue × GoValue)) = #[] from rfl]
    simp [supBy]

theorem goValueEntriesSup_eraseIdx {arr : Array (GoValue × GoValue)} {i : Nat}
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

/-! ## `StructFields.set` (the store path through a struct) -/

theorem goValueEntriesSup_set! {arr : Array (GoValue × GoValue)} {i : Nat}
    {p : GoValue × GoValue} :
    goValueEntriesSup (arr.set! i p).toList
      ≤ max (goValueEntriesSup arr.toList)
          (max (GoValue.locSup p.1) (GoValue.locSup p.2)) := by
  rw [Array.set!]
  exact goValueEntriesSup_setIfInBounds

theorem goValueListSup_set! {arr : Array GoValue} {i : Nat} {x : GoValue} :
    goValueListSup (arr.set! i x).toList
      ≤ max (goValueListSup arr.toList) (GoValue.locSup x) := by
  rw [Array.set!]
  exact goValueListSup_setIfInBounds

theorem StructFields.set_locSup {fields : Array (String × GoValue)}
    {needle : String} {v : GoValue} {out : Array (String × GoValue)}
    (h : StructFields.set fields needle v = .ok out) :
    goValueFieldsSup out.toList
      ≤ max (goValueFieldsSup fields.toList) (GoValue.locSup v) := by
  unfold StructFields.set at h
  simp only [bind_eq_ok] at h
  obtain ⟨st, hloop, hpost⟩ := h
  rw [← Array.forIn_toList] at hloop
  have hP := forIn_list_inv
    (P := fun st : MProd Bool (Array (String × GoValue)) =>
      goValueFieldsSup st.2.toList
        ≤ max (goValueFieldsSup fields.toList) (GoValue.locSup v))
    (l := fields.toList) ?step (Nat.zero_le _) hloop
  · split at hpost
    · simp only [pure_eq_ok, Except.ok.injEq] at hpost
      subst hpost
      exact hP
    · simp [throw, throwThe, MonadExceptOf.throw] at hpost
  · intro a ha b r hb hr
    obtain ⟨name, old⟩ := a
    have hmem : GoValue.locSup old ≤ goValueFieldsSup fields.toList := by
      rw [goValueFieldsSup_eq]
      exact supBy_mem (f := fun p => GoValue.locSup p.2) ha
    split at hr <;>
    · simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq] at hr
      subst hr
      simp only [forInStepVal, goValueFieldsSup_push]
      omega

/-! ## `storeLoc`: shape and preservation -/

theorem storeLoc_shape {σ : ExecState} :
    ∀ {l : Loc} {v : GoValue} {σ' : ExecState}, storeLoc σ l v = .ok σ' →
      σ'.types = σ.types ∧ σ'.functions = σ.functions
        ∧ σ'.methods = σ.methods ∧ σ'.nextAddr = σ.nextAddr
        ∧ Heap.locSup σ'.heap
            ≤ max (Heap.locSup σ.heap) (max (Loc.locSup l) (GoValue.locSup v)) := by
  intro l
  induction l with
  | base a =>
    intro v σ' h
    unfold storeLoc at h
    split at h
    · rename_i cell hcell
      split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨v', hv', hσ⟩ := h
        subst hσ
        have hb : GoValue.locSup v' ≤ GoValue.locSup v :=
          normalizeValueForTy_locSup hv'
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        refine Nat.le_trans Heap.set_locSup ?_
        have hc : HeapCell.locSup { cell with value := v' }
            = GoValue.locSup v' := rfl
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨v', hv', hσ⟩ := h
        subst hσ
        have hb : GoValue.locSup v' ≤ GoValue.locSup v :=
          coerceStoredValue_locSup hv'
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        refine Nat.le_trans Heap.set_locSup ?_
        have hc : HeapCell.locSup { cell with value := v' }
            = GoValue.locSup v' := rfl
        omega
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      refine Nat.le_trans Heap.set_locSup ?_
      have hc : HeapCell.locSup { value := v } = GoValue.locSup v := rfl
      omega
  | field b tid fname ih =>
    intro v σ' h
    unfold storeLoc at h
    simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · rename_i actual fields
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [Bind.bind, Except.bind] at h
        cases hset : StructFields.set fields fname v with
        | error e => rw [hset] at h; simp [Except.bind] at h
        | ok updated =>
          rw [hset] at h
          simp only [Except.bind] at h
          have hup := StructFields.set_locSup hset
          have hload := loadLoc_locSup hbv
          obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
          refine ⟨h1, h2, h3, h4, ?_⟩
          simp only [GoValue.locSup] at h5 hload
          simp only [Loc.locSup_field]
          omega
    · simp at h
  | index b i ih =>
    intro v σ' h
    unfold storeLoc at h
    simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · rename_i values
      simp only [bind_eq_ok] at h
      obtain ⟨updated, hupd, h⟩ := h
      have hup := arraySet_locSup hupd
      have hload := loadLoc_locSup hbv
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
      refine ⟨h1, h2, h3, h4, ?_⟩
      simp only [GoValue.locSup] at h5 hload
      simp only [Loc.locSup_index]
      omega
    · simp at h

theorem storeLoc_wf {σ : ExecState} {l : Loc} {v : GoValue} {σ' : ExecState}
    (hw : StateWf σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) (h : storeLoc σ l v = .ok σ') :
    StateWf σ' ∧ σ'.nextAddr = σ.nextAddr ∧ σ'.functions = σ.functions := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := storeLoc_shape h
  have hh := hw.heap_le
  have hf := hw.funcs_le
  refine ⟨StateWf.mk' ?_ ?_, h4, h2⟩
  · rw [h4]; omega
  · rw [h4, h2]; exact hf

/-! ## Allocation -/

theorem alloc_shape {σ : ExecState} {v : GoValue} {ty : Option Ty} {l : Loc}
    {σ' : ExecState} (h : σ.alloc v ty = (l, σ')) :
    l = .base ⟨σ.nextAddr⟩ ∧ σ'.nextAddr = σ.nextAddr + 1
      ∧ σ'.types = σ.types ∧ σ'.functions = σ.functions ∧ σ'.methods = σ.methods
      ∧ Heap.locSup σ'.heap
          ≤ max (Heap.locSup σ.heap) (max (σ.nextAddr + 1) (GoValue.locSup v)) := by
  -- definitional bridge to the explicit record form
  have h1 : Loc.base ⟨σ.nextAddr⟩ = l := congrArg Prod.fst h
  have h2 : ({ σ with
      heap := Heap.set σ.heap (Loc.base ⟨σ.nextAddr⟩) { declaredTy := ty, value := v },
      nextAddr := σ.nextAddr + 1 } : ExecState) = σ' := congrArg Prod.snd h
  subst h1
  subst h2
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine Nat.le_trans Heap.set_locSup ?_
  have hc : HeapCell.locSup { declaredTy := ty, value := v } = GoValue.locSup v := rfl
  have hl : Loc.locSup (.base ⟨σ.nextAddr⟩) = σ.nextAddr + 1 := rfl
  omega

theorem alloc_wf {σ : ExecState} {v : GoValue} {ty : Option Ty} {l : Loc}
    {σ' : ExecState} (hw : StateWf σ) (hv : GoValue.locSup v ≤ σ.nextAddr)
    (h : σ.alloc v ty = (l, σ')) :
    StateWf σ' ∧ Loc.locSup l ≤ σ'.nextAddr ∧ σ'.nextAddr = σ.nextAddr + 1
      ∧ σ'.functions = σ.functions := by
  obtain ⟨hl, h2, h3, h4, h5, h6⟩ := alloc_shape h
  have hh := hw.heap_le
  have hf := hw.funcs_le
  refine ⟨StateWf.mk' ?_ ?_, ?_, h2, h4⟩
  · rw [h2]; omega
  · rw [h2, h4]; omega
  · rw [h2, hl]
    simp [Loc.locSup, Loc.rootBase]

/-! ## List-op threading lemmas (call protocol) -/

theorem loadMany_locSup {σ : ExecState} :
    ∀ {locs : List Loc} {vs : List GoValue}, loadMany σ locs = .ok vs →
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

theorem storeMany_shape {σ : ExecState} :
    ∀ {locs : List Loc} {vs : List GoValue} {σ' : ExecState},
      storeMany σ locs vs = .ok σ' →
      σ'.types = σ.types ∧ σ'.functions = σ.functions
        ∧ σ'.methods = σ.methods ∧ σ'.nextAddr = σ.nextAddr
        ∧ Heap.locSup σ'.heap ≤ max (Heap.locSup σ.heap)
            (max (locListSup locs) (goValueListSup vs)) := by
  intro locs
  induction locs generalizing σ with
  | nil =>
    intro vs σ' h
    cases vs with
    | nil =>
      simp only [storeMany, pure_eq_ok, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, Nat.le_max_left _ _⟩
    | cons v rest => simp [storeMany] at h
  | cons l lrest ih =>
    intro vs σ' h
    cases vs with
    | nil => simp [storeMany] at h
    | cons v vrest =>
      simp only [storeMany, bind_eq_ok] at h
      obtain ⟨σ₁, hσ₁, h⟩ := h
      obtain ⟨a1, a2, a3, a4, a5⟩ := storeLoc_shape hσ₁
      obtain ⟨b1, b2, b3, b4, b5⟩ := ih h
      rw [a1] at b1; rw [a2] at b2; rw [a3] at b3; rw [a4] at b4
      refine ⟨b1, b2, b3, b4, ?_⟩
      simp only [locListSup, goValueListSup]
      omega

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
    ∀ {ps : List Param} {env : LocalEnv} {σ : ExecState} {env' : LocalEnv}
      {σ' : ExecState},
      allocDecls env σ ps = .ok (env', σ') → StateWf σ →
      LocalEnv.locSup env ≤ σ.nextAddr →
      StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.functions = σ.functions
        ∧ σ'.types = σ.types ∧ σ'.methods = σ.methods
        ∧ LocalEnv.locSup env' ≤ σ'.nextAddr := by
  intro ps
  induction ps with
  | nil =>
    intro env σ env' σ' h hw henv
    simp only [allocDecls, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, Nat.le_refl _, rfl, rfl, rfl, henv⟩
  | cons p rest ih =>
    intro env σ env' σ' h hw henv
    simp only [allocDecls, bind_eq_ok] at h
    obtain ⟨v, hv, h⟩ := h
    have hv0 := defaultValue_locSup hv
    cases halloc : σ.alloc v (some p.typ) with
    | mk loc σ₁ =>
      rw [halloc] at h
      dsimp only at h
      obtain ⟨hw₁, hloc, hna, hfuncs⟩ := alloc_wf hw (by omega) halloc
      obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
      try dsimp only at hw₁ hloc hna hfuncs d1 d2 d3 d4 d5
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ih h hw₁ (by
        refine Nat.le_trans LocalEnv.declare_locSup ?_
        rw [hna]
        refine Nat.max_le.mpr ⟨by omega, ?_⟩
        rw [← hna]; exact hloc)
      refine ⟨c1, by omega, by rw [c3, hfuncs], by rw [c4, d3], by rw [c5, d5], c6⟩

theorem bindParams_wf :
    ∀ {ps : List Param} {vals : List GoValue} {env : LocalEnv} {σ : ExecState}
      {env' : LocalEnv} {σ' : ExecState},
      bindParams env σ ps vals = .ok (env', σ') → StateWf σ →
      LocalEnv.locSup env ≤ σ.nextAddr → goValueListSup vals ≤ σ.nextAddr →
      StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.functions = σ.functions
        ∧ σ'.types = σ.types ∧ σ'.methods = σ.methods
        ∧ LocalEnv.locSup env' ≤ σ'.nextAddr := by
  intro ps
  induction ps with
  | nil =>
    intro vals env σ env' σ' h hw henv hvals
    cases vals with
    | nil =>
      simp only [bindParams, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, Nat.le_refl _, rfl, rfl, rfl, henv⟩
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
      cases halloc : σ.alloc v' (some p.typ) with
      | mk loc σ₁ =>
        rw [halloc] at h
        dsimp only at h
        obtain ⟨hw₁, hloc, hna, hfuncs⟩ := alloc_wf hw hvb halloc
        obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
        try dsimp only at hw₁ hloc hna hfuncs d1 d2 d3 d4 d5
        obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ih h hw₁ (by
          refine Nat.le_trans LocalEnv.declare_locSup ?_
          rw [hna]
          exact Nat.max_le.mpr ⟨by omega, by rw [← hna]; exact hloc⟩) (by
          simp only [goValueListSup] at hvals
          omega)
        exact ⟨c1, by omega, by rw [c3, hfuncs], by rw [c4, d3], by rw [c5, d5], c6⟩

/-! ## Map/assert helpers -/

theorem mapEntries_locSup {σ : ExecState} {m : MapValue}
    {out : Option (Loc × Array (GoValue × GoValue))}
    (h : mapEntries σ m = .ok out) :
    ∀ {baseLoc entries}, out = some (baseLoc, entries) →
      Loc.locSup baseLoc ≤ optLocSup m.base
        ∧ goValueEntriesSup entries.toList ≤ Heap.locSup σ.heap := by
  intro baseLoc entries hout
  subst hout
  unfold mapEntries at h
  split at h
  · simp at h
  · rename_i base heq
    simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · rename_i es
      simp only [pure_eq_ok, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      constructor
      · rw [heq]; exact Nat.le_refl _
      · have := loadLoc_locSup hbv
        simpa [GoValue.locSup] using this
    · simp at h

theorem mapEntryIndex?_ok_entries {σ : ExecState} {kt : Ty}
    {entries : Array (GoValue × GoValue)} {key : GoValue} {i : Nat}
    {isInsert : Bool}
    (h : mapEntryIndex? σ kt entries key isInsert = .ok (some i)) :
    True := trivial

theorem mapLookupValue_locSup {σ : ExecState} {m : MapValue} {key : GoValue}
    {kt vt : Ty} {rv : GoValue} {b : Bool}
    (h : mapLookupValue σ m key kt vt = .ok (rv, b)) :
    GoValue.locSup rv ≤ Heap.locSup σ.heap := by
  unfold mapLookupValue at h
  simp only [bind_eq_ok] at h
  obtain ⟨es, hes, h⟩ := h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, d, hd, rfl, rfl⟩ := h
    rw [defaultValue_locSup hd]
    exact Nat.zero_le _
  · rename_i baseLoc entries
    simp only [bind_eq_ok] at h
    obtain ⟨idx, hidx, h⟩ := h
    split at h
    · rename_i i
      split at h
      · rename_i k' v' hp
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem : (k', v') ∈ entries.toList :=
          List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp)
        have h2 := (mapEntries_locSup hes rfl).2
        have h3 := goValueEntriesSup_mem hmem
        simp only at h3
        omega
      · simp at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨d, hd, rfl, rfl⟩ := h
      rw [defaultValue_locSup hd]
      exact Nat.zero_le _

theorem typeAssertValue_locSup {σ : ExecState} {v : GoValue} {ty : Ty}
    {r : GoValue} {b : Bool} (h : typeAssertValue σ v ty = .ok (r, b)) :
    GoValue.locSup r ≤ GoValue.locSup v := by
  unfold typeAssertValue at h
  simp only [bind_eq_ok] at h
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

theorem dynamicDispatch?_locSup {σ : ExecState} {func : Func}
    {args : Array GoValue} {out : Option (Func × Array GoValue)}
    (h : dynamicDispatch? σ func args = .ok out) :
    ∀ {tf : Func} {args' : Array GoValue}, out = some (tf, args') →
      Func.locSup tf ≤ funcListSup σ.functions.toList
        ∧ goValueListSup args'.toList
            ≤ max (goValueListSup args.toList) (Heap.locSup σ.heap) := by
  intro tf args' hout
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
        split at h
        · rename_i concrete needsDeref hconc
          split at h
          · rename_i f' hf'
            have htfb : Func.locSup f' ≤ funcListSup σ.functions.toList :=
              findFunctionIn?_locSup hf'
            have hinner : GoValue.locSup inner ≤ goValueListSup args.toList := by
              have := goValueListSup_getElem? heq
              simpa [GoValue.locSup] using this
            split at h
            · -- needsDeref
              split at h
              · -- .addr loc: load
                rename_i loc
                split at h
                · simp at h
                · rename_i rv hrv
                  simp only [Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  refine ⟨htfb, ?_⟩
                  try rw [Array.set!]
                  refine Nat.le_trans goValueListSup_setIfInBounds ?_
                  have := loadLoc_locSup hrv
                  omega
              · simp at h
              · simp at h
            · -- no deref: receiver is the boxed value
              simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨htfb, ?_⟩
              try rw [Array.set!]
              refine Nat.le_trans goValueListSup_setIfInBounds ?_
              omega
          · simp at h
        · simp at h
      · simp at h
      · simp at h

theorem enterFrame_tail {σ : ExecState} {func₁ : Func} {argVals₁ : List GoValue}
    {argsEnv : LocalEnv} {s₁ : ExecState} {frameEnv₁ : LocalEnv} {s₂ : ExecState}
    {locs : List Loc}
    (hw : StateWf σ)
    (hf₁ : Func.locSup func₁ ≤ funcListSup σ.functions.toList)
    (hargs₁ : goValueListSup argVals₁ ≤ σ.nextAddr)
    (hbp : bindParams [] σ func₁.args.toList argVals₁ = .ok (argsEnv, s₁))
    (had : allocDecls argsEnv s₁ func₁.results.toList = .ok (frameEnv₁, s₂))
    (hpin : pinResultLocs frameEnv₁ func₁.results.toList = .ok locs) :
    StateWf s₂ ∧ σ.nextAddr ≤ s₂.nextAddr ∧ s₂.types = σ.types
      ∧ s₂.functions = σ.functions ∧ s₂.methods = σ.methods
      ∧ Stmt.locSup func₁.body ≤ s₂.nextAddr
      ∧ LocalEnv.locSup frameEnv₁ ≤ s₂.nextAddr
      ∧ locListSup locs ≤ s₂.nextAddr := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bindParams_wf hbp hw
    (by simp [LocalEnv.locSup]) hargs₁
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := allocDecls_wf had b1 b6
  have hpinb := pinResultLocs_locSup hpin
  have hfs := c1.funcs_le
  rw [c3, b3] at hfs
  have hbody : Stmt.locSup func₁.body ≤ funcListSup σ.functions.toList := hf₁
  exact ⟨c1, by omega, by rw [c4, b4], by rw [c3, b3], by rw [c5, b5],
    by omega, c6, by omega⟩

theorem enterFrame_wf {σ : ExecState} {fid : FuncId} {argVals : List GoValue}
    {func : Func} {frameEnv : LocalEnv} {resultLocs : List Loc} {σ' : ExecState}
    (hw : StateWf σ) (hargs : goValueListSup argVals ≤ σ.nextAddr)
    (h : enterFrame σ fid argVals = .ok (func, frameEnv, resultLocs, σ')) :
    StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.types = σ.types
      ∧ σ'.functions = σ.functions ∧ σ'.methods = σ.methods
      ∧ Stmt.locSup func.body ≤ σ'.nextAddr
      ∧ LocalEnv.locSup frameEnv ≤ σ'.nextAddr
      ∧ locListSup resultLocs ≤ σ'.nextAddr := by
  unfold enterFrame at h
  simp only [Bind.bind, Except.bind, pure, Except.pure, GoCore.stuck,
    throw, throwThe, MonadExceptOf.throw] at h
  split at h
  all_goals try (simp at h; done)
  rename_i func₀ hfunc₀
  have hf₀ : Func.locSup func₀ ≤ funcListSup σ.functions.toList :=
    findFunctionIn?_locSup hfunc₀
  split at h
  all_goals try (simp at h; done)
  split at h
  all_goals try (simp at h; done)
  rename_i dOut hdd
  split at h
  · -- dispatch hit
    rename_i tf ta
    obtain ⟨h1, h2⟩ := dynamicDispatch?_locSup hdd rfl
    split at h
    all_goals try (simp at h; done)
    split at h
    all_goals try (simp at h; done)
    rename_i p₁ hbp
    obtain ⟨argsEnv, s₁⟩ := p₁
    dsimp only at h
    split at h
    all_goals try (simp at h; done)
    rename_i p₂ had
    obtain ⟨frameEnv₁, s₂⟩ := p₂
    dsimp only at h
    split at h
    all_goals try (simp at h; done)
    rename_i locs hpin
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine enterFrame_tail hw h1 ?_ hbp had hpin
    have harr : goValueListSup argVals.toArray.toList
        = goValueListSup argVals := by simp
    have hh := hw.heap_le
    omega
  · -- no dispatch
    split at h
    all_goals try (simp at h; done)
    rename_i p₁ hbp
    obtain ⟨argsEnv, s₁⟩ := p₁
    dsimp only at h
    split at h
    all_goals try (simp at h; done)
    rename_i p₂ had
    obtain ⟨frameEnv₁, s₂⟩ := p₂
    dsimp only at h
    split at h
    all_goals try (simp at h; done)
    rename_i locs hpin
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact enterFrame_tail hw hf₀ hargs hbp had hpin

theorem bindIterVars_wf {env : LocalEnv} {σ : ExecState}
    {kv vv : Option String} {kt vt : Ty} {key value : GoValue}
    {env' : LocalEnv} {σ' : ExecState}
    (hw : StateWf σ) (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : GoValue.locSup key ≤ σ.nextAddr)
    (hv : GoValue.locSup value ≤ σ.nextAddr)
    (h : bindIterVars env σ kv vv kt vt key value = .ok (env', σ')) :
    StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.functions = σ.functions
      ∧ σ'.types = σ.types ∧ σ'.methods = σ.methods
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
    cases halloc : σ.alloc kv' (some kt) with
    | mk loc σa =>
      rw [halloc] at h
      dsimp only at h
      obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw hkb halloc
      obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
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
        cases halloc₂ : σa.alloc vv' (some vt) with
        | mk loc₂ σb =>
          rw [halloc₂] at h
          dsimp only at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨y1, y2, y3, y4⟩ := alloc_wf w1 hvb halloc₂
          obtain ⟨e1, e2, e3, e4, e5, _⟩ := alloc_shape halloc₂
          refine ⟨y1, by omega, by rw [y4, w4], by rw [e3, d3], by rw [e5, d5], ?_⟩
          refine Nat.le_trans LocalEnv.declare_locSup ?_
          exact Nat.max_le.mpr ⟨by omega, y2⟩
      · -- value unbound
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨w1, by omega, w4, d3, d5, henva⟩
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
      cases halloc : σ.alloc vv' (some vt) with
      | mk loc σa =>
        rw [halloc] at h
        dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw hvb halloc
        obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
        refine ⟨w1, by omega, w4, d3, d5, ?_⟩
        refine Nat.le_trans LocalEnv.declare_locSup ?_
        exact Nat.max_le.mpr ⟨by omega, w2⟩
    · -- neither bound
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, Nat.le_refl _, rfl, rfl, rfl, henv⟩

theorem mapRangeEntries_locSup {σ : ExecState} {v : GoValue}
    {entries : Array (GoValue × GoValue)}
    (h : mapRangeEntries σ v = .ok entries) :
    goValueEntriesSup entries.toList ≤ Heap.locSup σ.heap := by
  unfold mapRangeEntries at h
  simp only [bind_eq_ok] at h
  obtain ⟨m, hm, h⟩ := h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [goValueEntriesSup]
  · rename_i base
    simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h⟩ := h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      have := loadLoc_locSup hbv
      simpa [GoValue.locSup] using this
    · simp at h

/-- Inversion of the validated snapshot premise (sem-adequacy slice 3):
a successful `mapRangeSnapshotEntries` is exactly a successful raw
snapshot whose entries pass the self-normalization check. -/
theorem mapRangeSnapshotEntries_ok {σ : ExecState} {keyTy valTy : Ty}
    {v : GoValue} {entries : Array (GoValue × GoValue)}
    (h : mapRangeSnapshotEntries σ keyTy valTy v = .ok entries) :
    mapRangeEntries σ v = .ok entries
      ∧ snapshotEntriesSelfNormalized σ.types keyTy valTy entries = true := by
  unfold mapRangeSnapshotEntries at h
  simp only [bind_eq_ok] at h
  obtain ⟨es, hes, h⟩ := h
  split at h
  · rename_i hchk
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact ⟨hes, hchk⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem mapRangeSnapshotEntries_locSup {σ : ExecState} {keyTy valTy : Ty}
    {v : GoValue} {entries : Array (GoValue × GoValue)}
    (h : mapRangeSnapshotEntries σ keyTy valTy v = .ok entries) :
    goValueEntriesSup entries.toList ≤ Heap.locSup σ.heap :=
  mapRangeEntries_locSup (mapRangeSnapshotEntries_ok h).1

/-! ## Literal/aggregate builders -/

theorem buildStructFields_locSup {σ : ExecState} :
    ∀ {fds : List FieldDef} {vals : List GoValue}
      {arr : Array (String × GoValue)},
      buildStructFields σ fds vals = .ok arr →
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

theorem buildStructValueFuel_locSup :
    ∀ (fuel : Nat) {σ : ExecState} {ty : Ty} {args : Array GoValue} {r : GoValue},
      buildStructValueFuel fuel σ ty args = .ok r →
      GoValue.locSup r ≤ goValueListSup args.toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ ty args r h
    rw [buildStructValueFuel.eq_def] at h
    split at h <;> simp_all
  | succ n ih =>
    intro σ ty args r h
    rw [buildStructValueFuel.eq_def] at h
    split at h
    · rename_i fuel' name heq
      obtain rfl : fuel' = n := by omega
      split at h
      · split at h
        all_goals try (simp [Bind.bind, Except.bind] at h; done)
        simp only [Bind.bind, Except.bind, pure, Except.pure] at h
        rw [map_eq_ok] at h
        obtain ⟨fs, hfs, rfl⟩ := h
        simpa [GoValue.locSup] using buildStructFields_locSup hfs
      · exact ih h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
    · simp_all
    · simp at h
    · simp at h

theorem buildStructValue_locSup {σ : ExecState} {ty : Ty} {args : Array GoValue}
    {r : GoValue} (h : buildStructValue σ ty args = .ok r) :
    GoValue.locSup r ≤ goValueListSup args.toList := by
  unfold buildStructValue at h
  exact buildStructValueFuel_locSup _ h

theorem buildArrayValue_locSup {σ : ExecState} {len : Nat} {elem : Ty}
    {args : Array (Int × GoValue)} {r : GoValue}
    (h : buildArrayValue σ len elem args = .ok r) :
    GoValue.locSup r ≤ supBy (fun p => GoValue.locSup p.2) args.toList := by
  unfold buildArrayValue at h
  simp only [bind_eq_ok] at h
  obtain ⟨vs₁, hvs₁, h⟩ := h
  have hb₁ : goValueListSup vs₁.toList ≤ 0 := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hvs₁
    refine forIn_list_inv (P := fun vs : Array GoValue =>
      goValueListSup vs.toList ≤ 0) ?_ (Nat.zero_le _) hvs₁
    intro a _ b rr hbb hr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨d, hd, _, _, hrr⟩ := hr
    subst hrr
    have h0 := defaultValue_locSup hd
    simp only [forInStepVal, goValueListSup_push]
    omega
  obtain ⟨st, hloop, h⟩ := h
  rw [← Array.forIn_toList] at hloop
  have hP : goValueListSup st.2.toList
      ≤ supBy (fun p => GoValue.locSup p.2) args.toList := by
    refine forIn_list_inv (P := fun st : MProd (Array Int) (Array GoValue) =>
      goValueListSup st.2.toList ≤ supBy (fun p => GoValue.locSup p.2) args.toList)
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
          obtain ⟨_, _, _, _, nv, hnv, c, hc, _, _, hrr⟩ := hr
          subst hrr
          have h1 := normalizeValueForTy_locSup hnv
          have h2 := coerceStoredValue_locSup hc
          simp only [forInStepVal]
          refine Nat.le_trans goValueListSup_set! ?_
          omega
        · simp [Bind.bind, Except.bind] at hr
  simp only [pure_eq_ok, Except.ok.injEq] at h
  subst h
  simpa [GoValue.locSup] using hP

theorem buildDefaultArrayValue_locSup {σ : ExecState} {len : Nat} {elem : Ty}
    {r : GoValue} (h : buildDefaultArrayValue σ len elem = .ok r) :
    GoValue.locSup r = 0 := by
  unfold buildDefaultArrayValue at h
  have hb := buildArrayValue_locSup h
  have h0 : supBy (fun p => GoValue.locSup p.2)
      (#[] : Array (Int × GoValue)).toList = 0 := rfl
  omega

theorem sliceVisibleValues_locSup {σ : ExecState} {slice : SliceValue}
    {values : Array GoValue} (h : sliceVisibleValues σ slice = .ok values) :
    goValueListSup values.toList ≤ Heap.locSup σ.heap := by
  unfold sliceVisibleValues at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, vs, hloop, h⟩ := h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
  have hP := forIn_list_inv (P := fun vs : Array GoValue =>
      goValueListSup vs.toList ≤ Heap.locSup σ.heap)
    ?_ (Nat.zero_le _) hloop
  · simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact hP
  · intro a _ b rr hbb hr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨l, hl, v, hv, _, _, hrr⟩ := hr
    subst hrr
    have h1 := loadLoc_locSup hv
    simp only [forInStepVal, goValueListSup_push]
    omega

theorem buildAppendBackingValue_locSup {σ : ExecState} {elem : Ty}
    {oldValues elemValues : Array GoValue} {newCap : Nat} {r : GoValue}
    (h : buildAppendBackingValue σ elem oldValues elemValues newCap = .ok r) :
    GoValue.locSup r
      ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
  unfold buildAppendBackingValue at h
  simp only [bind_eq_ok] at h
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
    obtain ⟨nv, hnv, _, _, hrr⟩ := hr
    subst hrr
    have h1 := normalizeValueForTy_locSup hnv
    simp only [forInStepVal, goValueListSup_push]
    omega
  split at h
  · simp [Bind.bind, Except.bind] at h
  · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨_, _, vs₂, hloop₂, hr⟩ := h
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop₂
    have hb₂ : goValueListSup vs₂.toList
        ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList) := by
      refine forIn_list_inv (P := fun vs : Array GoValue =>
        goValueListSup vs.toList
          ≤ max (goValueListSup oldValues.toList) (goValueListSup elemValues.toList))
        ?_ hb₁ hloop₂
      intro a _ b rr hbb hr
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨d, hd, _, _, hrr⟩ := hr
      subst hrr
      have h0 := defaultValue_locSup hd
      simp only [forInStepVal, goValueListSup_push]
      omega
    subst hr
    simpa [GoValue.locSup] using hb₂

theorem applySlice_locSup {σ : ExecState} {b : GoValue} {lo hi : Int}
    {m : Option Int} {v : GoValue} {σ' : ExecState}
    (h : applySlice σ b lo hi m = .ok (v, σ')) :
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
    simp only [bind_eq_ok] at h
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
  simp only [bind_eq_ok] at h
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
  simp only [bind_eq_ok] at h
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
  simp only [bind_eq_ok] at h
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
  simp only [bind_eq_ok] at h
  obtain ⟨⟨xv, xk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨bits, hbits, vb, hvb, rfl⟩ := h
  rfl

theorem intShiftLeftResult_locSup {l r v : GoValue}
    (h : intShiftLeftResult l r = .ok v) : GoValue.locSup v = 0 := by
  unfold intShiftLeftResult at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨c, hc, rfl⟩ := h
  rfl

theorem intShiftRightResult_locSup {l r v : GoValue}
    (h : intShiftRightResult l r = .ok v) : GoValue.locSup v = 0 := by
  unfold intShiftRightResult at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, _, h⟩ := h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨c, hc, rfl⟩ := h
  rfl

/-! ## `applyStrictOp` preserves well-formedness -/

/-- The state-unchanged conclusion shape shared by every non-allocating
strict-op arm. -/
theorem strictWfSame {σ : ExecState} {v : GoValue} (hw : StateWf σ)
    (hv : GoValue.locSup v ≤ σ.nextAddr) :
    StateWf σ ∧ σ.nextAddr ≤ σ.nextAddr ∧ σ.functions = σ.functions
      ∧ σ.types = σ.types ∧ σ.methods = σ.methods
      ∧ GoValue.locSup v ≤ σ.nextAddr :=
  ⟨hw, Nat.le_refl _, rfl, rfl, rfl, hv⟩

theorem zip_snd_sup_le {keys : List Int} {vs : List GoValue} :
    supBy (fun p => GoValue.locSup p.2) ((keys.zip vs).toArray.toList)
      ≤ goValueListSup vs := by
  rw [goValueListSup_eq]
  refine supBy_le_iff.mpr fun p hp => ?_
  have hp' : p ∈ keys.zip vs := by simpa using hp
  exact supBy_mem (List.of_mem_zip hp').2

set_option maxHeartbeats 1600000 in
theorem applyStrictOp_wf {σ : ExecState} {op : StrictOp} {vs : List GoValue}
    {v : GoValue} {σ' : ExecState}
    (hw : StateWf σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStrictOp σ op vs = .ok (v, σ')) :
    StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.functions = σ.functions
      ∧ σ'.types = σ.types ∧ σ'.methods = σ.methods
      ∧ GoValue.locSup v ≤ σ'.nextAddr := by
  have hheap := hw.heap_le
  rw [applyStrictOp.eq_def] at h
  split at h
  · -- add
    split at h
    · -- int + int
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
    · -- float + float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · -- string + string
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- sub
    split at h
    · -- float - float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- mul
    split at h
    · -- float * float
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨iv, hiv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- div
    split at h
    · -- float / float (dispatches BEFORE the int zero check; never panics)
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨fv, hfv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [floatBinaryResult_locSup hfv]; omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨d, hd, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, iv, hiv, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- mod
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨d, hd, h⟩ := h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, iv, hiv, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [intBinaryResult_locSup hiv]; omega)
  · -- shiftLeft
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intShiftLeftResult_locSup hiv]; omega)
  · -- shiftRight
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intShiftRightResult_locSup hiv]; omega)
  · -- bitAnd
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitOr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitXor
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitwiseBinaryResult_locSup hiv]; omega)
  · -- bitClear
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitClearResult_locSup hiv]; omega)
  · -- bitNeg
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [intBitNegResult_locSup hiv]; omega)
  · -- neg (value-directed unary minus): int/float scalars out
    split at h <;>
      first
      | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h;
         obtain ⟨rfl, rfl⟩ := h;
         exact strictWfSame hw (by simp [GoValue.locSup]))
      | simp [Bind.bind, Except.bind] at h
  · -- floatLit (nullary; the rational kernel's scalar out)
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
  · -- not
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- eqCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- neqCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- atMostCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- atLeastCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- lessCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- greaterCmp
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- convert
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨cv, hcv, rfl, rfl⟩ := h
    have := convertValueToTy_locSup hcv
    simp only [goValueListSup] at hvs
    exact strictWfSame hw (by omega)
  · -- bytesFromString: the ONE allocating arm
    split at h
    · rename_i bytes
      try dsimp only at h
      cases halloc : σ.alloc
          (GoValue.array (bytes.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) IntKind.uint8))
          (some (Ty.array (bytes.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) IntKind.uint8).size
            (Ty.int IntKind.uint8))) with
      | mk base σa =>
        rw [halloc] at h
        dsimp only at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hvb : GoValue.locSup (.array (bytes.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) IntKind.uint8)) ≤ σ.nextAddr := by
          simp only [GoValue.locSup, goValueListSup_eq]
          refine Nat.le_trans (supBy_le_iff.mpr fun x hx => ?_) (Nat.zero_le _)
          rw [Array.toList_map] at hx
          obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
          exact Nat.le_refl _
        obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw hvb halloc
        obtain ⟨d1, d2, d3, d4, d5, d6⟩ := alloc_shape halloc
        refine ⟨w1, by omega, w4, d3, d5, ?_⟩
        show Loc.locSup base ≤ σa.nextAddr
        omega
    · simp at h
  · -- stringFromByteSlice
    try dsimp only at h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sl, hsl, vals, hvals, r, hr, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- stringFromRune
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, rfl, rfl⟩ := h
    exact strictWfSame hw (by simp [GoValue.locSup])
  · -- deref
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, lv, hlv, rfl, rfl⟩ := h
    have := loadLoc_locSup hlv
    exact strictWfSame hw (by omega)
  · -- fieldGet
    split at h
    · -- struct value
      split at h
      · -- field found
        rename_i fv hfv
        dsimp only at h
        split at h
        · simp [Bind.bind, Except.bind] at h
        · simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := StructFields.lookup_locSup hfv
          simp only [goValueListSup, GoValue.locSup] at hvs
          exact strictWfSame hw (by omega)
      · -- unknown field: stuck on both ite branches
        dsimp only at h
        split at h <;> simp [Bind.bind, Except.bind] at h
    · simp at h
  · -- fieldAddr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl⟩ := h
    have := valueAsLoc_locSup hl
    simp only [goValueListSup] at hvs
    refine strictWfSame hw ?_
    show Loc.locSup l ≤ σ.nextAddr
    omega
  · -- structLit
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨sv, hsv, rfl, rfl⟩ := h
    have := buildStructValue_locSup hsv
    refine strictWfSame hw ?_
    have h2 : goValueListSup vs.toArray.toList = goValueListSup vs := by simp
    omega
  · -- arrayLit
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, av, hav, rfl, rfl⟩ := h
      have := buildArrayValue_locSup hav
      exact strictWfSame hw (Nat.le_trans this (Nat.le_trans zip_snd_sup_le hvs))
  · -- toInterface
    rename_i tgt dynm v0
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨dynTy, hdt, h⟩ := h
    simp only [goValueListSup] at hvs
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by omega)
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
      obtain ⟨rfl, rfl⟩ := h
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by omega)
    · exfalso
      revert h
      split <;> intro h
      · simp only [bind_eq_ok] at h
        obtain ⟨m, hm, hc⟩ := h
        simp [GoCore.panic, throw, throwThe, MonadExceptOf.throw] at hc
      · simp_all [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · -- indexGet
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨iv, hiv, h⟩ := h
    simp only [goValueListSup] at hvs
    split at h
    · rename_i values
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨gv, hgv, rfl, rfl⟩ := h
      have hb := arrayGet_locSup hgv
      have h3 : GoValue.locSup (GoValue.array values)
          = goValueListSup values.toList := rfl
      exact strictWfSame hw (by omega)
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨gv, hgv, rfl, rfl⟩ := h
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
      obtain ⟨l, hl, lv, hlv, rfl, rfl⟩ := h
      have := loadLoc_locSup hlv
      have h2 := sliceIndexLoc_locSup hl
      exact strictWfSame hw (by omega)
    · simp at h
  · -- indexAddr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨l, hl, rfl, rfl⟩ := h
    simp only [goValueListSup] at hvs
    have h2 := indexTargetLoc_locSup hl
    refine strictWfSame hw ?_
    show Loc.locSup l ≤ σ.nextAddr
    omega
  · -- mapGet
    simp only [bind_eq_ok] at h
    obtain ⟨m, hm, key, hkey, h⟩ := h
    split at h
    · -- nil map
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, d, hd, rfl, rfl⟩ := h
      exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
    · rename_i baseLoc
      simp only [bind_eq_ok] at h
      obtain ⟨bv, hbv, h⟩ := h
      split at h
      · rename_i entries
        simp only [bind_eq_ok] at h
        obtain ⟨idx, hidx, h⟩ := h
        split at h
        · split at h
          · rename_i k' v' hp
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hmem : (k', v') ∈ entries.toList :=
              List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hp)
            have h2 := loadLoc_locSup hbv
            have h3 := goValueEntriesSup_mem hmem
            simp only [GoValue.locSup] at h2
            simp only at h3
            exact strictWfSame hw (by omega)
          · simp at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨d, hd, rfl, rfl⟩ := h
          exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · simp [Bind.bind, Except.bind] at h
  · -- sliceExpr false
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨lo, hlo, hi, hhi, h⟩ := h
    cases hsl : applySlice σ _ lo hi none with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sv, σs⟩ := p
      rw [hsl] at h
      simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hb⟩ := applySlice_locSup hsl
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by omega)
  · -- sliceExpr true
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨lo, hlo, hi, hhi, mx, hmx, h⟩ := h
    cases hsl : applySlice σ _ lo hi (some mx) with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok p =>
      obtain ⟨sv, σs⟩ := p
      rw [hsl] at h
      simp only [Bind.bind, Except.bind, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hb⟩ := applySlice_locSup hsl
      simp only [goValueListSup] at hvs
      exact strictWfSame hw (by omega)
  · -- lengthOf
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨bv, hbv, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [SeqRight.seqRight, Seq.seq, Function.const, Bind.bind,
          Except.bind, Functor.map, Except.map] at h
        split at h
        · simp at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨bv, hbv, h⟩ := h
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact strictWfSame hw (by simp [GoValue.locSup])
          · simp at h
      · -- chan: len(ch) — nil → 0; else the cell's buffer size
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨bv, hbv, h⟩ := h
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact strictWfSame hw (by simp [GoValue.locSup])
          · simp at h
      · simp at h
  · -- capacityOf
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨bv, hbv, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp at h
      · simp only [SeqRight.seqRight, Seq.seq, Function.const, Bind.bind,
          Except.bind, Functor.map, Except.map] at h
        split at h
        · simp at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
      · -- chan: cap(ch) — nil → 0; else the cell's capacity
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact strictWfSame hw (by simp [GoValue.locSup])
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨bv, hbv, h⟩ := h
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact strictWfSame hw (by simp [GoValue.locSup])
          · simp at h
      · simp at h
  · -- funcValOf
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine strictWfSame hw ?_
    show goValueListSup vs ≤ σ.nextAddr
    omega
  · -- minOf
    rename_i v₀ rest
    -- the float guard (floats slice F2): the refusing branch is never
    -- ok; the passing branch is the pre-float fold verbatim
    replace h := guard_ite_eq_ok (fun y => by simp [unsupported]) h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨best, hbest, rfl, rfl⟩ := h
    simp only [goValueListSup] at hvs
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
    -- the float guard (floats slice F2): the refusing branch is never
    -- ok; the passing branch is the pre-float fold verbatim
    replace h := guard_ite_eq_ok (fun y => by simp [unsupported]) h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨best, hbest, rfl, rfl⟩ := h
    simp only [goValueListSup] at hvs
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
      · obtain ⟨_, _, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- runeSizeAt
    split at h
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨off, hoff, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · obtain ⟨_, _, rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
    · simp at h
  · -- defaultValueOf
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
  · -- nilLit
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact strictWfSame hw (by simp [GoValue.locSup])
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · -- chan: typed nil literal → the nil-channel default value
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨d, hd, rfl, rfl⟩ := h
        exact strictWfSame hw (by rw [defaultValue_locSup hd]; omega)
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact strictWfSame hw (by simp [GoValue.locSup])
      · simp at h
      · simp at h
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

/-- The conclusion shape of the wide-op preservation lemmas. -/
def StmtOpPres (σ σ' : ExecState) : Prop :=
  StateWf σ' ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.functions = σ.functions
    ∧ σ'.types = σ.types ∧ σ'.methods = σ.methods

theorem stmtOpPres_refl {σ : ExecState} (hw : StateWf σ) : StmtOpPres σ σ :=
  ⟨hw, Nat.le_refl _, rfl, rfl, rfl⟩

theorem storeLoc_pres {σ : ExecState} {l : Loc} {v : GoValue} {σ' : ExecState}
    (hw : StateWf σ) (hl : Loc.locSup l ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr) (h : storeLoc σ l v = .ok σ') :
    StmtOpPres σ σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := storeLoc_shape h
  have hh := hw.heap_le
  have hf := hw.funcs_le
  exact ⟨StateWf.mk' (by omega) (by rw [h4, h2]; exact hf), by omega, h2, h1, h3⟩

theorem StmtOpPres.trans {σ₁ σ₂ σ₃ : ExecState} (a : StmtOpPres σ₁ σ₂)
    (b : StmtOpPres σ₂ σ₃) : StmtOpPres σ₁ σ₃ := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  exact ⟨b1, by omega, by rw [b3, a3], by rw [b4, a4], by rw [b5, a5]⟩

theorem storeMany_pres {σ : ExecState} {locs : List Loc} {vs : List GoValue}
    {σ' : ExecState} (hw : StateWf σ) (hl : locListSup locs ≤ σ.nextAddr)
    (hv : goValueListSup vs ≤ σ.nextAddr) (h : storeMany σ locs vs = .ok σ') :
    StmtOpPres σ σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := storeMany_shape h
  have hh := hw.heap_le
  have hf := hw.funcs_le
  exact ⟨StateWf.mk' (by omega) (by rw [h4, h2]; exact hf), by omega, h2, h1, h3⟩


set_option maxHeartbeats 1600000 in
/-- `mapAssignValue` preserves the loc invariant (verbatim the old
`mapAssign` wide-op case; shared with `storeTarget`'s map-element arm,
convergence round BUG-030). -/
theorem mapAssignValue_pres {σ : ExecState} {keyTy valueTy : Ty}
    {baseV keyV valueV : GoValue} {σ' : ExecState}
    (hw : StateWf σ)
    (hb : GoValue.locSup baseV ≤ σ.nextAddr)
    (hk : GoValue.locSup keyV ≤ σ.nextAddr)
    (hv : GoValue.locSup valueV ≤ σ.nextAddr)
    (h : mapAssignValue σ keyTy valueTy baseV keyV valueV = .ok σ') :
    StmtOpPres σ σ' := by
  have hheap := hw.heap_le
  unfold mapAssignValue at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨m, hm, key, hkey, value, hvalue, h⟩ := h
  have hkb : GoValue.locSup key ≤ σ.nextAddr := by
    have := normalizeValueForTy_locSup hkey
    omega
  have hvb : GoValue.locSup value ≤ σ.nextAddr := by
    have := normalizeValueForTy_locSup hvalue
    omega
  obtain ⟨entriesOut, hentries, h⟩ := h
  split at h
  · simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rename_i baseLoc entries
    obtain ⟨hbl, hent⟩ := mapEntries_locSup hentries rfl
    have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
      have := valueAsMap_locSup hm
      omega
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨idx, hidx, h⟩ := h
    split at h
    · rename_i i
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨y, hy, h⟩ := h
      subst hy
      refine storeLoc_pres hw hblb ?_ h
      show goValueEntriesSup (entries.set! i (key, value)).toList ≤ σ.nextAddr
      refine Nat.le_trans goValueEntriesSup_set! ?_
      simp only at *
      omega
    · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨y, hy, h⟩ := h
      subst hy
      refine storeLoc_pres hw hblb ?_ h
      show goValueEntriesSup (entries.push (key, value)).toList ≤ σ.nextAddr
      rw [goValueEntriesSup_push]
      simp only at *
      omega

/-- `resolveChain` output bound (round 4, BUG-033): the replayed
chain's cursor value stays bounded by the inputs and the heap (index
steps may read cells). The chain never allocates. -/
theorem resolveChain_locSup {σ : ExecState} :
    ∀ {steps : List TargetStep} {cur : GoValue} {idxs : List GoValue}
      {out : GoValue}, resolveChain σ cur steps idxs = .ok out →
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
        simp only [bind_eq_ok] at h
        obtain ⟨l, hl, h⟩ := h
        have h2 := indexTargetLoc_locSup hl
        have h3 := ih h
        have h4 : GoValue.locSup (GoValue.addr l) = Loc.locSup l := rfl
        simp only [goValueListSup] at *
        omega
    | field tid f =>
      simp only [bind_eq_ok] at h
      obtain ⟨l, hl, h⟩ := h
      have h2 := valueAsLoc_locSup hl
      have h3 := ih h
      have h4 : GoValue.locSup (GoValue.addr (Loc.field l tid f))
          = Loc.locSup l := rfl
      omega

/-- `storeTarget` preservation (convergence round, BUG-029; chain form
round 4, BUG-033): one phase-2 store keeps the loc invariant. -/
theorem storeTarget_pres {σ : ExecState} {r : TargetRef} {v : GoValue}
    {σ' : ExecState}
    (hw : StateWf σ) (hr : TargetRef.locSup r ≤ σ.nextAddr)
    (hv : GoValue.locSup v ≤ σ.nextAddr)
    (h : storeTarget σ r v = .ok σ') :
    StmtOpPres σ σ' := by
  have hheap := hw.heap_le
  unfold storeTarget at h
  cases r with
  | chain anchor idxs steps =>
    simp only [bind_eq_ok] at h
    obtain ⟨cur, hres, l, hl, h⟩ := h
    have h2 := resolveChain_locSup hres
    have h3 := valueAsLoc_locSup hl
    simp only [TargetRef.locSup, Nat.max_le] at hr
    exact storeLoc_pres hw (by omega) hv h
  | mapElem b k kt vt =>
    simp only [TargetRef.locSup, Nat.max_le] at hr
    exact mapAssignValue_pres hw hr.1 hr.2 hv h

theorem applyStmtOpCore_wf {σ : ExecState} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {σ' : ExecState}
    (hw : StateWf σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOpCore σ op nt vs = .ok σ') :
    StmtOpPres σ σ' := by
  have hheap := hw.heap_le
  rw [applyStmtOpCore.eq_def] at h
  split at h
  · -- newValue
    rename_i typ
    split at h
    · rename_i tv value
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨loc, hloc, σ₂, h, hσ⟩ := h
      subst hσ
      have hlocb := valueAsLoc_locSup hloc
      cases halloc : σ.alloc value typ with
      | mk nloc σa =>
        rw [halloc] at h
        dsimp only at h
        obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw (by omega) halloc
        obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
        refine storeLoc_pres w1 (by omega) ?_ h
        show Loc.locSup nloc ≤ σa.nextAddr
        exact w2
    · simp at h
  · -- makeSlice
    rename_i elem hasCap
    split at h
    all_goals try (simp [Bind.bind, Except.bind] at h; done)
    · -- no explicit cap
      rename_i tv lenV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨lenValue, hlenV, len, hlen, cap, hcap, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨backing, hbacking, loc, hloc, σ₂, h, hσ⟩ := h
        subst hσ
        have hb0 := buildDefaultArrayValue_locSup hbacking
        have hlocb := valueAsLoc_locSup hloc
        cases halloc : σ.alloc backing (some (Ty.array cap elem)) with
        | mk base σa =>
          rw [halloc] at h
          dsimp only at h
          obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw (by omega) halloc
          obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
          refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
          refine storeLoc_pres w1 (by omega) ?_ h
          show optLocSup (some base) ≤ σa.nextAddr
          exact w2
    · -- explicit cap
      rename_i tv lenV capV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨lenValue, hlenV, capValue, hcapV, len, hlen, cap, hcap, h⟩ := h
      split at h
      · simp [Bind.bind, Except.bind] at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨backing, hbacking, loc, hloc, σ₂, h, hσ⟩ := h
        subst hσ
        have hb0 := buildDefaultArrayValue_locSup hbacking
        have hlocb := valueAsLoc_locSup hloc
        cases halloc : σ.alloc backing (some (Ty.array cap elem)) with
        | mk base σa =>
          rw [halloc] at h
          dsimp only at h
          obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw (by omega) halloc
          obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
          refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
          refine storeLoc_pres w1 (by omega) ?_ h
          show optLocSup (some base) ≤ σa.nextAddr
          exact w2
  · -- makeMap
    rename_i hasSpace
    split at h
    rename_i p base s₁ halloc
    split at h
    all_goals try (simp [Bind.bind, Except.bind] at h; done)
    · -- no space hint
      rename_i tv
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨loc, hloc, σ₂, h, hσ⟩ := h
      subst hσ
      have hlocb := valueAsLoc_locSup hloc
      obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw
        (by simp [GoValue.locSup, goValueEntriesSup]) halloc
      obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
      refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
      refine storeLoc_pres w1 (by omega) ?_ h
      show optLocSup (some base) ≤ s₁.nextAddr
      exact w2
    · -- with space hint
      rename_i tv spaceV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨sz, hsz, _, _, loc, hloc, σ₂, h, hσ⟩ := h
      subst hσ
      have hlocb := valueAsLoc_locSup hloc
      obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw
        (by simp [GoValue.locSup, goValueEntriesSup]) halloc
      obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
      refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
      refine storeLoc_pres w1 (by omega) ?_ h
      show optLocSup (some base) ≤ s₁.nextAddr
      exact w2
  · -- makeChan
    rename_i hasCap
    split at h
    · -- no cap: capacity 0
      rename_i tv
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨loc, hloc, σ₂, h, hσ⟩ := h
      subst hσ
      have hlocb := valueAsLoc_locSup hloc
      cases halloc : σ.alloc (.chanData #[] 0 false) with
      | mk base σa =>
        rw [halloc] at h
        dsimp only at h
        obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw
          (by simp [GoValue.locSup, goValueListSup]) halloc
        obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
        refine storeLoc_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
    · -- explicit cap
      rename_i tv capV
      simp only [goValueListSup] at hvs
      simp only [pure_bind] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨size, hsize, capacity, hcapacity, loc, hloc, σ₂, h, hσ⟩ := h
      subst hσ
      have hlocb := valueAsLoc_locSup hloc
      cases halloc : σ.alloc (.chanData #[] capacity false) with
      | mk base σa =>
        rw [halloc] at h
        dsimp only at h
        obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw
          (by simp [GoValue.locSup, goValueListSup]) halloc
        obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
        refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
        refine storeLoc_pres w1 (by omega) ?_ h
        show optLocSup (some base) ≤ σa.nextAddr
        exact w2
    · simp [Bind.bind, Except.bind] at h
  · -- mapAssign
    rename_i keyTy valueTy
    split at h
    · rename_i baseV keyV valueV
      simp only [goValueListSup] at hvs
      exact mapAssignValue_pres hw (by omega) (by omega) (by omega) h
    · simp at h
  · -- mapLookup
    rename_i keyTy valueTy
    split at h
    · rename_i tv okv baseV keyV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨m, hm, key, hkey, ⟨rv, rb⟩, hpair, tloc, htloc, okloc, hokloc,
        σ₁, hσ₁, σ₂, h, hσ⟩ := h
      subst hσ
      dsimp only at hσ₁ h
      have hrb := mapLookupValue_locSup hpair
      have p1 := storeLoc_pres hw
        (by have := valueAsLoc_locSup htloc; omega)
        (by omega) hσ₁
      obtain ⟨q1, q2, q3, q4, q5⟩ := p1
      refine StmtOpPres.trans ⟨q1, q2, q3, q4, q5⟩ ?_
      refine storeLoc_pres q1 ?_ (by simp [GoValue.locSup]) h
      have := valueAsLoc_locSup hokloc
      omega
    · simp at h
  · -- typeAssertStmt
    rename_i targetTy
    split at h
    · rename_i tv okv value
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨⟨rv, rb⟩, hres, tloc, htloc, okloc, hokloc, σ₁, hσ₁, σ₂, h, hσ⟩ := h
      subst hσ
      dsimp only at hσ₁ h
      have hrb := typeAssertValue_locSup hres
      have p1 := storeLoc_pres hw
        (by have := valueAsLoc_locSup htloc; omega)
        (by omega) hσ₁
      obtain ⟨q1, q2, q3, q4, q5⟩ := p1
      refine StmtOpPres.trans ⟨q1, q2, q3, q4, q5⟩ ?_
      refine storeLoc_pres q1 ?_ (by simp [GoValue.locSup]) h
      have := valueAsLoc_locSup hokloc
      omega
    · simp at h
  · -- mapDelete
    rename_i keyTy
    split at h
    · rename_i baseV keyV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨m, hm, key, hkey, es, hes, h⟩ := h
      split at h
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨_, _, h⟩ := h
        subst h
        exact stmtOpPres_refl hw
      · rename_i baseLoc entries
        obtain ⟨hbl, hent⟩ := mapEntries_locSup hes rfl
        have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
          have := valueAsMap_locSup hm
          omega
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨idx, hidx, h⟩ := h
        split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨σ₂, h, hσ⟩ := h
          subst hσ
          refine storeLoc_pres hw hblb ?_ h
          show goValueEntriesSup _ ≤ σ.nextAddr
          refine Nat.le_trans goValueEntriesSup_eraseIdx! ?_
          omega
        · simp only [pure_eq_ok, Except.ok.injEq] at h
          subst h
          exact stmtOpPres_refl hw
    · simp at h
  · -- clearMap
    split at h
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨m, hm, es, hes, h⟩ := h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        exact stmtOpPres_refl hw
      · rename_i baseLoc entries
        obtain ⟨hbl, hent⟩ := mapEntries_locSup hes rfl
        have hblb : Loc.locSup baseLoc ≤ σ.nextAddr := by
          have := valueAsMap_locSup hm
          omega
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨σ₂, h, hσ⟩ := h
        subst hσ
        refine storeLoc_pres hw hblb ?_ h
        show goValueEntriesSup (#[] : Array (GoValue × GoValue)).toList ≤ σ.nextAddr
        simp [goValueEntriesSup]
    · simp at h
  · -- clearSlice
    rename_i elem
    split at h
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨sl, hsl, _, _, zero, hzero, cur, hloop, h⟩ := h
      subst h
      have hz := defaultValue_locSup hzero
      have hslb : optLocSup sl.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hsl
        omega
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop
      refine forIn_list_inv (P := fun cur => StmtOpPres σ cur)
        ?_ (stmtOpPres_refl hw) hloop
      intro a _ b rr hbb hr
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨l, hl, c, hc, _, _, hrr⟩ := hr
      subst hrr
      simp only [forInStepVal]
      refine StmtOpPres.trans hbb ?_
      obtain ⟨b1, b2, b3, b4, b5⟩ := hbb
      refine storeLoc_pres b1 ?_ (by omega) hc
      have := sliceIndexLoc_locSup hl
      omega
    · simp at h
  · -- sortSlice
    rename_i elem
    split at h
    · rename_i baseV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨sl, hsl, _, _, loaded, hloop1, h⟩ := h
      have hslb : optLocSup sl.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hsl
        omega
      obtain ⟨cur, hloop2, h⟩ := h
      subst h
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop2
      refine forIn_list_inv (P := fun cur => StmtOpPres σ cur)
        ?_ (stmtOpPres_refl hw) hloop2
      intro a _ b rr hbb hr
      split at hr
      all_goals try (simp [Bind.bind, Except.bind] at hr; done)
      all_goals
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
        obtain ⟨l, hl, c, hc, _, _, hrr⟩ := hr
        subst hrr
        simp only [forInStepVal]
        refine StmtOpPres.trans hbb ?_
        obtain ⟨b1, b2, b3, b4, b5⟩ := hbb
        refine storeLoc_pres b1 ?_ (by simp [GoValue.locSup]) hc
        have := sliceIndexLoc_locSup hl
        omega
    · simp at h
  · -- copySlice
    split at h
    · rename_i tv dstV srcV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨dst, hdst, src, hsrc, _, _, _, _, values, hload, h⟩ := h
      have hdstb : optLocSup dst.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hdst
        omega
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hload
      have hvalsb : goValueListSup values.toList ≤ σ.nextAddr := by
        refine forIn_list_inv (P := fun vals : Array GoValue =>
          goValueListSup vals.toList ≤ σ.nextAddr) ?_ (Nat.zero_le _) hload
        intro a _ b rr hbb hr
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
        obtain ⟨l, hl, lv, hlv, _, _, hrr⟩ := hr
        subst hrr
        simp only [forInStepVal, goValueListSup_push]
        have := loadLoc_locSup hlv
        omega
      obtain ⟨st, hloop, h⟩ := h
      have hpres : StmtOpPres σ st.1 := by
        rw [← Array.forIn_toList] at hloop
        refine forIn_list_inv
          (P := fun st : MProd ExecState Nat => StmtOpPres σ st.1)
          ?_ (stmtOpPres_refl hw) hloop
        intro a ha b rr hbb hr
        have hab : GoValue.locSup a ≤ σ.nextAddr := by
          have : GoValue.locSup a ≤ goValueListSup values.toList := by
            rw [goValueListSup_eq]
            exact supBy_mem ha
          omega
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
        obtain ⟨l, hl, c, hc, _, _, hrr⟩ := hr
        subst hrr
        simp only [forInStepVal]
        refine StmtOpPres.trans hbb ?_
        obtain ⟨b1, b2, b3, b4, b5⟩ := hbb
        refine storeLoc_pres b1 ?_ (by omega) hc
        have := sliceIndexLoc_locSup hl
        omega
      obtain ⟨tloc, htloc, σ₂, h, hσ⟩ := h
      subst hσ
      refine StmtOpPres.trans hpres ?_
      obtain ⟨b1, b2, b3, b4, b5⟩ := hpres
      refine storeLoc_pres b1 ?_ (by simp [GoValue.locSup]) h
      have := valueAsLoc_locSup htloc
      omega
    · simp at h
  · -- appendSlice: dispatches through applyStmtOp
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    cases h

set_option maxHeartbeats 1600000 in
theorem applyStmtOp_wf {σ : ExecState} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {σ' : ExecState} {ch' : Choices}
    (hw : StateWf σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOp σ ch op nt vs = .ok (σ', ch')) :
    StmtOpPres σ σ' := by
  have hheap := hw.heap_le
  rw [applyStmtOp.eq_def] at h
  split at h
  · -- appendSlice
    rename_i elem
    split at h
    · rename_i tv sliceV elemsV
      simp only [goValueListSup] at hvs
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨slice, hslice, elems, helems, _, _, _, _, elemValues, helemValues,
        tloc, htloc, h⟩ := h
      have hsliceb : optLocSup slice.base ≤ σ.nextAddr := by
        have := valueAsSlice_locSup hslice
        omega
      have hvalsb : goValueListSup elemValues.toList ≤ σ.nextAddr := by
        have := sliceVisibleValues_locSup helemValues
        omega
      have htlocb : Loc.locSup tloc ≤ σ.nextAddr := by
        have := valueAsLoc_locSup htloc
        omega
      split at h
      · -- in-place path
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨st, hloop, σ₂, h, hσ, hch⟩ := h
        subst hσ
        have hpres : StmtOpPres σ st.1 := by
          rw [← Array.forIn_toList] at hloop
          refine forIn_list_inv
            (P := fun st : MProd ExecState Nat => StmtOpPres σ st.1)
            ?_ (stmtOpPres_refl hw) hloop
          intro a ha b rr hbb hr
          have hab : GoValue.locSup a ≤ σ.nextAddr := by
            have : GoValue.locSup a ≤ goValueListSup elemValues.toList := by
              rw [goValueListSup_eq]
              exact supBy_mem ha
            omega
          split at hr
          · rename_i base hbase
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
            obtain ⟨c, hc, _, _, hrr⟩ := hr
            subst hrr
            simp only [forInStepVal]
            refine StmtOpPres.trans hbb ?_
            obtain ⟨b1, b2, b3, b4, b5⟩ := hbb
            refine storeLoc_pres b1 ?_ (by omega) hc
            have hob : optLocSup slice.base = Loc.locSup base := by rw [hbase]; rfl
            show Loc.locSup (Loc.index base _) ≤ b.1.nextAddr
            simp only [Loc.locSup, Loc.rootBase] at *
            omega
          · simp [Bind.bind, Except.bind] at hr
        refine StmtOpPres.trans hpres ?_
        obtain ⟨b1, b2, b3, b4, b5⟩ := hpres
        refine storeLoc_pres b1 ?_ ?_ h
        · omega
        · show optLocSup slice.base ≤ st.1.nextAddr
          omega
      · -- spill path
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨oldValues, holdValues, backing, hbacking, σ₂, h, hσ, hch⟩ := h
        subst hσ
        have holdb : goValueListSup oldValues.toList ≤ σ.nextAddr := by
          have := sliceVisibleValues_locSup holdValues
          omega
        have hbb := buildAppendBackingValue_locSup hbacking
        cases halloc : σ.alloc backing
            (some (Ty.array (slice.len + elemValues.size +
              ((appendGrowthCap slice.cap (slice.len + elemValues.size)
                  - (slice.len + elemValues.size)
                  + (ch.consume (appendSpillWidth slice.cap
                      (slice.len + elemValues.size))).fst)
                % appendSpillWidth slice.cap (slice.len + elemValues.size)))
              elem)) with
        | mk base σa =>
          rw [halloc] at h
          dsimp only at h
          obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hw (by omega) halloc
          obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
          refine StmtOpPres.trans ⟨w1, by omega, w4, d3, d5⟩ ?_
          refine storeLoc_pres w1 (by omega) ?_ h
          show optLocSup (some base) ≤ σa.nextAddr
          exact w2
    · simp at h
  · -- every other arm dispatches to applyStmtOpCore
    rename_i op' hne
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨σ₂, hcore, hσ, hch⟩ := h
    subst hσ
    exact applyStmtOpCore_wf hw hvs hcore


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

theorem assigneesExprs_locSup :
    ∀ {targets : List Assignee} {es : List Expr},
      assigneesExprs targets = some es →
      exprListSup es ≤ assigneeListSup targets := by
  intro targets
  induction targets with
  | nil =>
    intro es h
    simp only [assigneesExprs, List.mapM_nil, Option.pure_def,
      Option.some.injEq] at h
    subst h
    simp [exprListSup]
  | cons a rest ih =>
    intro es h
    rw [assigneesExprs, List.mapM_cons] at h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, htail, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    have h1 := assigneeExpr_locSup he
    have h2 := ih (show assigneesExprs rest = some tail from htail)
    simp only [exprListSup, assigneeListSup]
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
  case newValue target value typ =>
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
  case mapLookup target okT b i kt vt =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨oke, hoke, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    have h2 := assigneeExpr_locSup hoke
    simp only [Stmt.locSup, exprListSup, Nat.max_le]
    omega
  case typeAssert target okT e' tt =>
    simp only [stmtPlan] at h
    obtain ⟨te, hte, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨oke, hoke, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    have h1 := assigneeExpr_locSup hte
    have h2 := assigneeExpr_locSup hoke
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
  cases k <;>
    simp [seqCont, Cont.locSup, stmtListSup_append, Nat.max_le] <;>
    first
      | omega
      | (split <;> simp [Cont.locSup, stmtListSup_append, Nat.max_le] <;> omega)

theorem pushDefer_locSup {d : GoValue × List GoValue} :
    ∀ {k k' : Cont}, pushDefer d k = some k' →
      Cont.locSup k'
        ≤ max (max (GoValue.locSup d.1) (goValueListSup d.2)) (Cont.locSup k) := by
  intro k
  induction k <;> intro k' h <;>
    simp only [pushDefer, Option.map_eq_some_iff, Option.some.injEq] at h
  case frame targets results defers k _ =>
    subst h
    simp only [Cont.locSup, deferListSup, Nat.max_le]
    omega
  all_goals
    first
    | (obtain ⟨k₂, hk₂, rfl⟩ := h
       rename_i ih
       have := ih hk₂
       simp only [Cont.locSup, Nat.max_le] at *
       omega)
    | cases h

theorem panicPassthrough_locSup {k k' : Cont}
    (h : panicPassthrough k = some k') : Cont.locSup k' ≤ Cont.locSup k := by
  cases k <;> simp_all [panicPassthrough] <;> subst h <;>
    simp [Cont.locSup, Nat.max_le] <;> omega

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

set_option maxHeartbeats 1600000 in
/-- Companion to `recoverResult_locSup` for the below-the-frame walk
(wrapper transparency, arc-final audit F1). -/
theorem recoverThroughWrappers_locSup :
    ∀ {k : Cont} {v : GoValue} {k' : Cont}, recoverThroughWrappers k = some (v, k') →
      GoValue.locSup v ≤ Cont.locSup k ∧ Cont.locSup k' ≤ Cont.locSup k := by
  intro k
  induction k <;> intro v k' h
  case stop => simp [recoverThroughWrappers] at h
  case panicResumeK chain k _ =>
    simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
    obtain ⟨⟨v₀, chain'⟩, hmark, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨m1, m2⟩ := markNewestRecovered_locSup hmark
    constructor <;> (simp only [Cont.locSup, Nat.max_le] at m1 m2 ⊢; omega)
  case frame targets results defers k w ih =>
    cases w
    · simp [recoverThroughWrappers] at h
    · simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
      obtain ⟨⟨v₀, k₀⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨i1, i2⟩ := ih hin
      constructor <;> (simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢; omega)
  all_goals
    rename_i ih
    simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
    obtain ⟨⟨v₀, k₀⟩, hin, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨i1, i2⟩ := ih hin
    constructor
    · simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢
      omega
    · simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢
      first
        | omega
        | (constructor <;> omega)

set_option maxHeartbeats 1600000 in
theorem recoverResult_locSup :
    ∀ {k : Cont} {v : GoValue} {k' : Cont}, recoverResult k = (v, k') →
      GoValue.locSup v ≤ Cont.locSup k ∧ Cont.locSup k' ≤ Cont.locSup k := by
  intro k
  induction k <;> intro v k' h
  case stop =>
    simp only [recoverResult, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  case panicResumeK chain k _ =>
    simp only [recoverResult, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [GoValue.locSup]
  case frame targets results defers k w ih =>
    cases w
    · -- non-wrapper frame: the below-frame walk decides
      simp only [recoverResult] at h
      cases hin : recoverThroughWrappers k with
      | none =>
          rw [hin] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [GoValue.locSup]
      | some p =>
          obtain ⟨v₀, k₀⟩ := p
          rw [hin] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨m1, m2⟩ := recoverThroughWrappers_locSup hin
          constructor <;> (simp only [Cont.locSup, Nat.max_le] at m1 m2 ⊢; omega)
    · -- wrapper frame above the walk start: transparent
      simp only [recoverResult] at h
      cases hrk : recoverResult k with
      | mk v₀ k₀ =>
          rw [hrk] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨i1, i2⟩ := ih hrk
          constructor <;> (simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢; omega)
  all_goals
    rename_i ih
    obtain ⟨i1, i2⟩ := ih (v := _) (k' := _) rfl
    have hv := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    simp only [recoverResult] at hv hk
    try dsimp only at hv hk
    subst hv
    subst hk
    constructor
    · simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢
      omega
    · simp only [Cont.locSup, Nat.max_le] at i1 i2 ⊢
      first
        | omega
        | (constructor <;> omega)


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

theorem goValueListSup_reverse {a : List GoValue} :
    goValueListSup a.reverse = goValueListSup a := by
  simp [goValueListSup_eq, supBy_reverse]

theorem goValueEntriesSup_eraseIdxA {arr : Array (GoValue × GoValue)} {i : Nat}
    {hlt : i < arr.size} :
    goValueEntriesSup ((arr.eraseIdx i hlt).toList) ≤ goValueEntriesSup arr.toList :=
  goValueEntriesSup_eraseIdx

theorem runtimeErrorValue_locSup {msg : String} :
    GoValue.locSup (runtimeErrorValue msg) = 0 := rfl

/-- `panicPayload` never introduces locations: the nil arm's runtime
error is loc-free, every other payload passes through (modern
`panic(nil)` semantics, arc-final audit F21 2026-08-06). -/
theorem panicPayload_locSup {v : GoValue} :
    GoValue.locSup (panicPayload v) ≤ GoValue.locSup v := by
  cases v <;> simp [panicPayload, runtimeErrorValue_locSup, GoValue.locSup]


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

theorem chanCell_locSup {σ : ExecState} {loc : Loc} {buf : Array GoValue}
    {capacity : Nat} {closed : Bool}
    (h : chanCell σ loc = .ok (buf, capacity, closed)) :
    goValueListSup buf.toList ≤ Heap.locSup σ.heap := by
  unfold chanCell at h
  simp only [bind_eq_ok] at h
  obtain ⟨v, hv, h⟩ := h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simpa [GoValue.locSup] using loadLoc_locSup hv
  · simp at h

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

theorem readyClauses_subset {σ : ExecState} :
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
theorem enterRecvTargets_wf {σ : ExecState} {targets : List Assignee}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c' : Config} {σ' : ExecState}
    (hw : StateWf σ)
    (ht : assigneeListSup targets ≤ σ.nextAddr)
    (hvals : goValueListSup vals ≤ σ.nextAddr)
    (hbody : Stmt.locSup body ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : enterRecvTargets σ targets vals body env k = .ok (c', σ')) :
    StateWf σ' ∧ Config.locSup c' ≤ σ'.nextAddr ∧ σ'.types = σ.types
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  unfold enterRecvTargets at h
  split at h
  · rename_i sh e ops rest hplan
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hw, ?_, rfl, Nat.le_refl _⟩
    have hplans := targetsPlan_locSup hplan
    simp only [targetPlansSup, exprListSup, Nat.max_le] at hplans
    simp only [Config.locSup, Cont.locSup, goValueListSup, exprListSup,
      targetRefListSup, targetPlansSup, Nat.max_le]
    omega
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `commitClause` preservation: state stays wf (allocator monotone,
types unchanged) and the successor configuration is bounded. -/
theorem commitClause_wf {σ : ExecState} {env : LocalEnv} {k : Cont}
    {cl : EvClause} {c' : Config} {σ' : ExecState}
    (hw : StateWf σ) (hcl : evClauseSup cl ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : commitClause σ env k cl = .ok (c', σ')) :
    StateWf σ' ∧ Config.locSup c' ≤ σ'.nextAddr ∧ σ'.types = σ.types
      ∧ σ.nextAddr ≤ σ'.nextAddr := by
  have hheap := hw.heap_le
  rw [commitClause.eq_def] at h
  split at h
  · -- sendEv
    rename_i chv vv elem body
    simp only [evClauseSup, Nat.max_le] at hcl
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i loc hbase
      simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hw, ?_, rfl, Nat.le_refl _⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
          Nat.max_le]
        omega
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨v', hv', σ₂, hst, h⟩ := h
          obtain ⟨rfl, rfl⟩ := h
          have hv'b : GoValue.locSup v' ≤ σ.nextAddr := by
            have := normalizeValueForTy_locSup hv'
            omega
          obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
            (by rw [show GoValue.locSup (.chanData (buf.push v') capacity closed)
                  = goValueListSup (buf.push v').toList from rfl,
                goValueListSup_push]
                omega) hst
          refine ⟨w1, ?_, w4, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · -- recvEv
    rename_i chv targets elem body
    simp only [evClauseSup, Nat.max_le] at hcl
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i loc hbase
      simp only [bind_eq_ok] at h
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
        obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
          (by rw [show GoValue.locSup (.chanData (buf.eraseIdx! 0) capacity closed)
                = goValueListSup (buf.eraseIdx! 0).toList from rfl]
              exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨w1, ?_, w4, w2⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · rename_i t ts
          obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf w1
            (by omega)
            (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
            (by omega) (by omega) (by omega) h
          exact ⟨q1, q2, q3.trans w4, Nat.le_trans w2 q4⟩
      · -- closed-and-drained or unready
        split at h
        · simp only [pure_bind, bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          have hzb : GoValue.locSup z ≤ σ.nextAddr := by
            rw [defaultValue_locSup hz]; omega
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hw, ?_, rfl, Nat.le_refl _⟩
            simp only [Config.locSup, Nat.max_le]
            omega
          · rename_i t ts
            obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf hw
              (by omega)
              (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
              (by omega) (by omega) (by omega) h
            exact ⟨q1, q2, q3, q4⟩
        · simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind,
            Except.bind] at h

set_option maxHeartbeats 1600000 in
/-- `applyChanOp` preservation: wf state out, bounded successor
configuration, types unchanged, allocator monotone. -/
theorem applyChanOp_wf {σ : ExecState} {op : ChanStOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState}
    (hw : StateWf σ) (hvs : goValueListSup vs ≤ σ.nextAddr)
    (hop : chanStOpSup op ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applyChanOp σ op vs env k = .ok (c', σ')) :
    StateWf σ' ∧ Config.locSup c' ≤ σ'.nextAddr ∧ σ'.types = σ.types := by
  have hheap := hw.heap_le
  rw [applyChanOp.eq_def] at h
  split at h
  · -- send
    rename_i elem chv vv
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    obtain ⟨v', hv', h⟩ := h
    have hchb := valueAsChan_locSup hch
    have hv'b : GoValue.locSup v' ≤ σ.nextAddr := by
      have := normalizeValueForTy_locSup hv'
      omega
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hw, ?_, rfl⟩
      simp only [Config.locSup, optLocSup, Nat.max_le]
      omega
    · rename_i loc hbase
      simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hw, ?_, rfl⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
          Nat.max_le]
        omega
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨σ₂, hst, rfl, rfl⟩ := h
          obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
            (by rw [show GoValue.locSup (.chanData (buf.push v') capacity closed)
                  = goValueListSup (buf.push v').toList from rfl,
                goValueListSup_push]
                omega) hst
          refine ⟨w1, ?_, w4⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hw, ?_, rfl⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · -- recv (audit response BUG-022: communication FIRST, then targets)
    rename_i targets elem chv
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [chanStOpSup] at hop
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hw, ?_, rfl⟩
      simp only [Config.locSup, optLocSup, Nat.max_le]
      omega
    · rename_i loc hbase
      simp only [bind_eq_ok] at h
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
        simp only [bind_eq_ok] at h
        obtain ⟨σ₁, hst, h⟩ := h
        obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
          (by rw [show GoValue.locSup (.chanData (buf.eraseIdx! 0) capacity closed)
                = goValueListSup (buf.eraseIdx! 0).toList from rfl]
              exact Nat.le_trans goValueListSup_eraseIdx! (by omega)) hst
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨w1, ?_, w4⟩
          simp only [Config.locSup, Nat.max_le]
          omega
        · rename_i t ts
          obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf w1
            (by omega)
            (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
            (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) h
          exact ⟨q1, q2, q3.trans w4⟩
      · split at h
        · -- closed-and-drained: zero value, then deliver
          simp only [bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          have hzb : GoValue.locSup z ≤ σ.nextAddr := by
            rw [defaultValue_locSup hz]; omega
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hw, by simp only [Config.locSup, Nat.max_le]; omega, rfl⟩
          · rename_i t ts
            obtain ⟨q1, q2, q3, q4⟩ := enterRecvTargets_wf hw
              (by omega)
              (Nat.le_trans (recvStores_locSup ((t :: ts).length)) (by omega))
              (by simp [Stmt.locSup, stmtListSup]) (by omega) (by omega) h
            exact ⟨q1, q2, q3⟩
        · -- open-and-empty: block
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hw, ?_, rfl⟩
          simp only [Config.locSup, optLocSup, Nat.max_le]
          omega
  · -- close
    rename_i chv
    simp only [goValueListSup, Nat.max_le] at hvs
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    have hchb := valueAsChan_locSup hch
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hw, ?_, rfl⟩
      simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
        Nat.max_le]
      omega
    · rename_i loc hbase
      simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      have hbufb := chanCell_locSup hcell
      have hlocb : Loc.locSup loc ≤ σ.nextAddr := by
        rw [hbase] at hchb; simp only [optLocSup] at hchb; omega
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hw, ?_, rfl⟩
        simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
          Nat.max_le]
        omega
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl⟩ := h
        obtain ⟨w1, w2, w3, w4, w5⟩ := storeLoc_pres hw hlocb
          (by rw [show GoValue.locSup (.chanData buf capacity true)
                = goValueListSup buf.toList from rfl]
              omega) hst
        refine ⟨w1, ?_, w4⟩
        simp only [Config.locSup, Nat.max_le]
        omega
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

set_option maxHeartbeats 1600000 in
/-- Extract the source element behind one `mapM` output position (the
multi-ready select arm's commit list). -/
theorem mapM_getElem?_mem {α β : Type} {f : α → Except GoError β}
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
theorem applySelect_wf {σ : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState} {ch ch' : Choices}
    (hw : StateWf σ) (hcl : selectClausesSup clauses ≤ σ.nextAddr)
    (hd : optStmtSup default? ≤ σ.nextAddr)
    (hvs : goValueListSup vs ≤ σ.nextAddr)
    (henv : LocalEnv.locSup env ≤ σ.nextAddr)
    (hk : Cont.locSup k ≤ σ.nextAddr)
    (h : applySelect σ clauses default? vs env k ch = .ok (c', σ', ch')) :
    StateWf σ' ∧ Config.locSup c' ≤ σ'.nextAddr ∧ σ'.types = σ.types := by
  rw [applySelect.eq_def] at h
  simp only [bind_eq_ok] at h
  obtain ⟨outc, hcore, h⟩ := h
  rw [applySelectCore.eq_def] at hcore
  simp only [bind_eq_ok] at hcore
  obtain ⟨evs, hevs, hcore⟩ := hcore
  obtain ⟨rc, hrc, hcore⟩ := hcore
  have hevsb : evClausesSup evs ≤ σ.nextAddr := by
    have := evalClauses_sup hevs
    omega
  have hcommit : ∀ c ∈ rc, ∀ {c₂ : Config} {σ₂ : ExecState},
      commitClause σ env k c = .ok (c₂, σ₂) →
      StateWf σ₂ ∧ Config.locSup c₂ ≤ σ₂.nextAddr ∧ σ₂.types = σ.types := by
    intro c hmem c₂ σ₂ hcom
    have hcb : evClauseSup c ≤ σ.nextAddr := by
      have hmem' := readyClauses_subset hrc c hmem
      exact Nat.le_trans (evClausesSup_mem hmem') hevsb
    obtain ⟨w1, w2, w3, _⟩ := commitClause_wf hw hcb henv hk hcom
    exact ⟨w1, w2, w3⟩
  split at h
  · -- outc = .done c₂ σ₂: no pick was consumed
    rename_i c₂ σ₂
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    split at hcore
    · split at hcore <;>
        (simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore;
         obtain ⟨rfl, rfl⟩ := hcore)
      · rename_i d
        refine ⟨hw, ?_, rfl⟩
        simp only [optStmtSup] at hd
        simp only [Config.locSup, Nat.max_le]
        omega
      · refine ⟨hw, ?_, rfl⟩
        simp only [Config.locSup, Nat.max_le]
        omega
    · rename_i c
      simp only [bind_eq_ok] at hcore
      obtain ⟨⟨c₃, σ₃⟩, hcom, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore
      obtain ⟨rfl, rfl⟩ := hcore
      exact hcommit c (List.mem_cons_self ..) hcom
    · simp only [bind_eq_ok] at hcore
      obtain ⟨commits, hcommits, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq] at hcore
      cases hcore
  · -- outc = .picks commits: the L2 pick indexes the pre-committed list
    rename_i commits
    split at h
    · rename_i r₂c r₂σ hget
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      split at hcore
      · split at hcore <;>
          (simp only [pure_eq_ok, Except.ok.injEq] at hcore; cases hcore)
      · simp only [bind_eq_ok] at hcore
        obtain ⟨⟨c₃, σ₃⟩, hcom, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq] at hcore
        cases hcore
      · simp only [bind_eq_ok] at hcore
        obtain ⟨commits₂, hcommits, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.picks.injEq] at hcore
        subst hcore
        obtain ⟨cl, hmem, hf⟩ := mapM_getElem?_mem hcommits hget
        have hcom : commitClause σ env k cl = .ok (r₂c, r₂σ) := by
          cases hcc : commitClause σ env k cl with
          | ok r => rw [hcc] at hf; simp_all
          | error e =>
              rw [hcc] at hf
              cases e <;> simp_all
        exact hcommit cl hmem hcom
    · -- defensive `.inr` (unreachable today): the picked panic as a
      -- `.panicking` configuration over the input state
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hw, ?_, rfl⟩
      simp only [Config.locSup, panicChainSup, runtimeErrorValue_locSup,
        Nat.max_le]
      omega
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Iteration-typing transparency of the phase-1 target entry: the new
`tgtOpK` frame forwards to `k` and carries no snapshot. -/
theorem enterRecvTargets_itersNormalized {σ : ExecState}
    {targets : List Assignee} {vals : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont} {c' : Config} {σ' : ExecState}
    {types : TypeEnv}
    (h : enterRecvTargets σ targets vals body env k = .ok (c', σ'))
    (hk : Cont.itersNormalized types k = true) :
    Config.itersNormalized types c' = true := by
  unfold enterRecvTargets at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [Config.itersNormalized, Cont.itersNormalized] using hk
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- Iteration-typing transparency of `applyChanOp`: every successor
configuration's continuation is the input `k` (or a `tgtOpK` frame
over it that carries no snapshot), so the typing component transfers. -/
theorem applyChanOp_itersNormalized {σ : ExecState} {op : ChanStOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState} {types : TypeEnv}
    (h : applyChanOp σ op vs env k = .ok (c', σ'))
    (hk : Cont.itersNormalized types k = true) :
    Config.itersNormalized types c' = true := by
  rw [applyChanOp.eq_def] at h
  split at h
  · -- send
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, v', hv', h⟩ := h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [Config.itersNormalized] using hk
    · simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [Config.itersNormalized] using hk
      · split at h <;>
          (simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h)
        · obtain ⟨σ₂, hst, rfl, rfl⟩ := h
          simpa [Config.itersNormalized] using hk
        · obtain ⟨rfl, rfl⟩ := h
          simpa [Config.itersNormalized] using hk
  · -- recv: every outcome's continuation is k (or a tgtOpK over k)
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [Config.itersNormalized] using hk
    · simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      split at h
      · simp only [bind_eq_ok] at h
        obtain ⟨σ₁, hst, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa [Config.itersNormalized, Cont.itersNormalized] using hk
        · exact enterRecvTargets_itersNormalized h hk
      · split at h
        · simp only [bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simpa [Config.itersNormalized, Cont.itersNormalized] using hk
          · exact enterRecvTargets_itersNormalized h hk
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa [Config.itersNormalized] using hk
  · -- close
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [Config.itersNormalized] using hk
    · simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [Config.itersNormalized] using hk
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨σ₂, hst, rfl, rfl⟩ := h
        simpa [Config.itersNormalized] using hk
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- Iteration-typing transparency of `commitClause`. -/
theorem commitClause_itersNormalized {σ : ExecState} {env : LocalEnv}
    {k : Cont} {cl : EvClause} {c' : Config} {σ' : ExecState} {types : TypeEnv}
    (h : commitClause σ env k cl = .ok (c', σ'))
    (hk : Cont.itersNormalized types k = true) :
    Config.itersNormalized types c' = true := by
  rw [commitClause.eq_def] at h
  split at h
  · -- sendEv
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      split at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [Config.itersNormalized] using hk
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨v', hv', σ₂, hst, rfl, rfl⟩ := h
          simpa [Config.itersNormalized] using hk
        · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
  · -- recvEv
    simp only [bind_eq_ok] at h
    obtain ⟨ch, hch, h⟩ := h
    split at h
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind_eq_ok] at h
      obtain ⟨⟨buf, capacity, closed⟩, hcell, h⟩ := h
      -- The dequeue-or-zero prelude inlines its continuation per branch.
      split at h
      · simp only [pure_bind, bind_eq_ok] at h
        obtain ⟨σ₁, hst, h⟩ := h
        split at h
        · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa [Config.itersNormalized, Cont.itersNormalized] using hk
        · exact enterRecvTargets_itersNormalized h hk
      · split at h
        · simp only [pure_bind, bind_eq_ok] at h
          obtain ⟨z, hz, h⟩ := h
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simpa [Config.itersNormalized, Cont.itersNormalized] using hk
          · exact enterRecvTargets_itersNormalized h hk
        · simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind,
            Except.bind] at h

/-- Iteration-typing transparency of `applySelect`. -/
theorem applySelect_itersNormalized {σ : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState} {ch ch' : Choices} {types : TypeEnv}
    (h : applySelect σ clauses default? vs env k ch = .ok (c', σ', ch'))
    (hk : Cont.itersNormalized types k = true) :
    Config.itersNormalized types c' = true := by
  rw [applySelect.eq_def] at h
  simp only [bind_eq_ok] at h
  obtain ⟨outc, hcore, h⟩ := h
  rw [applySelectCore.eq_def] at hcore
  simp only [bind_eq_ok] at hcore
  obtain ⟨evs, hevs, hcore⟩ := hcore
  obtain ⟨rc, hrc, hcore⟩ := hcore
  split at h
  · -- outc = .done c₂ σ₂
    rename_i c₂ σ₂
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    split at hcore
    · split at hcore <;>
        (simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore;
         obtain ⟨rfl, rfl⟩ := hcore;
         simpa [Config.itersNormalized] using hk)
    · simp only [bind_eq_ok] at hcore
      obtain ⟨⟨c₃, σ₃⟩, hcom, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.done.injEq] at hcore
      obtain ⟨rfl, rfl⟩ := hcore
      exact commitClause_itersNormalized hcom hk
    · simp only [bind_eq_ok] at hcore
      obtain ⟨commits, hcommits, hcore⟩ := hcore
      simp only [pure_eq_ok, Except.ok.injEq] at hcore
      cases hcore
  · -- outc = .picks commits
    rename_i commits
    split at h
    · rename_i r₂c r₂σ hget
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      split at hcore
      · split at hcore <;>
          (simp only [pure_eq_ok, Except.ok.injEq] at hcore; cases hcore)
      · simp only [bind_eq_ok] at hcore
        obtain ⟨⟨c₃, σ₃⟩, hcom, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq] at hcore
        cases hcore
      · simp only [bind_eq_ok] at hcore
        obtain ⟨commits₂, hcommits, hcore⟩ := hcore
        simp only [pure_eq_ok, Except.ok.injEq, SelectOutcome.picks.injEq] at hcore
        subst hcore
        obtain ⟨cl, hmem, hf⟩ := mapM_getElem?_mem hcommits hget
        have hcom : commitClause σ env k cl = .ok (r₂c, r₂σ) := by
          cases hcc : commitClause σ env k cl with
          | ok r => rw [hcc] at hf; simp_all
          | error e =>
              rw [hcc] at hf
              cases e <;> simp_all
        exact commitClause_itersNormalized hcom hk
    · -- defensive `.inr`: the panicking configuration forwards `k`
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simpa [Config.itersNormalized] using hk
    · simp [throw, throwThe, MonadExceptOf.throw] at h

set_option maxHeartbeats 4000000 in
/-- The LOC half of the preservation theorem: one machine step keeps the
state and the configuration loc-bounded (every location root strictly
below `nextAddr`), and never mutates the type environment. The combined
`step_preserves_wf` below adds the map-iteration typing component. -/
theorem step_preserves_wf_loc {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ')
    (hs : StateWf σ) (hc : ConfigWf σ.nextAddr c) :
    StateWf σ' ∧ ConfigWf σ'.nextAddr c' ∧ σ'.types = σ.types := by

  have hheap := hs.heap_le
  have hfuncs := hs.funcs_le
  cases h
  all_goals try (
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega)
  case panicArgValue v k =>
    refine ⟨hs, ?_, rfl⟩
    have hp := panicPayload_locSup (v := v)
    simp only [ConfigWf, Config.locSup, Cont.locSup, Expr.locSup,
      GoValue.locSup, panicChainSup, Nat.max_le] at hc ⊢
    omega
  case evalRef id loc env k hlook =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := LocalEnv.lookup_locSup hlook
    simp only [ConfigWf, Config.locSup, Cont.locSup, Expr.locSup,
      GoValue.locSup, Nat.max_le] at hc ⊢
    omega
  case evalVar id loc v env k hlook hload =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := loadLoc_locSup hload
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case evalStrict e op e₁ rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := strictPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case evalStrictNullary e op v env k hplan happly =>
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := applyStrictOp_wf hs
      (by simp [goValueListSup]) happly
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case evalRecover env k v k' hrec =>
    obtain ⟨r1, r2⟩ := recoverResult_locSup hrec
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case strictApply op done v out env k happly =>
    have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := applyStrictOp_wf hs hop happly
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case seqn ss env k =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := seqCont_locSup (ss := ss.toList) (env := env) (k := k)
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case block decls ss env env' k hdecls =>
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := allocDecls_wf hdecls hs (by
      rw [LocalEnv.pushScope_locSup]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega)
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case initialization p v loc rest env k hdef halloc =>
    have hv0 := defaultValue_locSup hdef
    obtain ⟨w1, w2, w3, w4⟩ := alloc_wf hs (by omega) halloc
    obtain ⟨d1, d2, d3, d4, d5, _⟩ := alloc_shape halloc
    have hdecl := LocalEnv.declare_locSup (env := env) (id := p.id) (l := loc)
    refine ⟨w1, ?_, d3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case assign lhs te rhs env k hte =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := assigneeExpr_locSup hte
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case assignTargetLoc v loc rhs env k hloc =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := valueAsLoc_locSup hloc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case assignStore v loc k hstore =>
    have hb : Loc.locSup loc ≤ σ.nextAddr ∧ GoValue.locSup v ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3⟩ := storeLoc_wf hs hb.1 hb.2 hstore
    refine ⟨w1, ?_, (storeLoc_shape hstore).1⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callFirstTarget targets fid args te rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := assigneesExprs_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case callFirstArg targets fid args a rest env k hplan hargs =>
    refine ⟨hs, ?_, rfl⟩
    have h2 : exprListSup (a :: rest) = exprListSup args.toList := by rw [hargs]
    simp only [exprListSup] at h2
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h2 ⊢
    omega
  case callImmediate targets fid args func frameEnv resultLocs env k 
 hplan hargs henter =>
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs
      (by simp [goValueListSup]) henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callTargetLoc v loc fid locs te rest args env k hloc =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := valueAsLoc_locSup hloc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callTargetsDoneArg v loc fid locs a rest env k hloc =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := valueAsLoc_locSup hloc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callTargetsDoneEnter v loc fid locs func frameEnv resultLocs env k 
 hloc henter =>
    have h1 := valueAsLoc_locSup hloc
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs
      (by simp [goValueListSup]) henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callArgsDoneEnter v fid locs vals func frameEnv resultLocs env k 
 henter =>
    have hargb : goValueListSup (vals ++ [v]) ≤ σ.nextAddr := by
      rw [goValueListSup_append]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case stmtOpFirst stmt op nt e rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := stmtPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case stmtOpNullary stmt op nt env k ch ch' hplan happly =>
    obtain ⟨w1, w2, w3, w4, w5⟩ := applyStmtOp_wf hs
      (by simp [goValueListSup]) happly
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case stmtOpApply op nt done v env k ch ch' happly =>
    have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨w1, w2, w3, w4, w5⟩ := applyStmtOp_wf hs hop happly
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case mapRangeSnapshot v entries keyVar valVar keyTy valTy body env k hsnap =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := mapRangeSnapshotEntries_locSup hsnap
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case mapIterNext keyVar valVar keyTy valTy body remaining idx env env' k 
 hidx hbind =>
    have hentb : goValueEntriesSup remaining.toList ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    have hkb : max (GoValue.locSup remaining[idx].1)
        (GoValue.locSup remaining[idx].2) ≤ σ.nextAddr := by
      refine Nat.le_trans (goValueEntriesSup_mem ?_) hentb
      exact List.mem_of_getElem? (by
        rw [Array.getElem?_toList]
        exact Array.getElem?_eq_getElem hidx)
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := bindIterVars_wf hs
      (by rw [LocalEnv.pushScope_locSup]; simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc; omega)
      (by omega) (by omega) hbind
    have herase : goValueEntriesSup ((remaining.eraseIdx idx hidx).toList)
        ≤ goValueEntriesSup remaining.toList := goValueEntriesSup_eraseIdx
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callValueFirstTarget targets callee args te rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := assigneesExprs_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case callValTargetLoc v loc callee locs te rest args env k hloc =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := valueAsLoc_locSup hloc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callValTargetsDone v loc callee locs args env k hloc =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := valueAsLoc_locSup hloc
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callValCalleeEnter fid captured locs func frameEnv resultLocs env k 
 henter =>
    have hargb : goValueListSup captured ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case callValArgsEnter v fid captured locs vals func frameEnv resultLocs env
 k henter =>
    have hargb : goValueListSup (captured ++ vals ++ [v]) ≤ σ.nextAddr := by
      rw [goValueListSup_append, goValueListSup_append]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case frameReturn targets results k w vs hload hstore =>
    have h1 := loadMany_locSup hload
    have hb : locListSup targets ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    have p := storeMany_pres hs hb (by omega) hstore
    obtain ⟨w1, w2, w3, w4, w5⟩ := p
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case frameFall targets results k w vs hload hstore =>
    have h1 := loadMany_locSup hload
    have hb : locListSup targets ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    have p := storeMany_pres hs hb (by omega) hstore
    obtain ⟨w1, w2, w3, w4, w5⟩ := p
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case frameDeferFall targets results fid captured args ds k w func frameEnv
 resultLocs henter =>
    have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
      rw [goValueListSup_append]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case frameDeferReturn targets results fid captured args ds k w func frameEnv
 resultLocs henter =>
    have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
      rw [goValueListSup_append]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case deferCalleeNoArgs cv env k k' hdc hpush =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := pushDefer_locSup hpush
    simp only [Nat.max_le] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    simp only [goValueListSup] at h1
    omega
  case deferArgsDone v cv vals env k k' hpush =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := pushDefer_locSup hpush
    simp only [Nat.max_le, goValueListSup_append, goValueListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case panicUnwind chain k k' hpass =>
    refine ⟨hs, ?_, rfl⟩
    have h1 := panicPassthrough_locSup hpass
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  case panicFrameDefer chain targets results fid captured args ds k w func
 frameEnv resultLocs henter =>
    have hargb : goValueListSup (captured ++ args) ≤ σ.nextAddr := by
      rw [goValueListSup_append]
      simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := enterFrame_wf hs hargb henter
    refine ⟨w1, ?_, w3⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc ⊢
    omega
  -- Channel statements (channels arc slice 1).
  case chanStFirst stmt op e rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    obtain ⟨h1, h2⟩ := chanPlan_locSup hplan
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      goValueListSup_append, exprListSup_append, stmtListSup_append,
      locListSup_append, panicChainSup_append, goValueListSup_reverse,
      runtimeErrorValue_locSup, panicPayload, LocalEnv.pushScope_locSup,
      Nat.max_le] at hc h1 h2 ⊢
    omega
  case chanStApply op done v env k happly =>
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
    obtain ⟨w1, w2, w3⟩ := applyChanOp_wf hs h1 h2 h3 h4 happly
    exact ⟨w1, w2, w3⟩
  case selectFirst clauses default? e rest env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    have h1 : exprListSup (e :: rest) ≤ selectClausesSup clauses.toList := by
      rw [← hplan]; exact selectOperands_locSup
    simp only [exprListSup] at h1
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, Expr.locSup,
      GoValue.locSup, optLocSup, panicChainSup, goValueListSup, exprListSup,
      stmtListSup, locListSup, deferListSup, assigneeListSup, optExprSup,
      Nat.max_le] at hc h1 ⊢
    omega
  case selectNoClausesDefault clauses d env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, optStmtSup,
      Nat.max_le] at hc ⊢
    omega
  case selectNoClausesBlock clauses env k hplan =>
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup, evClausesSup,
      Nat.max_le] at hc ⊢
    omega
  case selectApply clauses default? done v env k ch ch' happly =>
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
    obtain ⟨w1, w2, w3⟩ := applySelect_wf hs h1 h2 h3 h4 h5 happly
    exact ⟨w1, w2, w3⟩
  case tgtOpNext sh ops v r sh' e ops' targets refs vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case tgtOpStores sh ops v r refs vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case tgtOpRhs sh ops v r refs e rest vals body env k hcomp =>
    have hr := completeTargetRef_locSup hcomp
    rw [goValueListSup_reverse] at hr
    refine ⟨hs, ?_, rfl⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, GoValue.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      targetRefListSup_append, Stmt.locSup, Nat.max_le] at hc hr ⊢
    omega
  case assignManyFirst left right sh e ops rest env k hsz hplan =>
    have hplans := targetsPlan_locSup hplan
    refine ⟨hs, ?_, rfl⟩
    simp only [targetPlansSup, exprListSup, Nat.max_le] at hplans
    simp only [ConfigWf, Config.locSup, Cont.locSup, Stmt.locSup,
      goValueListSup, exprListSup, targetRefListSup, targetPlansSup,
      stmtListSup, Nat.max_le] at hc ⊢
    omega
  case storeStep r rs val vals body env k hst =>
    have hbounds : TargetRef.locSup r ≤ σ.nextAddr
        ∧ GoValue.locSup val ≤ σ.nextAddr := by
      simp only [ConfigWf, Config.locSup, Cont.locSup, targetRefListSup,
        goValueListSup, Nat.max_le] at hc
      omega
    obtain ⟨w1, w2, w3, w4, w5⟩ := storeTarget_pres hs hbounds.1 hbounds.2 hst
    refine ⟨w1, ?_, w4⟩
    simp only [ConfigWf, Config.locSup, Cont.locSup, targetRefListSup,
      goValueListSup, Stmt.locSup, Nat.max_le] at hc ⊢
    omega



/-! ## Preservation of the map-iteration typing component -/

theorem snapshotEntriesSelfNormalizedList_mem {types : TypeEnv} {kt vt : Ty} :
    ∀ {l : List (GoValue × GoValue)},
      snapshotEntriesSelfNormalizedList types kt vt l = true →
      ∀ {e : GoValue × GoValue}, e ∈ l →
        isNormalForTy types kt e.1 = true ∧ isNormalForTy types vt e.2 = true := by
  intro l
  induction l with
  | nil => intro _ e he; cases he
  | cons p rest ih =>
    intro h e he
    obtain ⟨k, v⟩ := p
    simp only [snapshotEntriesSelfNormalizedList, Bool.and_eq_true] at h
    cases he with
    | head => exact ⟨h.1.1, h.1.2⟩
    | tail _ ht => exact ih h.2 ht

theorem snapshotEntriesSelfNormalizedList_of_mem {types : TypeEnv} {kt vt : Ty} :
    ∀ {l : List (GoValue × GoValue)},
      (∀ e ∈ l, isNormalForTy types kt e.1 = true
        ∧ isNormalForTy types vt e.2 = true) →
      snapshotEntriesSelfNormalizedList types kt vt l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    obtain ⟨k, v⟩ := p
    have hp := h (k, v) List.mem_cons_self
    simp only [snapshotEntriesSelfNormalizedList, Bool.and_eq_true]
    exact ⟨⟨hp.1, hp.2⟩, ih fun e he => h e (List.mem_cons_of_mem _ he)⟩

/-- Snapshot shrinkage preserves the typing check (`mapIterNext`'s
`eraseIdx` keeps a sub-multiset of the entries). -/
theorem snapshotEntriesSelfNormalized_eraseIdx {types : TypeEnv} {kt vt : Ty}
    {arr : Array (GoValue × GoValue)} {i : Nat} {h : i < arr.size}
    (hall : snapshotEntriesSelfNormalized types kt vt arr = true) :
    snapshotEntriesSelfNormalized types kt vt (arr.eraseIdx i h) = true := by
  unfold snapshotEntriesSelfNormalized at hall ⊢
  rw [Array.toList_eraseIdx]
  exact snapshotEntriesSelfNormalizedList_of_mem fun e he =>
    snapshotEntriesSelfNormalizedList_mem hall (List.mem_of_mem_eraseIdx he)

theorem seqCont_itersNormalized {types : TypeEnv} {ss : List Stmt}
    {env : LocalEnv} {k : Cont} :
    Cont.itersNormalized types (seqCont ss env k)
      = Cont.itersNormalized types k := by
  cases k <;> first
    | rfl
    | (simp only [seqCont]; split <;> rfl)

theorem pushDefer_itersNormalized {types : TypeEnv} {d : GoValue × List GoValue} :
    ∀ {k k' : Cont}, pushDefer d k = some k' →
      Cont.itersNormalized types k' = Cont.itersNormalized types k := by
  intro k
  induction k <;> intro k' h <;>
    simp only [pushDefer, Option.map_eq_some_iff, Option.some.injEq] at h
  case frame targets results defers k _ =>
    subst h
    rfl
  all_goals
    first
    | (obtain ⟨k₂, hk₂, rfl⟩ := h
       rename_i ih
       simp only [Cont.itersNormalized, ih hk₂])
    | cases h

theorem panicPassthrough_itersNormalized {types : TypeEnv} {k k' : Cont}
    (h : panicPassthrough k = some k')
    (hk : Cont.itersNormalized types k = true) :
    Cont.itersNormalized types k' = true := by
  cases k <;>
    simp_all [panicPassthrough, Cont.itersNormalized, Bool.and_eq_true]

/-- Companion to `recoverResult_itersNormalized` for the below-the-frame
walk (wrapper transparency, arc-final audit F1). -/
theorem recoverThroughWrappers_itersNormalized {types : TypeEnv} :
    ∀ {k : Cont} {v : GoValue} {k' : Cont}, recoverThroughWrappers k = some (v, k') →
      Cont.itersNormalized types k = true →
      Cont.itersNormalized types k' = true := by
  intro k
  induction k <;> intro v k' h hk
  case stop => simp [recoverThroughWrappers] at h
  case panicResumeK chain k _ =>
    simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
    obtain ⟨⟨v₀, chain'⟩, hmark, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hk
  case frame targets results defers k w ih =>
    cases w
    · simp [recoverThroughWrappers] at h
    · simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
      obtain ⟨⟨v₀, k₀⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Cont.itersNormalized] at hk ⊢
      exact ih hin hk
  all_goals
    rename_i ih
    simp only [recoverThroughWrappers, Option.map_eq_some_iff] at h
    obtain ⟨⟨v₀, k₀⟩, hin, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Cont.itersNormalized, Bool.and_eq_true] at hk ⊢
    first
      | exact ih hin hk
      | exact ⟨hk.1, ih hin hk.2⟩

theorem recoverResult_itersNormalized {types : TypeEnv} :
    ∀ {k : Cont} {v : GoValue} {k' : Cont}, recoverResult k = (v, k') →
      Cont.itersNormalized types k = true →
      Cont.itersNormalized types k' = true := by
  intro k
  induction k <;> intro v k' h hk
  case stop =>
    simp only [recoverResult, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hk
  case panicResumeK chain k _ =>
    simp only [recoverResult, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hk
  case frame targets results defers k w ih =>
    cases w
    · simp only [recoverResult] at h
      cases hin : recoverThroughWrappers k with
      | none =>
          rw [hin] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hk
      | some p =>
          obtain ⟨v₀, k₀⟩ := p
          rw [hin] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Cont.itersNormalized] at hk ⊢
          exact recoverThroughWrappers_itersNormalized hin hk
    · simp only [recoverResult] at h
      cases hrk : recoverResult k with
      | mk v₀ k₀ =>
          rw [hrk] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Cont.itersNormalized] at hk ⊢
          exact ih hrk hk
  all_goals
    rename_i ih
    have hi := ih (v := _) (k' := _) rfl
    have hv := congrArg Prod.fst h
    have hk2 := congrArg Prod.snd h
    simp only [recoverResult] at hv hk2
    try dsimp only at hv hk2
    subst hv
    subst hk2
    simp only [Cont.itersNormalized, Bool.and_eq_true] at hk ⊢
    first
      | exact hi hk
      | exact ⟨hk.1, hi hk.2⟩

/-- The TYPING half of the preservation theorem, at the (unchanged) type
environment of the source state: the snapshot rule ESTABLISHES the check
for the `mapIterK` it creates (its premise is the fail-closed validation),
`mapIterNext` shrinks a checked snapshot, and every other rule only
decomposes continuations structurally. -/
theorem step_preserves_iters {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ')
    (hi : Config.itersNormalized σ.types c = true) :
    Config.itersNormalized σ.types c' = true := by
  cases h
  all_goals try (exact hi)
  all_goals try (
    simp_all only [Config.itersNormalized, Cont.itersNormalized,
      Bool.and_eq_true]
    done)
  case seqn ss env k =>
    simp only [Config.itersNormalized] at hi ⊢
    rw [seqCont_itersNormalized]
    exact hi
  case mapRangeSnapshot v entries keyVar valVar keyTy valTy body env k hsnap =>
    simp only [Config.itersNormalized, Cont.itersNormalized,
      Bool.and_eq_true] at hi ⊢
    exact ⟨(mapRangeSnapshotEntries_ok hsnap).2, hi⟩
  case mapIterNext keyVar valVar keyTy valTy body remaining idx env env' k
      hidx hbind =>
    simp only [Config.itersNormalized, Cont.itersNormalized,
      Bool.and_eq_true] at hi ⊢
    exact ⟨snapshotEntriesSelfNormalized_eraseIdx hi.1, hi.2⟩
  case deferCalleeNoArgs cv env k k' hdc hpush =>
    simp only [Config.itersNormalized, Cont.itersNormalized] at hi ⊢
    rw [pushDefer_itersNormalized hpush]
    exact hi
  case deferArgsDone v cv vals env k k' hpush =>
    simp only [Config.itersNormalized, Cont.itersNormalized] at hi ⊢
    rw [pushDefer_itersNormalized hpush]
    exact hi
  case panicUnwind chain k k' hpass =>
    simp only [Config.itersNormalized] at hi ⊢
    exact panicPassthrough_itersNormalized hpass hi
  case evalRecover env k v k' hrec =>
    simp only [Config.itersNormalized] at hi ⊢
    exact recoverResult_itersNormalized hrec hi
  case chanStApply op done v env k happly =>
    simp only [Config.itersNormalized, Cont.itersNormalized] at hi
    exact applyChanOp_itersNormalized happly hi
  case selectApply clauses default? done v env k ch ch' happly =>
    simp only [Config.itersNormalized, Cont.itersNormalized] at hi
    exact applySelect_itersNormalized happly hi

/-- **The preservation theorem**: one machine step keeps the joint
invariant — loc-boundedness of state and configuration, plus the
map-iteration typing component (transported along the step's types
invariance). -/
theorem step_preserves_wf {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ') (hwf : MachineWf σ c) :
    MachineWf σ' c' := by
  obtain ⟨hs, hc, hi⟩ := hwf
  obtain ⟨hs', hc', ht⟩ := step_preserves_wf_loc h hs hc
  refine ⟨hs', hc', ?_⟩
  rw [ht]
  exact step_preserves_iters h hi

end GoLean.GoCore.Machine
