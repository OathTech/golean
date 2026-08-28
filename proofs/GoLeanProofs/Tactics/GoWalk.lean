import Lean
import Iris.ProofMode
import Iris.ProgramLogic.WeakestPre

/-!
# `go_walk` — the machine-walk tactic (proof-automation arc, phase 2)

Plan of record: `docs/2026-08-01_proof-automation-arc.md`. This module is
the tactic CORE. It contains **no** GoCore, no law and no program: it
knows only the shape `… ⊢ WP c @ s ; E {{ Φ }}` and a table of laws that
other modules register with `@[go_walk_law]`. That is the arc's standing
over-specialization check made structural — the file cannot name quorum
because it cannot see it.

## What it automates

The hand walks (`Specs/GoldenQuorumWP`, `Specs/GoldenRecover`) are a
mechanical loop:

```
iapply <the one law whose conclusion matches the configuration>
iapply fupd_intro; inext; iapply fupd_intro; iintro Hc   -- the modality dance
<discharge the law's rfl/assumption side conditions>
<simp the configuration back into normal form>
```

repeated until the goal is something a human has to decide. `go_walk`
runs that loop: match the goal's configuration in a `DiscrTree` of
registered law conclusions, apply, dance, normalize, repeat.

## The four tactics

* `go_walk` — the loop. `go_walk n` bounds it to `n` steps (needed where
  the walk must stop in front of a segment law a human supplies: a law
  whose conclusion is `Config.exec stmt env k` with `stmt` a VARIABLE,
  like `wp_stmt_op_first`, matches every statement and would otherwise
  descend into one the human meant to take whole). `go_walk with [h]`
  adds `h` to the between-step normalization.
* `go_walk_step law` — apply ONE law, given as a term with its semantic
  side conditions supplied, with the same modality/resource handling.
  This is what replaces a hand walk's
  `iapply (…) / isplitl [H] / iexact H / iintro H` block. `as [x, H, …]`
  names the introductions in order, for the allocation addresses and
  cells a later obligation must mention by name.
* `go_walk_finish H` — walk until the goal is the one the continuation
  hypothesis `H` delivers, then close it with `H`'s resources. The honest
  end of a segment: one step past it and a perfectly good law (the
  loop-exit rule, the next sequence pop) has already fired.
* `go_walk1` — one step, reporting which law fired. Debugging only.

## Where it stops (by design — never loops, never `sorry`)

* **No registered law matches the configuration.** Reported with the
  configuration's head shape.
* **A law's side condition is not `rfl`/`assumption`/`go_walk_simp`.**
  (`wp_assign_store`'s `hstore`, `wp_init`'s `hdef`: real proof
  obligations about `storeLoc`/`defaultValue`. A tactic that guessed at
  those would be guessing at the semantics.)
* **Invariant-carrying rules** (`wp_map_iter_inv`, `wp_while_inv`): their
  premise is a Lean-level `∀`-obligation whose `I` no goal determines.
  They are not registered, so the walk stops in front of them.
* **Nondeterministic branches** and any step whose next configuration is
  not determined by the current one.
* **Resource splits it cannot resolve uniquely.** See below.

In every case the tactic stops with the goal untouched by the failed
attempt, having made whatever progress it could; it never leaves a
half-applied law behind (each candidate is tried under a saved state).

## Resource threading (v1 policy)

A law whose left-hand side is `P₁ ∗ … ∗ Pₙ ∗ (Q -∗ WP c₁)` needs the
`Pᵢ` from the Iris context. v1 tries `iframe` — which cancels context
hypotheses against the `Pᵢ` — and then re-introduces `Q`. This is exactly
the hand walks' `isplitl [H] / iexact H / iintro H`, and it works in the
common case because the *address* of every resource a registered law
consumes is determined by the configuration or by an already-discharged
side condition, so at most one context hypothesis can match.

**Framing renames.** A hypothesis `iframe` cancels comes back with a
fresh, inaccessible name, so a `go_walk`ed proof cannot address its
resources by name afterwards. That is why the segment endings are
`go_walk_finish H` / `iframe` (name-free) rather than `isplitl [H₁ … Hₙ]`,
and why `go_walk_step … as […]` exists for the few cells a later
obligation genuinely has to name (an invariant's `i` cell, a callsite's
target cell).

**The boundary rule.** If a law matched the configuration and its side
conditions were mechanical but its resources could NOT be framed, the
walk stops there instead of falling through to a more generic law. That
is the honest reading: a composed operation law covers the statement
whole, and the generic law would take a smaller step INTO it. The human
then supplies the composed law with `go_walk_step`.

## Prior art

Perennial's `wp_pures`/`wp_load`/`wp_apply` family
(`deps/perennial/src/program_logic`, `new/golang/theory`) and iris-lean's
own `wp_pure`/`wp_pures` (`Iris/HeapLang/ProofMode.lean:346`). Both search
an EVALUATION CONTEXT (`findECtx`, `wp_bind`) and then fire a `PureExec`
typeclass instance. GoCore's machine is a CEK machine: the redex *is* the
configuration, so there is no context to search and no `wp_bind` — the
whole of `findECtx` collapses to "look at the head". What replaces
`PureExec` here is the registered law table, because our step laws are
not uniformly pure (`wp_eval_var` reads a cell, `wp_strict_apply_pin`
reads the type environment) and so cannot be a single typeclass with a
single conclusion shape. We deliberately reuse iris-lean's proof-mode
tactics (`iapply`, `inext`, `iframe`, `iintro`) rather than reimplement
entailment plumbing.

Two ordering deltas from `wp_pure` are ours, both forced by the law table
being a table rather than a typeclass: candidates are ranked
MOST-SPECIFIC-FIRST (`DiscrTree.getMatch` returns wildcard branches
first, which is exactly backwards for us), and each candidate's match and
side-condition discharge run under their own small heartbeat budget so a
hopeless candidate is rejected rather than eating the declaration's.

This file is metaprogramming, not proof-facing semantics: the two
`partial def`s (`sepArity`, structural on `Expr`; `dischargeToWp`, which
carries an explicit fuel) are `partial` because Lean cannot see their
termination through `TacticM`, and they generate no proof term of their
own. Every proof `go_walk` produces goes through the kernel like any
other, and the in-build `Audit` sweep checks its axioms.
-/

open Lean Meta Elab Tactic

namespace GoLean.Iris.GoWalk

/-- Configuration-normalization simp set: the rewrites the hand walks run
between steps (`seqCont` splicing, `List` append normal forms, …). Tagged
lemmas must be confluent and configuration-shaped; this set runs on the
whole proof-mode goal after every step. -/
register_simp_attr go_walk_simp

/-- A registered law: its name, and how SPECIFIC its conclusion's
configuration is (the number of non-wildcard discrimination keys). -/
structure LawEntry where
  declName : Name
  specificity : Nat
  deriving Inhabited, BEq, Repr

/-- The law table: a discrimination tree over the CONFIGURATION in each
registered law's conclusion. -/
initialize goWalkExt :
    SimpleScopedEnvExtension (Array DiscrTree.Key × LawEntry) (DiscrTree LawEntry) ←
  registerSimpleScopedEnvExtension {
    name := `goWalkLaws
    addEntry := fun d (ks, e) => d.insertKeyValue ks e
    initial := {}
  }

/-- Split `Δ ⊢ Q` into `(Δ, Q)`. Both the plain entailment (a law's
statement) and the proof mode's `Entails'` marker (the goal once `iintro`
has started the proof mode) are recognised. -/
def entailsParts? (ty : Expr) : Option (Expr × Expr) := do
  let ty := ty.consumeMData
  guard (ty.isAppOfArity ``Iris.BI.BIBase.Entails 4
    || ty.isAppOfArity ``Iris.ProofMode.Entails' 4)
  let args := ty.getAppArgs
  some (args[2]!, args[3]!)

/-- The configuration `c` of a `WP c @ s ; E {{ Φ }}`. -/
def wpConfig? (q : Expr) : Option Expr := do
  guard (q.isAppOfArity ``Iris.Wp.wp 9)
  q.getAppArgs[7]!

/-- The configuration a proof-mode goal `Δ ⊢ WP c @ s ; E {{ Φ }}` is
about — `none` if the goal is not of that shape. -/
def goalConfig? (ty : Expr) : Option Expr := do
  let (_, rhs) ← entailsParts? ty
  wpConfig? rhs

/-- Is this proof-mode goal a WP goal? -/
def isWpGoal (ty : Expr) : Bool := (goalConfig? ty).isSome

/-- The right-nested `∗`-conjunct count of `P₁ ∗ (P₂ ∗ … )`. -/
partial def sepArity (e : Expr) : Nat :=
  if e.isAppOfArity ``Iris.BI.BIBase.sep 4 then 1 + sepArity e.getAppArgs[3]!
  else 1

/-! ### The `@[go_walk_law]` attribute -/

/-- The configuration a law's conclusion is about, computed under the
law's binder telescope (so the keys `star` out its variables). -/
private def lawKeys (declName : Name) : MetaM (Array DiscrTree.Key) := do
  let info ← getConstInfo declName
  -- METAvariable telescope, not a free-variable one: `DiscrTree.mkPath`
  -- indexes an fvar by its id but an unassigned mvar by `*`, and a law's
  -- variables must be wildcards in the table.
  let (_, _, body) ← forallMetaTelescope info.type
  let some cfg := goalConfig? body
    | throwError "go_walk_law: `{declName}`'s conclusion is not of the form \
        `… ⊢ WP c @ s ; E \{\{ Φ }}`"
  DiscrTree.mkPath cfg

initialize registerBuiltinAttribute {
  name := `go_walk_law
  descr := "a weakest-precondition step law `… ⊢ WP c @ s ; E {{ Φ }}` \
    that `go_walk` may fire when the goal's configuration matches `c`"
  applicationTime := .afterTypeChecking
  add := fun declName _stx kind => do
    let keys ← (lawKeys declName).run'
    let specificity := keys.foldl (fun n k => if k == .star then n else n + 1) 0
    goWalkExt.add (keys, { declName, specificity }) kind
}

/-- The laws whose conclusion could match `cfg`, MOST SPECIFIC FIRST.

The order matters and `DiscrTree.getMatch`'s is the wrong one: it returns
wildcard branches before literal ones, so a generic step law would fire
before the composed operation law that covers the whole statement (and the
walk would descend into a statement the human meant to take in one step).
Sorting by the number of non-wildcard keys restores "the most specific law
wins", which is what a hand walk does by eye. -/
def candidates (cfg : Expr) : MetaM (Array Name) := do
  let es ← (goWalkExt.getState (← getEnv)).getMatch cfg
  return (es.qsort (fun a b => a.specificity > b.specificity)).map (·.declName)

/-- The configuration a goal is about, for an error message. -/
def stuckShape (ty : Expr) : MetaM MessageData := do
  match goalConfig? ty with
  | none => return m!"(the goal is not a weakest precondition)"
  | some cfg => return indentExpr (← instantiateMVars cfg)

/-! ### The step -/

/-- Run `x` under its OWN heartbeat budget.

`go_walk` tries laws speculatively, and a law that does not apply can be
arbitrarily expensive to reject: unifying two large configurations, or
`rfl` on a side condition that unfolds the whole interpreter. Without a
per-attempt bound one hopeless candidate eats the whole file's budget and
the failure is reported as a timeout at a tactic that was going to
succeed. Each attempt therefore gets a fresh, small budget; exceeding it
is an ordinary "this law did not fire". -/
def withBudget (n : Nat) (x : TacticM α) : TacticM α :=
  Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) x

/-- Budget (in `maxHeartbeats` units — 200000 is Lean's default for a whole
declaration) for one candidate law's configuration match. -/
def matchBudget : Nat := 20000

/-- Budget for one side condition's mechanical discharge. -/
def sideBudget : Nat := 40000

/-- Discharge a law's Lean-level side condition. Deliberately weak: the
walk is allowed to close bookkeeping (`rfl` plans, `assumption` for
environment-resolution hypotheses, the normalization set), and nothing
else. A side condition that is a real semantic obligation stops the walk
instead of being guessed at. -/
syntax (name := goWalkSideTac) "go_walk_side" : tactic
/-- The closers `go_walk_side` finishes a side condition with. `decide`
handles the plan/arity conditions once the normalization has reduced their
`List.length`s; `omega` catches the ones that still mention a variable
(`decide` refuses a goal with free variables). -/
syntax (name := goWalkCloseTac) "go_walk_close" : tactic

macro_rules
  | `(tactic| go_walk_close) =>
    `(tactic| first | done | rfl | assumption | decide | omega)

macro_rules
  | `(tactic| go_walk_side) =>
    `(tactic| first
        | rfl
        | assumption
        | (simp only [go_walk_simp]; go_walk_close)
        | (intros; go_walk_close)
        | (intros; simp only [go_walk_simp]; go_walk_close))

/-- The modality dance the lifted step laws all end in — or nothing, for
the laws (`wp_strict_apply_pin`, the composed walks) that carry no
modality. -/
syntax (name := goWalkDanceTac) "go_walk_dance" : tactic

macro_rules
  | `(tactic| go_walk_dance) =>
    `(tactic| first
        | (iapply Iris.fupd_intro
           inext
           iapply Iris.fupd_intro
           iintro -)
        | skip)

/-- Normalize the configuration between steps. -/
def normalizeGoal (extra : Array Term) : TacticM Unit := do
  let lemmas ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let stx ← `(tactic| simp only [go_walk_simp, $lemmas,*])
  try evalTactic stx catch _ => pure ()

/-- Names a step's introductions should use, in order, before falling back
to fresh ones. `go_walk_step law as [x, H]` is how a walk keeps hold of an
allocation address and its cell when a later obligation must mention them
by name. -/
structure Naming where
  names : Array Ident
  next : IO.Ref Nat

/-- The next caller-supplied name, or a fresh one. -/
private def Naming.pop (nm : Naming) (hint : Name) : TacticM Ident := do
  let i ← nm.next.get
  if h : i < nm.names.size then
    nm.next.set (i + 1)
    return nm.names[i]
  else
    return mkIdent (← mkFreshUserName hint)

/-- Introduce one `⟨H₁, …, Hₙ⟩` for an `n`-ary right-nested `∗`. -/
private def iintroFresh (nm : Naming) (n : Nat) : TacticM Unit := do
  let names ← (List.range n).toArray.mapM fun _ => nm.pop `Hgw
  if h : 0 < names.size ∧ n = 1 then
    evalTactic (← `(tactic| iintro $(names[0]'h.1):ident))
  else
    let alts ← names.mapM fun nm => do
      let p ← `(icasesPat| $nm:ident)
      `(Iris.ProofMode.icasesPatAlts| $p:icasesPat)
    evalTactic (← `(tactic| iintro ⟨$alts,*⟩))

/-- Drive the goal left behind by a law back to a weakest precondition.

A law's left-hand side is one of
`WP c₁` / `P₁ ∗ … ∗ Pₙ ∗ (Q -∗ WP c₁)` / `∀ a, Q a -∗ WP c₁`
(and nestings thereof). The resource conjuncts are cancelled against the
Iris context by `iframe`; the universally quantified allocation address
and the continuation's wand are introduced. Anything else — in
particular a `∗` that framing cannot cancel — is a boundary, and the step
is abandoned so the caller can restore the state.

`boundary` is set when the step failed at a RESOURCE as opposed to failing
to apply: the law's conclusion matched the configuration and its side
conditions were mechanical, but the cells its premise consumes could not be
cancelled against the Iris context. That is a boundary, not a mis-guess —
falling through to a more generic law would take a smaller step INTO a
statement this one covers whole — so the walk stops there. -/
private partial def dischargeToWp (boundary : IO.Ref Bool) (nm : Naming)
    (name : MessageData) (fuel : Nat := 8) : TacticM Unit := do
  if fuel = 0 then
    throwError "go_walk: {name}'s left-hand side is too deeply nested"
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, rhs) := entailsParts? ty
    | throwError "go_walk: {name} left a non-entailment goal"
  if (wpConfig? rhs).isSome then return
  if rhs.isAppOfArity ``Iris.BI.BIBase.sep 4 then
    evalTactic (← `(tactic| iframe))
    if (← getGoals).isEmpty then return
    let ty' ← instantiateMVars (← (← getMainGoal).getType)
    if ← isDefEq ty ty' then
      boundary.set true
      throwError "go_walk: {name} needs a resource `go_walk` cannot \
        find in the Iris context (stopping at the boundary)"
    dischargeToWp boundary nm name (fuel - 1)
  else if rhs.isAppOfArity ``Iris.BI.BIBase.wand 4 then
    iintroFresh nm (sepArity rhs.getAppArgs[2]!)
    dischargeToWp boundary nm name (fuel - 1)
  else if rhs.isAppOfArity ``Iris.BI.BIBase.«forall» 4 then
    let x ← nm.pop `agw
    evalTactic (← `(tactic| iintro %$x:ident))
    dischargeToWp boundary nm name (fuel - 1)
  else
    throwError "go_walk: {name} left a goal that is not a weakest \
      precondition (stopping at the boundary)"

/-- Apply one law — given as an already-elaborated term, so that both the
table-driven walk and the explicit `go_walk_step` escape hatch share the
whole of the step machinery — to the current WP goal.

Fails (leaving the caller to restore the state) if the law does not match
the configuration, if a side condition is not mechanical, or if the result
is not again a WP goal. -/
def applyLawTerm (lawE : Expr) (name : MessageData) (extra : Array Term)
    (boundary : IO.Ref Bool) (nm : Naming) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, rhs) := entailsParts? ty
    | throwError "go_walk: the goal is not an Iris entailment"
  unless (wpConfig? rhs).isSome do
    throwError "go_walk: the goal is not a weakest precondition"
  let (args, bis, concl) ← forallMetaTelescope (← inferType lawE)
  let some (_, lrhs) := entailsParts? concl
    | throwError "go_walk: {name} does not conclude an entailment"
  let matched ←
    try withBudget matchBudget (isDefEq lrhs rhs) catch _ => pure false
  unless matched do
    throwError "go_walk: {name} does not match the configuration\
      {← stuckShape ty}"
  -- instance arguments the unifier did not pin down
  for h : i in [0:args.size] do
    if bis[i]! == BinderInfo.instImplicit then
      let mid := args[i].mvarId!
      unless ← mid.isAssigned do
        mid.assign (← synthInstance (← mid.getType))
  -- Everything still open is a Lean-level side condition. Discharge those
  -- FIRST: many of a law's data arguments (`wp_assign_start`'s target
  -- expression, `wp_eval_ref`'s location) are determined only by the side
  -- condition's own unification, so the undetermined-argument check has to
  -- come after.
  let mut sides : Array MVarId := #[]
  for a in args do
    let mid := a.mvarId!
    unless ← mid.isAssigned do
      if ← isProp (← instantiateMVars (← mid.getType)) then
        sides := sides.push mid
  let saved ← getGoals
  for m in sides do
    unless ← m.isAssigned do
      setGoals [m]
      let mty ← instantiateMVars (← m.getType)
      try
        withBudget sideBudget (evalTactic (← `(tactic| go_walk_side)))
      catch e =>
        throwError "go_walk: {name}'s side condition is not mechanical\
          {indentExpr mty}\nthe closers reported: {e.toMessageData}"
      unless (← getGoals).isEmpty do
        throwError "go_walk: {name}'s side condition is not mechanical\
          {indentExpr mty}"
  setGoals saved
  let stx ← Term.exprToSyntax (mkAppN lawE args)
  let pmt ← `(pmTerm| $stx:term)
  evalTactic (← `(tactic| iapply $pmt))
  evalTactic (← `(tactic| go_walk_dance))
  dischargeToWp boundary nm name
  -- Framing may have closed the segment outright (the law's own continuation
  -- wand was the one in the context).
  if (← getGoals).isEmpty then return
  -- A data argument no premise determines (`wp_eval_var`'s cell) is the
  -- resource's, and framing has just assigned it. Anything STILL open after
  -- that would leave the configuration under-determined, so the step is
  -- refused rather than guessed.
  for a in args do
    unless ← a.mvarId!.isAssigned do
      throwError "go_walk: {name} leaves the argument \
        `{← instantiateMVars (← a.mvarId!.getType)}` undetermined"
  normalizeGoal extra
  let ty' ← instantiateMVars (← (← getMainGoal).getType)
  unless isWpGoal ty' do
    throwError "go_walk: {name} did not leave a weakest precondition"

/-- The table-driven form of `applyLawTerm`. -/
def applyLaw (declName : Name) (extra : Array Term) (boundary : IO.Ref Bool) :
    TacticM Unit := do
  applyLawTerm (← mkConstWithFreshMVarLevels declName) m!"`{declName}`" extra
    boundary { names := #[], next := ← IO.mkRef 0 }

/-- Try every candidate law for the current goal's configuration; return
the one that fired, or `none`. Each attempt is fully backtracked. -/
def stepOnce (extra : Array Term) : TacticM (Option Name) := withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let some cfg := goalConfig? ty | return none
  let cands ← candidates cfg
  trace[go_walk] "configuration {cfg}\n  candidates: {cands}"
  let boundary ← IO.mkRef false
  for declName in cands do
    let saved ← saveState
    boundary.set false
    try
      applyLaw declName extra boundary
      return some declName
    catch e =>
      trace[go_walk] "`{declName}` did not fire: {e.toMessageData}"
      restoreState saved
      if ← boundary.get then return none
  return none

/-- A readable description of where the walk stopped. -/
def stuckMessage (ty : Expr) : MetaM MessageData := do
  match goalConfig? ty with
  | none => return m!"the goal is no longer a weakest precondition"
  | some cfg =>
    let cfg ← instantiateMVars cfg
    let head := cfg.getAppFn
    let headName := if let .const n _ := head then m!"`{n}`" else m!"{head}"
    return m!"no registered `@[go_walk_law]` fires on the configuration \
      {headName}:{indentExpr cfg}"

/-! ### The tactics -/

/-- `go_walk` runs the deterministic spine of a machine walk: it repeatedly
matches the goal's configuration against the `@[go_walk_law]` table,
applies the law, discharges the modality dance and the mechanical side
conditions, and normalizes. It stops — without failing — as soon as no law
fires, provided it made at least one step.

`go_walk with [h₁, h₂]` adds `h₁`/`h₂` to the between-step normalization set
(the `IntKind.normalize` and pin equations a walk carries as hypotheses).

`go_walk n` bounds the number of steps (default 400). -/
syntax (name := goWalkTac) "go_walk" (ppSpace num)?
  (" with " "[" withoutPosition(term,*) "]")? : tactic

elab_rules : tactic
  | `(tactic| go_walk $[$fuel?:num]? $[with [$extra?,*]]?) => do
    let fuel := match fuel? with | some n => n.getNat | none => 400
    let extra : Array Term := match extra? with
      | some ts => ts.getElems
      | none => #[]
    normalizeGoal extra
    let mut n : Nat := 0
    while n < fuel do
      match ← stepOnce extra with
      | some _ => n := n + 1
      | none => break
    if n == 0 then
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      throwError "go_walk made no progress: {← stuckMessage ty}"
    -- An EXPLICIT budget is a deliberate "advance exactly n steps" (the walk
    -- must stop in front of a segment law the human supplies); only the
    -- DEFAULT budget running out is a surprise worth reporting.
    if n ≥ fuel && fuel?.isNone then
      logWarning m!"go_walk: the default step budget ({fuel}) ran out; \
        raise it with `go_walk <n>`"

/-- `go_walk1` is one step of `go_walk` — the debugging form: it reports
which law fired, and fails with the configuration's shape when none does. -/
syntax (name := goWalk1Tac) "go_walk1"
  (" with " "[" withoutPosition(term,*) "]")? : tactic

elab_rules : tactic
  | `(tactic| go_walk1 $[with [$extra?,*]]?) => do
    let extra : Array Term := match extra? with
      | some ts => ts.getElems
      | none => #[]
    normalizeGoal extra
    match ← stepOnce extra with
    | some declName => logInfo m!"go_walk1: applied `{declName}`"
    | none =>
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      throwError "go_walk1: {← stuckMessage ty}"

/-- `go_walk_finish H` walks until the goal is the one the continuation
hypothesis `H` delivers, and closes it with `H`'s resources.

This is the honest end of a walk segment: a body lemma's premise is
`… -∗ WP c` for the configuration the segment hands back, and the walk
must stop exactly there — one step further and a perfectly good law (the
loop-exit rule, the next sequence pop) has already fired past it. Rather
than counting steps, `go_walk_finish` tries `iapply H; iframe` after every
step and stops at the first one that closes the goal. -/
syntax (name := goWalkFinishTac) "go_walk_finish " term
  (" with " "[" withoutPosition(term,*) "]")? : tactic

elab_rules : tactic
  | `(tactic| go_walk_finish $h $[with [$extra?,*]]?) => do
    let extra : Array Term := match extra? with
      | some ts => ts.getElems
      | none => #[]
    let mut n : Nat := 0
    repeat
      if (← getGoals).isEmpty then return
      let saved ← saveState
      try
        evalTactic (← `(tactic| (iapply $h:term; iframe)))
        if (← getGoals).isEmpty then return
        restoreState saved
      catch _ =>
        restoreState saved
      match ← stepOnce extra with
      | some _ => n := n + 1
      | none =>
        throwError "go_walk_finish: after {n} step(s) the walk can neither \
          continue nor be closed by `{h}`"
      if n > 400 then
        throwError "go_walk_finish: step budget exhausted"

/-- `go_walk_step law` applies ONE named law with `go_walk`'s side-condition
and modality handling — the escape hatch for a step the table cannot pick
(an ambiguous configuration, or a law kept out of the table on purpose). -/
syntax (name := goWalkStepTac) "go_walk_step " term
  (" as " "[" withoutPosition(ident,*) "]")?
  (" with " "[" withoutPosition(term,*) "]")? : tactic

elab_rules : tactic
  | `(tactic| go_walk_step $law $[as [$as?,*]]? $[with [$extra?,*]]?) => do
    let extra : Array Term := match extra? with
      | some ts => ts.getElems
      | none => #[]
    let names : Array Ident := match as? with
      | some ns => ns.getElems
      | none => #[]
    let lawE ← withMainContext do
      -- Elaborate AGAINST the goal's weakest precondition when we can. A law
      -- supplied by hand carries `by simp …` proofs of its semantic side
      -- conditions, and those goals (`applyStrictOp σ op …`) are nothing but
      -- metavariables until the law's conclusion has been unified with the
      -- configuration. Handing the elaborator that conclusion as the expected
      -- type does the unification first, so the tactic blocks run on real
      -- goals. Falls back to an unconstrained elaboration (a law given with
      -- explicit arguments still open) when that does not typecheck.
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      let fallback := Term.elabTerm law none
      let some (_, rhs) := entailsParts? ty | fallback
      let A ← mkFreshExprMVar (← inferType rhs)
      let expected ← mkAppM ``Iris.BI.BIBase.Entails #[A, rhs]
      try
        Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm law expected
      catch _ => fallback
    applyLawTerm lawE m!"{law}" extra (← IO.mkRef false)
      { names, next := ← IO.mkRef 0 }

initialize registerTraceClass `go_walk

end GoLean.Iris.GoWalk
