import GoLean.GoCore.Syntax
import GoLean.GoCore.Value

namespace GoLean.GoCore

open GoLean

/-- One lexical scope: bindings from local names to heap-backed locations,
innermost binding first. -/
abbrev Scope := List (String × Loc)

/-- Lexical scope stack, innermost scope first. Name lookup walks scopes
inner to outer; declaration always creates a fresh binding in the innermost
scope, so shadowing gets a fresh location instead of reusing the outer one.
Block execution pushes a scope on entry and pops it on every exit path. -/
abbrev LocalEnv := List Scope

/-- A heap cell records the value and, when known at allocation, the declared
type of the allocation. Stores to a typed cell are normalized against the
declared type; untyped cells (legacy allocation paths, tracked for closure in
the semantics upgrade) fall back to value-shape coercion. -/
structure HeapCell where
  declaredTy : Option Ty := none
  value : GoValue
  deriving Repr, BEq

abbrev Heap := List (Loc × HeapCell)
abbrev TypeEnv := List (TypeId × TypeDef)

/-- The machine state. Locals are NOT here (reshape S4, 2026-07-23): the
current frame's environment lives in the control configuration
(`Machine.Config`, CEK env-in-control), so the state is program context +
heap only. The old interpreter's `locals` field — the correspondence
bridge `σ.locals ≈ Config.env` — is gone with the big-step cluster. -/
structure ExecState where
  types : TypeEnv := []
  functions : Array Func := #[]
  methods : Array MethodInfo := #[]
  /-- Method-set records (class closure of BUG-053; contract note
  `docs/2026-08-10_method-set-record-contract.md`): satisfaction and
  dispatch answer ONLY from these. Default `#[]` = fail closed — a
  hand-built state refuses every method-carrier query until its
  records are stated explicitly. -/
  methodSets : Array MethodSetRecord := #[]
  heap : Heap := []
  nextAddr : Nat := 0
  deriving Repr, BEq

structure Result where
  values : Array GoValue
  deriving Repr, BEq

/-- Statement-execution outcome classification. Survives the reshape S4
deletion because the Surface layer's `execStmt`-SHAPED wrapper (F4 §2's
decided interface, restored at R3) reproduces the old signature
`… → Except GoError (ExecOutcome × Choices)` over iterated `stepFn`. -/
inductive ExecOutcome where
  | normal (state : ExecState)
  | returned (state : ExecState)
  | broke (state : ExecState)
  | continued (state : ExecState)
  deriving Repr, BEq

def ExecOutcome.state : ExecOutcome → ExecState
  | .normal state => state
  | .returned state => state
  | .broke state => state
  | .continued state => state

def Scope.lookup : Scope → String → Option Loc
  | [], _ => none
  | (name, loc) :: rest, needle =>
      if name == needle then some loc else Scope.lookup rest needle

def LocalEnv.lookup : LocalEnv → String → Option Loc
  | [], _ => none
  | scope :: outer, needle =>
      match Scope.lookup scope needle with
      | some loc => some loc
      | none => LocalEnv.lookup outer needle

/-- Bind a name in the innermost scope. An empty environment is treated as a
single empty scope so frame setup can start from `[]`. -/
def LocalEnv.declare : LocalEnv → String → Loc → LocalEnv
  | [], name, loc => [[(name, loc)]]
  | scope :: outer, name, loc => ((name, loc) :: scope) :: outer

def LocalEnv.pushScope (env : LocalEnv) : LocalEnv :=
  [] :: env

-- `LocalEnv.popScope` deleted (reshape S4): scope exit is continuation
-- discard in the machine; nothing pops.

def Heap.lookup : Heap → Loc → Option HeapCell
  | [], _ => none
  | (loc, cell) :: rest, needle =>
      if loc == needle then some cell else Heap.lookup rest needle

def Heap.set : Heap → Loc → HeapCell → Heap
  | [], loc, cell => [(loc, cell)]
  | (loc, old) :: rest, needle, cell =>
      if loc == needle then
        (loc, cell) :: rest
      else
        (loc, old) :: Heap.set rest needle cell

def TypeEnv.lookup : TypeEnv → TypeId → Option TypeDef
  | [], _ => none
  | (id, defn) :: rest, needle =>
      if id == needle then some defn else TypeEnv.lookup rest needle

def StructFields.lookup : Array (String × GoValue) → String → Option GoValue
  | fields, needle =>
      fields.foldl
        (fun found (name, value) =>
          match found with
          | some value => some value
          | none => if name == needle then some value else none)
        none

def StructFields.set (fields : Array (String × GoValue)) (needle : String)
    (value : GoValue) : Except GoError (Array (String × GoValue)) := do
  let mut out := #[]
  let mut found := false
  for (name, old) in fields do
    if name == needle then
      out := out.push (name, value)
      found := true
    else
      out := out.push (name, old)
  if found then
    return out
  else
    throw (.stuck s!"unknown GoCore struct field: {needle}")

/-- The nondeterminism choice stream ("parser of randomness"): each
nondeterministic point consumes the next choice. The CANONICAL SITE
LIST is the `ChoiceSite` datatype below (W3.2 slice 1 stage A — the
census as code; the doctrine preamble and latitude-inventory §0
tables now point here instead of being hand-synced at audits). It is
threaded by the interpreter **external to
`ExecState`**, so the relation and the interpreter/relation
correspondence compare oracle-free states. GoCore never commits to
determinism Go lacks; the interpreter only picks a behavior by
instantiating this oracle, a testing convenience — see
`docs/nondeterminism-design.md` (whose own site list predates the
concurrency sites — the doctrine preamble is the current record) and
`docs/2026-07-19_reshape-b-oracle-externalization.md`. -/
abbrev Choices := List Nat

/-- The RAW stream pop: next choice modulo the bound, exhaustion
yielding 0 (the canonical default). Interpreter code NEVER calls this
directly — every consumption site goes through `Choices.consumeAt`
with its census tag (W3.2 slice 1 stage A, audit Q1); this primitive
remains public only because the proof layer unfolds through it. -/
def Choices.consume (choices : Choices) (bound : Nat) : Nat × Choices :=
  let b := max 1 bound
  match choices with
  | [] => (0, choices)
  | c :: rest => (c % b, rest)

/-- **The choice-site census, as a datatype** (W3.2 slice 1 stage A —
audit finding C-3/queue Q1, ruled G0 2026-08-20). One constructor per
consumption site in the semantic core; adding a site REQUIRES a
constructor here plus a `ChoiceSite.policy` row, an accountant arm
(`stepNeeds`/`stepNeedsSeq`, CLI.lean's lockstep inventory), and the
site's envelope statement in situ — the doc-resident census sweeps
(nondeterminism doctrine preamble, latitude inventory §0) are retired
by this type's exhaustiveness and now point here.

The sites and their consuming definitions:
* `mapIter`      — range-over-map pick-next (`stepFn`'s `.mapIterK`
                   arm, StepFn.lean). Envelope at `Cont.mapIterK`.
* `appendSpill`  — append reallocation capacity (`applyStmtOp`'s
                   `appendSlice` arm, Machine.lean). Envelope at
                   `appendSpillUpper` (Ops.lean).
* `l2Entry`      — multi-ready select clause pick, cell path
                   (`applySelect`, Machine.lean — its docstring is the
                   L2 envelope statement).
* `l2Arrival`    — multi-ready select clause pick, arrival path
                   (`arrivalPlan` at a `.multi` analysis, Multi.lean).
* `l4Waiter`     — parked-partner pick at a multi-candidate pairing
                   (`stepThread`, Multi.lean; envelope at
                   `chanArrivalPlan`).
* `l1Sched`      — the scheduler pick at a registry boundary
                   (`stepMulti`, Multi.lean; envelope at
                   `runnableIdxs`).
* `l5ExitWindow` — the main-exit window (`execProgLoop`, Multi.lean;
                   envelope at its docstring; bound is constant 2).

The scheduling sites — what a future `Fair : Choices → Prop`
quantifies over — are exactly `{l1Sched, l5ExitWindow}` today
(slice-1 stages C/D add `postOp`/`backEdge` constructors with the
boundary widening; they are NOT pre-declared here — an enum row
without a consuming site would be an inert placeholder). -/
inductive ChoiceSite where
  | mapIter | appendSpill
  | l2Entry | l2Arrival | l4Waiter
  | l1Sched | l5ExitWindow
  deriving Repr, DecidableEq

/-- Per-site consumption policy — ONE table (audit C-1: the per-site
width-1 behaviors become declarations instead of per-site
discoveries). -/
structure SitePolicy where
  /-- Does a CONSULTATION of this site pop the stream even at bound
  ≤ 1? `true` = the consuming code pops unconditionally wherever it
  consults the site (`mapIter` genuinely consults at width 1 — §9
  flag 5, the done-check pick; `appendSpill`/`l2Entry`/`l2Arrival`
  consult only where the bound is ≥ 2 BY CONSTRUCTION — spill width
  ≥ 2 always, `.picks`/`.multi` carry ≥ 2 ready clauses — so their
  `true` transcribes the current unconditional pop exactly and is
  vacuous at 1). `false` = a bound-≤-1 consultation consumes nothing
  (the L1/L4 singleton non-consumption that sequential conservation
  depends on, formerly caller-side special cases). -/
  consumeAtOne : Bool
  /-- The canonical member at slot 0 (audit C-2's cross-site
  convention, docstring-checked): the empty/exhausted stream must
  realize the machine's default behavior at this site. -/
  canonicalSlot0 : String

/-- The policy table. Every row transcribes the pre-Q1 code's exact
behavior at its site — byte-identical streams (stage A's acceptance:
the full differential holds with zero drift). -/
def ChoiceSite.policy : ChoiceSite → SitePolicy
  | .mapIter => ⟨true,
      "first remaining candidate in cell order (stop LAST; consumed even at width 1 — memo §5 ruling Q3)"⟩
  | .appendSpill => ⟨true,
      "the growth-formula capacity (extra = 0 keeps gc's deterministic point; width ≥ 2 always)"⟩
  | .l2Entry => ⟨true,
      "first ready clause in clause order (.picks is ≥ 2 ready by construction; singleton commit is .done upstream)"⟩
  | .l2Arrival => ⟨true,
      "first waiter-extended-ready clause in clause order (.multi is ≥ 2 ready by construction)"⟩
  | .l4Waiter => ⟨false,
      "first matched waiter in goroutine order (clause order within a select); a singleton candidate pairs without a pop"⟩
  | .l1Sched => ⟨false,
      "lowest-index runnable goroutine; a sole runnable steps without a pop (sequential conservation's hinge)"⟩
  | .l5ExitWindow => ⟨false,
      "exit now (0 = teardown at main's terminal; bound is constant 2, so the flag is inert)"⟩

/-- **THE one consumption combinator** (audit Q1): every
nondeterministic point in the interpreter resolves through this, with
its census tag — which is what makes a labeled consumption trace (Q2)
and per-site enumeration policy expressible. `Choices` itself stays
`List Nat` (streams stay writable by hand and by the enumerator). -/
def Choices.consumeAt (site : ChoiceSite) (bound : Nat) (ch : Choices) :
    Nat × Choices :=
  if bound ≤ 1 ∧ !site.policy.consumeAtOne then (0, ch)
  else ch.consume bound

/-- An always-popping site's consultation is the raw pop. -/
theorem Choices.consumeAt_pop {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (h : site.policy.consumeAtOne = true) :
    Choices.consumeAt site bound ch = ch.consume bound := by
  simp [Choices.consumeAt, h]

@[simp] theorem Choices.consumeAt_mapIter {bound : Nat} {ch : Choices} :
    Choices.consumeAt .mapIter bound ch = ch.consume bound :=
  Choices.consumeAt_pop rfl

@[simp] theorem Choices.consumeAt_appendSpill {bound : Nat} {ch : Choices} :
    Choices.consumeAt .appendSpill bound ch = ch.consume bound :=
  Choices.consumeAt_pop rfl

@[simp] theorem Choices.consumeAt_l2Entry {bound : Nat} {ch : Choices} :
    Choices.consumeAt .l2Entry bound ch = ch.consume bound :=
  Choices.consumeAt_pop rfl

@[simp] theorem Choices.consumeAt_l2Arrival {bound : Nat} {ch : Choices} :
    Choices.consumeAt .l2Arrival bound ch = ch.consume bound :=
  Choices.consumeAt_pop rfl

/-- A guarded site's bound-≤-1 consultation consumes nothing (the
declared singleton non-consumption). -/
theorem Choices.consumeAt_le_one {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (hb : bound ≤ 1)
    (h : site.policy.consumeAtOne = false) :
    Choices.consumeAt site bound ch = (0, ch) := by
  simp [Choices.consumeAt, hb, h]

/-- A guarded site's bound-≥-2 consultation is the raw pop. -/
theorem Choices.consumeAt_of_lt {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (hb : 1 < bound) :
    Choices.consumeAt site bound ch = ch.consume bound := by
  simp [Choices.consumeAt, Nat.not_le_of_lt hb]

/-- One labeled consumption: which site drew, at what bound, which
slot (W3.2 slice 1 stage B — the Q2 step-event channel's atom). The
labeled trace is what a future `Fair : Choices → Prop` quantifies over
and what the membership enumerator's width metadata rides on. -/
structure PickRecord where
  site  : ChoiceSite
  bound : Nat
  pick  : Nat
  deriving Repr, BEq

/-- `Choices.consumeAt` with its pick RECORD emitted (Q2): the record
list is `[]` exactly when the consultation consumed nothing (a guarded
site at bound ≤ 1), else the singleton labeled pick — emitted BY the
consuming site, never reconstructed from the stream. -/
def Choices.consumeAtE (site : ChoiceSite) (bound : Nat) (ch : Choices) :
    Nat × Choices × List PickRecord :=
  let (p, ch') := Choices.consumeAt site bound ch
  if bound ≤ 1 ∧ !site.policy.consumeAtOne then (p, ch', [])
  else (p, ch', [⟨site, bound, p⟩])

/-- The record-emitting form projects onto `consumeAt` (the two can
never disagree on pick or stream). -/
theorem Choices.consumeAtE_fst_snd {site : ChoiceSite} {bound : Nat}
    {ch : Choices} :
    ((Choices.consumeAtE site bound ch).1,
      (Choices.consumeAtE site bound ch).2.1)
      = Choices.consumeAt site bound ch := by
  simp only [Choices.consumeAtE]
  split <;> rfl

/-- An always-popping site's record-emitting consultation, in raw-pop
terms (the proof layer's working shape at `l2Arrival`-class sites). -/
theorem Choices.consumeAtE_pop {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (h : site.policy.consumeAtOne = true) :
    Choices.consumeAtE site bound ch
      = ((ch.consume bound).1, (ch.consume bound).2,
         [⟨site, bound, (ch.consume bound).1⟩]) := by
  simp [Choices.consumeAtE, Choices.consumeAt, h]

/-- A guarded site's bound-≤-1 record-emitting consultation consumes
nothing and records nothing. -/
theorem Choices.consumeAtE_le_one {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (hb : bound ≤ 1)
    (h : site.policy.consumeAtOne = false) :
    Choices.consumeAtE site bound ch = (0, ch, []) := by
  simp [Choices.consumeAtE, Choices.consumeAt, hb, h]

/-- A guarded site's bound-≥-2 record-emitting consultation is the raw
pop plus its record. -/
theorem Choices.consumeAtE_of_lt {site : ChoiceSite} {bound : Nat}
    {ch : Choices} (hb : 1 < bound) :
    Choices.consumeAtE site bound ch
      = ((ch.consume bound).1, (ch.consume bound).2,
         [⟨site, bound, (ch.consume bound).1⟩]) := by
  have hnb : ¬ bound ≤ 1 := Nat.not_le_of_lt hb
  simp [Choices.consumeAtE, Choices.consumeAt, hnb]

def ExecState.freshLoc (state : ExecState) : Loc × ExecState :=
  let loc := Loc.base { id := state.nextAddr }
  (loc, { state with nextAddr := state.nextAddr + 1 })

def ExecState.alloc (state : ExecState) (value : GoValue) (typ : Option Ty := none) :
    Loc × ExecState :=
  let (loc, state) := state.freshLoc
  (loc, { state with heap := Heap.set state.heap loc { declaredTy := typ, value } })

def unsupported {α : Type} (feature : String) : Except GoError α :=
  throw (.unsupported feature)

def panic {α : Type} (message : String) : Except GoError α :=
  throw (.panic message)

def stuck {α : Type} (message : String) : Except GoError α :=
  throw (.stuck message)

-- `lookupLoc` deleted (reshape S4): name resolution goes through the
-- control-side `LocalEnv` (`Machine.Config.env`), never the state.
