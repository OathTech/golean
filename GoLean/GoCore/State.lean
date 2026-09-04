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

/-- A heap cell (design-hygiene arc A3, 2026-09-04; review §3 A3): either a
Go VALUE at its declared type, or one of the two runtime PAYLOADS a value
may only reference — a map's entry table or a channel's buffer. The
payloads used to be `GoValue` constructors "no expression may produce";
the cell type now says so: `loadLoc`/`storeLoc` see values only (a payload
cell refuses there), `mapPayload?`/`storeMapPayload` and
`chanPayload?`/`storeChanPayload` see payloads only, and every STORE to a
value cell is normalized at its declared type (there are no untyped cells
— `Stmt.allocNew` always carries its type). The one hole, pre-existing and
byte-identical to the pre-A3 machine: ALLOCATION does not normalize —
`.allocNew`'s `s.alloc value typ` (Machine.lean) creates the value cell with
the evaluated value as is; the first store through it normalizes. -/
inductive HeapCell where
  /-- A Go value at the cell's declared type; stores normalize to it. -/
  | value (declaredTy : Ty) (v : GoValue)
  /-- A MAP's payload cell (design-hygiene A3: a cell, never a value — no
  expression can produce one): the
  live entries in CELL ORDER, each stamped with an ENTRY IDENTITY `id`
  (design-hygiene arc slice 1, B1 / the second audit's Q11, 2026-09-03),
  plus the per-map counter `nextId` the next created entry takes. An
  entry's id is allotted once, at creation (`mapAssignValue` on an absent
  key), kept across value updates of the same key (E10 always-replace
  keeps the id), and NEVER reused — deletion and `clear` erase entries
  but leave `nextId` where it is, so a deleted-then-re-created key is a
  NEW entry with a fresh id (the adopted reading of the range clause's
  created-entries sentence, `docs/spec-interpretations.md` I-1 / ledger
  L-012). Ids are the `mapIterK` frame's iteration state (which entries
  it has produced; which were live when the range began) — pure `Nat`
  membership, so a delete is a heap write and nothing else. Ids are
  runtime-internal identity: never observable, never on any wire (the
  observation JSON projects them away). The counter is PER MAP (not a
  global `ExecState` field) so the map representation change touches no
  state field and `StateWf` sees only the entry payloads. -/
  | mapPayload (entries : Array (Nat × GoValue × GoValue)) (nextId : Nat)
  /-- A CHANNEL's payload cell (the `mapPayload` precedent): the buffered
  elements in FIFO order (spec: "Channels act as first-in-first-out
  queues" — deterministic, strict lane), the buffer capacity (`cap = 0` ⟺
  unbuffered — ONE spec rule, not two channel kinds), and the closed flag.
  NO waiter queues (design of record D7): blocked goroutines are
  blocked-Config shapes, never channel state. -/
  | chanPayload (buf : Array GoValue) (capacity : Nat) (closed : Bool)
  deriving Repr, BEq

/-- The heap: a DENSE array of cells — an address IS an index
(design-hygiene arc A2, 2026-09-04; review §3 A2). `Loc.base ⟨i⟩` names
cell `i`; `ExecState.alloc` is `push`, so every address below the size has
a cell BY TYPE and the allocator's next address is the size. There is no
way to write a cell that does not exist: `storeLoc` refuses out of range
(BUG-085's phantom-materialization arm is unrepresentable — `Array.set`
carries its bounds proof). -/
abbrev Heap := Array HeapCell
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
  heap : Heap := #[]
  deriving Repr, BEq

/-- The allocator's NEXT address = the heap's size (dense heap, A2). A
derived quantity, not a field: it cannot drift from the heap. -/
def ExecState.nextAddr (state : ExecState) : Nat := state.heap.size

/-- The driver's READOUT: the subject's result values at its terminal
(renamed from `Result` in wave (iii) — `Result` is now the apply-boundary
outcome, Value.lean). -/
structure Readout where
  values : Array GoValue
  deriving Repr, BEq

/-- Statement-execution outcome classification. Survives the reshape S4
deletion because the Surface layer's `execStmt`-SHAPED wrapper (F4 §2's
decided interface, restored at R3) reproduces the old signature
`… → Except Stop (ExecOutcome × Choices)` over iterated `stepFn`. -/
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

/-- The cell at a ROOT address (`.base ⟨i⟩` ↦ `heap[i]?`); a field/index
path is not a heap key (`loadLoc`/`storeLoc` resolve paths to their root
first), so it has no cell. -/
def Heap.lookup (h : Heap) : Loc → Option HeapCell
  | .base ⟨i⟩ => h[i]?
  | _ => none

/-- A found root address is in range (the dense heap's bounds proof, used
by `storeLoc`'s `Array.set`). -/
theorem Heap.lookup_lt {h : Heap} {a : Addr} {c : HeapCell}
    (hl : Heap.lookup h (.base a) = some c) : a.id < h.size := by
  obtain ⟨i⟩ := a
  simp only [Heap.lookup] at hl
  exact (Array.getElem?_eq_some_iff.mp hl).1

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
    (value : GoValue) : Except Stop (Array (String × GoValue)) := do
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
constructor here plus a `ChoiceSite.policy` row, its consult in the
machine's own consumption projection (`seqConsumption`/`poolConsumption`,
Machine.lean/Multi.lean — since wave (iii) B8 the ONE account of where the
stream is consulted; the theorem `stepFn_consumption_*` breaks loudly on an
unaccounted arm), and the site's envelope statement in situ — the
doc-resident census sweeps (nondeterminism doctrine preamble, latitude
inventory §0) are retired by this type's exhaustiveness and now point here.

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
* `postOp`       — the post-op scheduling point at a registry-op
                   COMPLETION (W3.2 slice 1 stage C, B1 — G1 ruling
                   2026-08-20): the `.opDone` marker boundary
                   (`Config.opDone`, Machine.lean — the envelope
                   statement lives at the marker; consumed in
                   `stepMulti` via `schedSlots`).
* `backEdge`     — the preemption point at a loop back-edge (W3.2
                   slice 1 stage D, B2 — G1 ruling 2026-08-20): the
                   loop re-entry shapes `.next/.continuing (.loop …)`
                   and `.next (.mapIterK …)` are boundaries
                   (`Config.atBoundary`, Multi.lean — the envelope
                   statement lives there; consumed in `stepMulti` via
                   `schedSlots`, issuer-first like postOp).
* `nilValueMethodText` — the run-time panic TEXT when a VALUE-receiver
                   method is dispatched through an interface holding a
                   nil `*T` (BUG-087, [USER] ruling 2026-09-03 «demonic
                   choice so both are admitted», relayed — record in
                   `docs/2026-08-31_qrow-rulings.md`): gc realizes two
                   `runtime.Error` texts for ONE source, decided by its
                   optimizer (devirtualized deref → the nil-dereference
                   text; the autogenerated `(*T).M` wrapper →
                   `panicwrap`'s `value method <pkg>.<T>.<M> called
                   using nil *<T> pointer`). Width 2 exactly on the
                   wrapper family — `nilValueMethodText?` (Ops.lean:
                   the envelope statement, beside the nil arm of
                   `dynamicDispatch?`) — else a bound-1 consult that
                   pops nothing; consumed in `enterFramePick`
                   (Machine.lean) — THE one frame-entry funnel with the
                   stream in hand (B2), shared by every `stepFn` entry
                   arm and the `go`-statement entry `spawnStep`.
* `tryLock`      — TryLock/TryRLock's spurious-failure member
                   (Q-TRYLOCK, RULED [USER] 2026-08-31 row 5, implemented
                   2026-09-03): `applySyncOp`'s try-head arm, Machine.lean
                   — the envelope statement lives at `applyTryLock`.
                   Width 2 at an ACQUIRABLE cell (slot 0 = acquire, slot
                   1 = mem#locks' "may be considered to be able to
                   return false even when the mutex l is unlocked"),
                   bound 1 (no pop) at a held cell. A DATA pick, not a
                   scheduling pick.

The scheduling sites — what a future `Fair : Choices → Prop`
quantifies over — are exactly
`{l1Sched, l5ExitWindow, postOp, backEdge}`. -/
inductive ChoiceSite where
  | mapIter | appendSpill
  | l2Entry | l2Arrival | l4Waiter
  | l1Sched | l5ExitWindow
  | postOp
  | backEdge
  | nilValueMethodText
  | tryLock
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
  | .postOp => ⟨false,
      "the ISSUER continues (slot 0 = the goroutine that completed the op — the old machine's schedule, so the empty/default stream reproduces it exactly; slots 1.. = the other runnables in goroutine order; a sole-runnable issuer consults at bound 1 without a pop — sequential conservation's hinge, as at l1Sched)"⟩
  | .tryLock => ⟨false,
      "ACQUIRE (slot 0 = the success member — gc's realized point, so the empty/default stream reproduces gc's always-succeeds behavior and the strict lane's uncontended TryLock matches the oracle; slot 1 = mem#locks' spurious false: no state change, no HB edge); a HELD cell consults at bound 1 without a pop (the failure is forced, not chosen — a data site, not a scheduling one)"⟩
  | .backEdge => ⟨false,
      "the CURRENT goroutine continues (slot 0 = the looping goroutine — the old machine's schedule; slots 1.. = the other runnables in goroutine order; sole-runnable loops consult at bound 1 without a pop). THE FAIRNESS-EXPRESSIBILITY NOTE (boundary-set note §4, G1): this site is what makes a future Fair : stream → Prop NON-VACUOUS — a registry-free monopolist now OFFERS a scheduling pick at every iteration, so 'every goroutine runnable at infinitely many scheduling picks is picked at infinitely many' genuinely forces the partner to run; without it the liveness tier's fairness hypothesis would be unsatisfiable on exactly the spinner shapes it exists for"⟩
  | .nilValueMethodText => ⟨false,
      "the nil-dereference text `runtime error: invalid memory address or nil pointer dereference` (slot 0 = the pre-BUG-087 machine's only member, gc's default-build text on the devirtualized shapes; slot 1 = gc's panicwrap text `value method <pkg>.<T>.<M> called using nil *<T> pointer`, its text through the autogenerated wrapper — same source, `-gcflags=-l`); bound is 2 exactly on the wrapper family (nilValueMethodText? = some), 1 elsewhere, and a bound-1 consult pops nothing — every non-family frame entry consumes exactly as before"⟩

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

/-- Allocate a fresh cell: the new address is the heap's size and the
cell is pushed (dense heap, A2 — the ONLY way a cell comes to exist). -/
def ExecState.allocCell (state : ExecState) (cell : HeapCell) : Loc × ExecState :=
  (.base ⟨state.heap.size⟩, { state with heap := state.heap.push cell })

/-- Allocate a VALUE cell at its declared type. -/
def ExecState.alloc (state : ExecState) (value : GoValue) (typ : Ty) : Loc × ExecState :=
  state.allocCell (.value typ value)

/-- Overwrite root cell `a` through `f` (which sees the old cell), FAIL
CLOSED out of range: `.internal` (BUG-085 — an unallocated address is an
invariant breach, never Go behaviour). The ONE write path for every root
cell (`storeLoc`, `storeMapPayload`, `storeChanPayload`); `Array.set` under
`hi` is what makes a phantom cell unrepresentable (A2/A3). -/
def ExecState.updateCell (state : ExecState) (a : Addr)
    (f : HeapCell → Except Stop HeapCell) : Except Stop ExecState :=
  if hi : a.id < state.heap.size then do
    let cell ← f state.heap[a.id]
    return { state with heap := state.heap.set a.id cell hi }
  else
    throw (.internal s!"store to unallocated address {repr (Loc.base a)}: no heap cell (allocation goes through ExecState.alloc only)")

def unsupported {α : Type} (feature : String) : Except Stop α :=
  throw (.unsupported feature)

def panic {α : Type} (message : String) : Except Stop α :=
  throw (.panic message)

def stuck {α : Type} (message : String) : Except Stop α :=
  throw (.stuck message)

/-! ## Payload cells (A3): the map/channel readers and writers -/

/-- The map payload at a root cell: `(entries, nextId)`. Anything else
there (a value cell, a channel, no cell) is an ill-shaped program
operand — refused. -/
def mapPayload? (state : ExecState) (loc : Loc) :
    Except Stop (Array (Nat × GoValue × GoValue) × Nat) :=
  match Heap.lookup state.heap loc with
  | some (.mapPayload entries nextId) => return (entries, nextId)
  | some (.value _ v) => stuck s!"expected map data at {repr loc}, got value {repr v}"
  | some (.chanPayload ..) => stuck s!"expected map data at {repr loc}, got channel data"
  | none => stuck s!"unbound GoCore heap location: {repr loc}"

/-- The channel payload at a root cell: `(buf, capacity, closed)`. -/
def chanPayload? (state : ExecState) (loc : Loc) :
    Except Stop (Array GoValue × Nat × Bool) :=
  match Heap.lookup state.heap loc with
  | some (.chanPayload buf capacity closed) => return (buf, capacity, closed)
  | some (.value _ v) => stuck s!"expected channel data at {repr loc}, got value {repr v}"
  | some (.mapPayload ..) => stuck s!"expected channel data at {repr loc}, got map data"
  | none => stuck s!"unbound GoCore heap location: {repr loc}"

/-- Replace a map payload WHOLE (the only way a map cell is written); the
cell must already be a map payload. -/
def storeMapPayload (state : ExecState) (loc : Loc)
    (entries : Array (Nat × GoValue × GoValue)) (nextId : Nat) :
    Except Stop ExecState :=
  match loc with
  | .base a =>
      state.updateCell a fun
        | .mapPayload _ _ => pure (.mapPayload entries nextId)
        | .value _ v => stuck s!"expected map data at {repr loc}, got value {repr v}"
        | .chanPayload .. => stuck s!"expected map data at {repr loc}, got channel data"
  | other => stuck s!"map payload store through a non-root path {repr other}"

/-- Replace a channel payload WHOLE; the cell must already be a channel
payload. -/
def storeChanPayload (state : ExecState) (loc : Loc) (buf : Array GoValue)
    (capacity : Nat) (closed : Bool) : Except Stop ExecState :=
  match loc with
  | .base a =>
      state.updateCell a fun
        | .chanPayload .. => pure (.chanPayload buf capacity closed)
        | .value _ v => stuck s!"expected channel data at {repr loc}, got value {repr v}"
        | .mapPayload .. => stuck s!"expected channel data at {repr loc}, got map data"
  | other => stuck s!"channel payload store through a non-root path {repr other}"

-- `lookupLoc` deleted (reshape S4): name resolution goes through the
-- control-side `LocalEnv` (`Machine.Config.env`), never the state.
