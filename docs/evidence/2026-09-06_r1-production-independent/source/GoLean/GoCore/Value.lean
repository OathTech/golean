import GoLean.GoCore.Platform

namespace GoLean

namespace GoCore

inductive IntKind where
  | int
  | uint
  | int8
  | uint8
  | int16
  | uint16
  | int32
  | uint32
  | int64
  | uint64
  | unbounded (name : String)
  deriving Repr, BEq, Inhabited, DecidableEq

def IntKind.name : IntKind → String
  | .int => "int"
  | .uint => "uint"
  | .int8 => "int8"
  | .uint8 => "uint8"
  | .int16 => "int16"
  | .uint16 => "uint16"
  | .int32 => "int32"
  | .uint32 => "uint32"
  | .int64 => "int64"
  | .uint64 => "uint64"
  | .unbounded name => name

/-- The bit width of an integer kind on platform `p`: `int`/`uint` take
the platform's `intBits` (PINNED LATITUDE R1 — the envelope statement
lives on `gcAmd64`, `Platform.lean`); sized kinds are their own width;
untyped constants have none. -/
def IntKind.bitsAt (p : Platform) : IntKind → Option Nat
  | .int => some p.intBits
  | .uint => some p.intBits
  | .int8 => some 8
  | .uint8 => some 8
  | .int16 => some 16
  | .uint16 => some 16
  | .int32 => some 32
  | .uint32 => some 32
  | .int64 => some 64
  | .uint64 => some 64
  | .unbounded _ => none

/-- The bit width at THE pinned platform (`platform = gcAmd64`: 64-bit
`int`). -/
def IntKind.bits? : IntKind → Option Nat := IntKind.bitsAt platform

def IntKind.signed : IntKind → Bool
  | .int => true
  | .uint => false
  | .int8 => true
  | .uint8 => false
  | .int16 => true
  | .uint16 => false
  | .int32 => true
  | .uint32 => false
  | .int64 => true
  | .uint64 => false
  | .unbounded _ => true

def IntKind.normalize (kind : IntKind) (value : Int) : Int :=
  match kind.bits? with
  | none => value
  | some bits =>
      let modulus : Int := (2 : Int) ^ bits
      let wrapped := value % modulus
      if kind.signed then
        let half : Int := (2 : Int) ^ (bits - 1)
        if wrapped >= half then wrapped - modulus else wrapped
      else
        wrapped

def IntKind.isFlexible : IntKind → Bool
  | .unbounded _ => true
  | _ => false

/-- Go's floating-point kinds (floats slice F2, 2026-08-05;
`docs/2026-08-04_floats-design.md` decision 6). Unlike `IntKind` there is
no flexible/unbounded member: the frontend types every float constant
(go/types), so a float value's kind is always concrete. -/
inductive FloatKind where
  | float32
  | float64
  deriving Repr, BEq, Inhabited, DecidableEq

def FloatKind.name : FloatKind → String
  | .float32 => "float32"
  | .float64 => "float64"

def FloatKind.bits : FloatKind → Nat
  | .float32 => 32
  | .float64 => 64

/-- The width invariant's enforcement mask, exactly parallel to
`IntKind.normalize`: a stored `GoValue.float`'s bit pattern is always
`< 2^width` (design note §6; `FloatBits`' raw-encoding comparisons and
sign XORs assume it). Idempotent on well-formed patterns. -/
def FloatKind.normalizeBits (kind : FloatKind) (bits : Nat) : Nat :=
  bits % 2 ^ kind.bits

/-- Semantic function identity. The key is a canonical name produced only by
the frontend symbol map (source-level function name; receiver-scoped method
key; synthetic `F$litN` for a lifted func literal). Raw frontend names must
not construct this directly — lowering resolves them through its symbol map
and fails closed on unknown or colliding names.

Lives here rather than in `Syntax` because `GoValue.funcVal` carries it, the
same reason `TypeId` lives beside the values that carry it. -/
structure FuncId where
  key : String
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Channel direction, a STATIC type property (spec §Channel types: "A
channel may be constrained only to send or only to receive by assignment
or explicit conversion" — direction lives in the type, never in the
runtime value; the negative corpus pins direction misuse at the compile
stage via go/types). Carried on `Ty.chan` because direction is part of
type IDENTITY (a directional conversion changes the type but not the
channel), which interface boxing/asserts and `Ty.eqb` key on. -/
inductive ChanDir where
  | both
  | send
  | recv
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The sync-package primitive KINDS modeled as machine types
(spec-parity slice 2, `docs/2026-08-09_sync-package-design.md` §3; scope
D4: Mutex/RWMutex/WaitGroup/Once in — atomics/Map/Cond/Pool out, each
failing closed at the frontend). Like `ChanDir` this is a STATIC type
property: `Ty.sync kind` is the type of the sync struct, whose zero
value is the zero primitive ("The zero value for a Mutex is an unlocked
mutex"). -/
inductive SyncKind where
  | mutex
  | rwmutex
  | waitGroup
  | once
  deriving Repr, BEq, Inhabited, DecidableEq

def SyncKind.name : SyncKind → String
  | .mutex => "Mutex"
  | .rwmutex => "RWMutex"
  | .waitGroup => "WaitGroup"
  | .once => "Once"

def IntKind.compatibleResult (left right : IntKind) : Option IntKind :=
  if left == right then
    some left
  else if left.isFlexible then
    some right
  else if right.isFlexible then
    some left
  else
    none

end GoCore

/-! ## The stop grammar: `Refusal` / `Terminal` / `Stop` (design-hygiene
arc A1, 2026-09-04 — `docs/2026-09-03_grumpy-professor-review.md` §3 A1;
design note `docs/2026-09-03_hygiene-a-series-design.md` §A1)

A run that does not end `.ok` ends in exactly one of three CLASSES, and
the class is a TYPE, not a comment on a constructor:

* `Refusal` — the machine declined: nothing here is a Go behaviour.
* `Terminal` — a Go behaviour the run exhibited and stopped on (the
  differential compares these against `go run`).
* `Stop.fuelOut` — the model's budget ran out (a MODEL artifact).

The flat constructor names the code has always used (`.panic msg`,
`.stuck msg`, `.fuelOut`, …) remain valid in BOTH term and pattern
position as `@[match_pattern]` views over the nested type, so no caller
had to move; the outcome-grammar wave (review B2) retires the view. -/

/-- The three ways the MACHINE declines (none is a Go behaviour).

**THE REFUSAL RULE (design-hygiene A9, 2026-09-04) — stated once, applied
everywhere.** `unsupported` = a Go construct or behaviour the model does
not cover, reachable from a well-typed Go program: the fail-closed
FRONTIER (the differential's `unsupported` status). `stuck` = the machine
received a program, operand or plan outside the lowering contract
(ill-typed operand, malformed or unclassifiable shape, arity): a FRONTEND
bug, never Go behaviour (status `stuck`). `internal` = a machine invariant
broke between two of the machine's OWN definitions — a frame or plan the
machine itself built has a shape its consumer does not accept, a seeded
state fails its assertion, an address the allocator never handed out is
stored to: unreachable if the machine is correct (status `error`). The
test is WHO produced the offending shape: the program (→ `stuck`), the
machine (→ `internal`). Message text is diagnostic (the harness compares
STATUS); driver-level errors (`runProgramSetupM`'s missing subject /
arity) remain `stuck` pending a driver error type. -/
inductive Refusal where
  /-- A Go construct or behaviour the model does not cover, reachable from
  a well-typed Go program: the fail-closed FRONTIER. -/
  | unsupported (feature : String)
  /-- The machine received a program outside the lowering contract
  (ill-typed operand, malformed plan, arity): a FRONTEND bug. -/
  | stuck (message : String)
  /-- A machine invariant broke between two of the machine's own
  definitions: unreachable if the machine is correct. -/
  | internal (message : String)
  deriving Repr, BEq, Inhabited

/-- The Go behaviours a run can STOP on (each one an oracle-comparable
observation). -/
inductive Terminal where
  /-- A run-time panic. Inside the machine's helpers this is also the
  RECOVERABLE panic signal (`stepFn` turns a helper's `.panic` into a
  `.panicking` step); at `.stop` it is the terminal abort line. -/
  | panic (message : String)
  /-- An UNRECOVERABLE runtime throw — gc's `fatal error: <msg>` (exit
  status 2) that `recover` does NOT catch (probed: `sync: unlock of
  unlocked mutex` and the RWMutex misuse throws — runtime `fatal`, never
  a `panic()`), so it is neither `.panic` (a recover would wrongly
  intervene) nor a refusal (the behaviour is probed and deterministic).
  The message is gc's fixed string after "fatal error: ", compared on both
  sides (`expected_status: fatal`). -/
  | fatal (message : String)
  /-- Deadlock: the run reached a blocked configuration with no runnable
  goroutine, matching Go's runtime detector (`fatal error: all goroutines
  are asleep - deadlock!`, exit status 2). The message text is the
  detector's fixed line (latitude inventory row C9). -/
  | deadlock
  /-- Data race: the pool's happens-before detector found two HB-unordered
  conflicting accesses from different goroutines. Races FAIL CLOSED per
  run, deterministically given the stream; the differential oracle is
  `go run -race` (TSan; exit 66); the message is FIXED so per-stream
  refusal is choice-invariant in the harness. -/
  | raceDetected
  deriving Repr, DecidableEq, Inhabited

/-- The stop grammar: a refusal, a Go terminal, or the budget. -/
inductive Stop where
  | refusal (r : Refusal)
  | terminal (t : Terminal)
  /-- Fuel exhaustion — a MODEL artifact, not a program behaviour: the
  bounded run ended before the program did. Distinct from `.stuck` so
  interpreter-level safety can say "every run ends `.ok` or `.fuelOut`,
  never stuck/panicked" and mean it. -/
  | fuelOut
  deriving Repr, BEq, Inhabited

/-! The flat VIEW: the seven classified constructors under their historical
names, usable in patterns (`@[match_pattern]`). Term and pattern sites
throughout the machine are unchanged by A1; the nesting is what the types
say. -/

@[match_pattern] abbrev Stop.panic (message : String) : Stop := .terminal (.panic message)
@[match_pattern] abbrev Stop.fatal (message : String) : Stop := .terminal (.fatal message)
@[match_pattern] abbrev Stop.deadlock : Stop := .terminal .deadlock
@[match_pattern] abbrev Stop.raceDetected : Stop := .terminal .raceDetected
@[match_pattern] abbrev Stop.unsupported (feature : String) : Stop := .refusal (.unsupported feature)
@[match_pattern] abbrev Stop.stuck (message : String) : Stop := .refusal (.stuck message)
@[match_pattern] abbrev Stop.internal (message : String) : Stop := .refusal (.internal message)


/-! `simp` sees the view exactly as it saw the flat constructors:
injectivity and pairwise disjointness of the seven view constructors
(generated family; the nested type supplies the proofs). -/
@[simp] theorem Stop.panic_inj {a b : String} : Stop.panic a = Stop.panic b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩
@[simp] theorem Stop.fatal_inj {a b : String} : Stop.fatal a = Stop.fatal b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩
@[simp] theorem Stop.unsupported_inj {a b : String} : Stop.unsupported a = Stop.unsupported b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩
@[simp] theorem Stop.stuck_inj {a b : String} : Stop.stuck a = Stop.stuck b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩
@[simp] theorem Stop.internal_inj {a b : String} : Stop.internal a = Stop.internal b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩
@[simp] theorem Stop.panic_ne_fatal {a b : String} : (Stop.panic a = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.panic_ne_deadlock {a : String} : (Stop.panic a = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.panic_ne_raceDetected {a : String} : (Stop.panic a = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.panic_ne_unsupported {a b : String} : (Stop.panic a = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.panic_ne_stuck {a b : String} : (Stop.panic a = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.panic_ne_internal {a b : String} : (Stop.panic a = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_panic {a b : String} : (Stop.fatal a = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_deadlock {a : String} : (Stop.fatal a = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_raceDetected {a : String} : (Stop.fatal a = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_unsupported {a b : String} : (Stop.fatal a = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_stuck {a b : String} : (Stop.fatal a = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.fatal_ne_internal {a b : String} : (Stop.fatal a = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_panic {b : String} : (Stop.deadlock = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_fatal {b : String} : (Stop.deadlock = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_raceDetected : (Stop.deadlock = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_unsupported {b : String} : (Stop.deadlock = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_stuck {b : String} : (Stop.deadlock = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.deadlock_ne_internal {b : String} : (Stop.deadlock = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_panic {b : String} : (Stop.raceDetected = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_fatal {b : String} : (Stop.raceDetected = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_deadlock : (Stop.raceDetected = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_unsupported {b : String} : (Stop.raceDetected = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_stuck {b : String} : (Stop.raceDetected = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.raceDetected_ne_internal {b : String} : (Stop.raceDetected = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_panic {a b : String} : (Stop.unsupported a = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_fatal {a b : String} : (Stop.unsupported a = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_deadlock {a : String} : (Stop.unsupported a = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_raceDetected {a : String} : (Stop.unsupported a = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_stuck {a b : String} : (Stop.unsupported a = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.unsupported_ne_internal {a b : String} : (Stop.unsupported a = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_panic {a b : String} : (Stop.stuck a = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_fatal {a b : String} : (Stop.stuck a = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_deadlock {a : String} : (Stop.stuck a = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_raceDetected {a : String} : (Stop.stuck a = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_unsupported {a b : String} : (Stop.stuck a = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.stuck_ne_internal {a b : String} : (Stop.stuck a = Stop.internal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_panic {a b : String} : (Stop.internal a = Stop.panic b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_fatal {a b : String} : (Stop.internal a = Stop.fatal b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_deadlock {a : String} : (Stop.internal a = Stop.deadlock) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_raceDetected {a : String} : (Stop.internal a = Stop.raceDetected) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_unsupported {a b : String} : (Stop.internal a = Stop.unsupported b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩
@[simp] theorem Stop.internal_ne_stuck {a b : String} : (Stop.internal a = Stop.stuck b) ↔ False :=
  ⟨(fun h => nomatch h), fun h => h.elim⟩

/-- `cases_stop e` splits a `Stop` into its SEVEN flat view cases
(`unsupported`/`stuck`/`internal`/`panic`/`fatal`/`deadlock`/
`raceDetected`) plus `fuelOut` — the shape `cases e` produced before the
A1 nesting; `case panic msg => …` selects by tag suffix as before. -/
syntax "cases_stop " term : tactic
macro_rules
  | `(tactic| cases_stop $e) =>
    `(tactic| rcases $e:term with (_ | _ | _) | (_ | _ | _ | _) | _)

/-! ## The apply-boundary result (design-hygiene wave (iii), B2, 2026-09-04)

A helper that can raise a RECOVERABLE Go panic returns `Except Stop α`
and signals the panic as `.error (.panic msg)` — the same carrier the
refusals and the unrecoverable terminals use. At the APPLY BOUNDARY (the
one place a `stepFn` arm or a `Step` rule consumes a helper's outcome)
that signal is classified ONCE, by `toResult`: a value, or a panic to
deliver as an unwinding configuration (`Machine.deliver`). Refusals,
`fatal`/`deadlock`/`raceDetected` and `fuelOut` stay `Except` errors —
they have no successor configuration. The review's full route (the
`Result` monad THROUGH every helper) was measured and deferred: every
`Except Stop` signature in Ops/Machine/State and every helper lemma
(~230 sites) would move for the same one classification. -/

/-- The outcome of an apply: a value, or a recoverable Go panic (the text
of its `runtime.Error` payload). -/
inductive Result (α : Type) where
  | ok (a : α)
  | panic (msg : String)
  deriving Repr

/-- Classify a helper's outcome at the apply boundary: `.panic` becomes a
`Result.panic`; a value stays a value; every other stop propagates. -/
def toResult {α : Type} : Except Stop α → Except Stop (Result α)
  | .ok a => .ok (.ok a)
  | .error (.terminal (.panic msg)) => .ok (.panic msg)
  | .error e => .error e

@[simp] theorem toResult_ok {α : Type} {a : α} : toResult (.ok a : Except Stop α) = .ok (.ok a) := rfl

@[simp] theorem toResult_panic {α : Type} {msg : String} :
    toResult (.error (Stop.panic msg) : Except Stop α) = .ok (.panic msg) := rfl

@[simp] theorem toResult_refusal {α : Type} {r : Refusal} :
    toResult (.error (.refusal r) : Except Stop α) = .error (.refusal r) := rfl
@[simp] theorem toResult_fatal {α : Type} {msg : String} :
    toResult (.error (Stop.fatal msg) : Except Stop α) = .error (Stop.fatal msg) := rfl
@[simp] theorem toResult_deadlock {α : Type} :
    toResult (.error Stop.deadlock : Except Stop α) = .error Stop.deadlock := rfl
@[simp] theorem toResult_raceDetected {α : Type} :
    toResult (.error Stop.raceDetected : Except Stop α) = .error Stop.raceDetected := rfl
@[simp] theorem toResult_fuelOut {α : Type} :
    toResult (.error .fuelOut : Except Stop α) = .error .fuelOut := rfl

theorem toResult_error {α : Type} {e : Stop} (h : ∀ msg, e ≠ .panic msg) :
    toResult (.error e : Except Stop α) = .error e := by
  cases_stop e <;> first | rfl | exact absurd rfl (h _)

theorem toResult_eq_ok_ok {α : Type} {x : Except Stop α} {a : α} :
    toResult x = .ok (.ok a) ↔ x = .ok a := by
  cases x with
  | ok b => simp [toResult]
  | error e => cases_stop e <;> simp [toResult]

theorem toResult_eq_ok_panic {α : Type} {x : Except Stop α} {msg : String} :
    toResult x = .ok (.panic msg) ↔ x = .error (.panic msg) := by
  cases x with
  | ok b => simp [toResult]
  | error e => cases_stop e <;> simp [toResult]

theorem toResult_eq_error {α : Type} {x : Except Stop α} {e : Stop} :
    toResult x = .error e ↔ x = .error e ∧ ∀ msg, e ≠ .panic msg := by
  cases x with
  | ok b => simp [toResult]
  | error e' =>
    cases_stop e' <;> simp [toResult] <;> (intro h; subst h; simp)

/-- The `Result` of a successful classification, by cases: a value or a panic. -/
theorem toResult_cases {α : Type} {x : Except Stop α} {r : Result α}
    (h : toResult x = .ok r) :
    (∃ a, r = .ok a ∧ x = .ok a) ∨ (∃ msg, r = .panic msg ∧ x = .error (.panic msg)) := by
  cases r with
  | ok a => exact .inl ⟨a, rfl, toResult_eq_ok_ok.mp h⟩
  | panic msg => exact .inr ⟨msg, rfl, toResult_eq_ok_panic.mp h⟩

/-- The harness's status word for a refusal (the observation channel's
`status` field; `internal` reports as `error`). -/
def Refusal.status : Refusal → String
  | .unsupported _ => "unsupported"
  | .stuck _ => "stuck"
  | .internal _ => "error"

def Refusal.message : Refusal → String
  | .unsupported feature => feature
  | .stuck message => message
  | .internal message => message

/-- The harness's status word for a Go terminal. -/
def Terminal.status : Terminal → String
  | .panic _ => "panic"
  | .fatal _ => "fatal"
  | .deadlock => "deadlock"
  | .raceDetected => "race"

def Terminal.message : Terminal → String
  | .panic message => message
  | .fatal message => message
  | .deadlock => "all goroutines are asleep - deadlock!"
  | .raceDetected => "data race detected"

/-- Status per class (byte-identical to the pre-A1 flat table). -/
def Stop.status : Stop → String
  | .refusal r => r.status
  | .terminal t => t.status
  | .fuelOut => "fuel-out"

def Stop.message : Stop → String
  | .refusal r => r.message
  | .terminal t => t.message
  | .fuelOut => "GoCore execution fuel exhausted"

structure Addr where
  id : Nat
  deriving Repr, BEq, DecidableEq

/-- Semantic type identity. The key is the canonical source-level type name.
It is constructed by frontend lowering, which strips frontend name mangling
in exactly one place and fails closed on collisions between distinct
declared types; raw frontend names must not be used as type identity. The
string representation is transitional pending a compact ID table. -/
structure TypeId where
  key : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The derived `BEq` is the field's (lawful) `String` equality; recording
lawfulness lets `simp` discharge `id == id` / `id != id` goals (needed by
the self-normalization soundness proofs, sem-adequacy slice 3). -/
instance : LawfulBEq TypeId where
  eq_of_beq {a b} h := by
    obtain ⟨k1⟩ := a
    obtain ⟨k2⟩ := b
    have hk : k1 == k2 := h
    simpa using hk
  rfl {a} := by
    obtain ⟨k⟩ := a
    show (k == k) = true
    simp

/-- Strip the LEADING package qualifier — and, since the FR-19 scope
ordinal (design note `docs/2026-09-05_fr19-bug097-design.md` §2.2), the
`·N` scope marker of a function-local type — from a `TypeId` key,
matching Go's `reflect.Type.Name()`, the observation channel's naming
contract (`GoLean/CLI.lean`): `main.T` → `T`, `main.T·2` → `T`,
`main.box·1[int]` → `box[int]`. Generic instantiation keys
(`main.Pair[main.Inner]`, generics slice 2026-08-05, design note §3.4)
qualify their type ARGUMENTS inside the brackets too, and `Name()` keeps
those qualifiers (`Pair[main.Inner]`) — so only the segment BEFORE the
first `[` is touched (Go identifiers contain neither `.`, `·` nor `[`).
An anonymous-interface key (`interface{…}`) names an UNNAMED type, whose
`Name()` is `""`. For every other key (`struct{}`, `any`) the behavior is
unchanged. -/
def TypeId.unqualified (id : TypeId) : String :=
  if id.key.startsWith "interface{" then "" else
  let (head, rest) :=
    match id.key.splitOn "[" with
    | [] => (id.key, "")
    | h :: [] => (h, "")
    | h :: t => (h, "[" ++ "[".intercalate t)
  let head :=
    match head.splitOn "." with
    | [] => head
    | [_] => head
    | first :: _ => (head.drop (first.length + 1)).toString
  let head := (head.splitOn "·").headD head
  head ++ rest

/-- The POSITION of a declared type in the program's type table
(`TypeEnv := Array (TypeId × TypeDef)`, Syntax.lean; C-arc C2,
2026-09-05, gate G-C2 RULED [USER] 2026-09-04, relayed). `Ty.defined`
names a declared type by this index; the table is DEPENDENCY-ORDERED
(`TypeEnv.WellFounded`: every dependency of entry `i` sits at a smaller
index), which is what lets every type-directed recursion descend on the
index instead of on a fuel budget. The `TypeId` of the entry stays beside
it for interface identity, method-set records, and every gc-visible text
(panic messages name types by their key). -/
abbrev TypeIdx := Nat

namespace GoCore

/-- Go types. Lives here (not `Syntax.lean`) since the interfaces
campaign (S3, 2026-07-30) so `GoValue.interface` can carry its dynamic
type STRUCTURALLY — identity and typed operations on boxed values key on
canonical `Ty` equality (the Perennial `interface.mk_ok` design), never
on rendered name strings. Stays in the `GoCore` namespace (the golden
repr pins print `GoLean.GoCore.Ty.…`). -/
inductive Ty where
  | bool
  | int (kind : IntKind := IntKind.int)
  | float (kind : FloatKind)
  | string
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | map (key value : Ty)
  /-- A channel type `chan T` / `chan<- T` / `<-chan T` (channels arc
  slice 1, `docs/2026-08-06_channels-arc-design.md` D7). Direction is
  part of type identity; the runtime value (`GoValue.chan`) carries only
  the reference. -/
  | chan (dir : ChanDir) (elem : Ty)
  | pointer (elem : Ty)
  /-- A function type. Structural detail is carried for zero values,
  typing and TYPE IDENTITY (assert/boxing compare it structurally) —
  dispatch is by `FuncId`, never by this. `variadic` is the identity
  half spec#Type_identity adds beyond the param/result lists ("either
  both functions are variadic or neither is"): the variadic parameter's
  TYPE is `[]T` on both sides, so without the bit `func(...int)` and
  `func([]int)` are indistinguishable (BUG-067). -/
  | funcType (params results : List Ty) (variadic : Bool)
  | interface (id : TypeId)
  /-- A DECLARED type, by its position in the program's type table
  (`TypeIdx`; C2). Identity is positional: two `Ty.defined` are the same
  Go type iff they name the same entry — a `Program` is a constant, so
  positions are as stable as the names were. The entry's `TypeId` is
  read back for texts and records (`TypeEnv.nameOf?`). -/
  | defined (idx : TypeIdx)
  | unsupported (feature : String)
  /-- A sync-package primitive type (`sync.Mutex` / `sync.RWMutex` /
  `sync.WaitGroup` / `sync.Once`; spec-parity slice 2, design note §3).
  Zero value = the zero primitive (`GoValue.syncData`). Appended at the
  END of the inductive so positional case tags stay stable. -/
  | sync (kind : GoCore.SyncKind)
  deriving Repr, Inhabited

/-! **Why `Ty` does NOT `deriving BEq`** (quorum pilot phase 4,
2026-07-31). `Ty` is a NESTED inductive (`funcType` carries `List Ty`), and
for nested inductives Lean's `deriving BEq` emits an **opaque** equality
function — no equation lemmas, no `unfold`, no `decide`, not even `rfl` on
two syntactically identical closed types. Dynamic-type identity is decided
by `==` on `Ty` (`concreteMethodForDynamic?`, `typeAssert`, boxing,
interface satisfaction), so with the derived instance **no dispatch fact
was kernel-provable at all** — every interface WP law would have had an
undischargeable premise. (It is also a `partial`-flavoured definition
sitting in the semantic core, which the "proof-facing code is total"
contract does not want.) The replacement is an ordinary total, transparent
STRUCTURAL equality: a mutual block over `Ty` and the nested `List Ty`
(C2, 2026-09-05 — it was fuel-bounded at 1024 and failed closed on
exhaustion until Lean's structural recursion over nested inductives made
the fuel unnecessary; kernel-reducible, `decide`/`rfl` both work). -/
mutual

def Ty.eqb : Ty → Ty → Bool
  | .bool, .bool => true
  | .int k₁, .int k₂ => k₁ == k₂
  | .float k₁, .float k₂ => k₁ == k₂
  | .string, .string => true
  | .array n₁ e₁, .array n₂ e₂ => n₁ == n₂ && Ty.eqb e₁ e₂
  | .slice e₁, .slice e₂ => Ty.eqb e₁ e₂
  | .map k₁ v₁, .map k₂ v₂ => Ty.eqb k₁ k₂ && Ty.eqb v₁ v₂
  | .chan d₁ e₁, .chan d₂ e₂ => d₁ == d₂ && Ty.eqb e₁ e₂
  | .pointer e₁, .pointer e₂ => Ty.eqb e₁ e₂
  | .funcType p₁ r₁ v₁, .funcType p₂ r₂ v₂ =>
      v₁ == v₂ && Ty.eqbList p₁ p₂ && Ty.eqbList r₁ r₂
  | .interface a, .interface b => a == b
  | .defined a, .defined b => a == b
  | .unsupported a, .unsupported b => a == b
  | .sync a, .sync b => a == b
  | _, _ => false

/-- Pairwise `Ty.eqb` over the nested parameter/result lists. -/
def Ty.eqbList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.eqb a b && Ty.eqbList as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.eqb⟩

/-- Structural rendering of a (canonical) dynamic type for the
OBSERVATION channel only — identity never keys on this (S3). Named types
render UNQUALIFIED, like the struct `typeName` field beside them: the
observation channel's stated contract is `reflect.Type.Name()`, and the
qualified spelling contradicted it inside a single JSON object
(pre-merge audit 2026-07-31, finding 12). `nameOf` reads a declared
type's key back from the type table (`TypeEnv.nameOf?`, defined
downstream); an index the table does not have renders as a VISIBLE
marker, never as a guessed name (unreachable on a decoded program). -/
def Ty.dynamicName (nameOf : TypeIdx → Option TypeId) : Ty → String
  | .bool => "bool"
  | .int kind => kind.name
  | .float kind => kind.name
  | .string => "string"
  | .defined idx =>
      match nameOf idx with
      | some id => id.unqualified
      | none => s!"<unknown type index {idx}>"
  | .interface id => id.unqualified
  | .pointer e => "*" ++ Ty.dynamicName nameOf e
  | .slice e => "[]" ++ Ty.dynamicName nameOf e
  | .array n e => s!"[{n}]" ++ Ty.dynamicName nameOf e
  | .map k v => s!"map[{Ty.dynamicName nameOf k}]{Ty.dynamicName nameOf v}"
  -- reflect renders direction exactly this way ("chan int",
  -- "<-chan int", "chan<- int").
  | .chan .both e => "chan " ++ Ty.dynamicName nameOf e
  | .chan .send e => "chan<- " ++ Ty.dynamicName nameOf e
  | .chan .recv e => "<-chan " ++ Ty.dynamicName nameOf e
  | .funcType _ _ _ => "func"
  | .unsupported f => s!"<unsupported {f}>"
  -- reflect.Type.Name() on sync.Mutex is "Mutex" (package-unqualified,
  -- the observation channel's contract).
  | .sync kind => kind.name

end GoCore

inductive Loc where
  | base (addr : Addr)
  | field (base : Loc) (typeId : TypeId) (fieldName : String)
  | index (base : Loc) (index : Int)
  deriving Repr, BEq, DecidableEq

/-- The derived `BEq Addr` is the field's `Nat` equality — lawful. Needed
so address disequalities (an allocation at the FRESH address leaves every
bounded lookup unchanged — `Heap.lookup_push_ne`) are provable
(∀-choices kit, sem-adequacy slice 3). -/
instance : LawfulBEq Addr where
  eq_of_beq {a b} h := by
    obtain ⟨i⟩ := a
    obtain ⟨j⟩ := b
    have hij : i == j := h
    simpa using hij
  rfl {a} := by
    obtain ⟨i⟩ := a
    show (i == i) = true
    simp

/-- Lawfulness of the derived `BEq Loc` (componentwise from `Addr`/
`TypeId`/`String`/`Int`) — same motivation as `LawfulBEq Addr` above. -/
instance : LawfulBEq Loc where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b
    case base.base x y =>
      have hx : x == y := h
      simp [eq_of_beq hx]
    case field.field ba ta fa ih bb tb fb =>
      have h' : (ba == bb && (ta == tb && fa == fb)) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨h1, h2, h3⟩ := h'
      simp [ih h1, eq_of_beq h2, eq_of_beq h3]
    case index.index ba ia ih bb ib =>
      have h' : (ba == bb && ia == ib) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨h1, h2⟩ := h'
      simp [ih h1, eq_of_beq h2]
    all_goals exact Bool.noConfusion (h : false = true)
  rfl {a} := by
    induction a
    case base x =>
      show (x == x) = true
      simp
    case field b t f ih =>
      show (b == b && (t == t && f == f)) = true
      simp [ih]
    case index b i ih =>
      show (b == b && i == i) = true
      simp [ih]

structure SliceValue where
  base : Option Loc
  offset : Nat
  len : Nat
  cap : Nat
  deriving Repr, BEq

structure MapValue where
  base : Option Loc
  deriving Repr, BEq

/-- A channel REFERENCE (channels arc slice 1, the `MapValue` precedent):
`base` addresses the `HeapCell.chanPayload` cell; `none` is the nil
channel. Channel `==` is reference identity (spec: "equal if they were
created by the same call to `make` or if both have value `nil`") — the
derived `BEq` (base equality) IS that relation, which is also why
channels are valid map keys. Direction is NOT here: it is a static type
property (`Ty.chan`), and a directional conversion returns the same
reference. -/
structure ChanValue where
  base : Option Loc
  deriving Repr, BEq

/-- The runtime STATE of a sync-package primitive (spec-parity slice 2,
design note §§3-4). Sync structs are Go VALUES — probe p10: a copy of a
locked mutex carries the locked state and the runtime detects nothing —
so the state lives in the heap cell where the variable lives (no
reference cell, no registry), and struct copies copy it, exactly gc.
Every scalar here is state gc itself keeps in its state words:
`pendingW` (blocked write-lockers) realizes the DOCUMENTED
writer-exclusion of new readers (rwmutex.go: "a blocked Lock call
excludes new readers from acquiring the lock"); `waiters` (parked
Wait callers) mirrors gc's state-word wait count — reset by the
zeroing Add exactly as gc's `wg.state.Store(0)` (waitgroup.go:134-135;
its consumers are the wg-sema race pair's first-waiter condition and
the wake bookkeeping — the Add-side misuse panic gc guards with it is
unreachable at registry granularity and carries no arm here). NO waiter queues, no identities, no order — the
blocked goroutines themselves are `Config.blockedSync` shapes. -/
inductive SyncPrim where
  | mutex (locked : Bool)
  | rwmutex (writer : Bool) (readers : Nat) (pendingW : Nat)
  | waitGroup (counter : Int) (waiters : Nat)
  | once (started : Bool) (done : Bool)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The zero value of a sync kind ("The zero value for a Mutex is an
unlocked mutex" — and likewise for the other three). -/
def GoCore.SyncKind.zero : GoCore.SyncKind → SyncPrim
  | .mutex => .mutex false
  | .rwmutex => .rwmutex false 0 0
  | .waitGroup => .waitGroup 0 0
  | .once => .once false false

/-- The kind a primitive's state belongs to (the normalizer's
kind-compatibility check). -/
def SyncPrim.kind : SyncPrim → GoCore.SyncKind
  | .mutex _ => .mutex
  | .rwmutex _ _ _ => .rwmutex
  | .waitGroup _ _ => .waitGroup
  | .once _ _ => .once

structure GoString where
  bytes : Array UInt8
  deriving Repr, BEq

namespace GoString

def empty : GoString :=
  { bytes := #[] }

def fromLeanString (value : String) : GoString :=
  { bytes := value.toUTF8.data }

def replacementRune : GoString :=
  { bytes := #[0xef, 0xbf, 0xbd] }

def utf8Byte (value : Nat) : UInt8 :=
  UInt8.ofNat value

def fromCodePointNat (code : Nat) : GoString :=
  if code <= 0x7f then
    { bytes := #[utf8Byte code] }
  else if code <= 0x7ff then
    { bytes := #[
        utf8Byte (0xc0 + code / 0x40),
        utf8Byte (0x80 + code % 0x40)
      ] }
  else if code <= 0xffff then
    if 0xd800 <= code && code <= 0xdfff then
      replacementRune
    else
      { bytes := #[
          utf8Byte (0xe0 + code / 0x1000),
          utf8Byte (0x80 + (code / 0x40) % 0x40),
          utf8Byte (0x80 + code % 0x40)
        ] }
  else if code <= 0x10ffff then
    { bytes := #[
        utf8Byte (0xf0 + code / 0x40000),
        utf8Byte (0x80 + (code / 0x1000) % 0x40),
        utf8Byte (0x80 + (code / 0x40) % 0x40),
        utf8Byte (0x80 + code % 0x40)
      ] }
  else
    replacementRune

def fromCodePoint (code : Int) : GoString :=
  if code < 0 then
    replacementRune
  else
    fromCodePointNat code.toNat

def append (left right : GoString) : GoString :=
  { bytes := left.bytes ++ right.bytes }

def length (value : GoString) : Nat :=
  value.bytes.size

def byte? (value : GoString) (index : Nat) : Option UInt8 :=
  value.bytes[index]?

def slice (value : GoString) (low high : Nat) : GoString :=
  { bytes := value.bytes.extract low high }

def compareAt (left right : Array UInt8) (index : Nat) : Ordering :=
  match hl : left[index]?, right[index]? with
  | some l, some r =>
      if l.toNat < r.toNat then
        .lt
      else if r.toNat < l.toNat then
        .gt
      else
        have : index < left.size := (Array.getElem?_eq_some_iff.mp hl).1
        compareAt left right (index + 1)
  | none, some _ => .lt
  | some _, none => .gt
  | none, none => .eq
termination_by left.size - index

def compare (left right : GoString) : Ordering :=
  compareAt left.bytes right.bytes 0

def byteNats (value : GoString) : Array Nat :=
  value.bytes.map (fun b => b.toNat)

end GoString

inductive GoValue where
  | unit
  | bool (value : Bool)
  | int (value : Int) (kind : GoCore.IntKind := .int)
  /-- An IEEE-754 float as its BIT PATTERN (floats slice, design note
  decision 6): `bits < 2^kind.bits`, enforced by
  `FloatKind.normalizeBits` at every construction/normalization site.
  Semantics of the pattern live in `GoCore/FloatBits.lean`. NOTE the
  three equalities (note §4): Go `==` is `valueEq`'s IEEE arm
  (NaN ≠ NaN, +0 == -0); `GoValue.eqb` below is BIT equality
  (proof/infrastructure identity, never Go `==`). -/
  | float (bits : Nat) (kind : GoCore.FloatKind)
  | string (value : GoString)
  | addr (loc : Loc)
  | nil
  /-- An interface box: the CANONICAL dynamic type (aliases resolved at
  box time, defined-type identity kept — `checkedDynamicTy`) plus the
  boxed value. Identity comparisons, type asserts, method dispatch, and
  equality-at-dynamic-type all key on `dynamic` structurally (interfaces
  campaign S3, 2026-07-30; was a rendered `String`). A nil interface is
  `GoValue.nil`, never a box. -/
  | interface (dynamic : GoCore.Ty) (value : GoValue)
  | struct (typeId : TypeId) (fields : Array (String × GoValue))
  | array (values : Array GoValue)
  | slice (value : SliceValue)
  | map (value : MapValue)
  /-- A channel reference (channels arc slice 1; the `map` precedent). -/
  | chan (value : ChanValue)
  /-- A **function value**: the callee's semantic identity plus the values
  captured at closure-creation time. Closures are lambda-lifted by the
  frontend (`docs/2026-07-24_sequential-coverage-scoping.md` §8), so the
  captured values are the ADDRESSES of the captured variables — Go captures
  by reference, and making that explicit here is what keeps two closures
  over one variable sharing it. Method values and (later) deferred calls use
  the same shape. The zero value of a func type is `nil`, not this. -/
  | funcVal (fid : GoCore.FuncId) (captured : List GoValue)
  /-- A sync-package primitive's state, living in the cell where the
  sync struct lives (spec-parity slice 2, design note §3 — the VALUE
  model: copies carry state, probe p10). Contains no locations. -/
  | syncData (p : SyncPrim)
  deriving Repr


/-! ## Structural `GoValue` equality (arc-final audit, 2026-08-04)

`GoValue` is a NESTED inductive (arrays/lists of itself), so `deriving
BEq` compiles to a `partial`-class OPAQUE stub — a constant whose LOGICAL
value is an arbitrary inhabitant (`fun _ _ => default`), even though its
COMPILED behavior is real structural equality. That is the worst shape
for this project: the differential validates the compiled function while
theorems quantify the logical one, and at any semantic use the two can
disagree (found at `renderPanicHead`'s recovered-collapse check; same
class `Ty.eqb` fixed for `Ty` in the interfaces campaign, whose recipe
this mirrors). The replacement is total, transparent, STRUCTURAL — a
mutual block over `GoValue` and its nested element/field lists, the
arrays destructured in the patterns (C2, 2026-09-05; it was fuel-bounded
at 1024 and failed closed on exhaustion until then) — kernel-reducible,
and it agrees with the derived instance's compiled behavior on every
value a program can build. -/

/-- Pairwise equality over a list with an element comparator (kept for
the map-payload triples and the heap-cell comparators of `StateEqb.lean`,
which compare OUTSIDE `GoValue`'s own recursion). -/
def GoValue.eqbListWith (f : GoValue → GoValue → Bool) :
    List GoValue → List GoValue → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && GoValue.eqbListWith f as bs
  | _, _ => false

/-- Pairwise equality over stamped map entries (id, key, value) — the
map payload cell's (`HeapCell.mapPayload`, A3). -/
def GoValue.eqbTriplesWith (f : GoValue → GoValue → Bool) :
    List (Nat × GoValue × GoValue) → List (Nat × GoValue × GoValue) → Bool
  | [], [] => true
  | (i₁, k₁, v₁) :: as, (i₂, k₂, v₂) :: bs =>
      i₁ == i₂ && f k₁ k₂ && f v₁ v₂ && GoValue.eqbTriplesWith f as bs
  | _, _ => false

/-- Pairwise equality over named fields. -/
def GoValue.eqbFieldsWith (f : GoValue → GoValue → Bool) :
    List (String × GoValue) → List (String × GoValue) → Bool
  | [], [] => true
  | (n₁, v₁) :: as, (n₂, v₂) :: bs =>
      n₁ == n₂ && f v₁ v₂ && GoValue.eqbFieldsWith f as bs
  | _, _ => false

mutual

/-- Structural `GoValue` equality — THE `BEq GoValue` instance (replacing
the logically-opaque derived one). -/
def GoValue.eqb : GoValue → GoValue → Bool
  | .unit, .unit => true
  | .bool a, .bool b => a == b
  | .int v₁ k₁, .int v₂ k₂ => v₁ == v₂ && k₁ == k₂
  -- BIT equality on purpose (note §4): NaN == NaN at identical bits,
  -- +0 ≠ -0 — structural identity, never Go's ==.
  | .float b₁ k₁, .float b₂ k₂ => b₁ == b₂ && k₁ == k₂
  | .string a, .string b => a == b
  | .addr a, .addr b => a == b
  | .nil, .nil => true
  | .interface t₁ v₁, .interface t₂ v₂ =>
      GoCore.Ty.eqb t₁ t₂ && GoValue.eqb v₁ v₂
  | .struct id₁ ⟨fs₁⟩, .struct id₂ ⟨fs₂⟩ =>
      id₁ == id₂ && GoValue.eqbFieldList fs₁ fs₂
  | .array ⟨a⟩, .array ⟨b⟩ => GoValue.eqbList a b
  | .slice a, .slice b => a == b
  | .map a, .map b => a == b
  | .chan a, .chan b => a == b
  | .funcVal id₁ c₁, .funcVal id₂ c₂ =>
      id₁ == id₂ && GoValue.eqbList c₁ c₂
  | .syncData a, .syncData b => a == b
  | _, _ => false

/-- Pairwise `GoValue.eqb` over element lists (array elements, closure
captures). -/
def GoValue.eqbList : List GoValue → List GoValue → Bool
  | [], [] => true
  | a :: as, b :: bs => GoValue.eqb a b && GoValue.eqbList as bs
  | _, _ => false

/-- Pairwise `GoValue.eqb` over named struct fields. -/
def GoValue.eqbFieldList : List (String × GoValue) → List (String × GoValue) → Bool
  | [], [] => true
  | (n₁, a) :: as, (n₂, b) :: bs => n₁ == n₂ && GoValue.eqb a b && GoValue.eqbFieldList as bs
  | _, _ => false

end

instance : BEq GoValue := ⟨GoValue.eqb⟩

namespace GoCore

abbrev Value := GoValue

end GoCore
end GoLean
