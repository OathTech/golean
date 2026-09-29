import GoLean.GoCore.Ops
import GoLean.GoCore.Unseq

/-!
# The fine-grained machine (reshape R1, `docs/2026-07-23_reshape-r1r2-machine-design.md`)

Expression evaluation **in the configuration language**: this module replaces
the big-step `ExprR` premise style of `Rel.lean` (which it will retire at
stage S4, per the F4 deletion directive) with a machine whose atomic steps
are at memory-operation granularity — the prerequisite for honest
goroutine interleaving (BUG-002).

Design highlights (full rationale in the design note):

- **`evalE`/`retV` configurations**: evaluating an expression, delivering a
  value to the innermost continuation frame. Every frame receives operands
  through one uniform rule shape.
- **One generic strict-operator frame** (`Cont.strictK`) instead of one
  frame per operator: `strictPlan` classifies an expression into a
  defunctionalized head (`StrictOp`) plus its operand list, and
  `applyStrictOp` — a total function shared verbatim with the executable
  `stepFn` — computes the result. The relation's `enter`/`shift`/`apply`
  rules are generic over the op table, so the relation and the interpreter
  are literally one semantics, instantiated (the differential oracle
  validates the shared table; the *claims* surface stays scoped by which WP
  laws and witnesses exist).
- **Panic is unwinding, not teleport** (the unwinding arc,
  `docs/2026-07-25_unwinding-arc.md`): a panic step starts a `.panicking`
  configuration carrying the panic CHAIN, which strips continuation
  frames one step at a time, runs each frame's defers on the way out
  (where `recover` can cancel it), and an unrecovered chain reaching
  `.stop` is THE ABORT: a terminal configuration with no rule (B4 —
  the driver classifies it as the `panic` terminal, the pool as the
  goroutine's `aborted` tombstone; there is no k-less configuration).
  The old per-operator
  `binPanicLeft/Right`-style propagation rules still have no analogue —
  propagation is the one generic `panicUnwind` rule.
- **Fail closed**: unsupported/malformed forms have no rules (relation
  silence); `applyStrictOp` returns `.stuck`/`.unsupported` errors that no
  rule matches. The executable reports the *why* (S2).
- **Assignee desugaring**: an assignment target is evaluated as the
  expression it denotes (`.var id ↝ .ref id`, `.addr e ↝ e`), delivering an
  address value; the consuming frame turns nil into Go's nil-dereference
  panic via `valueAsLoc`, exactly where the interpreter does.

Known (Go-unreachable) divergences vs. the old interpreter, accepted and
gated by the S3 zero-drift differential (list re-checked by the 2026-07-23
mid-arc audit):
- operand *class* checks that the big-step interpreter performed between
  operand evaluations (e.g. `mapGet` checking the base is a map before
  evaluating the key; call arity checked before argument evaluation) here
  happen after all operands are evaluated — observable only for ill-typed
  programs the frontend cannot emit; both sides fail closed;
- a bare `.initialization` NOT directly under a statement sequence is
  stuck here where the big-step interpreter ran it as a dead no-op — the
  declaration's whole purpose is extending the enclosing sequence's
  environment, so outside one it fails closed; the frontend only ever
  emits initializations inside `.seqn`/`.block` statement lists.

Statement-side coverage (S2): the full interpreter fragment. Wide
statements (`allocNew`, make/assign/lookup for maps and
slices, `typeAssert`, `appendSlice`, `copySlice`) go through one generic
`stmtOpK` frame — an operand plan (`stmtPlan`) whose leading `ntargets`
operands are target addresses, checked as they arrive (preserving the
interpreter's resolve-targets-first order and nil-target panic timing) —
ending in a single `applyStmtOp` state-update step. `mapRange` gets a
dedicated iteration frame whose pick-next step is the machine's
nondeterministic step class (any in-range index is a legal step; the
executable instantiates it from `Choices`), together with `appendSlice`'s
capacity choice inside `applyStmtOp`. The multi-cell apply steps
(`appendSlice`, `copySlice`) are the granularity-ledger entries from the
design note §1: sequentially fine, re-audited before any concurrency
claim mentions them (R4).
-/

namespace GoLean.GoCore.Machine

open GoLean

-- B7 (2026-09-17): the immutable program facts are ONE explicit parameter
-- of every context-reading operation and of the `Step` relation (`variable`
-- makes it the first explicit argument of each def that mentions it);
-- theorems take it implicitly (`variable {ctx}` toggles below). Heap
-- readers/writers take the `Store`.
variable (ctx : ProgramCtx)

/-! ## Assignee desugaring -/

/-- The expression an assignment target denotes: evaluating it yields the
target *address* (`.var id` is exactly `.ref id`; `.addr e` is `e`).
`none` for unsupported assignees — the machine is silent there. -/
def assigneeExpr : Assignee → Option Expr
  | .var id => some (.ref id)
  | .addr e => some e
  | .mapElem _ _ _ _ => none
  | .unsupported _ => none

/-! ## Strict operators: the defunctionalized op table -/

/-- Head of a strict expression form: Go evaluates its operands
left-to-right, then applies the head in one step (`applyStrictOp`). The
apply step is where memory operations, panics, and allocation happen. -/
inductive StrictOp where
  | add | sub | mul | div | mod
  | shiftLeft | shiftRight | bitAnd | bitOr | bitXor | bitClear
  | bitNeg | not
  /-- Value-directed unary minus (floats slice): int `0 - v`; float IEEE
  sign-bit flip. -/
  | neg
  /-- A float constant's exact rational, rounded ONCE here at evaluation
  (nullary strict form, like `defaultValueOf`/`nilLit` — no new rule
  shapes; design note decision 5). -/
  | floatLit (num : Int) (den : Nat) (kind : FloatKind)
  | eqCmp (ty : Ty) | neqCmp (ty : Ty)
  | atMostCmp | atLeastCmp | lessCmp | greaterCmp
  | convert (ty : Ty)
  | bytesFromString | stringFromByteSlice | stringFromRune
  | deref (ty : Ty)
  /-- `&*p`: nil-assert on the pointer VALUE, yield it unchanged, no
  memory access (BUG-056 — gc's `TESTB` probe shape). -/
  | addrOfDeref
  | fieldGet (typeId : TypeId) (fieldName : String)
  | fieldAddr (typeId : TypeId) (fieldName : String)
  | structLit (ty : Ty)
  | arrayLit (length : Nat) (elem : Ty) (keys : List Int)
  | toInterface (target dynamic : Ty)
  | typeAssert (target : Ty) (source : Option Ty)
  | indexGet | indexAddr
  | mapGet (keyTy valueTy : Ty)
  | sliceExpr (hasMax : Bool)
  | lengthOf (typ : Option Ty)
  | capacityOf (typ : Option Ty)
  | defaultValueOf (ty : Ty)
  | nilLit (typ : Option Ty)
  /-- Build a closure value from its captured operands (§8). -/
  | funcValOf (fid : FuncId)
  /-- `min`/`max` over ints or strings (Go's ordered builtins). -/
  | minOf
  | maxOf
  /-- UTF-8 rune decode at a byte offset (range-over-string desugar). -/
  | runeAt
  | runeSizeAt
  /-- `[]rune(s)` / `string([]rune)` (triage L1, 2026-08-19). Appended
  last so positional proof bullets over earlier arms stay put. -/
  | runesFromString
  | stringFromRuneSlice
  /-- The `float-bits` primitive (stdlib slice 3; `floatBitsApply`,
  Ops.lean): pure, one operand, appended last. -/
  | floatBits (op : FloatBitsOp)
  deriving Repr, BEq

/-- Classify an expression as a strict-operator application: the head and
the operand list, in evaluation order. `none` for the forms with their own
rules (`var`/literals/`ref`/`global`, short-circuit `and`/`or`) and for
`unsupported`. -/
def strictPlan : Expr → Option (StrictOp × List Expr)
  | .convert ty e => some (.convert ty, [e])
  | .bytesFromString e => some (.bytesFromString, [e])
  | .stringFromByteSlice e => some (.stringFromByteSlice, [e])
  | .stringFromRune e => some (.stringFromRune, [e])
  | .add l r => some (.add, [l, r])
  | .sub l r => some (.sub, [l, r])
  | .mul l r => some (.mul, [l, r])
  | .div l r => some (.div, [l, r])
  | .mod l r => some (.mod, [l, r])
  | .shiftLeft l r => some (.shiftLeft, [l, r])
  | .shiftRight l r => some (.shiftRight, [l, r])
  | .bitAnd l r => some (.bitAnd, [l, r])
  | .bitOr l r => some (.bitOr, [l, r])
  | .bitXor l r => some (.bitXor, [l, r])
  | .bitClear l r => some (.bitClear, [l, r])
  | .bitNeg e => some (.bitNeg, [e])
  | .neg e => some (.neg, [e])
  | .floatLit num den kind => some (.floatLit num den kind, [])
  | .not e => some (.not, [e])
  | .eqCmp ty l r => some (.eqCmp ty, [l, r])
  | .neqCmp ty l r => some (.neqCmp ty, [l, r])
  | .atMostCmp l r => some (.atMostCmp, [l, r])
  | .atLeastCmp l r => some (.atLeastCmp, [l, r])
  | .lessCmp l r => some (.lessCmp, [l, r])
  | .greaterCmp l r => some (.greaterCmp, [l, r])
  | .deref e ty => some (.deref ty, [e])
  | .addrOfDeref e => some (.addrOfDeref, [e])
  | .structLit ty args => some (.structLit ty, args.toList)
  | .fieldGet recv typeId fieldName => some (.fieldGet typeId fieldName, [recv])
  | .fieldAddr base typeId fieldName => some (.fieldAddr typeId fieldName, [base])
  | .arrayLit n elem args =>
      some (.arrayLit n elem (args.toList.map (·.1)), args.toList.map (·.2))
  | .toInterface target dynamic e => some (.toInterface target dynamic, [e])
  | .typeAssert e target source => some (.typeAssert target source, [e])
  | .indexGet b i => some (.indexGet, [b, i])
  | .indexAddr b i => some (.indexAddr, [b, i])
  | .mapGet b i keyTy valueTy => some (.mapGet keyTy valueTy, [b, i])
  | .slice b lo hi none => some (.sliceExpr false, [b, lo, hi])
  | .slice b lo hi (some m) => some (.sliceExpr true, [b, lo, hi, m])
  | .length e ty => some (.lengthOf ty, [e])
  | .capacity e ty => some (.capacityOf ty, [e])
  | .defaultValue ty => some (.defaultValueOf ty, [])
  | .nil ty => some (.nilLit ty, [])
  | .funcVal fid captured => some (.funcValOf fid, captured.toList)
  | .minOf args => some (.minOf, args.toList)
  | .maxOf args => some (.maxOf, args.toList)
  | .runeAt s off => some (.runeAt, [s, off])
  | .runeSizeAt s off => some (.runeSizeAt, [s, off])
  | .runesFromString e => some (.runesFromString, [e])
  | .stringFromRuneSlice e => some (.stringFromRuneSlice, [e])
  | .floatBits op e => some (.floatBits op, [e])
  | _ => none

/-- Slice-expression application, after all operands are values (base, low,
high, optional max already as `Int`). Transcribed from the interpreter's
`.slice` arm. -/
def applySlice (s : Store) (b : GoValue) (lowValue highValue : Int)
    (maxValue : Option Int) : Except Stop (GoValue × Store) := do
  match b with
  | .string value => return ((← stringSlice value lowValue highValue maxValue), s)
  | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), s)
  | .addr baseLoc =>
      match ← loadLoc ctx s baseLoc with
      | .array values =>
          return ((← sliceFromArray baseLoc values.size lowValue highValue maxValue), s)
      | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), s)
      | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
  | .array values =>
      unsupported s!"slice expression over non-addressable array value of length {values.size}"
  | other => stuck s!"expected array or slice value for slice expression, got {repr other}"

/-- The element location of an index-addressed target: bounds-checked
against the base. Shared verbatim between the `indexAddr` strict op
(address in expression position — the check fires at evaluation) and
`storeTarget` (an assignment's OWN index target — spec §Assignments
defers the check to the STORE, phase 2; convergence round BUG-029,
pinned by `channels/recv-edge/oob-second-target-stores-first`). -/
def indexTargetLoc (s : Store) (b i : GoValue) : Except Stop Loc := do
  let indexValue ← valueAsInt i
  match b with
  | .slice slice => sliceIndexLoc slice indexValue
  -- A nil pointer-to-array base is gc's recoverable nil-pointer
  -- dereference, at exactly this point (round 4, BUG-038 — the
  -- `valueAsLoc` convention; previously a wrongly-stuck fall-through).
  | .nil => panic "runtime error: invalid memory address or nil pointer dereference"
  | .addr baseLoc =>
      match ← loadLoc ctx s baseLoc with
      | .array values => do
          let _ ← arrayIndexNat values indexValue
          return .index baseLoc indexValue
      | .slice slice => sliceIndexLoc slice indexValue
      | other => stuck s!"expected array or slice base for index address, got {repr other}"
  | other => stuck s!"expected array or slice base for index address, got {repr other}"

/-! ## The validate/commit seam of a store-bearing apply (C1 S3, cost B —
`docs/2026-09-17_c1-memory-module-charter.md` §2 B(b), §6 S3;
`docs/2026-09-11_bug090-rediagnosis.md` §3 mechanism B)

Every apply that WRITES memory is two phases. The VALIDATE phase only READS
the store: every check that can fail, in the arm's original order, every
recoverable panic among them. The COMMIT phase only WRITES (the allocations,
the emitting stores, the payload writes) and — by the per-arm
`…_commit_noPanic` theorems (MachineSound) — never raises a recoverable
panic: since S3 the write path's index re-check is a machine-invariant
check (`arrayIndexNatFormed`, Ops.lean), so nothing on the write path panics.
The validate phase BORROWS the store and returns the commit as a function of
the store it will OWN (`Commit`); the executable (`deliverV`, StepFn.lean)
runs the validate phase, then on `.ok` hands its ONE reference to the commit
and on `.panic` unwinds over the store the apply never touched. No reference
to the pre-apply store survives into a write, so the dense heap's
`push`/`set` run in place — BUG-090's cost B: before S3 the delivery kept the
pre-apply store for its rollback arm (`deliverS s …`) and every write of
every apply copied the whole heap. The relation names the COMPOSED apply
(validate, then commit on the same store — `applyStmtOp`, `applyStmtOpCore`,
`storeTarget`, `mapAssignValue`, `enterFrame`, `unseqLoad`: one-liners over
their `.plan`), so `Step` and every theorem about the composed functions keep
their statements; the split is definitional — ONE account. The applies still
delivered with the pre-apply store in hand are listed at `deliverS`. -/

/-- THE COMMIT PHASE of a store-bearing apply: the writes left to do once
every check has passed, as a function of the store it will own. -/
abbrev Commit (α : Type) := Store → Except Stop α

/-- Run a commit on the store it owns. A recoverable panic out of a commit is
UNREACHABLE (the per-arm `…_commit_noPanic` theorems, MachineSound): were one
to arrive, the pre-apply store is gone, so it is refused BY NAME as
`.internal` rather than rendered as a Go panic over the wrong store (fail
closed); `runCommit_of_noPanic` is the equation the coherence proofs use. -/
def runCommit {α : Type} (c : Commit α) (s : Store) : Except Stop α :=
  match c s with
  | .error (Stop.panic msg) =>
      throw (.internal s!"a commit phase raised a recoverable panic after its validate phase passed ({msg}): unreachable by the per-arm rollback theorems (C1 S3)")
  | r => r

/-- A stream-free commit in the stream-threading apply's shape: the stream
`ch` — consumed, if at all, by the validate phase — rides beside the result.
Names the fact the consumption theorems rest on: a commit never touches the
stream (`applyStmtOp.plan`'s every arm returns one of these). -/
def Commit.withStream (ch : Choices) (ps : List PickRecord) (c : Commit (Store × AccessTrace)) :
    Commit (Store × Choices × List PickRecord × AccessTrace) := fun s => do
  let (s', tr) ← c s
  return (s', ch, ps, tr)

/-- Store into a map element: normalize key and value at the map's
types, insert-or-overwrite; a NIL map is the run-time panic. Shared
verbatim between the `mapAssign` wide op and `storeTarget`'s
map-element arm (convergence round BUG-030 — a map-element receive
target's store is a phase-2 event like any other).

PINNED LATITUDE — `==`-equal key retention on overwrite (inventory
E10; site caveat added 2026-08-31, fidelity assessment A1-21 — the
inventory had asserted this caveat existed when it did not). The spec
is SILENT on which `==`-equal key a map stores after an overwrite;
the plausible envelope has two members: {the NEW key replaces the
stored key, the ORIGINAL stored key is retained}. The `entries.set! i
(key, value)` below realizes always-replace. Observable exposure:
exactly the key kinds where `==`-equal keys are distinguishable when
the stored key is later observed — float (±0), complex, string
(identity via later observation), interface, and arrays/structs over
them (gc's per-type `needkeyupdate` is true for precisely these
kinds, false where `==` implies bit-equality) — so always-replace is
observationally equal to gc on every key kind. TRANSFER CAVEAT: a
conforming ORIGINAL-KEY-RETAINING implementation is outside this
singleton; no claim about the stored key transfers to it. Re-envelope
(two-point retention choice) is XIMPL-gated — see inventory E10. -/
def mapAssignValue.plan (s : Store) (keyTy valueTy : Ty)
    (baseV keyV valueV : GoValue) : Except Stop (Commit (Store × AccessTrace)) := do
  let map ← valueAsMap baseV
  let key ← normalizeValueForTy ctx keyTy keyV
  let value ← normalizeValueForTy ctx valueTy valueV
  match ← mapEntries s map with
  | none => panic "assignment to entry in nil map"
  | some (baseLoc, entries, nextId) =>
      -- Entry-identity stamps (B1): a PRESENT key keeps its entry's id
      -- (the E10 always-replace pin unchanged — new key, new value, same
      -- identity); an ABSENT key creates a NEW entry stamped `nextId`,
      -- and the counter moves on. Ids are never reused.
      let (entries, nextId) ←
        match ← mapEntryIndex? ctx keyTy entries key (isInsert := true) with
        | some i =>
            match entries[i]? with
            | some (id, _, _) => pure (entries.set! i (id, key, value), nextId)
            | none => stuck s!"missing map entry at index {i}"
        | none => pure (entries.push (nextId, key, value), nextId + 1)
      -- The entries fetch above is the RMW's peek; the ONE access is the
      -- map write (gc's mapassign instrumentation point) — THE COMMIT (S3).
      return fun s => Mem.mapWrite s baseLoc entries nextId

@[inherit_doc mapAssignValue.plan]
def mapAssignValue (s : Store) (keyTy valueTy : Ty)
    (baseV keyV valueV : GoValue) : Except Stop (Store × AccessTrace) := do
  let c ← mapAssignValue.plan ctx s keyTy valueTy baseV keyV valueV
  c s

/-- Apply a strict operator to its (already evaluated, in evaluation order)
operand values. The single op table shared by the relation (as a rule
premise) and the executable `stepFn`: transcribed arm-by-arm from the
big-step interpreter's `evalExpr`, minus the recursion. Panics are Go
behavior (`.panic`); `.stuck`/`.unsupported` mean no relation rule matches
(fail closed). The catch-all arm covers head/arity mismatches unreachable
via `strictPlan`. -/
def applyStrictOp (s : Store) (leafOf : Loc → Loc) :
    StrictOp → List GoValue → Except Stop (GoValue × Store × AccessTrace)
  | .add, [l, r] =>
      match l, r with
      | .int .., .int .. => do return ((← intBinaryResult "+" (· + ·) l r), s, [])
      | .float .., .float .. => do
          return ((← floatBinaryResult "+" FloatBits.fadd64 FloatBits.fadd32 l r), s, [])
      | .string lv, .string rv => return (.string (GoString.append lv rv), s, [])
      | _, _ => stuck s!"mismatched + operands: {repr l} and {repr r}"
  | .sub, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "-" FloatBits.fsub64 FloatBits.fsub32 l r), s, [])
      | _, _ => do return ((← intBinaryResult "-" (· - ·) l r), s, [])
  | .mul, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "*" FloatBits.fmul64 FloatBits.fmul32 l r), s, [])
      | _, _ => do return ((← intBinaryResult "*" (· * ·) l r), s, [])
  | .div, [l, r] =>
      match l, r with
      -- Float division dispatches BEFORE the integer divide-by-zero
      -- check: it NEVER panics — IEEE ±Inf/NaN results (design note
      -- §3.2, an envelope narrowing matching gc everywhere; pinned by
      -- floats/division-specials).
      | .float .., .float .. => do
          return ((← floatBinaryResult "/" FloatBits.fdiv64 FloatBits.fdiv32 l r), s, [])
      | _, _ => do
          let divisor ← valueAsInt r
          if divisor == 0 then
            panic "runtime error: integer divide by zero"
          return ((← intBinaryResult "/" Int.tdiv l r), s, [])
  | .mod, [l, r] => do
      let divisor ← valueAsInt r
      if divisor == 0 then
        panic "runtime error: integer divide by zero"
      return ((← intBinaryResult "%" Int.tmod l r), s, [])
  | .shiftLeft, [l, r] => do return ((← intShiftLeftResult l r), s, [])
  | .shiftRight, [l, r] => do return ((← intShiftRightResult l r), s, [])
  | .bitAnd, [l, r] => do return ((← intBitwiseBinaryResult "&" Nat.land l r), s, [])
  | .bitOr, [l, r] => do return ((← intBitwiseBinaryResult "|" Nat.lor l r), s, [])
  | .bitXor, [l, r] => do return ((← intBitwiseBinaryResult "^" Nat.xor l r), s, [])
  | .bitClear, [l, r] => do return ((← intBitClearResult l r), s, [])
  | .bitNeg, [v] => do return ((← intBitNegResult v), s, [])
  | .neg, [v] =>
      match v with
      | .int value kind => return (.int (kind.normalize (0 - value)) kind, s, [])
      -- IEEE negation is the sign-bit flip, never 0 - x (wrong at +0).
      | .float bits kind => return (.float (kind.normalizeBits (kind.negBits bits)) kind, s, [])
      | other => stuck s!"mismatched unary - operand: {repr other}"
  | .floatLit num den kind, [] =>
      -- Malformed rationals fail closed at the decoder; defensive here.
      if den == 0 then stuck "malformed float literal: zero denominator"
      else return (.float (kind.normalizeBits (kind.ratToBits num den)) kind, s, [])
  | .not, [v] => do return (.bool (!(← valueAsBool v)), s, [])
  | .eqCmp ty, [l, r] => do return (.bool (← valueEq ctx ty l r), s, [])
  | .neqCmp ty, [l, r] => do return (.bool (!(← valueEq ctx ty l r)), s, [])
  | .atMostCmp, [l, r] => do return (.bool (← valueAtMost l r), s, [])
  | .atLeastCmp, [l, r] => do return (.bool (← valueAtLeast l r), s, [])
  | .lessCmp, [l, r] => do return (.bool (← valueLess l r), s, [])
  | .greaterCmp, [l, r] => do return (.bool (← valueGreater l r), s, [])
  | .convert ty, [v] => do return ((← convertValueToTy ctx ty v), s, [])
  -- ENVELOPE STATEMENT (recorded narrowing, arc-final audit F8,
  -- 2026-08-06). Spec §Conversions on `[]byte(s)`: "The capacity of the
  -- resulting slice is implementation-specific and may be larger than
  -- the slice length" — a declared latitude. The model resolves it to
  -- the SINGLETON cap = len, with no Choices consumption. gc's realized
  -- point depends on escape analysis: cap = len when the backing does
  -- not escape (probe go1.26.5: len 5 → cap 5, len 6 → cap 6), but
  -- roundupsize(len) when it escapes (len 5 → cap 8, len 33 → cap 48,
  -- len 100 → cap 112). TRANSFER CAVEAT: a theorem asserting
  -- cap([]byte(s)) = len(s) does NOT transfer to gc executions where
  -- the conversion escapes; the green version-tracking pin
  -- (strings/byte-conversion-cap, a non-escaping shape) tracks the
  -- agreeing point only. Widening this to a Choices site is deliberate
  -- future work if a cap-observing escaping shape ever needs to pass —
  -- do not silently match one compiler mode.
  | .bytesFromString, [v] =>
      match v with
      | .string value => do
          let bytes := value.bytes.map (fun b => GoValue.int (Int.ofNat b.toNat) .uint8)
          let (base, s') ← Store.alloc ctx s (.array bytes) (.array bytes.size (.int .uint8))
          return (.slice { base := some base, offset := 0, len := bytes.size, cap := bytes.size }, s', [])
      | other => stuck s!"expected string operand for []byte conversion, got {repr other}"
  | .stringFromByteSlice, [v] => do
      let slice ← valueAsSlice v
      let (values, tr) ← Mem.loadSlice ctx s slice
      let mut bytes := #[]
      for value in values do
        match value with
        | .int byte .uint8 =>
            if byte < 0 || byte > 255 then
              stuck s!"malformed uint8 byte value in string conversion: {byte}"
            bytes := bytes.push (UInt8.ofNat byte.toNat)
        | other => stuck s!"expected uint8 element in string conversion, got {repr other}"
      return (.string { bytes := bytes }, s, tr)
  | .stringFromRune, [v] => do
      return (.string (GoString.fromCodePoint (← valueAsInt v)), s, [])
  | .deref _, [v] => do
      -- THE POINTEE READ, narrowed by the caller's `leafOf` (the
      -- continuation's immediate projection chain — `projChainTarget`;
      -- O1's value-path whole-cell read otherwise).
      let l ← valueAsLoc v
      let (x, tr) ← Mem.loadFor ctx s l (leafOf l)
      return (x, s, tr)
  -- `&*p` (BUG-056): the nil check consumes the pointer VALUE already
  -- in hand — `.addr` passes through, `.nil` panics via `valueAsLoc`'s
  -- runtime-error arm, anything else is stuck. It reads and writes NO
  -- memory cell (gc: a bare TESTB nil-probe, no pointee load — memo
  -- §2), so it has no race-footprint arm on purpose (Race.lean's
  -- call-site inventory records the decision).
  | .addrOfDeref, [v] => do return (.addr (← valueAsLoc v), s, [])
  | .fieldGet typeId fieldName, [v] => do
      match v with
      | .struct actualType fields =>
          -- Tag-convertible mint tags are accepted (triage L7): the
          -- pointer conversion aliases the cell, whose tag stays.
          if actualType != typeId && !structTagCompatible ctx actualType typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return (value, s, [])
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct value for field access, got {repr other}"
  | .fieldAddr typeId fieldName, [v] => do
      return (.addr (.field (← valueAsLoc v) typeId fieldName), s, [])
  | .structLit ty, vs => do return ((← buildStructValue ctx ty vs.toArray), s, [])
  | .arrayLit n elem keys, vs => do
      if keys.length != vs.length then
        stuck s!"array literal expected {keys.length} element value(s), got {vs.length}"
      return ((← buildArrayValue ctx n elem (keys.zip vs).toArray), s, [])
  | .toInterface _ dynamic, [v] => do
      -- Box with the CANONICAL dynamic type (S3): aliases resolved,
      -- identity kept, fail closed on unsupported leaves. An
      -- interface-typed source is an interface→interface conversion:
      -- the existing box (or nil) passes through unchanged — Go never
      -- double-boxes.
      let dynTy ← checkedDynamicTy dynamic
      match dynTy with
      | .interface _ => return (v, s, [])
      | _ => return (.interface dynTy v, s, [])
  | .typeAssert targetTy sourceTy, [v] => do
      let result ← typeAssertValue ctx v targetTy
      if result.2 then
        return (result.1, s, [])
      else
        -- Go names the first UNMET requirement when the target is an
        -- interface; a nil operand has none to report.
        let missing ←
          match targetTy, v with
          | .interface interfaceName, .interface dynTy _ =>
              firstUnsatisfiedMethod? ctx dynTy interfaceName
          | _, _ => pure none
        panic (← typeAssertPanicMessage ctx v targetTy sourceTy missing)
  | .indexGet, [b, i] => do
      let indexValue ← valueAsInt i
      match b with
      | .array values => return ((← arrayGet values indexValue), s, [])
      | .string value => return ((← stringByteGet value indexValue), s, [])
      | .slice slice => do
          let (x, tr) ← Mem.load ctx s (← sliceIndexLoc slice indexValue)
          return (x, s, tr)
      -- Pointer-to-array base in READ position (triage L5;
      -- spec#Index_expressions: for `a` of pointer to array type,
      -- `a[x]` is shorthand for `(*a)[x]`): the read sibling of
      -- BUG-038's write-path `.addr` arm in `indexTargetLoc`. Only an
      -- ARRAY pointee is accepted — Go's index auto-deref applies to
      -- pointer-to-array alone; the write path's slice-pointee arm
      -- exists because assignment TARGETS carry the base cell's
      -- address, a shape read position never produces.
      | .addr baseLoc => do
          -- gc compiles a single ELEMENT load: the footprint is the
          -- element path (triage L5), the value the whole array's.
          let (cell, tr) ← Mem.loadFor ctx s baseLoc (.index baseLoc indexValue)
          match cell with
          | .array values => return ((← arrayGet values indexValue), s, tr)
          | other => stuck s!"expected array pointee for index access, got {repr other}"
      -- A nil pointer-to-array base is gc's recoverable nil-pointer
      -- dereference (triage L6; BUG-038's entry names this case as the
      -- deferred read-position sibling).
      | .nil => panic "runtime error: invalid memory address or nil pointer dereference"
      | other => stuck s!"expected array, slice, or string value for index access, got {repr other}"
  | .indexAddr, [b, i] => do
      return (.addr (← indexTargetLoc ctx s b i), s, [])
  | .mapGet keyTy valueTy, [b, i] => do
      let map ← valueAsMap b
      let key ← normalizeValueForTy ctx keyTy i
      match map.base with
      -- A NIL map still hashes the key before returning the zero value.
      | none => do
          checkKeyHashable ctx key (isInsert := false) (nonEmpty := false)
          return ((← defaultValue ctx valueTy), s, [])
      | some baseLoc =>
          let ((entries, _), tr) ← Mem.mapRead s baseLoc
          match ← mapEntryIndex? ctx keyTy entries key with
          | some idx =>
              match entries[idx]? with
              | some (_, _, value) => return (value, s, tr)
              | none => stuck s!"missing map entry at index {idx}"
          | none => return ((← defaultValue ctx valueTy), s, tr)
  | .sliceExpr false, [b, lo, hi] => do
      let (v, s') ← applySlice ctx s b (← valueAsInt lo) (← valueAsInt hi) none
      return (v, s', [])
  | .sliceExpr true, [b, lo, hi, m] => do
      let (v, s') ← applySlice ctx s b (← valueAsInt lo) (← valueAsInt hi) (some (← valueAsInt m))
      return (v, s', [])
  | .lengthOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) =>
          -- The length of a pointer-to-array is type-static (no deref, a nil
          -- pointer included: spec §Length and capacity); the operand must
          -- still BE a pointer value — an ill-typed operand refuses by name
          -- rather than answering from the type alone (C1 S2b, fail closed;
          -- the footprint table classified this arm by the VALUE's shape).
          match v with
          | .addr _ | .nil => return (.int n, s, [])
          | other => stuck s!"len of a pointer-to-array expected a pointer operand, got {repr other}"
      | _ =>
          match v with
          | .array values => return (.int values.size, s, [])
          | .addr baseLoc =>
              match ← loadLoc ctx s baseLoc with
              | .array values => return (.int values.size, s, [])
              | other => unsupported s!"len for non-array pointer value {repr other}"
          | .string value => return (.int value.length, s, [])
          | .slice slice =>
              validateSlice slice *> return (.int slice.len, s, [])
          | .map map =>
              match map.base with
              | none => return (.int 0, s, [])
              | some baseLoc =>
                  -- `len(m)` is a real instrumented map read on gc (S3 audit).
                  let (p, tr) ← Mem.mapRead s baseLoc
                  return (.int p.1.size, s, tr)
          -- len(ch) = elements queued in the buffer; nil channel = 0
          -- (spec §Length and capacity). Never panics, never blocks.
          | .chan ch =>
              match ch.base with
              | none => return (.int 0, s, [])
              | some baseLoc =>
                  let p ← chanPayload? s baseLoc
                  return (.int p.1.size, s, [])
          | other => unsupported s!"len for non-array/slice/map value {repr other}"
  | .capacityOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) =>
          -- Type-static like `len` (same fail-closed operand check, C1 S2b).
          match v with
          | .addr _ | .nil => return (.int n, s, [])
          | other => stuck s!"cap of a pointer-to-array expected a pointer operand, got {repr other}"
      | _ =>
          match v with
          | .array values => return (.int values.size, s, [])
          | .addr baseLoc =>
              match ← loadLoc ctx s baseLoc with
              | .array values => return (.int values.size, s, [])
              | other => unsupported s!"cap for non-array pointer value {repr other}"
          | .slice slice =>
              validateSlice slice *> return (.int slice.cap, s, [])
          -- cap(ch) = buffer capacity; nil channel = 0.
          | .chan ch =>
              match ch.base with
              | none => return (.int 0, s, [])
              | some baseLoc =>
                  let p ← chanPayload? s baseLoc
                  return (.int p.2.1, s, [])
          | other => unsupported s!"cap for non-array/slice value {repr other}"
  | .funcValOf fid, vs => return (.funcVal fid vs, s, [])
  | .minOf, v :: vs =>
      -- Float operands take the IEEE fold (triage L3, spec#Min_and_max:
      -- NaN propagates, min(-0,+0) = -0) over the softfloat comparison
      -- kernel — never valueLess, whose unordered `<` is false at NaN
      -- in BOTH directions and would silently make the first operand
      -- win. Left-associative like gc's lowering.
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax true best w
        return (best, s, [])
      else do
        let mut best := v
        for w in vs do
          if ← valueLess w best then
            best := w
        return (best, s, [])
  | .maxOf, v :: vs =>
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax false best w
        return (best, s, [])
      else do
        let mut best := v
        for w in vs do
          if ← valueLess best w then
            best := w
        return (best, s, [])
  | .runeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (decodeRuneAt str off.toNat).1 .int32, s, [])
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | .runeSizeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (Int.ofNat (decodeRuneAt str off.toNat).2) .int, s, [])
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | .defaultValueOf ty, [] => do return ((← defaultValue ctx ty), s, [])
  | .nilLit typ, [] =>
      match typ with
      | none => return (.nil, s, [])
      | some ty =>
          match ty with
          | .slice _ => do return ((← defaultValue ctx ty), s, [])
          | .map _ _ => do return ((← defaultValue ctx ty), s, [])
          | .chan _ _ => do return ((← defaultValue ctx ty), s, [])
          | .pointer _ => return (.nil, s, [])
          -- Interface and func are nilable types too (spec
          -- §Assignability; BUG-077 — the CONVERSION form `error(nil)`
          -- / `any(nil)` / `(func())(nil)` carries the target type on
          -- the nil wire node where the assignment form's bare nil
          -- landed in the arm above): their zero value is `.nil`,
          -- exactly what `defaultValue` yields for both.
          | .interface _ => return (.nil, s, [])
          | .funcType _ _ _ => return (.nil, s, [])
          | .unsupported feature => unsupported s!"nil literal for {feature}"
          | other => stuck s!"nil literal for non-nilable type {repr other}"
  -- `[]rune(s)` (triage L1, 2026-08-19): decode every code point
  -- (`runesOfString` — invalid encodings yield U+FFFD per byte, the
  -- same accept-range kernel as range-over-string) into a FRESH backing
  -- array, exactly the `bytesFromString` shape. ENVELOPE STATEMENT: the
  -- resulting capacity shares `bytesFromString`'s recorded narrowing —
  -- spec §Conversions declares the cap implementation-specific; the
  -- model pins the SINGLETON cap = len. The transfer caveat here is
  -- WIDER than the bytes arm's: gc is outside the singleton even on
  -- the small NON-escaping shape (probe go1.26.5:
  -- cap([]rune("héllo")) = 32 — the runtime's 32-rune conversion
  -- buffer), so no cap-observing rune case can pin an agreeing point
  -- (the byte-conversion-cap sibling was measured red and deliberately
  -- NOT added, R3's own precedent for the escaping byte shape). A
  -- theorem asserting cap([]rune(s)) = len does not transfer to gc;
  -- the re-envelope obligation is R3's, covering both arms (latitude
  -- inventory R3).
  | .runesFromString, [v] =>
      match v with
      | .string value => do
          let runes := (runesOfString value).map
            (fun r => GoValue.int r .int32)
          let (base, s') ← Store.alloc ctx s (.array runes)
            (.array runes.size (.int .int32))
          return (.slice { base := some base, offset := 0,
                           len := runes.size, cap := runes.size }, s', [])
      | other => stuck s!"expected string operand for []rune conversion, got {repr other}"
  -- `string(rs)` over a rune slice (triage L1): concatenate the UTF-8
  -- encodings of the individual rune values (spec §Conversions to and
  -- from a string type) — values outside the valid code-point range
  -- (negative, surrogate, > U+10FFFF) encode U+FFFD via the same
  -- `fromCodePoint` kernel `string(int)` uses.
  | .stringFromRuneSlice, [v] => do
      let slice ← valueAsSlice v
      let (values, tr) ← Mem.loadSlice ctx s slice
      let mut str := GoString.empty
      for value in values do
        match value with
        | .int r .int32 => str := str.append (GoString.fromCodePoint r)
        | other => stuck s!"expected rune element in string conversion, got {repr other}"
      return (.string str, s, tr)
  -- The `float-bits` primitive: a bit reinterpretation over the machine's
  -- own representation (Ops.lean `floatBitsApply` — bit-exact both ways;
  -- the canonical-NaN refusal is documented there). No state, no
  -- footprint (Race.lean's inventory), no consumption.
  | .floatBits op, [v] => do return ((← floatBitsApply op v), s, [])
  | op, vs => stuck s!"malformed strict-operator application: {repr op} on {vs.length} operand(s)"

/-! ## Shared list operations (env-threading; used as rule premises and by
`stepFn`) -/

/-- Declare typed locals: allocate each at its default value, extending the
environment (the functional form of the old `DeclsR`). -/
def allocDecls : LocalEnv → Store → List Param → Except Stop (LocalEnv × Store)
  | env, s, [] => return (env, s)
  | env, s, p :: rest => do
      let v ← defaultValue ctx p.typ
      let (loc, s₁) ← Store.alloc ctx s v p.typ
      allocDecls (env.declare p.id loc) s₁ rest

/-- Bind call parameters into a frame environment, normalized at declared
type (the functional form of the old `BindParamsR`). Arity is checked by
`enterFrame` before this runs. -/
def bindParams : LocalEnv → Store → List Param → List GoValue → Except Stop (LocalEnv × Store)
  | env, s, [], [] => return (env, s)
  | env, s, p :: ps, v :: vs => do
      let v' ← normalizeValueForTy ctx p.typ v
      let (loc, s₁) ← Store.alloc ctx s v' p.typ
      bindParams (env.declare p.id loc) s₁ ps vs
  | _, _, [], _ :: _ => stuck "extra argument value"
  | _, _, _ :: _, [] => stuck "missing argument"

/-- Resolve freshly declared result names to their frame locations, at call
time (the functional form of the old `LookupsR`; D2-proper result pinning). -/
def pinResultLocs (env : LocalEnv) : List Param → Except Stop (List Loc)
  | [] => return []
  | p :: ps =>
      match env.lookup p.id with
      | some loc => do return loc :: (← pinResultLocs env ps)
      | none => stuck s!"unbound GoCore result variable: {p.id}"

/-- Load a list of locations (frame-exit result reads; old `LoadsR`). -/
def loadMany (s : Store) : List Loc → Except Stop (List GoValue)
  | [] => return []
  | loc :: locs => do return (← loadLoc ctx s loc) :: (← loadMany s locs)

/-- The frame-EXIT result reads (the pinned result cells) — `loadMany`'s
emitting twin: one data read per result cell (named results are
addressable variables; a deferred closure may write them). `loadMany`
itself stays the drivers' PEEK readout after termination. -/
def loadResults (s : Store) : List Loc → Except Stop (List GoValue × AccessTrace)
  | [] => return ([], [])
  | loc :: locs => do
      let (v, t) ← Mem.loadBinding ctx s loc
      let (vs, ts) ← loadResults s locs
      return (v :: vs, t ++ ts)

-- DELETED (C1 S3, 2026-09-19): `storeMany` — the pairwise frame-exit target
-- writer (old `StoreManyR`). Dead since the tgtOpK spine took the caller-target
-- stores (BUG-025), kept alive only as `HeapNormal.of_storeMany`'s subject
-- (inventory rows «DEAD RAW WRITER — deletion owed to S3»); its lemmas
-- `HeapNormal.of_storeMany`, `storeMany_shape`, `storeMany_pres` (StateWf)
-- left with it. Tombstone: `docs/2026-09-19_c1-memory-module-s3-handoff.md`.

/-- The callee a frame entry names (design note
`docs/2026-09-28_gp-method-promotion-design.md` §3 `callee?` — G-P S2
replaces the callee half of `findFunctionIn?` in `enterFrame`): a declared
`Func`, or — a method expression `S.M` / `(*S).M` over a PROMOTED
method-set entry (design §2 S7, decision 5) — the promotion RECORD whose
carrier and member the id spells (`methodFuncId S M`; the retired
synthesized wrapper carried that id). `findFunctionIn?` itself keeps its
signature; its domain lost the wrapper `Func`s. -/
inductive Callee where
  | func (f : Func)
  | promotion (p : Promotion)

def callee? (fid : FuncId) : Option Callee :=
  match findFunctionIn? ctx.functions fid with
  | some f => some (.func f)
  | none =>
      match ctx.promotions.find? (fun p => methodFuncId p.type.key p.member == fid) with
      | some p => some (.promotion p)
      | none => none

/-- What a frame entry commits to (G-P S2): RUN the resolved declared
`Func`'s body in a fresh frame (its parameter and result cells bound and
pinned), or — a promotion path that ended in an embedded INTERFACE field
(design §2 S5, decision 4) — RE-DISPATCH the same call on the field's
value through the interface's anchor `fid` with the receiver-adjusted
arguments, as the NEXT machine step: no frame is pushed, `stepFn` stays
structurally total, a self-embedding cycle steps to fuel-out. The entry's
own loads (the path walk, S8) ride in the delivered trace either way. -/
inductive Entry where
  | run (func : Func) (frameEnv : LocalEnv) (resultLocs : List Loc)
  | again (fid : FuncId) (args : List GoValue)
  deriving Repr

/-- A method expression over a promoted entry, CALLED (design §2 S7): the
record is the callee; argument 0 is the receiver the expression's first
parameter takes — the carrier value for `S.M`, a pointer (possibly nil)
for `(*S).M` — and the record's path applies to it exactly as at a
dispatch (`receiverAt`), so the retired `(*S).M` deref-adapter refusal is
not needed for promoted entries: the record's adjustment dereferences.
The target is entered directly (a declared `Func`), or the embedded
interface's anchor is re-entered on the field's value (S5). A stub record
refuses by name with its cause; a target with no `Func` on the wire
refuses by name (never a silent answer). -/
def promotedCallee (s : Store) (fid : FuncId) (p : Promotion) (argVals : List GoValue) :
    Except Stop (Dispatched × AccessTrace) := do
  match p.unsupported with
  | some cause => throw (.unsupported cause)
  | none =>
  match p.target with
  | .method f =>
      match findFunctionIn? ctx.functions f with
      | none =>
          throw (.unsupported s!"promoted method expression {fid.key}: its target {f.key} has no \
declaration on the wire (an imported type's unexported method is not carried by the imported stub \
pass, docs/2026-08-10_method-set-record-contract.md §5) — refusing rather than calling from no body")
      | some tf =>
          if tf.args.size != argVals.length then
            stuck s!"function {fid.key} expected {tf.args.size} argument(s), got {argVals.length}"
          match argVals with
          | [] => stuck s!"promoted method expression {fid.key} called without a receiver argument"
          | root :: rest => do
              let (recv, tr) ← receiverAt ctx s root p.path p.adjust
              return (.target tf (recv :: rest).toArray, tr)
  | .iface i =>
      let anchorId := methodFuncId i.key p.member
      match findFunctionIn? ctx.functions anchorId with
      | none => stuck s!"GoCore function not found: {anchorId.key}"
      | some anchor =>
          if anchor.args.size != argVals.length then
            stuck s!"function {fid.key} expected {anchor.args.size} argument(s), got {argVals.length}"
          match argVals with
          | [] => stuck s!"promoted method expression {fid.key} called without a receiver argument"
          | root :: rest => do
              let (recv, tr) ← receiverAt ctx s root p.path p.adjust
              return (.again anchorId (recv :: rest).toArray, tr)

/-- Callee lookup (`callee?`), arity check, dynamic method dispatch
(`dynamicDispatch?` — the resolution and the path walk), parameter
binding, result declaration, and result-location pinning — everything
between "arguments are values" and "executing the callee body". One step in
the machine (frame entry). The two arity checks mirror the interpreter's
(pre-dispatch in `execFunctionCallWithLocs`, post-dispatch in
`execFunctionWithValues`); a record callee checks against its target. -/
def enterFrame.plan (s : Store) (fid : FuncId) (argVals : List GoValue) :
    Except Stop (Commit (Entry × Store × AccessTrace)) := do
  -- The entry's ONE possible user-memory access: the dispatch's receiver
  -- read (`dynamicDispatch?` — the pointee of the `*T ⊇ T` arm, or the
  -- promotion path's own loads). Binding and result declaration allocate
  -- fresh cells only.
  let (d, tr) ←
    match callee? ctx fid with
    | none => stuck s!"GoCore function not found: {fid.key}"
    | some (.func func) => do
        if func.args.size != argVals.length then
          stuck s!"function {fid.key} expected {func.args.size} argument(s), got {argVals.length}"
        match ← dynamicDispatch? ctx s func argVals.toArray with
        | (some d, tr) => pure (d, tr)
        | (none, tr) => pure (Dispatched.target func argVals.toArray, tr)
    | some (.promotion p) => promotedCallee ctx s fid p argVals
  match d with
  | .again fid' args' =>
      -- S5: the re-dispatch is the next step's entry; nothing to commit.
      return fun s => return (.again fid' args'.toList, s, tr)
  | .target func args =>
      if func.args.size != args.size then
        stuck s!"function {func.id.key} expected {func.args.size} argument(s), got {args.size}"
      -- THE COMMIT (S3): binding and result declaration allocate fresh cells only.
      return fun s => do
        let (argsEnv, s₁) ← bindParams ctx [] s func.args.toList args.toList
        let (frameEnv, s₂) ← allocDecls ctx argsEnv s₁ func.results.toList
        let resultLocs ← pinResultLocs frameEnv func.results.toList
        return (.run func frameEnv resultLocs, s₂, tr)

@[inherit_doc enterFrame.plan]
def enterFrame (s : Store) (fid : FuncId) (argVals : List GoValue) :
    Except Stop (Entry × Store × AccessTrace) := do
  let c ← enterFrame.plan ctx s fid argVals
  c s

/-- The `nilValueMethodText` site's stream bound at a frame entry
(BUG-087): 2 on the wrapper family (`nilValueMethodText?` — the
envelope statement, Ops.lean), 1 everywhere else. A bound-1 consult pops
nothing (the uniform rule, `Choices.consumeAt`), so every entry outside
the family consumes exactly what it consumed before the site existed. -/
def nilValueMethodWidth (fid : FuncId) (args : List GoValue) : Nat :=
  if (nilValueMethodText? ctx fid args).isSome then 2 else 1

/-- The frame-entry panic TEXT under the `nilValueMethodText` pick:
`msg` (the text `enterFrame` raised — the nil-dereference text on the
family) at slot 0, gc's `panicwrap` text at any other slot; outside the
family the pick is inert and `msg` stands. The relation's entry-panic
rules quantify `pick` freely (a `∃ pick`), which is exactly the
two-member set — every `pick ≠ 0` names the same member. -/
def entryPanicText (fid : FuncId) (args : List GoValue)
    (msg : String) (pick : Nat) : String :=
  match nilValueMethodText? ctx fid args with
  | some alt => if pick = 0 then msg else alt
  | none => msg

variable {ctx}
theorem nilValueMethodWidth_of_none {fid : FuncId} {args : List GoValue}
    (h : nilValueMethodText? ctx fid args = none) :
    nilValueMethodWidth ctx fid args = 1 := by
  simp [nilValueMethodWidth, h]

theorem entryPanicText_of_none {fid : FuncId} {args : List GoValue}
    {msg : String} {pick : Nat} (h : nilValueMethodText? ctx fid args = none) :
    entryPanicText ctx fid args msg pick = msg := by
  simp [entryPanicText, h]

/-- The site's bound-1 consult (outside the family) is inert — the
uniform rule (`Choices.consumeAt_one`), specialized to the site. -/
@[simp] theorem Choices.consumeAt_nilValueMethodText_one {ch : Choices} :
    Choices.consumeAt .nilValueMethodText 1 ch = (0, ch) :=
  Choices.consumeAt_one

/-- The `isSome = false` spellings of the two `_of_none` facts (the shape
`simp` leaves a `consumesNilValueMethod … = false` hypothesis in). -/
theorem nilValueMethodWidth_of_isSome_false {fid : FuncId}
    {args : List GoValue} (h : (nilValueMethodText? ctx fid args).isSome = false) :
    nilValueMethodWidth ctx fid args = 1 := by
  simp [nilValueMethodWidth, h]

theorem entryPanicText_of_isSome_false {fid : FuncId}
    {args : List GoValue} {msg : String} {pick : Nat}
    (h : (nilValueMethodText? ctx fid args).isSome = false) :
    entryPanicText ctx fid args msg pick = msg := by
  cases hn : nilValueMethodText? ctx fid args with
  | none => simp [entryPanicText, hn]
  | some alt => rw [hn] at h; simp at h

variable (ctx)
/-- **Frame entry WITH the choice stream — THE one stream-touching entry
funnel** (B2, replacing `enterFrameStep`/`enterFrameDeferPanicking` and
`spawnStep`'s copy). `enterFrame` itself is stream-free; its RECOVERABLE
panic (dynamic dispatch on a nil interface; the auto-deref of a nil
pointer box) is classified here (`toResult`) and, on the panic path
ONLY, the `nilValueMethodText` site is consulted at bound
`nilValueMethodWidth s fid args` (BUG-087, [USER] ruling 2026-09-03
«demonic choice so both are admitted», relayed —
`docs/2026-08-31_qrow-rulings.md`): 2 exactly on the wrapper family
(`nilValueMethodText?`, Ops.lean, the envelope statement), where slot 0
keeps the nil-dereference text `enterFrame` raised and slot 1
substitutes gc's `panicwrap` text; 1 elsewhere, where the uniform
bound-≤-1 rule makes the consult a no-op
(`Choices.consumeAt_nilValueMethodText_one`) — so every non-family entry
consumes exactly as before the site existed. The successful entry
returns the stream untouched. Every frame entry of the machine goes
through here: the seven `stepFn` positions (`entryCallSite?`) and the
`go`-statement spawn (`spawnStep`, Multi.lean); the relation's entry
rules quantify the stream (`ch`/`ch'`, the `stmtOpApply` idiom). -/
def enterFramePick (s : Store) (fid : FuncId) (args : List GoValue) (ch : Choices) :
    Except Stop (Result (Entry × Store × AccessTrace) × Choices × List PickRecord) :=
  match toResult (enterFrame ctx s fid args) with
  | .ok (.ok r) => .ok (.ok r, ch, [])
  | .ok (.panic msg) =>
      let (pick, ch', ps) := Choices.consumeAtE .nilValueMethodText (nilValueMethodWidth ctx fid args) ch
      .ok (.panic (entryPanicText ctx fid args msg pick), ch', ps)
  | .error e => .error e

/-- `enterFramePick`'s VALIDATE half (C1 S3, cost B): the same classification
and the same `nilValueMethodText` consult on the panic path, over
`enterFrame.plan` — so the entry's COMMIT (the parameter and result cells)
runs on a store the caller no longer holds. THE executable's entry funnel
(`stepFn`'s seven positions, `stepFrameExit`, `spawnStep`); `enterFramePick`
itself stays the relation's premise. The bridge is `enterFramePickV_cases`
with `enterFramePick_of_V_ok`/`enterFramePick_of_V_panic` (below) and
`enterFramePickV_of_ok`/`_of_panic`/`_of_plan_ok`/`_of_plan_panic`/
`_of_nopanic` (MachineSound) — S3 audit F2, 2026-09-19 [AGENT]: the
`enterFramePickV_ok`/`_panic`/`_error` this docstring used to name were
never declared. -/
def enterFramePickV (s : Store) (fid : FuncId) (args : List GoValue) (ch : Choices) :
    Except Stop (Result (Commit (Entry × Store × AccessTrace)) × Choices × List PickRecord) :=
  match toResult (enterFrame.plan ctx s fid args) with
  | .ok (.ok c) => .ok (.ok c, ch, [])
  | .ok (.panic msg) =>
      let (pick, ch', ps) := Choices.consumeAtE .nilValueMethodText (nilValueMethodWidth ctx fid args) ch
      .ok (.panic (entryPanicText ctx fid args msg pick), ch', ps)
  | .error e => .error e

variable {ctx}
/-- A successful entry never touches the stream. -/
theorem enterFramePick_ok {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} {e : Entry} {s' : Store} {tr : AccessTrace}
    (h : enterFrame ctx s fid args = .ok (e, s', tr)) :
    enterFramePick ctx s fid args ch = .ok (.ok (e, s', tr), ch, []) := by
  simp [enterFramePick, h]

/-- The entry panic's text and the popped stream, on the panic path. -/
theorem enterFramePick_panic {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} {msg : String}
    (h : enterFrame ctx s fid args = .error (.panic msg)) :
    enterFramePick ctx s fid args ch =
      .ok (.panic (entryPanicText ctx fid args msg
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1),
          (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).2,
          (PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid args) (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)) := by
  simp [enterFramePick, h, Choices.consumeAtE_eq]

/-- Any other stop propagates. -/
theorem enterFramePick_error {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} {e : Stop} (h : enterFrame ctx s fid args = .error e) (hp : ∀ msg, e ≠ .panic msg) :
    enterFramePick ctx s fid args ch = .error e := by
  simp [enterFramePick, h, toResult_error hp]

/-- The two ways an entry classifies (the proof layer's case split):
an entered frame with the stream untouched, or the entry panic's text
under the site's pick with the stream popped. -/
theorem enterFramePick_cases {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {ps : List PickRecord} {r : Result (Entry × Store × AccessTrace)}
    (h : enterFramePick ctx s fid args ch = .ok (r, ch', ps)) :
    (∃ e s' tr, r = .ok (e, s', tr)
        ∧ enterFrame ctx s fid args = .ok (e, s', tr) ∧ ch' = ch ∧ ps = [])
    ∨ (∃ msg, r = .panic (entryPanicText ctx fid args msg
          (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)
        ∧ enterFrame ctx s fid args = .error (.panic msg)
        ∧ ch' = (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).2
        ∧ ps = (PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid args) (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)) := by
  unfold enterFramePick at h
  cases hx : toResult (enterFrame ctx s fid args) with
  | error e => rw [hx] at h; cases h
  | ok r₀ =>
    rw [hx] at h
    cases r₀ with
    | ok a =>
      obtain ⟨e, s', tr⟩ := a
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inl ⟨e, s', tr, rfl, toResult_eq_ok_ok.mp hx, rfl, rfl⟩
    | panic msg =>
      simp only [Choices.consumeAtE_eq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inr ⟨msg, rfl, toResult_eq_ok_panic.mp hx, rfl, rfl⟩

/-- An entry that does NOT panic never touches the stream. -/
theorem enterFramePick_of_nopanic {s : Store} {fid : FuncId} {args : List GoValue}
    (hnp : ∀ msg, enterFrame ctx s fid args ≠ .error (.panic msg)) (ch : Choices) :
    enterFramePick ctx s fid args ch = (toResult (enterFrame ctx s fid args)).map (·, ch, []) := by
  unfold enterFramePick
  cases hx : toResult (enterFrame ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok a => rfl
    | panic msg => exact absurd (toResult_eq_ok_panic.mp hx) (hnp msg)

/-- An entry that classifies under one stream classifies under every
stream (the classification is `enterFrame`'s, stream-free; only the
panic TEXT and the popped tail depend on the stream). -/
theorem enterFramePick_any_ch {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {ps : List PickRecord} {r : Result (Entry × Store × AccessTrace)}
    (h : enterFramePick ctx s fid args ch = .ok (r, ch', ps)) (ch₂ : Choices) :
    ∃ r₂ ch₂' ps₂, enterFramePick ctx s fid args ch₂ = .ok (r₂, ch₂', ps₂) := by
  rcases enterFramePick_cases h with ⟨e, s', tr, -, hX, -⟩ | ⟨msg, -, hX, -⟩
  · exact ⟨_, _, _, enterFramePick_ok hX⟩
  · exact ⟨_, _, _, enterFramePick_panic hX⟩

/-- Outside the wrapper family the entry is stream-oblivious: the
panic-path consult is at bound 1 and pops nothing. -/
theorem enterFramePick_of_isSome_false {fid : FuncId} {args : List GoValue}
    (hn : (nilValueMethodText? ctx fid args).isSome = false) :
    ∀ (s : Store) (ch : Choices),
      enterFramePick ctx s fid args ch = (toResult (enterFrame ctx s fid args)).map (·, ch, []) := by
  -- B7: the store is quantified AFTER the family test — the test reads the
  -- context only, so `s` can no longer be inferred from `hn`.
  intro s ch
  unfold enterFramePick
  cases toResult (enterFrame ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok a => rfl
    | panic msg =>
      simp [nilValueMethodWidth_of_isSome_false hn, entryPanicText_of_isSome_false hn, Except.map,
        Choices.consumeAtE_eq, PickRecord.ofPick]

/-- The family-free entry, ∀-stream form. -/
theorem enterFramePick_oblivious_of_isSome_false {fid : FuncId}
    {args : List GoValue} (hn : (nilValueMethodText? ctx fid args).isSome = false)
    (s : Store) (ch : Choices) :
    enterFramePick ctx s fid args ch = (toResult (enterFrame ctx s fid args)).map (·, ch, []) :=
  enterFramePick_of_isSome_false hn s ch

@[inherit_doc enterFramePick_of_isSome_false]
theorem enterFramePick_of_none {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} (hn : nilValueMethodText? ctx fid args = none) :
    enterFramePick ctx s fid args ch = (toResult (enterFrame ctx s fid args)).map (·, ch, []) := by
  unfold enterFramePick
  cases toResult (enterFrame ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok a => rfl
    | panic msg =>
      simp [nilValueMethodWidth_of_none hn, entryPanicText_of_none hn, Except.map,
        Choices.consumeAtE_eq, PickRecord.ofPick]

/-! ### The V funnel's bridge (C1 S3): `enterFramePickV` against `enterFramePick` -/

/-- The composed apply (`do let c ← plan; c s`) on the error side: either the
validate phase failed, or it passed and the commit failed. -/
theorem plan_run_error {α : Type} {plan : Except Stop (Commit α)} {s : Store} {e : Stop}
    (h : (do let c ← plan; c s : Except Stop α) = .error e) :
    plan = .error e ∨ ∃ c, plan = .ok c ∧ c s = .error e := by
  cases hp : plan with
  | error e' =>
    rw [hp] at h
    simp only [Bind.bind, Except.bind, Except.error.injEq] at h
    exact .inl (by rw [h])
  | ok c =>
    rw [hp] at h
    simp only [Bind.bind, Except.bind] at h
    exact .inr ⟨c, rfl, h⟩

/-- The V funnel's two classifications (`enterFramePick_cases`' twin): a
commit with the stream untouched, or the entry panic's text under the site's
pick with the stream popped. -/
theorem enterFramePickV_cases {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {ps : List PickRecord}
    {r : Result (Commit (Entry × Store × AccessTrace))}
    (h : enterFramePickV ctx s fid args ch = .ok (r, ch', ps)) :
    (∃ c, r = .ok c ∧ enterFrame.plan ctx s fid args = .ok c ∧ ch' = ch ∧ ps = [])
    ∨ (∃ msg, r = .panic (entryPanicText ctx fid args msg
          (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)
        ∧ enterFrame.plan ctx s fid args = .error (.panic msg)
        ∧ ch' = (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).2
        ∧ ps = (PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid args) (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)) := by
  unfold enterFramePickV at h
  cases hx : toResult (enterFrame.plan ctx s fid args) with
  | error e => rw [hx] at h; cases h
  | ok r₀ =>
    rw [hx] at h
    cases r₀ with
    | ok c =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inl ⟨c, rfl, toResult_eq_ok_ok.mp hx, rfl, rfl⟩
    | panic msg =>
      simp only [Choices.consumeAtE_eq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inr ⟨msg, rfl, toResult_eq_ok_panic.mp hx, rfl, rfl⟩

/-- Outside the wrapper family the V entry is stream-oblivious
(`enterFramePick_of_isSome_false`'s twin). -/
theorem enterFramePickV_of_isSome_false {fid : FuncId} {args : List GoValue}
    (hn : (nilValueMethodText? ctx fid args).isSome = false) :
    ∀ (s : Store) (ch : Choices),
      enterFramePickV ctx s fid args ch = (toResult (enterFrame.plan ctx s fid args)).map (·, ch, []) := by
  intro s ch
  unfold enterFramePickV
  cases toResult (enterFrame.plan ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok c => rfl
    | panic msg =>
      simp [nilValueMethodWidth_of_isSome_false hn, entryPanicText_of_isSome_false hn, Except.map,
        Choices.consumeAtE_eq, PickRecord.ofPick]

@[inherit_doc enterFramePickV_of_isSome_false]
theorem enterFramePickV_of_none {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} (hn : nilValueMethodText? ctx fid args = none) :
    enterFramePickV ctx s fid args ch = (toResult (enterFrame.plan ctx s fid args)).map (·, ch, []) := by
  unfold enterFramePickV
  cases toResult (enterFrame.plan ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok c => rfl
    | panic msg =>
      simp [nilValueMethodWidth_of_none hn, entryPanicText_of_none hn, Except.map,
        Choices.consumeAtE_eq, PickRecord.ofPick]

/-- A V `.ok` whose commit runs IS the composed funnel's `.ok` entry (the stream
untouched on this path). -/
theorem enterFramePick_of_V_ok {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {ps : List PickRecord}
    {c : Commit (Entry × Store × AccessTrace)}
    {a : Entry × Store × AccessTrace}
    (hv : enterFramePickV ctx s fid args ch = .ok (.ok c, ch', ps)) (hc : c s = .ok a) :
    enterFramePick ctx s fid args ch = .ok (.ok a, ch', ps) ∧ ch' = ch ∧ ps = [] := by
  rcases enterFramePickV_cases hv with ⟨c', hce, hplan, rfl, rfl⟩ | ⟨msg, hr, -, -⟩
  · simp only [Result.ok.injEq] at hce
    subst hce
    have henter : enterFrame ctx s fid args = .ok a := by
      simp [enterFrame, hplan, Bind.bind, Except.bind, hc]
    exact ⟨by simp [enterFramePick, henter], rfl, rfl⟩
  · cases hr

/-- A V `.panic` IS the composed funnel's `.panic` (same text, same popped stream). -/
theorem enterFramePick_of_V_panic {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {ps : List PickRecord} {msg : String}
    (hv : enterFramePickV ctx s fid args ch = .ok (.panic msg, ch', ps)) :
    enterFramePick ctx s fid args ch = .ok (.panic msg, ch', ps) := by
  rcases enterFramePickV_cases hv with ⟨c, hce, -, -⟩ | ⟨msg₀, hr, hplan, rfl, rfl⟩
  · cases hce
  · simp only [Result.panic.injEq] at hr
    subst hr
    have henter : enterFrame ctx s fid args = .error (.panic msg₀) := by
      simp [enterFrame, hplan, Bind.bind, Except.bind]
    exact enterFramePick_panic henter

/-! ## Wide statements: the statement-op table -/

variable (ctx)
/-- Head of a wide statement: evaluate the operand plan (targets first, as
addresses, then the value operands), then perform the state update in one
`applyStmtOp` step. -/
inductive StmtOp where
  | allocNew (typ : Ty)
  | makeSlice (elem : Ty) (hasCap : Bool)
  | makeMap (hasSpace : Bool)
  /-- `make(chan T[, n])` (channels arc slice 1): allocate an empty
  `chanPayload` cell (the `makeMap` shape; a payload cell, A3). Negative capacity ⇒ the recoverable run-time panic
  `makechan: size out of range` (probe p21); so does a buffer whose
  byte size (`elem`'s R16 size × n) exceeds `maxAllocBytes -
  chanHeaderBytes` (t5-maxalloc, 2026-09-02) — which is why the op
  carries `elem` since that slice. -/
  | makeChan (elem : Ty) (hasCap : Bool)
  | mapAssign (keyTy valueTy : Ty)
  | appendSlice (elem : Ty)
  | copySlice
  | mapDelete (keyTy : Ty)
  | clearMap
  | clearSlice (elem : Ty)
  | sortSlice (elem : Ty)
  /-- `print`/`println` (stdlib slice 3, 2026-09-04; `Stmt.print`): the
  apply step VALIDATES the operands against gc's printable kinds
  (`renderPrint`) and changes no state — the bytes are the pool layer's
  OUTPUT EVENT, derived from the same `renderPrint` at the same apply
  position (`printOut?`). Appended last. -/
  | print (newline : Bool)
  deriving Repr, BEq

/-- Classify a wide statement: the head, how many leading operands are
target addresses, and the operand expressions in evaluation order (the
interpreter's order: all targets, then the value operands). `none` for
statements with their own rules and for unsupported assignees.
`assignMany` no longer rides this plan: the convergence round (BUG-025)
moved it onto the phase-split delivery machinery (`tgtOpK`/`rhsK`/
`storeK`), whose per-store phase 2 the one-shot `applyStmtOp` cannot
express. -/
def stmtPlan : Stmt → Option (StmtOp × Nat × List Expr)
  | .allocNew target value typ => do
      let te ← assigneeExpr target
      return (.allocNew typ, 1, [te, value])
  | .makeSlice target elem len cap => do
      let te ← assigneeExpr target
      return (.makeSlice elem cap.isSome, 1, [te, len] ++ cap.toList)
  | .makeMap target _ _ space => do
      let te ← assigneeExpr target
      return (.makeMap space.isSome, 1, [te] ++ space.toList)
  | .makeChan target elem capacity => do
      let te ← assigneeExpr target
      return (.makeChan elem capacity.isSome, 1, [te] ++ capacity.toList)
  | .mapAssign base index value keyTy valueTy =>
      return (.mapAssign keyTy valueTy, 0, [base, index, value])
  | .appendSlice target elem slice elems => do
      let te ← assigneeExpr target
      return (.appendSlice elem, 1, [te, slice, elems])
  | .copySlice target dst src => do
      let te ← assigneeExpr target
      return (.copySlice, 1, [te, dst, src])
  | .mapDelete base index keyTy =>
      return (.mapDelete keyTy, 0, [base, index])
  | .clearMap base => return (.clearMap, 0, [base])
  | .clearSlice base elem => return (.clearSlice elem, 0, [base])
  | .sortSlice base elem => return (.sortSlice elem, 0, [base])
  -- `print`/`println`: zero targets, the operands in source order. An
  -- EMPTY operand list has no plan (`none` — the shape refuses at the
  -- frontend and the decoder by name; A8: no plan is nullary).
  | .print nl args =>
      match args.toList with
      | [] => none
      | e :: rest => return (.print nl, 0, e :: rest)
  | _ => none

/-! ## `print`/`println` — gc's `runtime/print.go` formats, pinned

The formatting of `print`/`println` is implementation-specific by the
spec's own sentence (spec#Bootstrapping: "formatting of arguments is
implementation-specific") — the (b)-pin class of the latitude inventory
(row R17, sibling of R9/R10, which the SAME runtime printing code
realizes for panic payloads). Pinned to gc go1.26.5
`deps/go/src/runtime/print.go`:

- `printbool` (:120-126): `true` / `false`.
- `printint` (:162-177): decimal, `-` for negatives; `printuint`
  (:154-160): decimal. The kind decides which: a signed `IntKind`
  prints as `printint`, an unsigned one as `printuint` (the compiler
  selects by the operand's type; a defined type prints as its
  underlying kind — `print` never calls methods).
- `printstring` (:256-258): the bytes verbatim.
- `printsp` = `" "`, `printnl` = `"\n"` (:112-118): `println` writes
  `printsp` BETWEEN arguments and `printnl` after the last (the
  compiler's `walkPrint`, cmd/compile/internal/walk/builtin.go);
  `print` writes neither.
- REFUSED by name, permanently: pointers, channels, maps, funcs,
  slices (`[len/cap]0xaddr`, :260-264), interfaces
  (`(0xtypeword,0xdata)`, :266-272) and unsafe.Pointer print ADDRESSES
  the machine does not have (and gc's are not stable across runs — memo
  §4). `nil` reaches this arm only as one of those kinds (an untyped
  `nil` operand is a compile error), so it refuses with them.
- REFUSED by name THIS SLICE ([AGENT] call, disclosed in the design
  note §3.3): floats and complex. gc's `printfloat64` (:128-131) is
  `internal/strconv.AppendFloat(v, 'g', -1, 64)` — the SHORTEST
  round-trip decimal (Ryū-class `ftoa` + `bigFtoa`/`roundShortest`, a
  Go 1.26 change: commit 9035f7ae "runtime: use internal/strconv";
  1.25 printed `+1.500000e+000`), not a 40-line transcription; the
  faithful route (source-through `internal/strconv`, now unblocked by
  the `float-bits` primitive, CALLED from the print arm) is a new
  machine-op shape that needs its own argument. Complex rides floats.

The rendering is ONE definition consumed twice: the sequential apply
step validates through it (a refusal at the apply position, like every
other wide op), and the pool layer derives the emitted event from it
at the same configuration (`printOut?`) — so the event carries exactly
the bytes the step validated. -/

/-- One operand's bytes (gc's `print*` helper selected by kind). -/
def renderPrintOperand : GoValue → Except Stop GoString
  | .bool b => return GoString.fromLeanString (if b then "true" else "false")
  | .int v kind =>
      match kind with
      | .unbounded name =>
          stuck s!"print of an untyped {name} constant operand (the frontend types every print operand)"
      | _ => return GoString.fromLeanString (toString v)
  | .string s => return s
  | .float _ kind =>
      unsupported s!"print of a {kind.name} operand: gc formats floats with internal/strconv.AppendFloat 'g' -1 (shortest round-trip, go1.26 commit 9035f7ae), not transcribed this slice — refused by name (rows builtins/print/refused/float and refused/float32)"
  | .nil => unsupported "print of a nil pointer/interface/slice/map/chan/func operand: gc prints an ADDRESS (0x0 / (0x0,0x0) / [0/0]0x0), which the machine does not model — refused by name"
  | .addr _ => unsupported "print of a pointer operand: gc prints its address (runtime/print.go printpointer), which the machine does not model — refused by name"
  | .interface .. => unsupported "print of an interface operand: gc prints (0xtypeword,0xdata) (runtime/print.go printeface/printiface), addresses the machine does not model — refused by name"
  | .slice _ => unsupported "print of a slice operand: gc prints [len/cap]0xaddr (runtime/print.go printslice), an address the machine does not model — refused by name"
  | .map _ => unsupported "print of a map operand: gc prints its address, which the machine does not model — refused by name"
  | .chan _ => unsupported "print of a channel operand: gc prints its address, which the machine does not model — refused by name"
  | .funcVal .. => unsupported "print of a func operand: gc prints its code address, which the machine does not model — refused by name"
  | other => stuck s!"print of an operand gc's print does not accept: {repr other}"

/-- The whole statement's bytes: `println` = operands joined by `printsp`
with `printnl` after; `print` = the operands' bytes concatenated. -/
def renderPrint (newline : Bool) : List GoValue → Except Stop GoString
  | [] => return (if newline then GoString.fromLeanString "\n" else GoString.empty)
  | v :: rest => do
      let head ← renderPrintOperand v
      let tail ← renderPrint newline rest
      if newline then
        match rest with
        | [] => return head.append tail
        | _ :: _ => return (head.append (GoString.fromLeanString " ")).append tail
      else
        return head.append tail

/-- The integer elements of a value run, in order — `sortSlice`'s operand check
(C1 S2b): one refusal text, at the first non-integer element; structural, so
`intElems_length` (the run keeps its length) is by induction. -/
def intElems : List GoValue → Except Stop (List (Int × IntKind))
  | [] => return []
  | .int v kind :: rest => do return (v, kind) :: (← intElems rest)
  | other :: _ => stuck s!"sortSlice expected int element, got {repr other}"

/-- The choices-FREE core of `applyStmtOp`: every wide-op arm except
`appendSlice` (whose spill path consumes a capacity choice; its arm HERE
is an unreachable fail-closed `.internal` — real dispatch happens in the
wrapper, and the wrapper never routes `appendSlice` here). Extracted at
the sem-adequacy arc's notions slice (2026-08-03) so that
choices-obliviousness of wide-op success is TRUE BY CONSTRUCTION — the
correspondence kit's `∀ choices` lemmas dispatch through this core rather
than a per-arm congruence bash. Arms are verbatim from the old
`applyStmtOp` minus the trailing `choices` threading.

C1 S3 (cost B): THE VALIDATE PHASE. Every arm reads, checks and panics in
its original order, then returns its COMMIT (`Commit`, the seam docstring
above) — the allocations and the emitting writes, none of which can panic
(`applyStmtOpCore_commit_noPanic`). Three arms reorder a PURE nil-target
check ahead of an allocation or an element run it used to follow
(`makeSlice`, `makeMap`, `makeChan`, `copySlice` — the S0 audit's W arms):
the observable is unchanged, because the delivery rolled those writes back
on that panic. The composed `applyStmtOpCore` (below) is the relation's.
-/
def applyStmtOpCore.plan (s : Store) (op : StmtOp)
    (vs : List GoValue) : Except Stop (Commit (Store × AccessTrace)) := do
  match op with
  | .allocNew typ =>
      match vs with
      | [tv, value] => do
          let loc ← valueAsLoc tv
          return fun s => do
            let (nloc, s₁) ← Store.alloc ctx s value typ
            Mem.store ctx s₁ loc (.addr nloc)
      | _ => stuck "malformed allocNew operands"
  | .makeSlice elem hasCap => do
      let (tv, lenV, capV?) ←
        match vs, hasCap with
        | [tv, lenV], false => pure (tv, lenV, none)
        | [tv, lenV, capV], true => pure (tv, lenV, some capV)
        | _, _ => stuck "malformed makeSlice operands"
      let lenValue ← valueAsInt lenV
      let capValue ←
        match capV? with
        | none => pure lenValue
        | some capV => valueAsInt capV
      -- gc's `makeslice` check, verbatim in structure (runtime/slice.go:
      -- 102–115; R16 pin, t5-maxalloc 2026-09-02): the CAP request is
      -- bad when negative, when its byte size exceeds `maxAllocBytes`,
      -- or when len > cap; a bad cap request reports `len out of range`
      -- when the LEN alone is already bad (negative or over the byte
      -- limit — golang.org/issue/4085: `make([]T, huge)` blames len)
      -- and `cap out of range` otherwise. The byte size is `elemSize ×
      -- n` under the gc-amd64 layout (`tySizeBytes`); the check
      -- precedes materialization, so an over-limit request never
      -- builds its backing (probe matrix: docs/evidence/
      -- 2026-09-02_t5-maxalloc-probes/). Exactly-at-limit requests
      -- pass (gc then fails to ALLOCATE — the true-OOM class, register
      -- #7 rider / D-001, not modeled).
      let elemSize ← tySizeBytes ctx.types elem
      if capValue < 0 || capValue * elemSize > maxAllocBytes
          || lenValue < 0 || lenValue > capValue then
        if lenValue < 0 || lenValue * elemSize > maxAllocBytes then
          panic "runtime error: makeslice: len out of range"
        else
          panic "runtime error: makeslice: cap out of range"
      let len := lenValue.toNat
      let cap := capValue.toNat
      let backing ← buildDefaultArrayValue ctx cap elem
      -- S3: the target's nil check precedes the allocation (a pure reorder —
      -- before S3 the allocation came first and the panic rolled it back).
      let loc ← valueAsLoc tv
      return fun s => do
        let (base, s₁) ← Store.alloc ctx s backing (.array cap elem)
        Mem.store ctx s₁ loc (.slice { base := some base, offset := 0, len, cap })
  | .makeMap hasSpace => do
      let (tv, spaceV?) ←
        match vs, hasSpace with
        | [tv], false => pure (tv, none)
        | [tv, spaceV], true => pure (tv, some spaceV)
        | _, _ => stuck "malformed makeMap operands"
      match spaceV? with
      | none => pure ()
      | some spaceV => do
          -- The hint is EVALUATED (operand order, type) and otherwise
          -- ignored: spec §Making slices, maps and channels makes the
          -- hint's effect "implementation-dependent", and gc (go1.26.5,
          -- runtime/map.go:60–67) silently CLAMPS a negative or over-
          -- `maxAlloc` hint to 0 — it never panics (probes map-hint-neg
          -- / map-hint-over, t5-maxalloc 2026-09-02). Until that slice
          -- this arm panicked `makemap: size out of range` on a
          -- negative hint — an older gc string the pinned oracle never
          -- produces — but the arm was DEAD CODE end-to-end: the native
          -- frontend did not lower the hint (the `make-map` wire node
          -- had no hint field; NativeToIR passed `none`), which also
          -- dropped the hint expression's EVALUATION. That was BUG-082
          -- (FIXED 2026-09-02, bug082-maphint: the frontend emits the
          -- optional `hint` field, NativeToIR decodes it into
          -- `initialSpace`, and it lands here — its calls already
          -- hoisted by the frontend in operand order, the residual
          -- expression evaluated as this op's operand; corpus
          -- builtins/make-map-hint-eval/*). This arm's realized
          -- behavior is gc's.
          let _ ← valueAsInt spaceV
      -- S3 (the S0 audit's reachable W arm): the hint-less form arrives
      -- without the target nil check, so the check moved BEFORE the payload
      -- allocation — a pure reorder (the allocation was rolled back on it).
      let loc ← valueAsLoc tv
      return fun s => do
        let (base, s₁) := s.allocCell (.mapPayload #[] 0)
        Mem.store ctx s₁ loc (.map { base := some base })
  | .makeChan elem hasCap => do
      let (tv, capV?) ←
        match vs, hasCap with
        | [tv], false => pure (tv, none)
        | [tv, capV], true => pure (tv, some capV)
        | _, _ => stuck "malformed makeChan operands"
      let capacity ←
        match capV? with
        | none => pure 0
        | some capV => do
            let size ← valueAsInt capV
            -- Negative ⇒ run-time panic; the message is gc's realized
            -- string (probe p21) — spec pins only THAT a panic occurs
            -- (runtime error values are unspecified), matching the
            -- repo's existing makeslice narrowing. The same panic when
            -- the BUFFER's byte size exceeds `maxAllocBytes -
            -- chanHeaderBytes` (gc makechan, runtime/chan.go:86–89; R16
            -- pin, t5-maxalloc 2026-09-02): the threshold sits 112
            -- bytes below the slice one, and a zero-size element
            -- (`chan struct{}`) never trips it at any n — gc realizes
            -- `make(chan struct{}, 1<<62)` (probe chan-struct0-huge),
            -- and so does this arm (the buffer is a capacity NUMBER
            -- here, never materialized).
            let elemSize ← tySizeBytes ctx.types elem
            if size < 0 || size * elemSize > maxAllocBytes - chanHeaderBytes then
              panic "makechan: size out of range"
            pure size.toNat
      -- S3 (the S0 audit's reachable W arm): as `makeMap` — the cap-less
      -- form's nil check moved before the payload allocation.
      let loc ← valueAsLoc tv
      return fun s => do
        let (base, s₁) := s.allocCell (.chanPayload #[] capacity false)
        Mem.store ctx s₁ loc (.chan { base := some base })
  | .mapAssign keyTy valueTy =>
      match vs with
      | [baseV, keyV, valueV] => mapAssignValue.plan ctx s keyTy valueTy baseV keyV valueV
      | _ => stuck "malformed mapAssign operands"
  | .mapDelete keyTy =>
      match vs with
      | [baseV, keyV] => do
          let map ← valueAsMap baseV
          let key ← normalizeValueForTy ctx keyTy keyV
          match ← mapEntries s map with
          -- Nil map: no-op (the key evaluated) — but Go still HASHES the
          -- key, so an unhashable one panics here too (probed 2026-07-31).
          | none => do
              checkKeyHashable ctx key (isInsert := false) (nonEmpty := false)
              return fun s => return (s, [])
          | some (baseLoc, entries, nextId) =>
              match ← mapEntryIndex? ctx keyTy entries key with
              | some i =>
                  -- A delete is a heap write and nothing else (B1): the
                  -- entry leaves the cell, its id is never reissued
                  -- (`nextId` unchanged), and every in-flight range
                  -- sees the absence at its next pick.
                  return fun s => Mem.mapWrite s baseLoc (entries.eraseIdx! i) nextId
              | none =>
                  -- ABSENT key: the payload is unchanged, but the delete
                  -- IS a map write (gc instruments `mapdelete` as a write
                  -- unconditionally — the footprint table always said so):
                  -- the unchanged payload is rewritten so the write is
                  -- emitted (C1 S2a).
                  return fun s => Mem.mapWrite s baseLoc entries nextId
      | _ => stuck "malformed mapDelete operands"
  | .clearMap =>
      match vs with
      | [baseV] => do
          let map ← valueAsMap baseV
          match ← mapEntries s map with
          | none => return fun s => return (s, []) -- nil map: no-op
          | some (baseLoc, _, nextId) =>
              -- `clear` empties the cell; the id counter stays (B1).
              return fun s => Mem.mapWrite s baseLoc #[] nextId
      | _ => stuck "malformed clearMap operands"
  | .clearSlice elem =>
      -- Multi-cell in one apply step, like copySlice: a granularity-ledger
      -- entry to re-audit before any concurrency claim mentions it (R4).
      match vs with
      | [baseV] => do
          let slice ← valueAsSlice baseV
          validateSlice slice
          let zero ← defaultValue ctx elem
          -- One emitting write per visible element (`Mem.storeRun`; a nil
          -- base passes `validateSlice` only at length 0).
          return fun s => Mem.storeRun ctx s slice 0 (List.replicate slice.len zero)
      | _ => stuck "malformed clearSlice operands"
  | .sortSlice _ =>
      -- SINGLE-cell read+write loop in one apply step (granularity-ledger
      -- entry, like clearSlice — a slice's elements all live in ONE
      -- backing cell, so "multi-cell" was the wrong word; corrected
      -- 2026-07-31, pre-merge audit finding 3): load the visible
      -- elements, sort by INTEGER value with the structural `sortLe`
      -- (insertion sort — de-WF 2026-08-03; normalized ints compare
      -- exactly as Go's unsigned/signed order; equal ints are
      -- indistinguishable, so sort stability is unobservable), store
      -- back. Non-int elements fail closed. DEAD since 2026-09-04: the
      -- frontend has never emitted `sort-slice` since memo §3 row M
      -- (slices.Sort is the real pdqsort stencil) and the decoder refuses
      -- the node by name (NativeToIR.lean); this op's deletion is owed to
      -- the design-hygiene arc (item A11).
      match vs with
      | [baseV] => do
          let slice ← valueAsSlice baseV
          let (values, trR) ← Mem.loadSlice ctx s slice
          -- The integer operand check is the structural `intElems` (C1 S2b:
          -- the former `for` accumulator, same refusal at the first non-int
          -- element; `intElems_length` is what the trace theorem needs).
          let loaded ← intElems values.toList
          -- `sortLe`, not `List.mergeSort`: the latter is WF-compiled and
          -- kernel-irreducible (de-WF, 2026-08-03; output provably agrees).
          let sorted := (sortLe (fun a b => a.1 ≤ b.1) loaded).map
            fun (v, kind) => GoValue.int v kind
          return fun s => do
            let (s', trW) ← Mem.storeRun ctx s slice 0 sorted
            return (s', trR ++ trW)
      | _ => stuck "malformed sortSlice operands"
  | .copySlice =>
      match vs with
      | [tv, dstV, srcV] => do
          let dstSlice ← valueAsSlice dstV
          let srcSlice ← valueAsSlice srcV
          validateSlice dstSlice
          validateSlice srcSlice
          let count := Nat.min dstSlice.len srcSlice.len
          -- `count` element reads from the source run, `count` element
          -- writes into the destination run, then the count into the
          -- target — each an emitting operation (a nil base is admitted
          -- only at length 0, where `count = 0`).
          let (values, trR) ← Mem.loadRun ctx s srcSlice count
          -- S3: the count target's nil check precedes the element writes (a
          -- pure reorder — before S3 it followed them and rolled them back).
          let tloc ← valueAsLoc tv
          return fun s => do
            let (current, trW) ← Mem.storeRun ctx s dstSlice 0 values
            let (s', trT) ← Mem.store ctx current tloc (.int (Int.ofNat count))
            return (s', trR ++ trW ++ trT)
      | _ => stuck "malformed copySlice operands"
  | .print newline =>
      -- VALIDATE only (refusals name the kind). The bytes are the step
      -- label's `out` (`stmtOpOut`, the same `renderPrint`), which the pool
      -- event carries since the step-label reshape; the state is untouched
      -- (gc: fd 2 only). [AGENT packet B worker] 2026-09-28, audit F3.
      let _ ← renderPrint newline vs
      return fun s => return (s, [])
  | .appendSlice _ =>
      throw (.internal "applyStmtOpCore: appendSlice dispatches through applyStmtOp")

@[inherit_doc applyStmtOpCore.plan]
def applyStmtOpCore (s : Store) (op : StmtOp)
    (vs : List GoValue) : Except Stop (Store × AccessTrace) := do
  let c ← applyStmtOpCore.plan ctx s op vs
  c s

variable {ctx}
/-- The growth policy never shrinks below the requested length. -/
theorem appendGrowthCap_ge {oldCap newLen : Nat} (h : oldCap < newLen) :
    newLen ≤ appendGrowthCap oldCap newLen := by
  unfold appendGrowthCap
  rw [if_neg (by omega)]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · have hloop : ∀ cap, newLen ≤ appendGrowthCap.loop newLen cap := by
          intro cap
          fun_induction appendGrowthCap.loop with
          | case1 c hge => simpa using hge
          | case2 c hlt ih => exact ih
        exact hloop oldCap

/-- The append-spill site's bound is ≥ 2 at EVERY operand pair: the
envelope's upper end (`appendSpillUpper` = max 32 (2 × growth cap)) is
strictly above the new length, so the spill consult always has a choice
and the uniform rule always pops there — the "width ≥ 2 by construction"
fact the retired per-site policy table asserted in prose. -/
theorem one_lt_appendSpillWidth (oldCap newLen : Nat) :
    1 < appendSpillWidth oldCap newLen := by
  unfold appendSpillWidth appendSpillUpper
  by_cases h : oldCap < newLen
  · have := appendGrowthCap_ge h
    omega
  · unfold appendGrowthCap
    rw [if_pos (by omega)]
    omega

/-- The spill consult is the raw pop (its bound is ≥ 2 always). -/
@[simp] theorem Choices.consumeAt_appendSpill {oldCap newLen : Nat} {ch : Choices} :
    Choices.consumeAt .appendSpill (appendSpillWidth oldCap newLen) ch
      = ch.consume (appendSpillWidth oldCap newLen) :=
  Choices.consumeAt_of_lt (one_lt_appendSpillWidth oldCap newLen)

/-- The spill consult's record-emitting form: the raw pop plus its record. -/
@[simp] theorem Choices.consumeAtE_appendSpill {oldCap newLen : Nat} {ch : Choices} :
    Choices.consumeAtE .appendSpill (appendSpillWidth oldCap newLen) ch
      = ((ch.consume (appendSpillWidth oldCap newLen)).1,
         (ch.consume (appendSpillWidth oldCap newLen)).2,
         [⟨.appendSpill, appendSpillWidth oldCap newLen,
           (ch.consume (appendSpillWidth oldCap newLen)).1⟩]) :=
  Choices.consumeAtE_of_lt (one_lt_appendSpillWidth oldCap newLen)

variable (ctx)
/-- Apply a wide statement's head to its evaluated operands (`nt` leading
target addresses, then values). One state-update step. `appendSlice`'s
spill path consumes a capacity choice — the second nondeterministic point
— and is the ONLY arm that touches the stream; everything else dispatches
to the choices-free `applyStmtOpCore`.

C1 S3 (cost B): THE VALIDATE PHASE (the seam docstring at `Commit`); the
spill's capacity consult happens here, before the seam, so the commit is
the fresh backing's allocation and the header write and consumes nothing.
The composed `applyStmtOp` (below) is the relation's. -/
def applyStmtOp.plan (s : Store) (choices : Choices) (op : StmtOp) (_nt : Nat)
    (vs : List GoValue) : Except Stop (Commit (Store × Choices × List PickRecord × AccessTrace)) := do
  match op with
  | .appendSlice elem =>
      match vs with
      | [tv, sliceV, elemsV] => do
          let slice ← valueAsSlice sliceV
          let elems ← valueAsSlice elemsV
          validateSlice slice
          validateSlice elems
          let (elemValues, trE) ← Mem.loadSlice ctx s elems
          let newLen := slice.len + elemValues.size
          let tloc ← valueAsLoc tv
          if newLen <= slice.cap then
            -- In place: the appended elements are written into the backing's
            -- cells [len, newLen) (one emitting write each), then the header.
            -- (`Mem.storeRun`: a nil base admits only the empty run — the
            -- former «cannot append … into nil slice in place» refusal was
            -- unreachable under `validateSlice`, C1 S2a record.)
            return Commit.withStream choices [] fun s => do
              let (current, trW) ← Mem.storeRun ctx s slice slice.len elemValues.toList
              let (s', trT) ← Mem.store ctx current tloc (.slice { slice with len := newLen })
              return (s', trE ++ trW ++ trT)
          else
            -- gc's `growslice` refusals (runtime/slice.go:191–252; R16
            -- pin, t5-maxalloc 2026-09-02): the new length overflowing
            -- `int`, or the grown backing's byte size exceeding
            -- `maxAllocBytes`, is the recoverable panic `growslice: len
            -- out of range`. Decided on the NEW LENGTH's byte size, NOT
            -- on the chosen capacity: `applyStmtOp_appendSlice_congr`
            -- (MachineSound) states that the outcome CLASS of a spill is
            -- stream-independent, and a cap-based check would make it
            -- false. Consequence, recorded on R16: gc panics on a
            -- SUPERSET — gc panics iff capmem > maxAlloc with capmem =
            -- roundupsize(nextslicecap(newLen, oldCap)·esize) ≥
            -- newLen·esize, this arm iff newLen ≥ 2^63 ∨ newLen·esize >
            -- 2^48 — so wherever newLen's bytes fit but the grown cap's
            -- (≈1.25×) do not, gc raises a recoverable `runtime.Error`
            -- where this arm allocates. That band is a DETERMINISTIC-
            -- PANIC RESIDUAL of fidelity decision 5(b) (observed ∉
            -- modeled; gc never reaches the allocator there, so it is
            -- NOT an allocation failure and NOT under the register #7
            -- rider), unreachable by the corpus (it needs an existing
            -- >2^47-byte slice or `unsafe.Slice`; gc probe append-
            -- growth-over-unsafe is the witness); the in-place path is
            -- never checked (gc calls no growslice there).
            let elemSize ← tySizeBytes ctx.types elem
            if newLen ≥ intExclusiveUpperBound || newLen * elemSize > maxAllocBytes then
              panic "runtime error: growslice: len out of range"
            let (oldValues, trO) ← Mem.loadSlice ctx s slice
            -- The capacity ENVELOPE is [newLen, appendSpillUpper] (the
            -- statement and containment argument live on
            -- `appendSpillUpper`, Ops.lean — arc-final audit F2 /
            -- BUG-021, replacing growth+[0,8), which go1.26.5 escapes
            -- in both directions). The choice is offset so the EMPTY
            -- stream (extra = 0) keeps the growth-formula point — the
            -- strict lane's deterministic behavior is unchanged — while
            -- extra ranges bijectively over the whole envelope.
            let width := appendSpillWidth slice.cap newLen
            let (extra, choices, ps) := Choices.consumeAtE .appendSpill width choices
            let newCap := newLen +
              ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            let backing ← buildAppendBackingValue ctx elem oldValues elemValues newCap
            return Commit.withStream choices ps fun s => do
              let (base, current) ← Store.alloc ctx s backing (.array newCap elem)
              -- Spill: the old elements were read out above; the new backing
              -- is FRESH (no access — the malloc convention); the header write.
              let (s', trT) ← Mem.store ctx current tloc
                (.slice { base := some base, offset := 0, len := newLen, cap := newCap })
              return (s', trE ++ trO ++ trT)
      | _ => stuck "malformed appendSlice operands"
  | op => do
      let c ← applyStmtOpCore.plan ctx s op vs
      return Commit.withStream choices [] c

@[inherit_doc applyStmtOp.plan]
def applyStmtOp (s : Store) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : Except Stop (Store × Choices × List PickRecord × AccessTrace) := do
  let c ← applyStmtOp.plan ctx s choices op nt vs
  c s

/-- Range START (BUG-005 (L) surgery, replacing the retired snapshot):
the ranged map's base cell and its START-ID set — the entry ids live
when the range begins (ids only, never keys or values: keys and values
are read LIVE at production, the spec's forced production-table
clause; entry-identity stamps, B1). Shared verbatim by rule
`Step.mapRangeStart` and `stepFn`'s `mapRangeK` arm. The load here is
a real heap read (the footprint's `mapRangeK` arm). -/
def mapRangeStartSets (s : Store) (v : GoValue) :
    Except Stop (Option Loc × Array Nat × AccessTrace) := do
  let map ← valueAsMap v
  match map.base with
  | none => return (none, #[], [])
  | some base =>
      let (p, tr) ← Mem.mapRead s base
      return (some base, p.1.map (·.1), tr)

/-- The LIVE entries of an in-flight range's map cell (`none` base =
nil map = no entries), ids included. Every `mapIterNext` pick —
including the final done-check — performs this read (gc's exhausted
`mapIterNext` still reads; the U1-closing footprint arm records it). -/
def mapIterLiveEntries (s : Store) (base : Option Loc) :
    Except Stop (Array (Nat × GoValue × GoValue) × AccessTrace) := do
  match base with
  | none => return (#[], [])
  | some l =>
      let (p, tr) ← Mem.mapRead s l
      return (p.1, tr)

/-- Are all entries of a `mapRange` snapshot self-normalized at the range
key/value types — keys at `keyTy`, values at `valTy`? The pick-free
typing check the snapshot step fails closed on (sem-adequacy arc slice 3,
2026-08-04): `mapAssign` only ever stores normalized keys AND values, so
every legitimate snapshot passes identically (differential-validated),
while an ill-typed entry — which would make `mapIterNext`'s per-pick
`bindIterVars` normalization succeed at one pick and fail at another —
is rejected before any pick exists. Structural over the entry list;
kernel-reducible (`isNormalForTy`'s contract — the two-layer index
descent since C2, no fuel). Note the recorded
design named only the KEYS; the value check is forced by the same
obstruction one constructor over — `bindIterVars` normalizes the VALUE
at `valTy` whenever a value variable is bound, so key-only validation
leaves iteration success pick-dependent through the values. -/
def snapshotEntriesSelfNormalizedList (types : TypeEnv) (keyTy valTy : Ty) :
    List (Nat × GoValue × GoValue) → Bool
  | [] => true
  | (_, k, v) :: rest =>
      isNormalForTy types keyTy k && isNormalForTy types valTy v
        && snapshotEntriesSelfNormalizedList types keyTy valTy rest

@[inherit_doc snapshotEntriesSelfNormalizedList]
def snapshotEntriesSelfNormalized (types : TypeEnv) (keyTy valTy : Ty)
    (entries : Array (Nat × GoValue × GoValue)) : Bool :=
  snapshotEntriesSelfNormalizedList types keyTy valTy entries.toList

/-- The PICK-TIME candidate list (BUG-005 (L) surgery; entry-identity
stamps, B1): the live entries, in cell order, whose id is not yet in
`produced`. Pure `Nat` membership — no key comparison, no `Except`, no
fuel: a removed entry is simply absent from the cell, a re-created key
is a new entry with a fresh id and so a candidate again. -/
def filterCandidateList (produced : Array Nat)
    (es : List (Nat × GoValue × GoValue)) : List (Nat × GoValue × GoValue) :=
  es.filter (fun e => !produced.contains e.1)

/-- The PICK-TIME candidates: `filterCandidateList` over the live cell,
VALIDATED self-normalized at the range key/value types — fail closed
otherwise. The validation is the sem-adequacy obstruction's guard,
moved from the retired snapshot step to the pick: an ill-typed live
entry would make `bindIterVars` succeed at one pick and fail at
another, so it is rejected BEFORE any choice is consumed, keeping pick
success choices-independent (`step_complete_any_wf`'s mapIterNext
case rests on exactly this). Shared VERBATIM by the `Step.mapIter*`
rules and `stepFn`. -/
def mapIterCandidates (s : Store) (keyTy valTy : Ty)
    (base : Option Loc) (produced : Array Nat) :
    Except Stop (Array (Nat × GoValue × GoValue) × AccessTrace) := do
  let (entries, tr) ← mapIterLiveEntries s base
  let out := (filterCandidateList produced entries.toList).toArray
  if snapshotEntriesSelfNormalized ctx.types keyTy valTy out then
    return (out, tr)
  else
    throw (.stuck s!"map range live entry not self-normalized at range \
key/value types ({repr keyTy}, {repr valTy})")

/-- Does a MANDATORY candidate remain — a candidate whose id is in the
START-ID set (an entry live when the range began and never removed
since; a deleted-then-re-created key carries a NEW id, so its mandatory
status is gone with the old entry)? While `true`, the STOP slot is
illegal: the spec's production table traverses every surviving entry
("For each iteration, iteration values are produced …"), so an entry
neither removed nor created must be produced before iteration may
end. Pure (B1). Shared verbatim by rule `Step.mapIterStop` and
`stepFn`. -/
def mapIterMandatoryRemains (candidates : Array (Nat × GoValue × GoValue))
    (start : Array Nat) : Bool :=
  candidates.any (fun e => start.contains e.1)

/-- Declare a `mapRange` iteration's key/value variables in a fresh scope
(normalized at the range types), mirroring the interpreter's per-iteration
`declareLocal`s. -/
def bindIterVars (env : LocalEnv) (s : Store) (keyVar valVar : Option String)
    (keyTy valTy : Ty) (key value : GoValue) :
    Except Stop (LocalEnv × Store) := do
  let (env, s) ←
    match keyVar with
    | some name => do
        let kv ← normalizeValueForTy ctx keyTy key
        let (loc, s') ← Store.alloc ctx s kv keyTy
        pure (env.declare name loc, s')
    | none => pure (env, s)
  match valVar with
  | some name => do
      let vv ← normalizeValueForTy ctx valTy value
      let (loc, s') ← Store.alloc ctx s vv valTy
      pure (env.declare name loc, s')
  | none => pure (env, s)

/-! ## Channel statements (channels arc slice 1,
`docs/2026-08-06_channels-arc-design.md` D4/D7)

Send/receive/close follow the wide-statement pattern (an operand plan
evaluated under one frame, `Cont.chanStK`, targets first as checked
addresses) but end in `applyChanOp` — whose outcome is a CONFIGURATION,
not just a state, because a channel op may proceed (`.next`), panic
(`.panicking`), or BLOCK (a `.blocked*` configuration: relation-silent,
step-function-terminal; in this zero-scheduler slice a blocked
configuration is classified as the deadlocked run — exactly Go's
single-goroutine behavior, `fatal error: all goroutines are asleep -
deadlock!`). Buffer FIFO is SPEC ("Channels act as first-in-first-out
queues") — deterministic, no `Choices` consumption anywhere in this
module's channel machinery. -/

/-- One step of a target's address-former CHAIN (round 4, BUG-033):
an index step (consumes one evaluated index operand) or a field step.
gc treats the target's WHOLE chain as one phase-2 address computation —
every step's bounds/nil check fires AT THE STORE, after earlier
targets' stores landed. -/
inductive TargetStep where
  | index
  | field (typeId : TypeId) (fieldName : String)
  deriving Repr, BEq

/-- The phase-1 SHAPE of an assignment target: which operand
expressions phase 1 evaluates for it, and how phase 2 stores through
it. Spec §Assignments evaluates the target's OPERANDS in phase 1; the
address CHAIN's own checks — nil implicit indirections (`p.b`), index
bounds (`bs[9]`, and the INNER `a[9]` of `a[9].f` — BUG-033), a nil
map — are the assignment's, deferred to the STORE in phase 2 (pinned
by `channels/recv-edge/{field,oob}-second-target-stores-first`,
`multi-assign/chain-field-over-index/*` and
`channels/recv-map-elem/first-store-lands`). -/
inductive TargetShape where
  | chain (steps : List TargetStep)
  | mapElem (keyTy valueTy : Ty)
  deriving Repr, BEq

/-- A target resolved by phase 1: its operands' VALUES, store-ready.
The chain's checks live in `storeTarget`/`resolveChain` (phase 2). -/
inductive TargetRef where
  | chain (anchor : GoValue) (idxs : List GoValue) (steps : List TargetStep)
  | mapElem (base key : GoValue) (keyTy valueTy : Ty)
  deriving Repr, BEq

/-- The number of index operands a chain consumes (field steps take
none). -/
def indexStepCount : List TargetStep → Nat
  | [] => 0
  | .index :: rest => indexStepCount rest + 1
  | .field _ _ :: rest => indexStepCount rest

/-- Decompose a target address expression into its address-former SPINE
(the `indexAddr`/`fieldAddr` steps from the anchor outward, inner
first) and the operand expressions phase 1 evaluates: the ANCHOR (the
first non-address-former sub-expression) followed by the index
operands in lexical order. The probed gc boundary (round 4, BUG-033):
the chain's own checks are phase-2 store-time events, while any VALUE
operation in the base — an index-GET producing an inner slice value
(`aa[9]` of `aa[9][0]` on `[][]int`), a deref (`(*bp)[0]`) — is an
index-expression OPERAND, evaluated (checks included) in phase 1. -/
def targetSpine : Expr → List TargetStep × List Expr
  | .indexAddr b i =>
      let (st, ops) := targetSpine b
      (st ++ [.index], ops ++ [i])
  | .fieldAddr b tid f =>
      let (st, ops) := targetSpine b
      (st ++ [.field tid f], ops)
  | e => ([], [e])

/-- Classify one assignment target: its shape plus the operand
expressions phase 1 evaluates for it, left-to-right (always ≥ 1).
`none` fails closed. -/
def targetPlan : Assignee → Option (TargetShape × List Expr)
  | .var id => some (.chain [], [.ref id])
  | .addr e =>
      let (st, ops) := targetSpine e
      some (.chain st, ops)
  | .mapElem b k kt vt => some (.mapElem kt vt, [b, k])
  | .unsupported _ => none

def targetsPlan (targets : List Assignee) : Option (List (TargetShape × List Expr)) :=
  targets.mapM targetPlan

/-- Rebuild a store-ready reference from a shape and its evaluated
operands (arity-checked; `none` is a malformed frame — no rule, fail
closed). -/
def completeTargetRef : TargetShape → List GoValue → Option TargetRef
  | .chain steps, anchor :: idxs =>
      if idxs.length = indexStepCount steps then
        some (.chain anchor idxs steps)
      else none
  | .mapElem kt vt, [b, k] => some (.mapElem b k kt vt)
  | _, _ => none

/-- Replay a resolved chain at STORE time (phase 2): starting from the
anchor value, apply each index/field step — bounds checks
(`indexTargetLoc`) and nil-pointer checks (`valueAsLoc`) fire HERE,
after earlier targets' stores landed (BUG-029/BUG-033). Structural on
`steps`; arity mismatches are malformed frames (fail closed). -/
def resolveChain (s : Store) : GoValue → List TargetStep → List GoValue →
    Except Stop GoValue
  | cur, [], [] => return cur
  | cur, .index :: steps, i :: idxs => do
      resolveChain s (.addr (← indexTargetLoc ctx s cur i)) steps idxs
  | cur, .field tid f :: steps, idxs => do
      resolveChain s (.addr (.field (← valueAsLoc cur) tid f)) steps idxs
  | _, _, _ => stuck "malformed target chain"

/-- Phase 2, one target, one step: the store, with the target chain's
OWN checks — nil address (`valueAsLoc`), bounds (`indexTargetLoc`),
nil field bases, nil map — firing HERE (spec §Assignments: "the
assignments are carried out in left-to-right order"). -/
def storeTarget.plan (s : Store) (r : TargetRef) (v : GoValue) :
    Except Stop (Commit (Store × AccessTrace)) := do
  match r with
  | .chain anchor idxs steps =>
      -- Chain resolution is address formation (peeks) — the VALIDATE phase;
      -- the ONE access is the write at the resolved path — the COMMIT (S3).
      let loc ← valueAsLoc (← resolveChain ctx s anchor steps idxs)
      return fun s => Mem.store ctx s loc v
  | .mapElem b k kt vt => mapAssignValue.plan ctx s kt vt b k v

@[inherit_doc storeTarget.plan]
def storeTarget (s : Store) (r : TargetRef) (v : GoValue) : Except Stop (Store × AccessTrace) := do
  let c ← storeTarget.plan ctx s r v
  c s

/-- The VALUE SOURCE for a spine-riding assignment's stores (round 4,
BUG-034/BUG-037): `.vals` — the evaluated right-hand expressions ARE
the stored values (plain single/multi assign); or a comma-ok source
applied to them at the END of phase 1 — a map lookup
(`[base, key] ↦ [v, ok]`; a nil map yields the zero value, an
unhashable key panics HERE, before any store) or a type assertion
(`[x] ↦ [v, ok]`; the comma-ok form never panics). -/
inductive RhsOp where
  | vals
  | mapLookup (keyTy valueTy : Ty)
  | typeAssert (targetTy : Ty)
  deriving Repr, BEq

/-- Apply the value source to the evaluated right-hand operands.
Shared verbatim by rule `Step.rhsStores` and
`stepFn`'s `rhsK` finish arm. -/
def applyRhsOp (s : Store) : RhsOp → List GoValue → Except Stop (List GoValue × AccessTrace)
  | .vals, vs => return (vs, [])
  | .mapLookup keyTy valueTy, [baseV, keyV] => do
      let map ← valueAsMap baseV
      let key ← normalizeValueForTy ctx keyTy keyV
      let (pair, tr) ← mapLookupValue ctx s map key keyTy valueTy
      return ([pair.1, .bool pair.2], tr)
  | .typeAssert targetTy, [value] => do
      let result ← typeAssertValue ctx value targetTy
      return ([result.1, .bool result.2], [])
  | _, _ => stuck "malformed comma-ok source operands"

/-! ## The `unseq` construct's machine helpers (Stage B, 2026-09-16; design
`docs/2026-09-16_evaluation-order-model-v2.md` §3.3–§3.4). Each is a rule
premise of the `Step.unseq*` rules AND `stepUnseqNext`/`stepUnseqValue`/
`stepUnseqEnter`'s (StepFn.lean) body — one definition per fact. -/

/-- A TARGET-PLAN operand ATOM (v2.1 §3.1's internal normal form): a slot or
admitted source-local read (`.var`), the address of a local (`.ref`), or an
int/bool constant — resolved in ONE step, no evaluation frame, no panic (a
target plan checks NOTHING; its checks are the store's, phase 2). Anything
else refuses by name. -/
def unseqAtom (env : LocalEnv) (s : Store) : Expr → Except Stop (GoValue × AccessTrace)
  | .var id =>
      match env.lookup id with
      | some loc => Mem.loadBinding ctx s loc
      | none => stuck s!"unseq: unbound target operand '{id}'"
  | .ref id =>
      match env.lookup id with
      | some loc => return (.addr loc, [])
      | none => stuck s!"unseq: unbound target operand '{id}'"
  | .intLit value kind => return (.int (kind.normalize value) kind, [])
  | .boolLit b => return (.bool b, [])
  | .stringLit v => return (.string v, [])   -- Stage E E2: a string map key
  | other => stuck s!"unseq: target operand is not an atom (a slot, an admitted local, the address of a local, or an int/bool/string constant): {repr other}"

/-- A binder cell's location: declared in the sweep's scope at ENTER. -/
def unseqCellLoc (env : LocalEnv) (bind : String) : Except Stop Loc :=
  match env.lookup bind with
  | some loc => return loc
  | none => stuck s!"unseq: binder cell '{bind}' is not declared in the sweep's scope"

/-- The frozen target plan bound to `tgt` in the continuation's table. -/
def unseqLookupTarget : List (String × TargetRef) → String → Except Stop TargetRef
  | [], tgt => stuck s!"unseq: target binder '{tgt}' has not been produced"
  | (n, r) :: rest, tgt => if n == tgt then return r else unseqLookupTarget rest tgt

/-- ONE checked access through a frozen target plan (review R6): replay the
chain's own checks (`resolveChain` — bounds, nil) on the FROZEN operand
values — the header and index VALUES the plan froze, never a re-read of
the variable (review R4) — and load. A frozen MAP-ELEMENT plan (Stage E E2,
2026-09-21) reads the entry of the frozen map VALUE at the frozen key VALUE —
the same lookup the comma-ok source performs (`applyRhsOp .mapLookup`:
normalize the key at the key type, `mapLookupValue`; a nil map yields the zero
value after hashing the key; an absent key the zero value) — the compound
form's `m[k] op= …` load through the ONE identity its store uses. -/
def unseqReadTarget (s : Store) : TargetRef → Except Stop (GoValue × AccessTrace)
  | .chain anchor idxs steps => do
      Mem.load ctx s (← valueAsLoc (← resolveChain ctx s anchor steps idxs))
  | .mapElem b k kt vt => do
      let map ← valueAsMap b
      let key ← normalizeValueForTy ctx kt k
      let (pair, tr) ← mapLookupValue ctx s map key kt vt
      return (pair.1, tr)

/-- The `load` body: read through the target, then write the binder cell.
The read's panic precedes the store, so a failing load leaves the state as
it was (the sweep's first failure over the pre-state). -/
def unseqLoad.plan (s : Store) (env : LocalEnv) (targets : List (String × TargetRef))
    (bind tgt : String) : Except Stop (Commit (Store × AccessTrace)) := do
  let r ← unseqLookupTarget targets tgt
  let (v, t₁) ← unseqReadTarget ctx s r
  let loc ← unseqCellLoc env bind
  -- THE COMMIT (S3): the binder cell's write.
  return fun s => do
    let (s', t₂) ← Mem.store ctx s loc v
    return (s', t₁ ++ t₂)

@[inherit_doc unseqLoad.plan]
def unseqLoad (s : Store) (env : LocalEnv) (targets : List (String × TargetRef))
    (bind tgt : String) : Except Stop (Store × AccessTrace) := do
  let c ← unseqLoad.plan ctx s env targets bind tgt
  c s

/-- The atoms of a target plan's operand list, in order (`loadMany`'s shape). -/
def unseqAtoms (env : LocalEnv) (s : Store) : List Expr → Except Stop (List GoValue × AccessTrace)
  | [] => return ([], [])
  | e :: es => do
      let (v, t) ← unseqAtom ctx env s e
      let (vs, ts) ← unseqAtoms env s es
      return (v :: vs, t ++ ts)

/-- The FROZEN-ANCHOR check on a target plan (audit F2, 2026-09-16; design
§3.4): `resolveChain` replays a chain from its anchor VALUE at the checked
load AND at the phase-2 store, and `indexTargetLoc` on an `.addr loc` whose
cell holds a SLICE loads THE CURRENT HEADER at each replay — so a plan
anchored at the ADDRESS of a slice variable (`&a` for `a[i]`), or reaching a
slice-valued cell through `.field`/`.index` steps, reads through one header
and stores through another whenever an occurrence rebinds the variable in
between: the reference's FORBIDDEN hybrid (spike R4, `old 10 20 / a 11
200`). The frozen header must come through a binder (the header VALUE as
the anchor: `.var "$hdr"`, or the source local read at the plan step). This
walks the chain's SHAPE at plan time and performs no check of the plan's
own (a plan checks nothing — its bounds/nil checks stay in phase 2): a step
it cannot see through ends the walk with no refusal; an `.index` step on an
`.addr loc` whose cell holds a `.slice` is refused BY NAME. An ARRAY
variable's address is a stable identity (arrays do not rebind) and passes.
Structural on the step list. -/
def unseqUnfrozenAnchor? (s : Store) : GoValue → List TargetStep → List GoValue → Option String
  | .addr loc, .index :: steps, i :: idxs =>
      match loadLoc ctx s loc with
      | .ok (.slice _) =>
          some s!"unseq: target plan indexes a SLICE VARIABLE through its address ({repr loc}) — the header would be re-read at the load and again at the store, not frozen; freeze the header VALUE through a binder"
      | .ok (.array _) =>
          match valueAsInt i with
          | .ok n => unseqUnfrozenAnchor? s (.addr (.index loc n)) steps idxs
          | .error _ => none
      | _ => none
  | .addr loc, .field tid f :: steps, idxs =>
      unseqUnfrozenAnchor? s (.addr (.field loc tid f)) steps idxs
  | .slice sl, .index :: steps, i :: idxs =>
      match valueAsInt i with
      | .ok n =>
          match sliceIndexLoc sl n with
          | .ok loc => unseqUnfrozenAnchor? s (.addr loc) steps idxs
          | .error _ => none
      | .error _ => none
  | _, _, _ => none

/-- The frozen-anchor check over a completed plan (a map-element plan
carries the map VALUE and the key VALUE — a reference and a value, nothing
re-read; its read is `unseqReadTarget`'s map arm since Stage E E2). -/
def unseqUnfrozenPlan? (s : Store) : TargetRef → Option String
  | .chain anchor idxs steps => unseqUnfrozenAnchor? ctx s anchor steps idxs
  | .mapElem .. => none

/-- The `target` body: the machine's own target resolution
(`targetPlan`/`completeTargetRef`) on FROZEN operand atoms — a plan of sort
TARGET that checks nothing; a plan whose anchor is NOT frozen (a slice
variable's address under an index step) is refused by name
(`unseqUnfrozenPlan?`, audit F2). -/
def unseqTargetPlan (s : Store) (env : LocalEnv) (lhs : Assignee) :
    Except Stop (TargetRef × AccessTrace) :=
  match targetPlan lhs with
  | none => stuck "unseq: unsupported target plan assignee"
  | some (sh, ops) => do
      let (vals, tr) ← unseqAtoms ctx env s ops
      match completeTargetRef sh vals with
      | some r =>
          match unseqUnfrozenPlan? ctx s r with
          | some msg => stuck msg
          | none => return (r, tr)
      | none => stuck "unseq: malformed target plan arity"

/-- The `guard` body (review R2's entry/completion protocol): read the test
binder; equal to `when` → the region ACTIVATES (the guard is DONE); else the
region is SKIPPED (`UnseqGraph.skipRegion`), the completion binder is set to
the short-circuit constant `!when` and its occurrence marked DONE (the only
join), and the guard is DONE. -/
def unseqGuard (s : Store) (g : UnseqGraph) (env : LocalEnv) (st : List UnseqStatus)
    (i : Nat) (test : String) (w : Bool) (out : String) :
    Except Stop (List UnseqStatus × Store × AccessTrace) := do
  let (tv, t₁) ← Mem.loadBinding ctx s (← unseqCellLoc env test)
  let b ← valueAsBool tv
  if b == w then
    return (st.set i .done, s, t₁)
  else
    let st₁ := g.skipRegion st i
    let (s', t₂) ← Mem.store ctx s (← unseqCellLoc env out) (.bool (!w))
    match g.producer? out with
    | some ci => return ((st₁.set ci .done).set i .done, s', t₁ ++ t₂)
    | none => stuck s!"unseq: guard completion binder '{out}' has no producer"

/-- Phase 2's store plan: the frozen target refs and the binder VALUES, in
store order (left to right) — handed to the existing phase-2 spine
(`Cont.storeK`: one store per step, each store's own check at the store,
spec#Assignment_statements). -/
def unseqStorePlan (s : Store) (env : LocalEnv) (targets : List (String × TargetRef)) :
    List (String × String) → Except Stop (List TargetRef × List GoValue)
  | [] => return ([], [])
  | (t, v) :: rest => do
      let r ← unseqLookupTarget targets t
      let val ← loadRoot ctx s (← unseqCellLoc env v)
      let (rs, vs) ← unseqStorePlan s env targets rest
      return (r :: rs, val :: vs)

/-- The `invoke` body's statement: a value call whose targets are the
predeclared binder cells (the results are WRITTEN there by the call's own
phase-2 stores — never declared; v2.1 §3.3). -/
def unseqInvokeStmt (binds : List String) (callee : Expr) (args : List Expr) : Stmt :=
  .callValue (binds.map Assignee.var).toArray callee args.toArray

/-- The `recv` body's statement (Stage E E3): a channel receive whose targets
are the predeclared binder cells — the value (and the comma-ok flag) are
WRITTEN there by the receive's own delivery, never declared. -/
def unseqRecvStmt (binds : List String) (ch : Expr) (elem : Ty) : Stmt :=
  .chanRecv (binds.map Assignee.var).toArray ch elem

/-- The `alloc` body's statement (Stage E E4): the hoisted allocation with the
binder cell as its target — `new` (`&T{…}`, `new(T)`), `make`, or a slice
literal's `makeSlice` followed by its element stores (the decoder's own
`slice-lit` shape, `NativeToIR`). -/
def unseqAllocStmt (bind : String) : AllocSpec → Stmt
  | .new v ty => .allocNew (.var bind) v ty
  | .makeSlice elem len cap => .makeSlice (.var bind) elem len cap
  | .makeMap k v hint => .makeMap (.var bind) k v hint
  | .makeChan elem cap => .makeChan (.var bind) elem cap
  | .sliceLit elem len elems =>
      .seqn (#[Stmt.makeSlice (.var bind) elem (.intLit (Int.ofNat len) .int)
                (some (.intLit (Int.ofNat len) .int))] ++
        (elems.map (fun (iv : Int × Expr) =>
          Stmt.assign (.addr (.indexAddr (.var bind) (.intLit iv.1 .int))) iv.2)).toArray)
  | .mapLit k v entries =>
      -- Stage E5 E5c: the fresh map, then the entry stores in order (the emitter's own map-literal shape).
      .seqn (#[Stmt.makeMap (.var bind) k v none] ++
        (entries.map (fun (kv : Expr × Expr) => Stmt.mapAssign (.var bind) kv.1 kv.2 k v)).toArray)

/-- The `wide` body's statement (Stage E5 E5a, 2026-09-22): the hoisted wide
built-in with the binder cells as its targets — `append` (`Stmt.appendSlice`:
the base slice and the packed / spread elements, already evaluated) and `copy`
(`Stmt.copySlice`), each writing its ONE result cell. The arity is checked
statically (`UnseqGraph.wellFormed?`); a binder list of another length reaches
the machine's own `unsupported` refusal by name, never a silent store. -/
def unseqWideStmt (binds : List String) : WideSpec → Stmt
  | .append elem slice elems =>
      match binds with
      | [b] => .appendSlice (.var b) elem slice elems
      | _ => .unsupported "unseq: wide append with a result arity other than one"
  | .copy dst src =>
      match binds with
      | [b] => .copySlice (.var b) dst src
      | _ => .unsupported "unseq: wide copy with a result arity other than one"
  | .mapLookup base key kt vt =>
      -- Stage E5 E5b: the comma-ok lookup writes the value and the ok flag into the two cells.
      match binds with
      | [v, ok] => .mapLookup (.var v) (.var ok) base key kt vt
      | _ => .unsupported "unseq: wide map lookup with a result arity other than two"
  | .typeAssert operand target =>
      match binds with
      | [v, ok] => .typeAssert (.var v) (.var ok) operand target
      | _ => .unsupported "unseq: wide type assertion with a result arity other than two"

/-- Head of a channel statement (send/receive/close). `elem` is the
element type: sends normalize the value at it (the `mapAssign` key/value
discipline, so buffered values are self-normalized); receives build the
closed-channel zero value from it. The receive head CARRIES its target
assignees (audit response BUG-022): spec §Assignments is two-phase —
the RECEIVE is phase 1's communication, target operands evaluate after
it, and the stores (with their nil-deref / out-of-range panics) are
phase 2 — exactly like the select path's step 4. -/
inductive ChanStOp where
  | send (elem : Ty)
  | recv (targets : List Assignee) (elem : Ty)
  | close
  deriving Repr, BEq

/-- Classify a channel statement: op head plus the operands evaluated
BEFORE the communication, in order — channel THEN value for a send
(pinned by `ordinary-send-eval-order`), just the channel for a receive
(its targets ride the op head, evaluated after the communication —
BUG-022; the drain discriminators `channels/recv-edge/*` pin both the
drain and the deadlock-not-panic classification). `none` for unsupported
assignees and >2 receive targets (fail closed). -/
def chanPlan : Stmt → Option (ChanStOp × List Expr)
  | .chanSend ch value elem => some (.send elem, [ch, value])
  | .chanRecv targets ch elem => do
      if targets.size > 2 then none else
      let _ ← targetsPlan targets.toList
      return (.recv targets.toList elem, [ch])
  | .closeChan ch => some (.close, [ch])
  | _ => none

variable {ctx}
/-- The channel-statement plan and the wide-statement plan classify
DISJOINT statements: a statement `chanPlan` recognizes is never one
`stmtPlan` recognizes. `step_det`'s rule-disjointness sweep cites this
(as a conditional simp lemma) to refute the generic-statement cross
pairs without casing the statement. -/
theorem stmtPlan_of_chanPlan {stmt : Stmt} {p : ChanStOp × List Expr}
    (h : chanPlan stmt = some p) : stmtPlan stmt = none := by
  cases stmt <;> simp_all [chanPlan, stmtPlan]

variable (ctx)
/-- Load a channel's data cell: (buffer, capacity, closed). -/
def chanCell (s : Store) (loc : Loc) :
    Except Stop (Array GoValue × Nat × Bool) :=
  chanPayload? s loc

/-- The values a receive delivers to its target list: the received value,
plus the comma-ok Bool when the form has two targets. -/
def recvStores (v : GoValue) (ok : Bool) : Nat → List GoValue
  | 2 => [v, .bool ok]
  | 1 => [v]
  | _ => []

/-! ## Sync-package primitives (spec-parity slice 2,
`docs/2026-08-09_sync-package-design.md`)

THE REGISTRY ENTRY (the channels-arc D2+D3 growth contract exercised as
designed — one registration, nothing revises): each sync op's APPLY
position is (a) a SCHEDULING POINT — it joins `Config.atBoundary`, so
the EXISTING L1 scheduler site is consulted there (consumed only at
|runnable| > 1; the sync ops add ZERO new `Choices` sites — see the
envelope statement at `applySyncOpCore` — EXCEPT the [USER]-ruled
`tryLock` site of the TRY heads, Q-TRYLOCK row 5: the envelope
statement at `applyTryLock`) — and (b) an HB EDGE SOURCE — `raceUpdate`
(Multi.lean) classifies sync applies/wakes and advances the per-cell
sync clocks (`RaceState.syncAcquire`/`syncRelease`, Race.lean; the
package-doc sentences quoted there). Blocked ops are the ONE new
blocked-Config shape `.blockedSync`; wake is CELL-based (`wakeReady`),
and which contender acquires next is pure L1 latitude — sync needs no
arrival intercept, no pairing step, and no L4-analogue waiter pick,
because nothing transfers between goroutines except through the cell. -/

/-- Machine-level sync operation: the `SyncStmtOp` head with the
`onceBegin` target payload validated in (the `ChanStOp.recv` shape).
The TRY heads (Q-TRYLOCK) carry their Bool result target the same way
— a list of length ≤ 1 (empty = the result is discarded). -/
inductive SyncOp where
  | lock
  | unlock
  | rlock
  | runlock
  | wlock
  | wunlock
  | wgAdd
  | wgWait
  | onceBegin (targets : List Assignee)
  | onceComplete
  | tryLock (targets : List Assignee)
  | tryRLock (targets : List Assignee)
  | tryWLock (targets : List Assignee)
  deriving Repr, BEq

/-- The TRY heads' result targets — `some` exactly for the three heads
that draw the `tryLock` site (`applySyncOp` dispatches on this; the
consumption predicates `consumesTryLock`/`stepNeeds` mirror it). -/
def SyncOp.tryTargets? : SyncOp → Option (List Assignee)
  | .tryLock ts | .tryRLock ts | .tryWLock ts => some ts
  | .lock | .unlock | .rlock | .runlock | .wlock | .wunlock
  | .wgAdd | .wgWait | .onceBegin _ | .onceComplete => none

/-- Classify a sync statement: op head plus the operands evaluated
before the apply — the receiver ADDRESS expression, plus the delta for
`wgAdd`. Fails closed (`none`) on arity drift, on targets anywhere but
`onceBegin` and the TRY heads, on a target count ≠ 1 for `onceBegin`,
on a target count > 1 for a TRY head (0 = discarded result), and on
unsupported target assignees (the `chanPlan` discipline). -/
def syncPlan : Stmt → Option (SyncOp × List Expr)
  | .syncStmt .lock args targets =>
      if targets.isEmpty && args.size == 1 then some (.lock, args.toList) else none
  | .syncStmt .unlock args targets =>
      if targets.isEmpty && args.size == 1 then some (.unlock, args.toList) else none
  | .syncStmt .rlock args targets =>
      if targets.isEmpty && args.size == 1 then some (.rlock, args.toList) else none
  | .syncStmt .runlock args targets =>
      if targets.isEmpty && args.size == 1 then some (.runlock, args.toList) else none
  | .syncStmt .wlock args targets =>
      if targets.isEmpty && args.size == 1 then some (.wlock, args.toList) else none
  | .syncStmt .wunlock args targets =>
      if targets.isEmpty && args.size == 1 then some (.wunlock, args.toList) else none
  | .syncStmt .wgAdd args targets =>
      if targets.isEmpty && args.size == 2 then some (.wgAdd, args.toList) else none
  | .syncStmt .wgWait args targets =>
      if targets.isEmpty && args.size == 1 then some (.wgWait, args.toList) else none
  | .syncStmt .onceComplete args targets =>
      if targets.isEmpty && args.size == 1 then some (.onceComplete, args.toList) else none
  | .syncStmt .onceBegin args targets =>
      if args.size == 1 && targets.size == 1 then
        match targetsPlan targets.toList with
        | some _ => some (.onceBegin targets.toList, args.toList)
        | none => none
      else none
  | .syncStmt .tryLock args targets => tryPlan .tryLock args targets
  | .syncStmt .tryRLock args targets => tryPlan .tryRLock args targets
  | .syncStmt .tryWLock args targets => tryPlan .tryWLock args targets
  | _ => none
where
  /-- A TRY head's plan: one receiver operand; zero targets (discarded
  result) or one plannable target. -/
  tryPlan (mk : List Assignee → SyncOp) (args : Array Expr)
      (targets : Array Assignee) : Option (SyncOp × List Expr) :=
    if args.size == 1 then
      match targets.toList with
      | [] => some (mk [], args.toList)
      | [t] =>
          match targetsPlan [t] with
          | some _ => some (mk [t], args.toList)
          | none => none
      | _ :: _ :: _ => none
    else none

variable {ctx}
/-- Sync statements and wide statements classify DISJOINT statements
(the `stmtPlan_of_chanPlan` twin, for `step_det`'s rule-disjointness
sweep). -/
theorem stmtPlan_of_syncPlan {stmt : Stmt} {p : SyncOp × List Expr}
    (h : syncPlan stmt = some p) : stmtPlan stmt = none := by
  cases stmt <;> simp_all [syncPlan, stmtPlan]

/-- Sync statements and channel statements classify disjoint
statements. -/
theorem chanPlan_of_syncPlan {stmt : Stmt} {p : SyncOp × List Expr}
    (h : syncPlan stmt = some p) : chanPlan stmt = none := by
  cases stmt <;> simp_all [syncPlan, chanPlan]

variable (ctx)
/-- Load a sync primitive's cell. A non-sync cell is `stuck` (fail
closed — the frontend types every receiver). -/
def syncCell (s : Store) (loc : Loc) : Except Stop SyncPrim := do
  match ← loadLoc ctx s loc with
  | .syncData p => return p
  | other => stuck s!"expected sync primitive data, got {repr other}"

/-! ## `sync/atomic` integer ops (the atomics arc, wave 1 —
Q-ATOMIC RULED [USER] 2026-09-02 option A′; design note
`docs/2026-09-03_atomics-w1-design.md`)

THE REGISTRY ENTRY, in the sync mold (the channels-arc D2+D3 growth
contract, one registration): each atomic op's APPLY position is (a) a
SCHEDULING POINT — it joins `Config.atBoundary`, its proceeding outcome
opens the goroutine's `postOp` boundary (B1/C5: `Thread.afterStep`,
Multi.lean), and the EXISTING L1 site is consulted
there; the op itself consumes ZERO choices (the envelope statement at
`applyAtomicOp`) — and (b) an HB EDGE SOURCE — `raceUpdate` (Multi.lean)
records the op's access kind and advances the per-ADDRESS atomic clock
(`RaceState.atomicAcquire`/`atomicReleaseStore`/`atomicReleaseAcquire`,
Race.lean — TSan's realized edges, mem#atomic's "synchronized before"
quoted there). No blocked shape: atomics never park. -/

/-- Machine-level atomic operation: the `AtomicStmtOp` head, the
addressed cell's integer kind, and the validated result target (the
`SyncOp.onceBegin` payload shape — a `List Assignee` of length ≤ 1;
always `[]` for `store`). -/
structure AtomicOp where
  head : AtomicStmtOp
  kind : IntKind
  targets : List Assignee
  deriving Repr, BEq

/-- Operand count of an atomic head: the address, then the value
operands (`store`/`add`/`swap`: one; `cas`: old, new). -/
def atomicArity : AtomicStmtOp → Nat
  | .load => 1
  | .store => 2
  | .add => 2
  | .swap => 2
  | .cas => 3

/-- The integer kinds the wave-1 op family is defined over — exactly
the `sync/atomic` integer functions' operand types (`uintptr` arrives
as `uint64` from the frontend, the R1 pin). Any other kind is a
malformed statement (fail closed at the plan). -/
def atomicKindOk : IntKind → Bool
  | .int32 | .int64 | .uint32 | .uint64 => true
  | _ => false

/-- Classify an atomic statement (`atomicPlan`): op + kind + result
target, plus the operands evaluated before the apply (address first).
Fails closed (`none`) on arity drift, on an unsupported kind, and on a
target list `atomicTargetsOk` rejects — any target for `store`, more
than one target, or an unsupported target assignee (the
`syncPlan`/`chanPlan` discipline). -/
def atomicTargetsOk : AtomicStmtOp → List Assignee → Bool
  | .store, ts => ts.isEmpty
  | _, [] => true
  | _, [t] => (targetsPlan [t]).isSome
  | _, _ :: _ :: _ => false

@[inherit_doc atomicTargetsOk]
def atomicPlan : Stmt → Option (AtomicOp × List Expr)
  | .atomicStmt op kind args targets =>
      if args.size == atomicArity op && atomicKindOk kind
          && atomicTargetsOk op targets.toList then
        some (⟨op, kind, targets.toList⟩, args.toList)
      else none
  | _ => none

variable {ctx}
/-- Atomic statements and wide statements classify DISJOINT statements
(the `stmtPlan_of_syncPlan` twin). -/
theorem stmtPlan_of_atomicPlan {stmt : Stmt} {p : AtomicOp × List Expr}
    (h : atomicPlan stmt = some p) : stmtPlan stmt = none := by
  cases stmt <;> simp_all [atomicPlan, stmtPlan]

/-- Atomic statements and channel statements classify disjoint
statements. -/
theorem chanPlan_of_atomicPlan {stmt : Stmt} {p : AtomicOp × List Expr}
    (h : atomicPlan stmt = some p) : chanPlan stmt = none := by
  cases stmt <;> simp_all [atomicPlan, chanPlan]

/-- Atomic statements and sync statements classify disjoint
statements. -/
theorem syncPlan_of_atomicPlan {stmt : Stmt} {p : AtomicOp × List Expr}
    (h : atomicPlan stmt = some p) : syncPlan stmt = none := by
  cases stmt <;> simp_all [atomicPlan, syncPlan]

variable (ctx)
/-- The VALUE semantics of one atomic op on the cell's current value
`cur` (already at `kind`) and the evaluated value operands:
`(new?, result)` — the value to store (`none` = the cell is untouched)
and the value delivered to the result target. Every value operand is
normalized at `kind` (the cell's own kind; the frontend types every
operand at it — `IntKind.normalize` is the two's-complement wrap of
spec#Integer_overflow, which is what `Add` realizes: "AddInt32 …
atomically adds delta to *addr" with the ordinary wrapping
arithmetic — `AddUint32(&x, ^uint32(c-1))` is the documented
decrement idiom). `cas`: swapped iff `cur == old` at `kind`. Pure
(the state update and the delivery are `applyAtomicOp`'s), shared
with `raceUpdate`'s atomic arm, which re-derives a CAS's outcome from
the pre-state to pick the release/acquire shape. -/
def atomicCompute (head : AtomicStmtOp) (kind : IntKind) (cur : Int)
    (operands : List GoValue) : Except Stop (Option Int × GoValue) :=
  match head, operands with
  | .load, [] => return (none, .int cur kind)
  | .store, [v] => do return (some (kind.normalize (← valueAsInt v)), .unit)
  | .add, [d] => do
      let n := kind.normalize (cur + (← valueAsInt d))
      return (some n, .int n kind)
  | .swap, [v] => do return (some (kind.normalize (← valueAsInt v)), .int cur kind)
  | .cas, [o, n] => do
      if cur == kind.normalize (← valueAsInt o) then
        return (some (kind.normalize (← valueAsInt n)), .bool true)
      else
        return (none, .bool false)
  | head, vs =>
      stuck s!"malformed atomic-operator application: {repr head} on {vs.length} value operand(s)"

/-- One `select` clause with its entry-time operands EVALUATED (spec
§Select statements, step 1): the channel value (and send value) are
pinned; receive targets stay as their assignee expressions — evaluated
only after selection (step 4). The payload of the readiness step and of
the `.blockedSelect` configuration. -/
inductive EvClause where
  | sendEv (chv v : GoValue) (elem : Ty) (body : Stmt)
  | recvEv (chv : GoValue) (targets : List Assignee) (elem : Ty) (body : Stmt)
  deriving Repr, BEq

/-- The entry-time operand list of a `select` (step 1, source order): per
clause the channel operand, plus the RHS value for send clauses. -/
def selectOperands : List (SelectClauseHead × Stmt) → List Expr
  | [] => []
  | (.send ch v _, _) :: rest => ch :: v :: selectOperands rest
  | (.recv _ ch _, _) :: rest => ch :: selectOperands rest

/-- Zip the evaluated entry operands back onto the clauses (the inverse
of `selectOperands`' flattening). Fails closed on arity drift and on
unsupported receive-target assignees. -/
def evalClauses : List (SelectClauseHead × Stmt) → List GoValue →
    Except Stop (List EvClause)
  | [], [] => return []
  | (.send _ _ elem, body) :: rest, chv :: vv :: vs => do
      return .sendEv chv vv elem body :: (← evalClauses rest vs)
  | (.recv targets _ elem, body) :: rest, chv :: vs => do
      match targetsPlan targets.toList with
      | some _ => return .recvEv chv targets.toList elem body :: (← evalClauses rest vs)
      | none => throw (.unsupported "unsupported select receive target assignee")
  | _, _ => stuck "malformed select operand values"

/-- Clause readiness — a pure function of the channel cells (spec step 2
"can proceed", with one runtime-pinned subtlety: a SEND on a closed
channel counts as READY and panics when selected — probe p23;
`select.go`'s pass-1 send check tests closed first). A nil channel is
never ready. -/
def clauseReady (s : Store) : EvClause → Except Stop Bool
  | .sendEv chv _ _ _ => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return false
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          return closed || buf.size < capacity
  | .recvEv chv _ _ _ => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return false
      | some loc => do
          let (buf, _, closed) ← chanCell s loc
          return buf.size > 0 || closed

/-- The ready sublist, in clause order. -/
def readyClauses (s : Store) : List EvClause → Except Stop (List EvClause)
  | [] => return []
  | c :: rest => do
      let tail ← readyClauses s rest
      if ← clauseReady s c then return c :: tail else return tail

/-! ## The registry ops' EMISSIONS (C1 S2c, charter §7 D9) — what a channel, select,
sync or atomic apply puts in its label, in gc's instrumentation order

The module's discipline (Ops.lean, «The memory module's access discipline»)
extends to synchronization: the apply that performs a registry op EMITS the
memory-model events gc's `-race` runtime realizes there — the channel-object
reads/writes (BUG-045/BUG-046), the sync primitives' own word accesses
(BUG-080), the `sync/atomic` op's access at its cell, and the happens-before
ACTIONS (`HbAction`) the runtime performs — and the detector's fold
(`raceUpdate`, Multi.lean) consumes them. Until S2c these were the fold's
REGISTRY ARMS, re-derived from the pre-configuration and the pre/post cells
(`raceWakeEvent`, `racePairEvent`, `raceCommitClauseEvent`, `raceChanEntryReads`,
`tryLockAcquired`): two accounts of one step, kept in lockstep by review. Now
there is one. The tables below are the derivations; the applies call them. -/

/-- The channel a chan-value points at (`none` for nil channels and
non-channel values). -/
def chanValueLoc : GoValue → Option Loc
  | .chan cv => cv.base
  | _ => none

/-- gc's `chansend` reads the channel object at ENTRY (`racereadpc(c.raceaddr())`,
chan.go; BUG-045): recorded whether the send then commits, parks or panics — the
`.chanObj` key, exact identity (`ShadowKey.overlap`). A nil channel has no object
(the caller emits nothing). -/
def chanSendEntry (loc : Loc) : AccessTrace := [.access .read (.chanObj loc.canon)]

/-- `closechan`'s `racewritepc(c.raceaddr())` on its SUCCESS path (BUG-045; the
closed/nil panics fire before it) — checked under the closer's pre-release clock,
so it PRECEDES the `.closeOp` action in the label. -/
def chanCloseWrite (loc : Loc) : AccessTrace := [.access .write (.chanObj loc.canon)]

/-- `selectgo` pass 1 (select.go; BUG-046): one channel-object READ per EVERY send
clause — the UNION over gc's random `pollorder` (select.go:270–299: pass 1 walks
`pollorder` and leaves at the first ready case, so gc's `racereadpc(c.raceaddr())`
fires only for the send cases reached up to and including the chosen one; which
those are is the shuffle's, and any pollorder is gc's, so the weakest-machine
reading records them all — fail-closed, refusals ⊇ gc's per schedule; the C1 S2c
audit's F7, `docs/2026-09-19_c1-s2c-audit.md`, litmus `selectPollVsClose`: gc
2–3/5 by pollorder luck, the machine on every path; latitude inventory C10) —
receive clauses are acquire-only, nil channels are not in `pollorder`. Emitted at
the select's apply position on every path from it (the cell path
`applySelectCore`, the arrival pairing and the arrival commit — `arrivalPoll`,
Multi.lean), never at a WAKE (the sudog was dequeued by the partner;
`resumeThread` re-polls nothing). Recording in clause order is
detection-equivalent (same pre-op clock; same-goroutine re-records upsert). -/
def selectPoll : List EvClause → AccessTrace
  | [] => []
  | .sendEv chv _ _ _ :: rest =>
      (match chanValueLoc chv with
      | some loc => chanSendEntry loc
      | none => []) ++ selectPoll rest
  | .recvEv _ _ _ _ :: rest => selectPoll rest

/-- The access KIND a `sync/atomic` op records at the addressed cell —
both registers agree (Race.lean, section "sync/atomic — the per-address
clocks"): a Load is an atomic read; Store, Add, Swap and CompareAndSwap
(succeed or fail) atomic writes. -/
def atomicOpKind : AtomicStmtOp → AccessKind
  | .load => .atomicRead
  | .store | .add | .swap | .cas => .atomicWrite

/-! ## The sync primitives' OWN state words (BUG-080 — U4 CLOSED; Q-U4RESIDUAL RULED (A))

Two registers say what a sync op does to its primitive's own words,
and since the [USER] ruling of 2026-09-02 (Q-U4RESIDUAL, option (A) —
`docs/2026-08-31_qrow-rulings.md` row 9) the detector records the UNION
of both — the union itself an [AGENT] READING of the ruling,
COUNTERSIGNED [USER] 2026-09-03 (provenance chain: ledger [DL-10]):

1. **go_mem's operation kind** (mem#model, verbatim: "Some memory
   operations are read-like, including read, atomic read, mutex lock,
   and channel receive. Other memory operations are write-like,
   including write, atomic write, mutex unlock, channel send, and
   channel close. Some, such as atomic compare-and-swap, are both
   read-like and write-like."). Every sync op is a SYNCHRONIZING
   operation on its primitive, so its kind is recorded as an ATOMIC
   kind — `.atomicRead` for a read-like op, `.atomicWrite` for a
   write-like one: by mem#model's read-write/write-write definitions
   ("at least one of which is non-synchronizing") two sync ops never
   race each other, while a plain access beside a write-like op — or a
   plain write beside a read-like one — IS a data race, TSan or no
   TSan. mem#locks names the ops for BOTH `sync.Mutex` and
   `sync.RWMutex` ("The sync package implements two lock data types"):
   `RLock`/`Lock` are mutex lock = read-like, `RUnlock`/`Unlock` are
   mutex unlock = write-like. mem#more defers WaitGroup and Once to
   their package docs: `Done` "synchronizes before" the return of the
   `Wait` it unblocks (waitgroup.go), the release/acquire shape of
   unlock/lock and send/receive — so `Add`/`Done` (the counter RMW) are
   write-like and `Wait` read-like; `Once.Do`'s completion
   "synchronizes before" every return (mem#once), so the first `Do` is
   write-like and a `Do` observing completion read-like.
2. **What gc's `-race` build realizes** on the words, read PRIMITIVE BY
   PRIMITIVE from the pinned sources (go1.26.5) — the oracle's register
   (#13). `sync`, `internal/sync` and `sync/atomic` are
   `noRaceFuncPkgs` (cmd/internal/objabi/pkgspecial.go), and under
   `-race` the SSA builder skips memory instrumentation for every
   function of such a package (cmd/compile/internal/ssagen/
   ssa.go:340-342) — so their own plain loads/stores (e.g. `lockSlow`'s
   `old := m.state`) are invisible and the packages annotate by hand.
   Exactly three things reach TSan: `race.Read/Write` annotations,
   `race.Acquire/Release*` hooks, and `sync/atomic` calls — which the
   -race build routes to TSan's atomic hooks (runtime/race_amd64.s
   `racecallatomic`) UNLESS `race.Disable()` is active, in which case
   Go's TSan glue performs them un-instrumented (measured:
   `probes/u4kind/{wg-copy-vs-done,rw-copy-vs-rlock}` gc-green).

Why the union ([AGENT] reading), and why it is sound: mem#restrictions
licenses ANY implementation to "report the race and halt execution" on
detecting a data race, so a refusal the oracle would not issue costs
completeness (a go_mem-racy program the `-race` build happens to run)
never soundness; and every access TSan realizes is kept, so nothing
the oracle refuses is run here (no HOLE cell opens). WHERE THIS
DEPARTS FROM LITERAL go_mem: mem#model's operation-level list makes
EVERY mutex lock read-like, `sync.Mutex.Lock` included, so "follow
go_mem exactly" read literally would RUN a lone copy beside
`Mutex.Lock`. gc's `-race` build REFUSES it — the Lock is a CAS on
`m.state`, reported by TSan as a Write (measured: `probes/u4gomem/
mu-copy-vs-lock-only`, the copy unordered with the Lock op ALONE, gc
RACE 20/20 at GOMAXPROCS 1 and 8, machine RACE — agree-race; and the
BUG-080 pin `race/negative-sync/mutex-copy`). Dropping the realized
`.atomicWrite` would open a HOLE cell against the oracle, so the
[AGENT] kept it, grounded in mem#model's own sentence that a
compare-and-swap "is both read-like and write-like" (the read-like
half adds no conflict an atomic write lacks). THE CONSEQUENCE, plainly:
a lone copy beside `sync.Mutex.Lock` REFUSES, a lone copy beside
`sync.RWMutex.Lock`/`RLock` RUNS (`race/free-sync/rw-copy-beside-
{rlock,lock}`) — because TSan realizes Mutex's CAS but runs RWMutex's
counter RMW under `race.Disable`, leaving only go_mem's read-like lock
kind to apply. The asymmetry is the oracle's, inherited on purpose,
and [USER]-countersigned 2026-09-03 (above).
Where TSan realizes NOTHING (`race.Disable`) the go_mem kind alone is
recorded — the former residual (a), now closed BY DESIGN.

WHERE each access lands — the gc WORD, the `ShadowKey.syncWord` of the
sync cell's path, kind and word (`SyncWordName`: the field names of the
pinned struct definitions). A whole-struct copy/overwrite at the
primitive's or an enclosing path overlaps every word
(`ShadowKey.overlap`'s data/word arm is `locPrefix`); a SIBLING field's
plain access overlaps none (check
(i) of the BUG-080 ruling — `probes/u4kind/mu-siblings-under-lock`,
`mu-disjoint-prims`, `mu-sibling-beside-lock` and the corpus rows
`race/free-sync/{mutex-siblings,disjoint-prims}` are the green guards).
The words being DISTINCT is load-bearing: the `wg.sema` misuse pair
and RWMutex's `race.Read(&rw.w)` are PLAIN accesses in TSan's
realization, and had they shared one path with the go_mem atomic
kinds, a legal `Done` (atomic write) would conflict with a legal first
`Wait` (plain sema write), and a contending `RLock` (plain `rw.w`
read) with an `Unlock` (atomic write). On gc's own layout they are
different words and never meet — exactly as they never meet under
TSan.

THE TABLE (entry = before the op's acquire/release action, under the
pre-op clock, commit or park alike — `syncEntryKinds`; tail = after a
committed op's release action, at the bumped epoch —
`syncReleaseTailKinds`; both EMITTED by the sync apply in that order,
C1 S2c):

* **Mutex** (`internal/sync/mutex.go`): `Lock` → `.atomicWrite @state`
  (the CAS, :63, whether it wins or falls into `lockSlow`'s CAS loop —
  TSan "Write … CompareAndSwapInt32"; go_mem's read-like lock is
  subsumed); `Unlock` → entry nothing, tail `.atomicWrite @state` (the
  Add at :194 follows `race.Release` :190). go_mem's write-like unlock
  is covered by the tail alone: an access unordered with the op is
  unordered with the tail (the release joins nothing INTO the
  unlocker's clock), and the tail additionally catches the acquirer's
  own later plain read — TSan's verdict. The `_ = m.state` at :189 is
  an uninstrumented load in a `noRaceFuncPkgs` package — nothing
  (guards: ledger [DL-15]).
* **RWMutex** (`sync/rwmutex.go`): every op opens with
  `race.Read(unsafe.Pointer(&rw.w))` (:69/:116/:146/:203) → `.read @w`
  (realized, kept), then under `race.Disable()` performs its counter
  RMW → the go_mem kind `@readerCount`: `RLock`/`Lock` → `.atomicRead`
  (lock is read-like: a copy beside the LOCK OP ALONE is read-like
  beside read-like, NO race — the ruling's own statement of what is
  NOT in the class), `RUnlock`/`Unlock` → `.atomicWrite` (unlock is
  write-like: a copy beside them REFUSES where TSan is green — by
  design). Probe isolations and the BUG-080 probe-shape note: ledger
  [DL-16].
* **WaitGroup** (`sync/waitgroup.go`): the state RMW runs under
  `race.Disable()` (:83, :162) → go_mem kind `@state`: `Add`/`Done` →
  `.atomicWrite` (a copy or overwrite beside them refuses — TSan sees
  neither), `Wait` → `.atomicRead` (an overwrite beside a `Wait` at
  counter 0 refuses; a copy beside any `Wait` that is not the first
  blocking waiter does not). Realized and kept, `@sema`: the misuse
  pair — a plain READ when an Add takes the counter off 0 upward
  (:111-115), a plain WRITE when the FIRST waiter registers before
  parking (:184-190); Add↔Wait misuse detection is unchanged (same
  pair, same check, at its own word), and the first waiter's plain
  write is why a copy beside a first blocking `Wait` stays red (probe:
  ledger [DL-17]).
* **Once** (`sync/once.go`, no `race.Disable`): `Do` opens with the
  atomic LOAD of `o.done` (:67) — a Do observing completion is that
  `.atomicRead @done` alone (read-like: a copy beside it is green, an
  overwrite red); every other Do takes `doSlow`, whose `o.m.Lock()` CAS
  is `.atomicWrite @m` (the winner's and the parked contender's
  alike). The winner's completion (`onceComplete`) is the deferred
  `o.done.Store(true)` → `.atomicWrite @done` BEFORE the deferred
  `o.m.Unlock()` (LIFO) — then the Unlock's release and its trailing
  Add → tail `.atomicWrite @m`. go_mem and TSan agree on every Once
  row.

* **TryLock / TryRLock** (Q-TRYLOCK, RULED [USER] 2026-08-31 row 5):
  `Mutex.TryLock` (`internal/sync/mutex.go:76-93`) on an UNLOCKED cell →
  `.atomicWrite @state` on BOTH envelope members (the CAS at :85 is
  realized whether it wins or loses); on a HELD cell → NOTHING (the early
  return is an uninstrumented plain load); go_mem adds nothing to a
  failed call ("An unsuccessful call has no synchronizing effect at
  all"). `RWMutex.TryRLock`/`TryLock` (`sync/rwmutex.go:87-112,169-198`):
  the realized `race.Read(&rw.w)` precedes `race.Disable` on EVERY
  outcome → `.read @w` always; the counter CAS runs under `race.Disable`,
  so only go_mem's kind applies and only to a SUCCESSFUL call →
  `.atomicRead @readerCount` when acquired (the `rlock`/`wlock` row).
  HB: the acquire edge on success only. Probe runs (20 each at
  GOMAXPROCS 1 and 8) and the one schedule-dependent, unpinnable gc
  shape: ledger [DL-11].

Atomic↔atomic never conflicts, so contending ops on one primitive stay
green (guards: ledger [DL-18]).

Wakes record nothing: a parked goroutine released nothing after its
entry, so no other goroutine can be HB-after the entry without being
HB-after the wake — every conflict a wake-time access would find, the
entry access already found (gc's woken `lockSlow` CAS is thus
detection-redundant here).

THE DESIGNED DIVERGENCE FROM THE `-race` ORACLE (was residual (a);
[USER]-ruled 2026-09-02 — recorded at BUGS.md BUG-084 and the ruling
sheet's row 9, provenance chain there): a plain access beside a
write-like op gc runs under `race.Disable` — `RUnlock`, RWMutex
`Unlock`, WaitGroup `Add`/`Done` — or a plain OVERWRITE beside `Wait`
at counter 0, is REFUSED here and RUN by gc's `-race` build. The racy
lane's three-way rule (our refusal + `-race` green on every sample)
files such a row as an investigation, never a pass; these rows are
classified BY DESIGN as go_mem-racy (one write-like operand, one
non-synchronizing — mem#model). The corpus pins them as born-FAIL rows
against gc's `ok` observation (`race/gomem-only/*`, BUG-084's Cases
line) so the divergence stays visible and never counts as a pass. NOT
in the class, and unchanged: a copy beside `RLock`/`Lock` ALONE (two
read-likes) and every race-free program (vet's `copylocks` flags every
shape in the class). Probe families and guards: ledger [DL-19].

RESIDUAL (b), an outcome-CLASS deviation — both sides ABORT, but the
machine's abort is an asserted program outcome (`Stop.fatal`,
Value.lean:207-217) where gc's is the race report then the same abort:
the
detector folds SUCCESSFUL pool steps only (`execProgLoop` runs
`raceUpdate` after `stepMulti` returns), so a sync op whose apply is
FATAL — an `Unlock`/`RUnlock` after a concurrent plain overwrite reset
the primitive to unlocked — ends the run `fatal` before its entry
access is ever checked, where gc's `race.Read`/state Add precede the
misuse check and TSan reports the race first, then the fatal fires.
Reachable only by an overwrite-then-cross-goroutine-unlock shape
(`probes/u4kind/rw-overwrite-vs-{runlock,unlock}`, possible-HOLE by the
runner's definition, diagnosed at BUG-080). The owed fix's scope and
its call-site list are AUTHORITATIVE at TODO.md's BUG-080 follow-up
item (S–M, trust-surface) — cited, not restated here. -/

/-- The gc WORD of a sync primitive an access lands on: the
`ShadowKey.syncWord` of the primitive's own cell path, its kind and the
word (`state`/`sema` for Mutex and WaitGroup, `w`/`readerCount` for
RWMutex, `done`/`m` for Once — the section docstring's table). A shadow
KEY (A6; formerly a phantom `Loc.field` path under a made-up `TypeId`):
`ShadowKey.overlap` is what makes a copy/overwrite of the primitive (or
its enclosing struct) overlap the word while sibling fields and sibling
words stay disjoint. -/
def syncWord (loc : Loc) (kind : SyncKind) (word : SyncWordName) : ShadowKey :=
  .syncWord loc.canon kind word

/-- The accesses recorded on the primitive's own words at a sync op's
ENTRY — before the op's release/acquire hook — from the op and the
PRE-step cell (`delta` is `wgAdd`'s operand, 0 for every other op):
TSan's realized set ∪ go_mem's operation kind, each at its gc word
(the section docstring's table is the derivation; Q-U4RESIDUAL (A)).
EMITTED by the sync apply (`applySyncOpCore`/`applyTryLock`, C1 S2c) at
the head of its label — so the fold records them under the goroutine's
current clock, before the op's acquire/release action — commit or park
alike. `acquired` is the TRY heads' outcome (`applyTryLock` knows it: a
pre-committed acquire not taken by the spurious member) — it selects the success-only go_mem lock kind of RWMutex `TryLock`/
`TryRLock`; every other head's row ignores it (their kinds are
outcome-independent — commit or park alike). -/
def syncEntryKinds (op : SyncOp) (pre : SyncPrim) (delta : Int) (acquired : Bool)
    (loc : Loc) : AccessTrace :=
  let at_ := syncWord loc pre.kind
  match op, pre with
  -- Mutex: the state CAS (TSan: atomic write; go_mem's read-like lock
  -- is subsumed by it).
  | .lock, _ => [.access .atomicWrite (at_ .state)]
  -- Mutex Unlock: the state Add FOLLOWS the release (`syncReleaseTailKinds`).
  | .unlock, _ => []
  -- RWMutex: the realized `race.Read(&rw.w)` + the counter RMW's go_mem
  -- kind (lock read-like, unlock write-like).
  | .rlock, _ | .wlock, _ => [.access .read (at_ .w), .access .atomicRead (at_ .readerCount)]
  | .runlock, _ | .wunlock, _ => [.access .read (at_ .w), .access .atomicWrite (at_ .readerCount)]
  -- WaitGroup Add/Done: the state RMW is write-like (go_mem); the
  -- realized sema READ when the counter leaves 0 upward.
  | .wgAdd, .waitGroup counter _ =>
      (if delta > 0 && counter == 0 then [.access .read (at_ .sema)] else [])
        ++ [.access .atomicWrite (at_ .state)]
  | .wgAdd, _ => [.access .atomicWrite (at_ .state)]
  -- WaitGroup Wait: the counter read is read-like (go_mem); the
  -- realized sema WRITE for the FIRST blocking waiter.
  | .wgWait, .waitGroup counter waiters =>
      (if counter != 0 && waiters == 0 then [.access .write (at_ .sema)] else [])
        ++ [.access .atomicRead (at_ .state)]
  | .wgWait, _ => [.access .atomicRead (at_ .state)]
  -- Once: a Do observing completion is the atomic load of `o.done`;
  -- every other Do is `doSlow`'s `o.m.Lock()` CAS; completion is the
  -- `o.done.Store(true)` (its Unlock's Add is the tail).
  -- RECORDED, NOT FIXED (the C1 S2c audit's F5, 2026-09-19 — pre-existing,
  -- main's fold had the same order): this row's read is recorded at the
  -- PRE-acquire clock — `applySyncOpCore` emits it before the
  -- `.hb (.syncAcquire …)` — where gc's `o.done.Load()` is a `sync/atomic`
  -- load whose TSan hook acquires FIRST and records second (the machine's
  -- own `atomicEvents .load` has that order). The difference is visible
  -- only against a plain OVERWRITE of the Once cell, a program racy in
  -- some schedule for gc as well (no program-level wrong verdict; per
  -- schedule the machine refuses where gc's acquire-first read would be
  -- ordered — fail-closed). A reorder is a semantic change and needs its
  -- own row; the label-shape fact in `Tests/GoCoreEval.lean` pins the
  -- order as it stands. Record: BUG-111's entry, `docs/BUGS.md`.
  | .onceBegin _, .once true true => [.access .atomicRead (at_ .done)]
  | .onceBegin _, _ => [.access .atomicWrite (at_ .m)]
  | .onceComplete, _ => [.access .atomicWrite (at_ .done)]
  -- Q-TRYLOCK (the section docstring's TryLock rows). Mutex TryLock on
  -- an UNLOCKED cell: the state CAS (:85), realized by TSan whether it
  -- wins (the acquire) or loses (gc's realization of the spurious
  -- member) — `.atomicWrite @state` on BOTH members; on a HELD cell:
  -- the plain early return (:77-79) in a noRaceFuncPkgs package —
  -- nothing realized, and go_mem gives an unsuccessful call no kind
  -- ("no synchronizing effect at all").
  | .tryLock _, .mutex locked => if locked then [] else [.access .atomicWrite (at_ .state)]
  -- RWMutex TryRLock/TryLock: the realized `race.Read(&rw.w)` opens
  -- every outcome (:89/:171, BEFORE `race.Disable`); the counter CAS is
  -- under `race.Disable` (nothing realized), so only go_mem's kind
  -- applies, and only to a SUCCESSFUL call ("equivalent to a call to
  -- l.RLock/l.Lock" — lock is read-like → `.atomicRead @readerCount`,
  -- the `rlock`/`wlock` row); a failed call has no go_mem kind.
  | .tryRLock _, .rwmutex .. | .tryWLock _, .rwmutex .. =>
      .access .read (at_ .w) :: (if acquired then [.access .atomicRead (at_ .readerCount)] else [])
  -- KIND MISMATCH — UNREACHABLE BY NAME (audit fix round F4; the
  -- `wakeReady` discipline): `tryAcquire` is `stuck` on a TRY head over
  -- the wrong primitive before any state change, and the fold reads the
  -- labels of SUCCESSFUL pool steps only, so no such (op, cell) pair
  -- reaches this table. Enumerated per kind, never `_`-absorbed, so a new primitive or
  -- a new head is a compile error here; the empty list is the honest
  -- value for a step that cannot have happened (an access on a
  -- fabricated word would be the fail-OPEN mistake — `at_` keys words by
  -- `pre.kind`, so a Mutex-word access under a TryRLock would be a
  -- fiction).
  | .tryLock _, .rwmutex .. | .tryLock _, .waitGroup .. | .tryLock _, .once .. => []
  | .tryRLock _, .mutex .. | .tryRLock _, .waitGroup .. | .tryRLock _, .once .. => []
  | .tryWLock _, .mutex .. | .tryWLock _, .waitGroup .. | .tryWLock _, .once .. => []

/-- The accesses `-race` realizes AFTER a sync op's release hook:
`Mutex.Unlock`'s state Add follows `race.Release` (mutex.go:188-194),
and so does the Add inside Once's deferred `o.m.Unlock()`. EMITTED after
the `.hb (.syncRelease …)` action in the apply's label (C1 S2c), hence
recorded at the bumped epoch, so a goroutine that ACQUIRES
this very release and then plainly reads the primitive still conflicts
— TSan's verdict exactly; it also covers go_mem's write-like unlock
(section docstring, Mutex row). -/
def syncReleaseTailKinds (op : SyncOp) (pre : SyncPrim) (loc : Loc) :
    AccessTrace :=
  let at_ := syncWord loc pre.kind
  match op with
  | .unlock => [.access .atomicWrite (at_ .state)]
  | .onceComplete => [.access .atomicWrite (at_ .m)]
  -- Every other head's recorded set lies entirely at ENTRY
  -- (`syncEntryKinds`). Enumerated, never `_`-absorbed, so a new
  -- constructor is a compile error here as in every other sync arm.
  | .lock => []
  | .rlock => []
  | .runlock => []
  | .wlock => []
  | .wunlock => []
  | .wgAdd => []
  | .wgWait => []
  | .onceBegin _ => []
  | .tryLock _ => []
  | .tryRLock _ => []
  | .tryWLock _ => []


/-- The `sync/atomic` op's label (the atomics arc wave 1; Race.lean's section
"sync/atomic — the per-address clocks" is the derivation): its ATOMIC-kind access at
the addressed cell's own path and its clock action, in TSan's instruction order —
Load = acquire THEN record `.atomicRead`; Store = record `.atomicWrite` THEN
release-store; Add/Swap = record THEN release-acquire; CompareAndSwap = record, then
release-acquire on success (`stored`) / acquire on failure. Emitted by `applyAtomicOp`
on a COMMITTED op only (a nil-address panic is delivered with the empty label — gc's
`racecallatomic` faults on the address before any TSan call). -/
def atomicEvents (head : AtomicStmtOp) (loc : Loc) (stored : Bool) : AccessTrace :=
  let l := loc.canon
  let acc : MemEvent := .access (atomicOpKind head) (.data l)
  match head with
  | .load => [.hb (.atomicAcquire l), acc]
  | .store => [acc, .hb (.atomicReleaseStore l)]
  | .add | .swap => [acc, .hb (.atomicReleaseAcquire l)]
  | .cas => [acc, .hb (if stored then .atomicReleaseAcquire l else .atomicAcquire l)]

/-! ## The panic chain (the unwinding arc, `docs/2026-07-25_unwinding-arc.md` §A1–A3) -/

/-- One entry of a goroutine's panic chain: the payload (the interface
value `recover` returns) and whether a `recover` has caught it. The chain
is oldest-first; Go's abort output prints it in this order and the
differential's fault identity compares the FIRST line, so the head entry
(with its `recovered` flag) is what terminal rendering must get right. -/
structure PanicEntry where
  value : GoValue
  recovered : Bool
  deriving Repr, BEq

-- `runtimeErrorTypeId` moved to Syntax.lean (2026-08-05, slice-2 stage 5):
-- the decoder synthesizes the runtime-panic payload for the nil-interface
-- method-value creation check and must name the sentinel without importing
-- the machine. It resolves here unqualified via namespace ascent.

/-- The payload of a Go runtime panic (nil dereference, division by zero,
…): a `runtime.Error` interface value, tagged with a `TypeId` no source type
can spell, so type asserts against user types correctly fail on it. -/
def runtimeErrorValue (msg : String) : GoValue :=
  .interface (.defined runtimeErrorTypeIdx) (.string (GoString.fromLeanString msg))

/-- The chain entry of a fresh RUNTIME panic (B2): the `runtime.Error`
payload, not yet recovered. The one spelling behind every conversion of
a helper's `.panic msg` into an unwinding configuration (`deliver`) and
behind the in-helper channel/nil-callee panics. -/
def panicEntry (msg : String) : PanicEntry := ⟨runtimeErrorValue msg, false⟩

/-- The payload of a PACKAGE-CODE panic raised with a string literal —
gc's sync package panics this way (`panic("sync: negative WaitGroup
counter")`, waitgroup.go:118): a plain `string` interface box, dynamic
type `string`, NOT `$runtime.Error`. That class distinction is
observable: `recover().(string)` answers true on it in gc (arc-end fix
round 2026-08-10, payload-class finding; pinned by
`sync/waitgroup-panic-payload` — the abort TEXT is identical for both
payload kinds, so only a recover discriminator can see it). The channel
panics stay `runtimeErrorValue`: gc raises those as `runtime.plainError`
(runtime/chan.go), a genuine `runtime.Error`. -/
def stringPanicValue (msg : String) : GoValue :=
  .interface .string (.string (GoString.fromLeanString msg))

/-- Coerce a delivered `panic` argument to its chain payload. MODERN
(Go 1.21+) semantics since the arc-final audit (F21, 2026-08-06): the
spec says "calling panic with a nil interface value (or an untyped nil)
causes a run-time panic", so a nil payload becomes the
`*runtime.PanicNilError` runtime error (message verbatim from gc's
realized behavior; our runtime-error payloads share one machine-internal
dynamic type, `$runtime.Error`). The differential oracle is aligned by
`GODEBUG=panicnil=0` on every `go run` (scripts/diff-coverage
`go_run_oracle`) — GOPATH mode otherwise defaults to the LEGACY
behavior (recover() returns nil), which the model previously matched
only by that config coincidence (recorded, unwinding arc §A2).
Differentially pinned by `panic-recover/panic-nil-recover` (Go answer 1
under the modern config) and `panic-recover/panic-nil-abort`. A TYPED
nil payload (`panic((*T)(nil))`) is a non-nil interface and passes
through unchanged (`panic-typed-nil-recover`). -/
def panicPayload : GoValue → GoValue
  | .nil => runtimeErrorValue "panic called with nil argument"
  | v => v

/-- Strict, constructive UTF-8 decode for abort rendering (landing chunk
L3, `docs/2026-09-07_land-panic-text-tape.md` §2.1; the decoder is the
sprint's `ff7173dd`, credited). Core's `String.fromUTF8?` depends on
`Classical.choice` (its validation proofs) and the machine-correspondence
theorems are pinned constructive, so this reuses the machine's own total
`decodeRuneAt` (the decoder string range/conversion already use): its
invalid-encoding sentinel is U+FFFD with width 1; a correctly encoded
U+FFFD has width 3 and is kept. The offset strictly advances, as in
`runesOfStringAux`. Newlines are preserved here — the first-line
projection is `stringFirstLine?`'s, at the BYTE level. -/
def utf8StringAux? (s : GoString) (off : Nat) (acc : String) : Option String :=
  if _h : off < s.length then
    let (rune, width) := decodeRuneAt s off
    if rune == 0xFFFD && width == 1 then none
    else utf8StringAux? s (off + max 1 width) (acc.push (Char.ofNat rune.toNat))
  else some acc
termination_by s.length - off
decreasing_by
  have : 1 ≤ max 1 (decodeRuneAt s off).2 := Nat.le_max_left _ _
  omega

/-- The decoded text of a byte string, or `none` unless the bytes are
valid UTF-8 — checked by the decoder AND by the byte round trip
`text.toUTF8.data == bytes`, so a `some` answer's UTF-8 bytes ARE the
payload bytes (`utf8String?_bytes`, a theorem of this definition, not a
trust in the custom decoder). Every invalid encoding (a stray
continuation byte, an overlong form, a surrogate, a code point above
U+10FFFF, a truncated sequence) is `none`: gc writes such bytes raw
(`printindented` byte-copies) and a Lean `String` cannot carry them, so
the abort REFUSES by name rather than print a form Go never prints
(BUG-004 item 3 / landing decision D5). -/
def utf8String? (bytes : Array UInt8) : Option String :=
  match utf8StringAux? ⟨bytes⟩ 0 "" with
  | some text => if text.toUTF8.data == bytes then some text else none
  | none => none

variable {ctx}
theorem utf8String?_bytes {bytes : Array UInt8} {text : String}
    (h : utf8String? bytes = some text) : text.toUTF8.data = bytes := by
  unfold utf8String? at h
  split at h
  · split at h
    · rename_i hb
      cases h
      exact eq_of_beq hb
    · contradiction
  · contradiction

variable (ctx)
/-- gc's FIRST abort line for a string payload's bytes, with whether the
payload continues past it. `printindented` (runtime/error.go:306–318 at
the pin) writes the payload's raw bytes, a `\t` after every `\n`, and the
`[recovered…]` suffix follows the WHOLE payload (panic.go:748–752) — on
its LAST line. So the first line is the bytes BEFORE the first LF,
decoded strictly, and a multi-line payload's first line carries NO
suffix (`panic("first\nsecond")` recovered then re-panicked prints
`panic: first⏎⇥second [recovered]…`; gc witness w14). A payload whose
first line is valid UTF-8 renders even if a later line is not: the
observation compared IS the first line, and its bytes are gc's bytes
(witness w16: `panic("a\n\xff")` → `a`). Nothing is claimed about the
unseen tail. -/
def stringFirstLine? (bytes : Array UInt8) : Option (String × Bool) :=
  let line := bytes.takeWhile (· != 0x0A)
  (utf8String? line).map fun text => (text, line.size < bytes.size)

/-- Does `dynTy` carry `member() string` — the shape of BOTH interfaces Go's
`preprintpanics` consults (`error`'s `Error() string` and `stringer`'s
`String() string`)? Checked against the METHOD SET directly rather than
through a wire interface declaration: those two interfaces are built into
the runtime, so the rewrite applies whether or not the program ever
mentions `error`/`fmt.Stringer`. -/
def hasNoArgStringMethod (dynTy : Ty) (member : Declaration.MemberId) : Bool :=
  match resolveMethod? ctx dynTy member with
  | some r =>
      match resolvedSignature? ctx member r with
      | some (params, results, variadic) =>
          params.isEmpty && results == #[Ty.string] && !variadic
      | none => false
  | none => false

/-- The payload rewrite Go performs before printing: `v.Error()` for an
`error`, `v.String()` for a `fmt.Stringer`. -/
def panicPayloadIsRewritten (dynTy : Ty) : Bool :=
  hasNoArgStringMethod ctx dynTy ⟨"Error", ""⟩ || hasNoArgStringMethod ctx dynTy ⟨"String", ""⟩

/-- Render a panic payload as Go's first abort line renders it (after
`panic: `): the payload's TEXT and whether the payload continues onto a
second line (string payloads only — `stringFirstLine?`; every other
family is single-line). The recovered-suffix and first-line rule is
`renderPanicHead`'s.

Go's `preprintpanics` REWRITES the payload to `v.Error()` / `v.String()`
before `printpanicval` runs, so `printanycustomtype`'s `main.T(v)` shape
applies only to a defined type with NEITHER method. The rewritten form
would require CALLING a method at abort time — which the terminal rule
cannot do — so a payload whose dynamic type implements either interface
fails CLOSED here (pre-merge audit 2026-07-31, finding 3; the unconditional
`main.T(v)` arm this replaces was a fail-closed → wrong-answer regression).
A string whose FIRST LINE is not valid UTF-8 is `none` (D5: no byte
channel — `utf8String?`). Everything else not pinned is `none` for the
same reason. -/
def renderPanicPayload : GoValue → Option (String × Bool)
  -- A RAW nil payload never reaches a chain: `panicPayload` maps
  -- `panic(nil)` to the `*runtime.PanicNilError` runtime error under the
  -- pinned `GODEBUG=panicnil=0` (the only raise site, `.panicArgK`), and
  -- gc prints `panic called with nil argument` there — never `nil`. The
  -- arm is dead; it fails CLOSED rather than stand as a latent wrong
  -- answer (audit fix round 2026-09-07, L4, [AGENT]; was `some ("nil", false)`).
  | .nil => none
  | .interface (.defined idx) (.string s) =>
      if idx == runtimeErrorTypeIdx then stringFirstLine? s.bytes else none
  | .interface .string (.string s) => stringFirstLine? s.bytes
  | .interface (.int dkind) (.int v kind) =>
      if dkind == kind then some (toString v, false) else none
  | .interface .bool (.bool b) => some (if b then "true" else "false", false)
  -- A DEFINED-type payload renders qualified with Go's
  -- `printanycustomtype` shape: `main.Code(7)` (BUG-004 item 2 — the
  -- identity is modeled since the interfaces campaign; the type prints
  -- its DISPLAY record — gc's type string — never its key, design note
  -- 2026-09-05 §3.2; the record is read through the table INDEX, C2).
  -- Only the int-underlying form is pinned; other underlyings stay
  -- closed.
  | .interface (.defined idx) (.int v _) =>
      if idx == runtimeErrorTypeIdx then
        none
      else if !dynamicMethodSetRecorded ctx (.defined idx) then
        -- BUG-053 class, renderer consumer (contract note §4,
        -- 2026-08-10): with no method-set record,
        -- `panicPayloadIsRewritten`'s "no Error()/String()" below would
        -- be an answer from absence — gc may well rewrite the payload
        -- through a method we never saw. Fail closed to an unrenderable
        -- abort, never a fabricated `main.T(v)`. (`Error`/`String` are
        -- exported names, so an `exported`-coverage record suffices to
        -- decide honestly.)
        none
      else if panicPayloadIsRewritten ctx (.defined idx) then
        none -- Error()/String() would have to be CALLED: fail closed
      else
        -- The entry is read back from the type table; an index the table
        -- does not have is unrenderable (fail closed), never a guess. A
        -- present entry renders its DISPLAY record (no record: the visible
        -- marker, never the key — design note 2026-09-05 §3.2).
        (ctx.types.nameOf? idx).map fun name => (s!"{displayNameOfId ctx name}({v})", false)
  | _ => none

/-- The diagnostic suffix of the unrenderable-abort refusal: a boxed
payload's dynamic type by the KEY read back from the table
(`goTypeNameForMessage`), beside the `repr` that now prints a bare
`Ty.defined i` (C2; audit fix R16). Diagnostic only — no baseline or
observation carries the text. -/
def payloadDynamicTypeNote : GoValue → String
  | .interface dynTy _ => s!" (dynamic type {goTypeNameForMessage ctx dynTy})"
  | _ => ""

/-- **The `repanicCollapse` envelope statement** (`ChoiceSite.repanicCollapse`,
State.lean; landing chunk L3, `docs/2026-09-07_land-panic-text-tape.md`
§2.2): the abort's head entry is RECOVERED and its successor carries an
EQUAL payload — a recovered panic value re-panicked. gc decides whether the
two lines COLLAPSE into one `… [recovered, repanicked]` by eface IDENTITY —
a bitwise compare of the interface's type word AND data pointer
(`preprintpanics`, runtime/panic.go:715 at the pin), NOT semantic
equality (pre-merge audit 2026-07-25; the §A3 probe that suggested
otherwise was constant-folded — `"or"+"ig"` shares a static eface,
`mk("or","ig")` at runtime does not). Value-level state decides only one
direction: structurally UNEQUAL payloads can never share a box, so
` [recovered]` is forced there; structurally EQUAL payloads collapse when
the recovered box is passed through (`panic(r)`, `panic(recover())`),
do NOT collapse when the value is re-boxed (`panic(r.(string))`, a
runtime-computed string — a fresh allocation), and collapse or not by
LINKER dedup when both are literal constants — and every go ≤ 1.24
printed the two-line form for all of them (the collapse is CL 645916,
go1.25). The machine has no boxing identity, so here the marker is
LATITUDE relative to its state and is reified on the tape (an [AGENT]
extension of BUG-087's ruling SHAPE — «demonic choice so both are
admitted», [USER] 2026-09-03 relayed, ruled for ONE choice at the nil
arm/R9a — to this marker under R-1's re-envelope authority: the rendered
text is spec-silent; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off)), never
decided in evaluator recursion and never a single hard-coded member. -/
def repanicEqualNext (first : PanicEntry) (rest : List PanicEntry) : Bool :=
  first.recovered && (match rest with
    | e :: _ => e.value == first.value
    | [] => false)

/-- The site's width at an abort: 2 exactly on the `repanicEqualNext`
shape (slot 0 = COLLAPSE, slot 1 = the two-line form's first line), 1
everywhere else — a bound-1 consult pops nothing (G-U), so every other
abort consumes exactly as before. Decided by the chain SHAPE alone, never
by renderability: a chain the renderer then refuses consults too, and the
refusal is the same under either pick. -/
def repanicCollapseWidth (first : PanicEntry) (rest : List PanicEntry) : Nat :=
  if repanicEqualNext first rest then 2 else 1

/-- THE abort's consult — the ONE place the `repanicCollapse` pick is
drawn (shared by `stepFn`'s `.panicking _ .stop` arm and the pool's
tombstone arm, `stepThread`): `Choices.consumeAt` at
`repanicCollapseWidth`, under the uniform rule. The abort is the only
transition that observes the marker, so the draw is observable exactly
when it exists (a draw at the re-raise would pop on re-panics that are
later recovered and never print). -/
def abortConsult (first : PanicEntry) (rest : List PanicEntry) (ch : Choices) :
    Nat × Choices :=
  Choices.consumeAt .repanicCollapse (repanicCollapseWidth first rest) ch

/-- The suffix gc appends to the payload (panic.go:749–752 at the pin):
` [recovered, repanicked]` iff the head is recovered AND its duplicate
successor line is suppressed — the `repanicCollapse` pick 0 on the
`repanicEqualNext` shape; ` [recovered]` iff recovered otherwise; nothing
for an unrecovered head (gc's oldest line carries no suffix whether or
not a later duplicate is suppressed — witness w25). -/
def recoveredSuffix (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) : String :=
  if !first.recovered then ""
  else if repanicEqualNext first rest && pick == 0 then " [recovered, repanicked]"
  else " [recovered]"

/-- Go's first abort line for a panic chain, given the `repanicCollapse`
pick: the payload's first line (`renderPanicPayload`), then the suffix —
appended ONLY when the payload is single-line, because gc writes the
suffix after the WHOLE payload, i.e. on its last line (`stringFirstLine?`;
witnesses w14/w15/w34). `none` exactly where the payload refuses
(`renderPanicPayload`'s fail-closed arms). -/
def renderPanicHead (first : PanicEntry) (rest : List PanicEntry)
    (pick : Nat) : Option String :=
  (renderPanicPayload ctx first.value).map fun (base, multiline) =>
    if multiline then base else base ++ recoveredSuffix first rest pick

/-- Mark the newest (last) chain entry recovered, returning its payload —
what `recover()` yields. `none` if the chain is empty or the newest entry
is already recovered (Go: a second `recover` in the same deferred call
returns nil — `panic-recover/recover-twice`). -/
def markNewestRecovered : List PanicEntry → Option (GoValue × List PanicEntry)
  | [] => none
  | [e] =>
      if e.recovered then none
      else some (e.value, [{ e with recovered := true }])
  | e :: rest =>
      (markNewestRecovered rest).map (fun (v, rest') => (v, e :: rest'))

/-- Whether the newest (last) chain entry has been recovered — decides
whether a completed panic-path deferred call cancels the unwind. -/
def chainNewestRecovered (chain : List PanicEntry) : Bool :=
  (chain.getLast?.map (·.recovered)).getD false

/-! ## Continuations and configurations -/

/-- Continuations. The statement frames (`seq`/`loop`/`frame`) are exactly
the old relation's (env-in-control CEK, scope = continuation extent, frame
exit reads call-time-pinned result locations). The expression and
statement-glue frames are new: each names the context awaiting a `retV`
value. Wide-statement frames arrive at S2. -/
inductive Cont where
  | stop
  /-- Remaining statements of a sequence, with the environment active for
  them. Exhausting the sequence discards this `env` (scope exit). -/
  | seq (rest : List Stmt) (env : LocalEnv) (k : Cont)
  /-- Loop context: normal completion and `continue` retest the condition,
  `break` resumes after the loop, `return` keeps unwinding. -/
  | loop (cond : Expr) (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- Call frame: at frame exit, run the `defers` chain (LIFO), THEN read
  `results` (call-time-pinned frame cell locations) and store into
  `targets`. Running defers before the read is what makes a deferred call's
  mutation of a named result observable (W3 §9).
  DELETED (G-P S2, 2026-09-28): the trailing `wrapper : Bool` marker of a
  frame entered through a compiler-synthesized promotion wrapper (BUG-015,
  2026-08-06; gc's `abi.FuncIDWrapper`, skipped by the recover walk). No
  synthesized frame exists any more — a promoted method-set entry is a
  promotion RECORD resolved at dispatch (`resolveMethod?`/`receiverAt`,
  Ops.lean) and the target's own frame is the deferred frame (design note
  `docs/2026-09-28_gp-method-promotion-design.md` §2 S6) — so every frame
  is an ordinary frame and `recoverResult` needs no transparency.
  ADDED in the same reshape ([USER] Mike 2026-09-28 «Agree on (1)» — the
  logic team's request 6, option 1; relayed by the [AGENT] coordinator,
  cite as relayed): `fid`, the id of the FUNCTION WHOSE BODY THIS FRAME
  RUNS — the callee `enterFrame` resolves and enters (for a promoted
  dispatch the declared TARGET method actually entered, never an interface
  anchor or a record), set by every entry site from `Entry.run`'s `Func`
  (`Entry.callConfig`/`Entry.drainConfig`); the drivers' entry frames name
  the entry point / `pkgInitFuncId`. A REPRESENTATION field only: no rule
  reads it, so a client can observe «`fid` returned `vs`» from the
  configuration at frame exit (`frame_exit_returns`) while the step label
  and every behaviour stay as they were (`Entry.callConfig_run`,
  `enterFrame_declared`). -/
  | frame (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
      (results : List Loc)
      (defers : List (GoValue × List GoValue)) (k : Cont) (fid : FuncId)
  /-- Awaiting a deferred call's callee value. -/
  | deferCalleeK (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting a deferred call's arguments; they are evaluated AT DEFER
  TIME (Go), then the pending call — the callee VALUE plus argument
  values — is prepended to the innermost frame's chain. A nil callee
  REGISTERS fine and panics only at invocation (pre-merge audit
  2026-07-25; Go's rule). -/
  | deferArgsK (callee : GoValue) (vals : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Breakable scope (`Stmt.breakable`): catches the `brk` signal, passes
  every other through (the `signalStep` table's `breakableK` row). -/
  | breakableK (k : Cont)
  /-- Label scope (`Stmt.labeled`, control-flow slice): catches `brkTo`
  at a matching label; a `loop`/`mapIterK` whose IMMEDIATE continuation
  is a matching `labelK` is the labeled loop `contTo` targets
  (`contHeadLabel`). The bare signals pass through — a bare break
  targets the innermost for/switch regardless of labels (the
  `signalStep` table's `labelK` row). -/
  | labelK (label : String) (k : Cont)
  /-- Awaiting the CALLEE value of a value call (a `funcVal`, or `nil`
  → panic). Carries the caller-target PLANS untouched (BUG-052 — the
  spec leaves the call/target-operand order UNSPECIFIED and gc realizes
  CALL-FIRST, so target operands evaluate only at frame exit, through
  the tgtOpK spine). -/
  | callValCalleeK (targets : List (TargetShape × List Expr))
      (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting an argument of a value call. Carries the callee VALUE: a
  funcVal's captures are prepended at frame entry; a nil callee evaluates
  every argument first and panics at the invocation step (Go's order —
  pre-merge audit 2026-07-25). -/
  | callValArgsK (callee : GoValue) (targets : List (TargetShape × List Expr))
      (vals : List GoValue) (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Strict-operator evaluation: `done` holds evaluated operands (most
  recent first), `pending` the rest, in evaluation order. -/
  | strictK (op : StrictOp) (done : List GoValue) (pending : List Expr)
      (env : LocalEnv) (k : Cont)
  /-- Awaiting the left operand of `&&`. -/
  | andK (right : Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting the left operand of `||`. -/
  | orK (right : Expr) (env : LocalEnv) (k : Cont)
  /-- Coerce a short-circuit right-operand result to bool (fail-closed on
  non-bool, as the interpreter's `valueAsBool` is). -/
  | boolK (k : Cont)
  /-- Awaiting an `if` condition value. -/
  | ifK (thenBranch elseBranch : Stmt) (env : LocalEnv) (k : Cont)
  /-- Awaiting a `while` condition value. -/
  | whileK (cond : Expr) (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- Awaiting a call argument value; then remaining arguments, then
  frame entry. Carries the caller-target PLANS untouched (BUG-052): NO
  target operand evaluates before the call — spec §Order of evaluation
  leaves the order of the call against "the evaluation and indexing of
  x and the evaluation of y" UNSPECIFIED, and gc deterministically
  realizes CALL-FIRST (probed go1.26.5, the S1-audit matrix), so the
  machine pins that point (the deterministic-latitude precedent: panic
  identity, hidden-dep init order). Target operands evaluate at frame
  EXIT through the tgtOpK spine, then the stores. -/
  | callArgsK (fid : FuncId) (targets : List (TargetShape × List Expr))
      (vals : List GoValue) (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Wide-statement operand evaluation: the leading `ntargets` operands are
  target addresses (checked as they arrive); `done` holds evaluated
  operands most recent first. Ends in one `applyStmtOp` step. -/
  | stmtOpK (op : StmtOp) (ntargets : Nat) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting the `mapRange` map value; the start step (base loc +
  start-key set — the BUG-005 (L) surgery, ruled 2026-08-19) follows. -/
  | mapRangeK (keyVar valVar : Option String) (keyTy valTy : Ty)
      (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- `mapRange` iteration context — LIVE iteration over ENTRY-IDENTITY
  STAMPS (BUG-005 (L), ruled 2026-08-19; B1, 2026-09-03 — the retired
  snapshot and key-set designs: ledger [DL-13]). The frame carries the ranged map's `base` cell
  (`none` = nil map), the `produced` ID set (ids of the entries already
  bound, in production order) and the `start` ID set (ids of the
  entries live when the range began). Each pick-next step LOADS the
  live cell (the U1-closing race footprint), takes `candidates` = live
  entries whose id ∉ produced, in cell order (removed entries drop out
  by absence — the spec's forced removal clause; a re-created key is a
  NEW entry with a fresh id and so a candidate again — the adopted
  reading, `docs/spec-interpretations.md` I-1 / ledger L-012; keys and
  values come live — the forced production-table clause), and
  consumes ONE choice of width `candidates.size + stop`, where the
  trailing STOP slot is legal only when no candidate id remains in
  `start` (a surviving never-removed start entry is MANDATORY —
  spec-forced traversal). No step ever rewrites this frame's sets
  except its own pick (`produced.push id`): a `mapDelete`/`clearMap`
  is a heap write and nothing else, in any goroutine — the frame
  observes it at its next pick, through the cell load. `break`
  finishes the range, `continue` proceeds, `return` unwinds. The
  per-iteration scope is the entered body's environment; this frame
  carries the *original* `env` for subsequent iterations (scope exit
  by discard, as everywhere in the CEK design).

  ENVELOPE STATEMENT (doctrine requirement 1, SPEC class —
  spec#For_statements, range clause, maps): "The iteration order over
  maps is not specified …. If a map entry that has not yet been
  reached is removed during iteration, the corresponding iteration
  value will not be produced. If a map entry is created during
  iteration, that entry may be produced during the iteration or may be
  skipped. The choice may vary for each entry created and from one
  iteration to the next." The realized set: any interleaved
  production order over live entries; each live entry produced AT
  MOST ONCE (its id enters `produced`); removal exact (absent at pick
  time ⇒ not a candidate); values live at production; created entries
  — any subset produced, each at any interleaved position,
  re-creations re-producible as the new entries they are (the FULL
  literal envelope: the 2026-08-19 ruling REJECTED the
  at-most-once-per-KEY and re-created-start-keys-mandatory
  narrowings). Consequences carried deliberately: self-inserting loops
  have genuinely unbounded trace sets (∀-streams certification fails
  closed on them — membership lane territory), and the CANONICAL
  member is BY DEFINITION the machine at the zero choice stream (index
  0 = first candidate in cell order, stop ordered LAST), so
  mutation-free ranges keep the first-remaining-in-insertion-order
  pick sequence and self-inserting loops fuel-out VISIBLY on the
  strict lane — correct behavior. Cross-goroutine mutation (E9,
  closed 2026-09-02 by the now-retired pool-level prune, carried
  identically by the stamps): a DRF cross-goroutine
  delete-then-re-create (handshake-ordered against the ranging
  goroutine's picks) makes the re-created key a fresh candidate and
  non-mandatory exactly as a same-goroutine one does, because the
  frame reads identity off the cell it loads — no goroutine's
  continuation is ever rewritten by another's step (the thread-locality
  NPDRF's obstruction 7 asked for). gc EXHIBITS the re-production
  member; the pins, measured frequencies and set-equality records:
  ledger [DL-14]. UNSYNCHRONIZED cross-goroutine mutation is refused by the detector
  (pick-time load vs the delete's write, HB-unordered; row
  `.../racy`), so no narrowing hides behind a refusal either.
  Keys whose Go `==` is irreflexive (NaN, and aggregates/interfaces
  holding one) are ordinary stamped entries here — each produced once
  — where the retired key-set frame could never mark them produced
  (`maps/nan-key-range`, BUG-088). -/
  | mapIterK (keyVar valVar : Option String) (keyTy valTy : Ty) (body : Stmt)
      (base : Option Loc) (produced : Array Nat)
      (start : Array Nat) (env : LocalEnv) (k : Cont)
  /-- Awaiting a `panic` payload value. -/
  | panicArgK (k : Cont)
  /-- The suspended panic chain while a panic-path deferred call runs
  above it (arc doc §A1). Built ONLY by the panic-drain rule, directly
  under the deferred call's frame — which is what makes the `recover`
  walk's "cross exactly one frame onto a marker" test Go's
  called-directly-by-a-deferred-function rule. On the deferred call's
  completion: newest entry recovered → the chain is discarded and the
  frame below resumes its normal exit path; otherwise unwinding resumes.
  A NEW panic unwinding through the marker merges behind the suspended
  chain. -/
  | panicResumeK (chain : List PanicEntry) (k : Cont)
  /-- Channel-statement operand evaluation (channels arc slice 1): the
  pre-communication operands (send: channel then value; receive: the
  channel; close: the channel), ending in one `applyChanOp` step whose
  outcome may be next / panicking / blocked / a receive's phase-1
  target entry (`tgtOpK` — a receive's targets evaluate only AFTER the
  communication — BUG-022/BUG-029, spec §Assignments). Appended at the
  END of the inductive (with its select/delivery siblings) so
  positional case tags in the correspondence proofs stay stable. -/
  | chanStK (op : ChanStOp) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- `select` entry-time operand evaluation (spec step 1, source order);
  ends in one `applySelect` readiness/commit step. -/
  | selectOpsK (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
      (done : List GoValue) (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Receive delivery, PHASE 1 (convergence round, BUG-029; spec
  §Assignments' two phases split — targets evaluate only AFTER the
  communication, spec §Select step 4 / BUG-022): awaiting one operand
  value of the CURRENT target. `sh`/`ops`/`pending` are the current
  target's shape, evaluated operands (most recent first) and remaining
  operand expressions; `refs` the targets already resolved (in order);
  `targets` the target plans still to evaluate. For the RECEIVE paths
  `vals` carries the delivery values phase 2 will store (`rhs = []`);
  for the general multi-assign (BUG-025) `rhs` carries the right-hand
  expressions, evaluated under `rhsK` after the targets (`vals = []`).
  Each target completes into a store-ready
  `TargetRef` — the OUTER nil/bounds check stays deferred to phase 2. -/
  | tgtOpK (sh : TargetShape) (ops : List GoValue) (pending : List Expr)
      (refs : List TargetRef) (targets : List (TargetShape × List Expr))
      (rop : RhsOp) (rhs : List Expr) (vals : List GoValue) (body : Stmt)
      (env : LocalEnv) (k : Cont)
  /-- The RHS evaluation of a spine-riding assignment (BUG-025;
  comma-ok sources round 4, BUG-034): after phase 1 resolved every
  target (`rop`/`rhs` carried through `tgtOpK`), the right-hand
  expressions evaluate left-to-right into `done`; the last value
  applies `rop` (`applyRhsOp` — identity for plain assigns, the
  lookup/assert for comma-ok forms) and enters phase 2 (`storeK`).
  The receive path never uses this frame (its delivery values are
  already known). -/
  | rhsK (rop : RhsOp) (refs : List TargetRef) (done : List GoValue)
      (pending : List Expr) (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- Receive delivery, PHASE 2 (`.next`-driven, one store per step,
  LEFT-TO-RIGHT — an earlier target's store is observable before a
  later target's store-time panic; pinned by
  channels/recv-edge/second-target-panic-stores-first and the
  field/oob-second-target-stores-first discriminators). The last store
  enters `body` (the clause body; `.seqn #[]` for the statement form). -/
  | storeK (refs : List TargetRef) (vals : List GoValue)
      (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- Awaiting a `go` statement's callee value (channels arc slice 2):
  the spawn's callee and arguments evaluate NOW, in the spawning
  goroutine (spec §Go statements) — the `deferCalleeK` shape. The
  completed spawn position (`.retV cv (.goCalleeK [] …)` /
  `.retV v (.goArgsK cv vals [] …)`) is a POOL step: relation-silent
  per-goroutine, fail-closed in `stepFn` (which is what refuses `go`
  during `$pkginit` — the init phase is sequential this slice).
  Appended at the END of the inductive so positional case tags in the
  correspondence proofs stay stable. -/
  | goCalleeK (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting a `go` statement's argument values (evaluated at the go
  statement, in the spawning goroutine). Carries the callee VALUE; a
  nil callee is gc's "go of nil func value" fatal at the SPAWN
  (probed 2026-08-07) — refused fail-closed at the pool's spawn step,
  not during the argument walk (gc evaluates the arguments first). -/
  | goArgsK (callee : GoValue) (vals : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Sync-statement operand evaluation (spec-parity slice 2): the
  receiver address (plus `wgAdd`'s delta), ending in one `applySyncOp`
  step whose outcome may be next / panicking / blocked / fatal / an
  `onceBegin` delivery entry. Appended at the END of the inductive so
  positional case tags stay stable. -/
  | syncStK (op : SyncOp) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Atomic-statement operand evaluation (atomics arc wave 1): the
  address (arg 0) then the value operands, ending in ONE
  `applyAtomicOp` step whose outcome is next / a result delivery entry
  / panicking (nil address). Appended at the END of the inductive so
  positional case tags stay stable. -/
  | atomicStK (op : AtomicOp) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- **The unsequenced-operand probe frame** (latitude E13 option (b),
  `e13-b` 2026-09-05; `Stmt.unseqProbe` is the envelope statement): the
  probed operand is being evaluated above `k`. A VALUE arriving here is
  discarded (`.next k`) — the operand is re-evaluated at its residual
  position; a PANIC arriving here is the `ChoiceSite.unseqPanic` pick
  (`stepFn`'s `.panicking` arm: DEFER → `.next k`, RAISE → `.panicking
  chain k`). Its own `FrameClass` (`.probe`): NOT glue — `panicPassthrough`
  must not strip it, `break`/`continue`/`return` have no rule at it
  (unreachable: only expression evaluation happens under a probe). -/
  | probeK (k : Cont)
  /-- **The `unseq` sweep frame** (evaluation-order model v2.1 §3.3; Stage B,
  lane `core/unseq-scheduler-b-0916`, 2026-09-16): the RUNTIME RECORD of one
  dynamic sweep — the static graph `g` (shared, never copied per pick) and
  its completion statement `thenB`; the per-occurrence `status`
  (active/done/skipped — «completed» ≠ «produced»: a binder is PRODUCED iff
  its occurrence is DONE, `UnseqGraph.produced`); the continuation-owned
  TARGET table (frozen plans of sort TARGET, `TargetRef` — never a
  `GoValue`, review R4); the sweep's SCOPE `env` (the source environment
  with the binder cells declared in it at ENTER — the `.initialization`
  idiom, so `thenB`'s source declarations survive the sweep and the cells
  fall out of scope with the enclosing block); and the `phase`: `.pick` (the
  scheduler's step — review R2's cases (i)–(iii), `stepUnseqNext`), `.run i`
  (occurrence `i` starts this step), `.wait i` (its value / statement
  completion is awaited). `FrameClass.exprGlue`: a panic reaching it is the
  sweep's FIRST failure — `panicPassthrough` strips the frame, its binders
  and its pending work; the effect prefix stands; defers and `recover` are
  the callee frames' business, never this frame's. A control signal cannot
  reach it (only expression and callee evaluation runs under it — the
  `probeK` reachability argument; `signalRefusal`'s expression-frame arm
  names the shape). Appended at the END so positional case tags stay
  stable. -/
  | unseqK (g : UnseqGraph) (thenB : Stmt) (status : List UnseqStatus)
      (targets : List (String × TargetRef)) (env : LocalEnv) (phase : UnseqPhase) (k : Cont)

/-! ## The `Cont` algebra (design-hygiene wave (iii), B3, 2026-09-04)

Every frame but `.stop` has exactly ONE tail — the continuation it
forwards to. The type says so through `Cont.tail`/`Cont.withTail`, and
the frame CLASSES say which frames are glue (forward every walk to their
tail) and which are load-bearing (`frame`, `panicResumeK`, `stop`). The
continuation walks (`pushDefer`, `recoverResult`; before G-P S2 also
`recoverThroughWrappers`) are instances of ONE well-founded combinator,
`Cont.rebuild`: descend through the frames a predicate admits, act at
the first it does not, and rebuild the spine above the action. Adding a
frame is one `tail`/`withTail` arm plus a class — not a new arm in every
walk. `panicPassthrough` is "glue → tail". Preservation: each instance was
proved EQUAL to the retired 30-arm definition before the swap
(`docs/evidence/2026-09-04_hygiene-wave3/b3-prototype/Proto.lean`). -/

/-- The tail (immediate continuation) of a frame; `.stop` has none. -/
def Cont.tail : Cont → Option Cont
  | .stop => none
  | .seq _ _ k | .loop _ _ _ k | .frame _ _ _ _ k _ | .deferCalleeK _ _ k
  | .deferArgsK _ _ _ _ k | .breakableK k | .labelK _ k | .callValCalleeK _ _ _ k
  | .callValArgsK _ _ _ _ _ k | .strictK _ _ _ _ k | .andK _ _ k | .orK _ _ k
  | .boolK k | .ifK _ _ _ k | .whileK _ _ _ k | .callArgsK _ _ _ _ _ k
  | .stmtOpK _ _ _ _ _ k | .mapRangeK _ _ _ _ _ _ k | .mapIterK _ _ _ _ _ _ _ _ _ k
  | .panicArgK k | .panicResumeK _ k | .chanStK _ _ _ _ k | .selectOpsK _ _ _ _ _ k
  | .tgtOpK _ _ _ _ _ _ _ _ _ _ k | .rhsK _ _ _ _ _ _ k | .storeK _ _ _ _ k
  | .goCalleeK _ _ k | .goArgsK _ _ _ _ k | .syncStK _ _ _ _ k | .atomicStK _ _ _ _ k
  | .probeK k
  | .unseqK _ _ _ _ _ _ k => some k

/-- Replace the tail, keeping the frame's own payload. `.stop` is unchanged. -/
def Cont.withTail : Cont → Cont → Cont
  | .stop, _ => .stop
  | .seq a b _, t => .seq a b t
  | .loop a b c _, t => .loop a b c t
  | .frame a b c d _ f, t => .frame a b c d t f
  | .deferCalleeK a b _, t => .deferCalleeK a b t
  | .deferArgsK a b c d _, t => .deferArgsK a b c d t
  | .breakableK _, t => .breakableK t
  | .labelK a _, t => .labelK a t
  | .callValCalleeK a b c _, t => .callValCalleeK a b c t
  | .callValArgsK a b c d e _, t => .callValArgsK a b c d e t
  | .strictK a b c d _, t => .strictK a b c d t
  | .andK a b _, t => .andK a b t
  | .orK a b _, t => .orK a b t
  | .boolK _, t => .boolK t
  | .ifK a b c _, t => .ifK a b c t
  | .whileK a b c _, t => .whileK a b c t
  | .callArgsK a b c d e _, t => .callArgsK a b c d e t
  | .stmtOpK a b c d e _, t => .stmtOpK a b c d e t
  | .mapRangeK a b c d e f _, t => .mapRangeK a b c d e f t
  | .mapIterK a b c d e f g h i _, t => .mapIterK a b c d e f g h i t
  | .panicArgK _, t => .panicArgK t
  | .panicResumeK a _, t => .panicResumeK a t
  | .chanStK a b c d _, t => .chanStK a b c d t
  | .selectOpsK a b c d e _, t => .selectOpsK a b c d e t
  | .tgtOpK a b c d e f g h i j _, t => .tgtOpK a b c d e f g h i j t
  | .rhsK a b c d e f _, t => .rhsK a b c d e f t
  | .storeK a b c d _, t => .storeK a b c d t
  | .goCalleeK a b _, t => .goCalleeK a b t
  | .goArgsK a b c d _, t => .goArgsK a b c d t
  | .syncStK a b c d _, t => .syncStK a b c d t
  | .atomicStK a b c d _, t => .atomicStK a b c d t
  | .probeK _, t => .probeK t
  | .unseqK a b c d e f _, t => .unseqK a b c d e f t

variable {ctx}
theorem Cont.sizeOf_tail_lt {k k' : Cont} (h : k.tail = some k') : sizeOf k' < sizeOf k := by
  cases k <;> simp_all [Cont.tail] <;> omega

/-- Putting a frame's own tail back is the identity. -/
theorem Cont.withTail_tail : ∀ k : Cont, (k.tail.map k.withTail).getD k = k := by
  intro k; cases k <;> rfl

theorem Cont.tail_withTail {k t : Cont} (h : k ≠ .stop) : (k.withTail t).tail = some t := by
  cases k <;> first | exact absurd rfl h | rfl

variable (ctx)
/-- What a frame IS to the walks: statement glue (`seq`/`loop`/scopes/
the range frame — what `break`/`continue`/`return` and `defer` cross),
expression glue (an operand or delivery frame — crossed only by a
panic), a call frame, the suspended-chain marker, or the end. -/
inductive FrameClass where
  | stmtGlue | exprGlue | callFrame | resumeMarker | stop
  /-- The unsequenced-operand probe frame (`Cont.probeK`, E13 option (b)):
  crossed by NO walk — the `.panicking` arm ACTS on it (the `unseqPanic`
  pick), `recover` does not see through it (a probed operand never
  contains `recover()`: frontend rule + decoder refusal), and the
  statement-level travellers (`break`/`continue`/`return`) cannot reach it. -/
  | probe
  deriving DecidableEq, Repr

def Cont.class : Cont → FrameClass
  | .stop => .stop
  | .frame .. => .callFrame
  | .panicResumeK .. => .resumeMarker
  | .probeK .. => .probe
  | .seq .. | .loop .. | .breakableK .. | .labelK .. | .mapIterK .. => .stmtGlue
  -- EXHAUSTIVE on purpose (audit fix F2): a new frame must be classified
  -- here by hand — no absorbing default can make it glue silently.
  | .deferCalleeK .. | .deferArgsK .. | .callValCalleeK .. | .callValArgsK .. | .strictK ..
  | .andK .. | .orK .. | .boolK .. | .ifK .. | .whileK .. | .callArgsK .. | .stmtOpK ..
  | .mapRangeK .. | .panicArgK .. | .chanStK .. | .selectOpsK .. | .tgtOpK .. | .rhsK ..
  | .storeK .. | .goCalleeK .. | .goArgsK .. | .syncStK .. | .atomicStK ..
  -- The `unseq` sweep frame (Stage B): a panic strips it — the sweep's
  -- first failure; nothing else crosses it.
  | .unseqK .. => .exprGlue

/-- Is the frame glue of either kind (forwards every walk to its tail)? -/
def Cont.isGlue (k : Cont) : Bool := k.class = .stmtGlue || k.class = .exprGlue

/-- **The one continuation walk**: descend through the frames `descend`
admits (a frame whose tail is `none` — `.stop` — is acted on), ACT at
the first frame it does not, and rebuild the spine above the action
(`withTail`). `none` = the action refused (the walk found nothing to do). -/
def Cont.rebuild {β : Type} (descend : Cont → Bool) (act : Cont → Option (β × Cont)) (k : Cont) :
    Option (β × Cont) :=
  if descend k then
    match _h : k.tail with
    | some k' => (Cont.rebuild descend act k').map fun (b, k'') => (b, k.withTail k'')
    | none => act k
  else act k
termination_by sizeOf k
decreasing_by exact Cont.sizeOf_tail_lt _h

variable {ctx}
theorem Cont.rebuild_descend {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {k : Cont} (hd : descend k = true) :
    Cont.rebuild descend act k =
      match k.tail with
      | some k' => (Cont.rebuild descend act k').map fun (b, k'') => (b, k.withTail k'')
      | none => act k := by
  rw [Cont.rebuild]; simp only [hd, ↓reduceIte]; split <;> simp_all

theorem Cont.rebuild_act {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {k : Cont} (hd : descend k = false) : Cont.rebuild descend act k = act k := by
  rw [Cont.rebuild]; simp [hd]

theorem Cont.rebuild_stop {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)} :
    Cont.rebuild descend act .stop = act .stop := by
  rw [Cont.rebuild]; split <;> simp [Cont.tail]

/-- A walk whose action always answers, answers (G-P S3): the `getD` on
such a walk's result is totality plumbing only. -/
theorem Cont.rebuild_isSome {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    (hact : ∀ k, (act k).isSome) (k : Cont) : (Cont.rebuild descend act k).isSome := by
  rw [Cont.rebuild]
  split
  · split
    · rename_i k' hk'
      have := Cont.rebuild_isSome (descend := descend) hact k'
      simpa [Option.isSome_map] using this
    · exact hact k
  · exact hact k
termination_by sizeOf k
decreasing_by exact Cont.sizeOf_tail_lt (by assumption)

/-- Descent through an admitted frame, read at the answer: the walk's result
at `k` is its result at the tail, with the spine above rebuilt (`withTail`)
— for a walk whose action always answers. -/
theorem Cont.rebuild_getD_glue {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    (hact : ∀ k, (act k).isSome) {k k' : Cont} (hd : descend k = true) (hk : k.tail = some k')
    (d d' : β × Cont) :
    (Cont.rebuild descend act k).getD d =
      (((Cont.rebuild descend act k').getD d').1,
        k.withTail ((Cont.rebuild descend act k').getD d').2) := by
  rw [Cont.rebuild_descend hd, hk]
  obtain ⟨⟨v, k''⟩, h⟩ := Option.isSome_iff_exists.mp (Cont.rebuild_isSome (descend := descend) hact k')
  simp [h]

variable (ctx)
/-- The continuation for entering a `.seqn`: under a same-env governing
sequence, SPLICE the statements into it (D1) — Go statement lists splice
and only blocks scope. Any other continuation wraps in a fresh seq node. -/
def seqCont (ss : List Stmt) (env : LocalEnv) : Cont → Cont
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

/-- The label carried by the HEAD of a continuation, if it is a `labelK`.
The labeled-loop test for the `contTo` signal: the frontend attaches
`Stmt.labeled` directly around the loop-forming statement, so a labeled
loop's `Cont.loop`/`Cont.mapIterK` has its `labelK` as the immediate
continuation — and ONLY labeled loops do. -/
def contHeadLabel : Cont → Option String
  | .labelK name _ => some name
  | _ => none

/-- A value that may sit in callee position: a function value, or nil
(which panics at INVOCATION, not at evaluation/registration). -/
def deferrableCallee : GoValue → Bool
  | .funcVal _ _ => true
  | .nil => true
  | _ => false

/-- Prepend a pending call onto the innermost enclosing frame's defer chain
(LIFO): walk through STATEMENT glue to the first call frame and push. A
`defer` outside any frame (or under an expression frame, which cannot
contain a statement) finds nothing — fail closed. -/
def pushDefer (d : GoValue × List GoValue) (k : Cont) : Option Cont :=
  (Cont.rebuild (fun k => k.class = .stmtGlue)
    (fun k => match k with
      | .frame t te r ds k f => some ((), .frame t te r (d :: ds) k f)
      | _ => none) k).map (·.2)

/-- One unwinding step through a continuation frame: GLUE of either kind
is stripped with the chain unchanged — statement glue AND expression
frames (a panic can surface mid-expression, unlike `break`/`continue`/
`return`). The three non-glue heads (call frame, suspended-chain marker,
`.stop`) each have their own unwinding rules. -/
def panicPassthrough (k : Cont) : Option Cont :=
  if k.isGlue then k.tail else none

/-- Below the deferred function's frame (design note
`docs/2026-09-28_gp-method-promotion-design.md` §3 `recoverAtDeferred`,
§2 S6 — G-P S2 replaces `recoverThroughWrappers`, whose glue-and-wrapper
skip existed only for a synthesized wrapper's body glue between the
promoted method's frame and the wrapper's; `Cont.recoverTransparent` left
with it): `recover` applies exactly when the deferred frame sits DIRECTLY
on a `panicResumeK` whose newest entry is unrecovered — the shape the
panic-drain rule builds (`panicFrameDefer` constructs the deferred frame on
the marker; a promoted deferred call re-queued through its embedded
interface field, `Entry.again`, re-enters on the same marker; nothing
inserts glue below an entered frame). Returns the payload and the marker
with the entry marked; `none` = no recoverable panic here. -/
def recoverAtDeferred : Cont → Option (GoValue × Cont)
  | .panicResumeK chain k =>
      (markNewestRecovered chain).map fun (v, chain') => (v, .panicResumeK chain' k)
  | _ => none

/-- The `recover()` builtin (arc doc §A1): walk the continuation through
statement/expression GLUE to the first call frame — gc's rule, verbatim
from runtime/panic.go (`gorecover`): "there must be exactly one non-wrapper
frame between gopanic and gorecover" (since G-P S2 every frame is a
non-wrapper frame: a promoted method's own frame IS the deferred frame,
`defer i.M()` / `defer S.M(s)` recover inside the promoted `M` exactly as
gc's wrapper-skipping walk does). Recover applies exactly when that frame
sits directly on a `panicResumeK` whose newest entry is not yet recovered
(`recoverAtDeferred`). Returns the recovered payload and the continuation
with the entry marked, or `.nil` and the continuation unchanged (never
stuck: `recover` outside a panic-run deferred function is a defined no-op
in Go). The action always answers (`.nil` where the walk finds no frame),
so the `getD` is totality plumbing only. -/
def recoverResult (k : Cont) : GoValue × Cont :=
  (Cont.rebuild Cont.isGlue
    (fun k => match k with
      | .frame t te r ds k' f =>
          some (match recoverAtDeferred k' with
            | some (v, k'') => (v, .frame t te r ds k'' f)
            | none => (.nil, .frame t te r ds k' f))
      | k => some (.nil, k)) k).getD (.nil, k)

/-! ### The recover rule's equations (G-P S3, design §3 `recoverResult_eq`; §2 S6, decision 7)

What S2 shipped, stated for a client: `recover()` walks the continuation
through glue to the first call frame; it recovers exactly when that frame
sits DIRECTLY on a `panicResumeK` whose newest entry is unrecovered. No
frame is transparent (every frame is a non-wrapper frame since G-P S2). -/

variable {ctx}
/-- `recoverAtDeferred` at the marker: the newest unrecovered entry is marked
and its payload returned (`markNewestRecovered`); `none` when every entry is
already recovered. Definitional. -/
theorem recoverAtDeferred_marker (chain : List PanicEntry) (k : Cont) :
    recoverAtDeferred (.panicResumeK chain k) =
      (markNewestRecovered chain).map fun (v, chain') => (v, .panicResumeK chain' k) := rfl

/-- `recoverAtDeferred` below anything but the marker: nothing to recover —
a deferred frame not sitting directly on the marker sees no panic. -/
theorem recoverAtDeferred_none {c : Cont} (h : ∀ chain k, c ≠ .panicResumeK chain k) :
    recoverAtDeferred c = none := by
  cases c <;> first | rfl | exact absurd rfl (h _ _)

/-- **`recover` at a call frame** (the frame rule): the walk acts at the
first call frame — `recoverAtDeferred` on its tail decides; a hit returns the
payload with the marker's entry marked, a miss returns `.nil` and the frame
unchanged. The frame's `fid` rides along untouched. -/
theorem recoverResult_frame {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {f : FuncId} :
    recoverResult (.frame t te r ds k' f) =
      match recoverAtDeferred k' with
      | some (v, k'') => (v, .frame t te r ds k'' f)
      | none => (.nil, .frame t te r ds k' f) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  rfl

/-- **The recover rule** (design §3 `recoverResult_eq`): the deferred frame
directly on the marker — the shape the panic-drain rule builds
(`panicFrameDefer`; a promoted deferred call re-queued through its embedded
interface field, `Entry.again`, re-enters on the same marker) — recovers the
newest unrecovered entry's payload and marks it; with every entry already
recovered it answers `.nil` (a second `recover` in the same deferred call). -/
theorem recoverResult_eq {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {ds : List (GoValue × List GoValue)} {chain : List PanicEntry} {k : Cont} {f : FuncId} :
    recoverResult (.frame t te r ds (.panicResumeK chain k) f) =
      match markNewestRecovered chain with
      | some (v, chain') => (v, .frame t te r ds (.panicResumeK chain' k) f)
      | none => (.nil, .frame t te r ds (.panicResumeK chain k) f) := by
  rw [recoverResult_frame, recoverAtDeferred_marker]
  cases hm : markNewestRecovered chain with
  | none => rfl
  | some vc => obtain ⟨v, chain'⟩ := vc; rfl

/-- A call frame NOT directly on the marker: `recover()` is the no-op `.nil`
(Go: recover outside a panic-run deferred function). -/
theorem recoverResult_frame_none {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {f : FuncId}
    (h : ∀ chain k, k' ≠ .panicResumeK chain k) :
    recoverResult (.frame t te r ds k' f) = (.nil, .frame t te r ds k' f) := by
  rw [recoverResult_frame, recoverAtDeferred_none h]

/-- **`recover` through glue** (`Cont.isGlue`: statement or expression glue):
the answer is the tail's, with the glue frame rebuilt above the tail's
answer. Glue is the ONLY thing the walk crosses. -/
theorem recoverResult_glue {k k' : Cont} (hg : k.isGlue = true) (hk : k.tail = some k') :
    recoverResult k = ((recoverResult k').1, k.withTail (recoverResult k').2) := by
  unfold recoverResult
  refine Cont.rebuild_getD_glue ?_ hg hk _ _
  intro k; cases k <;> rfl
variable (ctx)

/-- **The non-local control signals** (design-hygiene B4, review Q6):
what `break`, `continue`, `return`, `break L` and `continue L` put in
flight. ONE control form carries all five (`Config.signal`); ONE table
says what each statement frame does with each of them (`signalStep`).
`brkTo`/`contTo` travel to the `labelK` for `L` / the loop whose head is
the `labelK` for `L` (`contHeadLabel` — the frontend's placement
invariant); none of the five ever crosses a call frame except `ret`,
which EXITS it (`go/types` guarantees enclosure — the machine fails
closed on the rest). `goto` (FR-11/FR-20), if it ever lowers, lowers to a
signal — never to a frame-discarding jump (the reasoning-surface plan
§1.3: signals respect `fill`). -/
inductive Signal where
  | brk
  | cont
  | ret
  | brkTo (label : String)
  | contTo (label : String)
  deriving Repr, DecidableEq

/-- The signal a statement RAISES, if it is one of the five control
transfers (the `signalStmt` rule's premise; `none` for every other
statement). -/
def _root_.GoLean.GoCore.Stmt.signal? : Stmt → Option Signal
  | .returnStmt => some .ret
  | .breakStmt => some .brk
  | .continueStmt => some .cont
  | .breakTo label => some (.brkTo label)
  | .continueTo label => some (.contTo label)
  | _ => none

/-- Control configurations (the Iris `Expr` projection; the `Store` is
the paired `Step` component, as before). New over the old relation:
`evalE` (expression under evaluation) and `retV` (value delivery). The
terminal remains `.next .stop`; `retV` never reaches `.stop` because an
expression always evaluates under at least one frame. -/
inductive Config where
  | exec (stmt : Stmt) (env : LocalEnv) (k : Cont)
  | evalE (e : Expr) (env : LocalEnv) (k : Cont)
  | retV (v : GoValue) (k : Cont)
  | next (k : Cont)
  /-- A control SIGNAL travelling outward through the continuation (B4 —
  the former `.breaking`/`.continuing`/`.returning`/`.breakingTo`/
  `.continuingTo` constructors, one form): each statement frame either
  passes it on, catches it, or refuses it — the frame×signal table
  `signalStep`; the call frame catches `ret` alone (frame exit — the
  `.next` frame-exit rules' twins, state-touching, so they are rules of
  their own). -/
  | signal (sg : Signal) (k : Cont)
  /-- Unwinding: a panic (chain, arc doc §A1) travelling outward through
  the continuation. Frames strip; call frames run their defers (which is
  where `recover` can catch it); `.stop` renders the terminal abort. -/
  | panicking (chain : List PanicEntry) (k : Cont)
  -- (The terminal abort is `.panicking chain .stop` itself — B4: no
  -- k-less configuration; `Config.abort?` names the shape, the drivers
  -- and the pool render it (`abortMsg`). `.panicking` under a frame is
  -- the recoverable, non-terminal form.)
  -- Blocked configurations (channels arc slice 1, design of record D7:
  -- "blocked goroutines are blocked-Config shapes; NO waiter queues in
  -- channel state"). NO outgoing rules in the per-goroutine relation — in
  -- slice 2's ThreadPool the PAIRING/wake steps live at the pool level,
  -- and per-goroutine relation-silence here is what makes that extension
  -- additive. In this zero-scheduler slice the driver classifies any
  -- blocked configuration as the deadlocked run (`Stop.deadlock`):
  -- one blocked goroutine with no siblings IS Go's "all goroutines are
  -- asleep" state. Payloads carry what a future pairing step needs
  -- (channel identity, in-flight value, delivery targets); `ch = none` is
  -- the nil channel (blocks forever — no partner can exist).
  | blockedSend (ch : Option Loc) (v : GoValue) (k : Cont)
  | blockedRecv (ch : Option Loc) (targets : List Assignee) (elem : Ty) (env : LocalEnv) (k : Cont)
  | blockedSelect (clauses : List EvClause) (env : LocalEnv) (k : Cont)
  -- (The registry-op COMPLETION marker `.opDone sched inner` LEFT this
  -- type at C5 (2026-09-05): a scheduling annotation is not control. It
  -- is the per-goroutine `boundary` flag of `Thread.running`
  -- (Multi.lean), set by `Thread.afterStep` — the envelope statement of
  -- `ChoiceSite.postOp` lives there now.)
  /-- A goroutine parked on a sync primitive (spec-parity slice 2,
  design note §6): the op it will re-attempt, the primitive's cell.
  Relation-silent per-goroutine like the channel blocked shapes; the
  sequential driver classifies it as the deadlocked run (a parked sync
  op with no sibling IS "all goroutines are asleep" — probes p06-p08),
  and the pool wakes it cell-based (`wakeReady`/`resumeThread`). NO
  loc-option: a sync receiver address is never nil here (nil panics at
  the apply). Appended at the END so positional case tags stay
  stable. -/
  | blockedSync (op : SyncOp) (loc : Loc) (env : LocalEnv) (k : Cont)

/-- The configuration a CALL position's frame entry delivers (G-P S2):
RUN the callee's body in a fresh frame — the caller's target plans and
environment ride to frame exit, the frame names the function it runs
(`func.id`) — or, on `Entry.again`, RE-ENTER the same call position on the
interface's anchor with the receiver-adjusted arguments: a nullary value
call carrying every argument as a capture (`callValCalleeK`), so the NEXT
step is that anchor's ordinary entry under the same targets, environment
and continuation (design §2 S5: one machine step, no frame pushed). -/
def Entry.callConfig (plans : List (TargetShape × List Expr)) (env : LocalEnv) (k : Cont) :
    Entry → Config
  | .run func frameEnv resultLocs =>
      .exec func.body frameEnv (.frame plans env resultLocs [] k func.id)
  | .again fid args => .retV (.funcVal fid args) (.callValCalleeK plans [] env k)

/-- The configuration a DEFERRED call's drain — or the `go` spawn — delivers
(G-P S2): RUN the callee's body in a targetless, resultless frame on
`barrier` (a deferred call's results are discarded; the frame names the
function it runs), or, on `Entry.again`, RE-QUEUE the re-dispatch — the
anchor with the receiver-adjusted arguments as a function value — as the
pending call the draining frame enters at its NEXT step (`requeue`: the
drain's own configuration over the frame with the call at the head of its
chain; the spawn's child, a barrier frame holding the call). -/
def Entry.drainConfig (barrier : Cont) (requeue : GoValue → Config) : Entry → Config
  | .run func frameEnv _ => .exec func.body frameEnv (.frame [] [] [] [] barrier func.id)
  | .again fid args => requeue (.funcVal fid args)

variable {ctx}
/-- The frame a CALL position pushes on a RUN entry names the resolved
callee (the `fid` field, [USER] 2026-09-28 «Agree on (1)», relayed):
definitional. -/
theorem Entry.callConfig_run {plans : List (TargetShape × List Expr)} {env : LocalEnv} {k : Cont}
    {func : Func} {frameEnv : LocalEnv} {resultLocs : List Loc} :
    Entry.callConfig plans env k (.run func frameEnv resultLocs)
      = .exec func.body frameEnv (.frame plans env resultLocs [] k func.id) := rfl

/-- The frame a DRAIN (or the spawn) pushes on a RUN entry names the
resolved callee: definitional. -/
theorem Entry.drainConfig_run {barrier : Cont} {requeue : GoValue → Config}
    {func : Func} {frameEnv : LocalEnv} {resultLocs : List Loc} :
    Entry.drainConfig barrier requeue (.run func frameEnv resultLocs)
      = .exec func.body frameEnv (.frame [] [] [] [] barrier func.id) := rfl
variable (ctx)

/-- **The terminal shape, named once** (B3; ONE since B4): a goroutine
with nothing left to do is `.next .stop`. A signal at `.stop` is NOT a
terminal (B4: every driver runs its subject under a barrier frame, so a
`return`/`break`/`continue` reaching `.stop` is a refusal that names its
cause — `signalRefusal`), and the unrecovered-panic abort is
`.panicking chain .stop` (`Config.abort?`), classified by the drivers and
the pool, never a terminal SHAPE of the goroutine. -/
def Config.isTerminal : Config → Bool
  | .next .stop => true
  | _ => false

/-- **THE ABORT** (B4): an unrecovered panic chain at the empty
continuation — `some (first, rest)` at `.panicking (first :: rest) .stop`.
The configuration has no rule; what happens next is the DRIVER's:
`stepFn` (the sequential machine) raises the `panic` terminal there, the
pool (`stepThread`) turns the goroutine into its `aborted` tombstone —
both through `abortMsg`, both as ONE machine step, so the fuel accounting
of the old `.panicked` step is exact. An empty chain at `.stop` is a
machine-internal breach (`stepFn` refuses it by name). -/
def Config.abort? : Config → Option (PanicEntry × List PanicEntry)
  | .panicking (first :: rest) .stop => some (first, rest)
  | _ => none

/-- The cause a refused abort rendering NAMES (fail closed BY NAME, CLAUDE.md):
a string or `runtime.Error` payload whose FIRST LINE is not valid UTF-8 is
the D5 refusal — gc writes the raw bytes and the `String`-valued
observation cannot carry them (BUG-004 item 3, `docs/2026-09-07_land-panic-
text-tape.md` §2.3); everything else is the standing payload refusal
(BUG-004 item 4's `Error()`/`String()` rewrite, an unpinned family, a
carrier without a method-set record), named by the payload's dynamic type
key beside the `repr`, which prints a bare `Ty.defined i` since C2
(`payloadDynamicTypeNote`, audit fix R16). -/
def abortRefusal (first : PanicEntry) : String :=
  let invalidFirstLine : Option (Array UInt8) := match first.value with
    | .interface .string (.string gs) =>
        if (stringFirstLine? gs.bytes).isNone then some gs.bytes else none
    | .interface (.defined idx) (.string gs) =>
        if idx == runtimeErrorTypeIdx && (stringFirstLine? gs.bytes).isNone then some gs.bytes
        else none
    | _ => none
  match invalidFirstLine with
  | some bytes =>
      s!"panic abort rendering: the string payload's first line is not valid UTF-8 ({bytes.size} payload byte(s), first line {(bytes.takeWhile (· != 0x0A)).toList.map (·.toNat)}) — gc prints the raw bytes and the String-valued observation cannot carry them (BUG-004 item 3 / landing decision D5: no byte channel)"
  | none =>
      s!"panic abort rendering for payload {repr first.value}{payloadDynamicTypeNote ctx first.value}"

/-- Go's first `panic: ` line for an abort under the `repanicCollapse`
pick, or the refusal that names why it cannot be rendered. Shared by the
sequential machine's abort (`stepFn`) and the pool's (`stepThread`); both
draw the pick through `abortConsult` first. -/
def abortMsg (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) :
    Except Stop String :=
  match renderPanicHead ctx first rest pick with
  | some msg => return msg
  | none => throw (.unsupported (abortRefusal ctx first))

/-- The stream after an abort's consult, from the configuration: what the
pool returns and the sequential driver DROPS (the machine stops at its
`panic` terminal — no leftover is returned on any error path), exposed so
enumerators that replay `stepFn` can account for the pop exactly. `ch`
itself at a non-abort configuration. -/
def abortLeftover (c : Config) (ch : Choices) : Choices :=
  match c.abort? with
  | some (first, rest) => (abortConsult first rest ch).2
  | none => ch

/-! ## The signal table (B4) -/

/-- **THE FRAME×SIGNAL TABLE** — the one place that says what a
statement frame does with a control signal (review Q6: ~40 longhand
rules were this table written out). `some c'` is the successor; `none`
means the frame does NOT resolve the signal purely — the call frame's
`ret` (frame EXIT, state-touching: the `frameReturn*` rules /
`stepFrameExit`), and every REFUSAL (`signalRefusal` names the cause).

| frame ╲ signal | `brk`         | `cont`                | `ret` | `brkTo L`                    | `contTo L`                                   |
|---|---|---|---|---|---|
| `seq`          | pass          | pass                  | pass  | pass                         | pass                                         |
| `breakableK`   | exit → `next` | pass                  | pass  | pass                         | pass                                         |
| `labelK name`  | pass          | pass                  | pass  | name = L → `next`; else pass | name = L → REFUSE (non-loop label); else pass |
| `loop`         | exit → `next` | re-test (`while`)     | pass  | pass                         | head label = L → re-test; else pass          |
| `mapIterK`     | exit → `next` | re-pick (`next` frame) | pass | pass                         | head label = L → re-pick; else pass          |
| `frame`        | REFUSE        | REFUSE                | EXIT (rules) | REFUSE                | REFUSE                                       |
| `stop`         | REFUSE        | REFUSE                | REFUSE (past the entry frame) | REFUSE (escaped label) | REFUSE (escaped label)        |
| expression glue | REFUSE (internal) | … | … | … | … |

"pass" = `.signal sg k'` (strip the frame, keep travelling). The
re-test of a `loop` re-enters the `while` (its condition is evaluated
again); the re-pick of a `mapIterK` returns to the frame's pick step. -/
def signalStep (sg : Signal) : Cont → Option Config
  | .seq _ _ k' => some (.signal sg k')
  | .breakableK k' =>
      match sg with
      | .brk => some (.next k')
      | _ => some (.signal sg k')
  | .labelK name k' =>
      match sg with
      | .brkTo L => if name = L then some (.next k') else some (.signal sg k')
      | .contTo L => if name = L then none else some (.signal sg k')
      | _ => some (.signal sg k')
  | .loop c b env k' =>
      match sg with
      | .brk => some (.next k')
      | .cont => some (.exec (.while c b) env k')
      | .contTo L =>
          if contHeadLabel k' = some L then some (.exec (.while c b) env k')
          else some (.signal sg k')
      | _ => some (.signal sg k')
  | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
      match sg with
      | .brk => some (.next k')
      | .cont => some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'))
      | .contTo L =>
          if contHeadLabel k' = some L then
            some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'))
          else some (.signal sg k')
      | _ => some (.signal sg k')
  | _ => none

variable {ctx}
/-- The table has no `.frame` row (a call frame is exited by `ret` — the
frame-exit rules — and refuses every other signal) and no `.stop` row (a
signal at the empty continuation is relation-terminal). -/
@[simp] theorem signalStep_frame {sg : Signal} {targets : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {ds : List (GoValue × List GoValue)}
    {k : Cont} {fr : FuncId} :
    signalStep sg (.frame targets tenv results ds k fr) = none := rfl

@[simp] theorem signalStep_stop {sg : Signal} : signalStep sg .stop = none := rfl

variable (ctx)
/-- The REFUSAL a signal meets where the table has no successor and the
frame is not `ret`-at-a-call-frame — every one names its cause (fail
closed): a signal escaping its function body or its label, `continue`
to a non-loop label, a signal delivered to an expression frame (a
machine-internal shape breach). Total, so `stepFn`'s signal arm has no
absorbing default. -/
def signalRefusal (sg : Signal) : Cont → Stop
  | .frame .. =>
      match sg with
      | .brk => .stuck "function body escaped with break"
      | .cont => .stuck "function body escaped with continue"
      | .ret => .internal "return at a call frame is the frame exit, never a refusal"
      | .brkTo _ => .stuck "function body escaped with labeled break"
      | .contTo _ => .stuck "function body escaped with labeled continue"
  | .stop =>
      match sg with
      | .brk => .stuck "break outside loop"
      | .cont => .stuck "continue outside loop"
      | .ret => .internal "return unwound past the entry frame"
      | .brkTo L => .stuck s!"labeled break escaped its label: {L}"
      | .contTo L => .stuck s!"labeled continue escaped its label: {L}"
  | .labelK _ _ =>
      match sg with
      | .contTo L => .stuck s!"continue to non-loop label {L}"
      | _ => .internal "signal at a label frame the table resolves"
  -- The four other statement frames resolve EVERY signal in the table
  -- (`signalStep` has a `some` in each of their cells), so these arms
  -- are unreachable from `stepFn` today; they are stated by name (audit
  -- fix R7, 2026-09-05) so that a table row removed in the future
  -- refuses as "signal at a <frame> the table resolves", never as a
  -- mis-named "delivered to expression continuation".
  | .seq .. => .internal "signal at a seq frame the table resolves"
  | .loop .. => .internal "signal at a loop frame the table resolves"
  | .breakableK _ => .internal "signal at a breakable frame the table resolves"
  | .mapIterK .. => .internal "signal at a map-iteration frame the table resolves"
  | _ =>
      match sg with
      | .brk => .internal "break delivered to expression continuation"
      | .cont => .internal "continue delivered to expression continuation"
      | .ret => .internal "return delivered to expression continuation"
      | .brkTo _ => .internal "labeled break delivered to expression continuation"
      | .contTo _ => .internal "labeled continue delivered to expression continuation"

/-- The head of an APPLY position (A7): which apply the last operand's
arrival triggers. -/
inductive ApplyHead where
  | strict (op : StrictOp)
  | stmt (op : StmtOp) (nt : Nat)
  | chan (op : ChanStOp)
  | select (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
  | sync (op : SyncOp)
  | atomic (op : AtomicOp)
  | rhs (rop : RhsOp) (refs : List TargetRef) (body : Stmt)

/-- **The apply-position accessor** (A7, review U6): the one place that
knows the operand encoding. `some (head, operands, env, k)` exactly at a
`.retV v (…K … done [] env k)` whose last operand `v` just arrived, with
the operands in evaluation order (`(v :: done).reverse` — the frames
accumulate most-recent-first). Consumers that only need to know "is this
an apply of X to vs" read this instead of re-matching the seven frames. -/
def Config.applyPos : Config → Option (ApplyHead × List GoValue × LocalEnv × Cont)
  | .retV v (.strictK op done [] env k) => some (.strict op, (v :: done).reverse, env, k)
  | .retV v (.stmtOpK op nt done [] env k) => some (.stmt op nt, (v :: done).reverse, env, k)
  | .retV v (.chanStK op done [] env k) => some (.chan op, (v :: done).reverse, env, k)
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      some (.select clauses default?, (v :: done).reverse, env, k)
  | .retV v (.syncStK op done [] env k) => some (.sync op, (v :: done).reverse, env, k)
  | .retV v (.atomicStK op done [] env k) => some (.atomic op, (v :: done).reverse, env, k)
  | .retV v (.rhsK rop refs done [] body env k) =>
      some (.rhs rop refs body, (v :: done).reverse, env, k)
  | _ => none

/-- **The output event of a configuration** (stdlib slice 3; G-OUT): the
bytes the step about to be taken writes to fd 2 — `some bytes` exactly at
a `print`/`println` APPLY position whose operands render, `none`
everywhere else. Since the step-label reshape (2026-09-28) the STEP emits
its output itself (`stmtOpOut`, in `stepFn`'s and `Step.stmtOpApply`'s
label; `printOut?_toList` is the agreement) and the pool takes it from
that label; this pre-configuration reading remains the init phase's
refusal test (`initPrintRefusal?`). Derived from the PRE-configuration
by the same `renderPrint` the apply step validates through: when the
step succeeds the rendering succeeded, so the event carries the validated
bytes; when the rendering refuses, the step itself refuses and no event
is observed. A statement that consumes no choice and touches no state —
the event IS its whole effect. -/
def printOut? : Config → Option GoString
  | .retV v (.stmtOpK (.print newline) _ done [] _ _) =>
      match renderPrint newline (v :: done).reverse with
      | .ok bytes => some bytes
      | .error _ => none
  | _ => none

/-- **The OUTPUT a wide statement's apply writes** (step-label reshape,
2026-09-28): a `print`/`println` apply's rendered bytes — the same
`renderPrint` the apply validates through, so on a successful apply the
element is exactly the validated rendering — and `[]` for every other
head. The `out` channel of `stepFn`'s and `Step.stmtOpApply`'s label (on
the apply's value path; a delivered panic writes nothing). -/
def stmtOpOut : StmtOp → List GoValue → List GoString
  | .print newline, vs =>
      match renderPrint newline vs with
      | .ok bytes => [bytes]
      | .error _ => []
  | _, _ => []

/-- The step's own output agrees with the pre-configuration reading at an
apply position. -/
theorem printOut?_toList {v : GoValue} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {env : LocalEnv} {k : Cont} :
    (printOut? (.retV v (.stmtOpK op nt done [] env k))).toList
      = stmtOpOut op (v :: done).reverse := by
  cases op <;> simp only [printOut?, stmtOpOut, Option.toList]
  generalize renderPrint _ _ = r
  cases r <;> rfl

/-- The lowering contract at an `appendSlice` apply (audit fix F1): the
frontend hoists EVERY append into a fresh local temp (`emit.go`, the
append lowering), so the target operand addresses a ROOT cell — a store
into it cannot panic (`storeLoc_base_noPanic`, MachineSound), which is
what refutes the post-pop-panic disjunct of `stepFn_consumption_some`.
Every other configuration satisfies it vacuously. -/
def Config.appendTargetLocal : Config → Prop
  | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
      ∃ a rest, (v :: done).reverse = .addr (.base a) :: rest
  | _ => True

/-- **Apply, then deliver** (B2): the ONE bridge from an apply's `Result`
to the machine's control side. A value continues as `next a`; a
RECOVERABLE panic becomes the unwinding configuration `.panicking (chain
++ [panicEntry msg]) k` over the PRE-apply state `s` — the apply's
effects are discarded, exactly as every former `.error (.panic msg) ⇒
.panicking …` conversion site did. `chain` is the suspended chain a
PANIC-PATH deferred-call entry joins (audit F1+F5, 2026-08-05: the entry
panic is the deferred invocation's panic and joins newest-last); every
other site delivers under the empty chain. `panicPicks` are the tape
consultations the apply KEPT on its way to the panic (the frame entry's
`nilValueMethodText` text pick, drawn on the panic path only); every other
site passes none. Shared verbatim by the relation's apply/entry rules,
`stepFn` (through `deliverS`/`deliverV`, which add the executable's
stream) and `spawnStep`. Since the step-label reshape (2026-09-28) the
delivered value is the step's full `StepLabel`. -/
def deliver {α : Type} (s : Store) (k : Cont) (next : α → Config × Store × StepLabel)
    (r : Result α) (chain : List PanicEntry := []) (panicPicks : List PickRecord := []) :
    Config × Store × StepLabel :=
  match r with
  | .ok a => next a
  -- The delivered panic carries the EMPTY trace and no output (C1 S2a):
  -- the apply's effects are discarded, its accesses never happened — the
  -- detector's standing convention («the step panicked: the access never
  -- happened»); only the panic path's own kept consultations are recorded.
  | .panic msg => (.panicking (chain ++ [panicEntry msg]) k, s, ⟨[], panicPicks, []⟩)

variable {ctx}
@[simp] theorem deliver_ok {α : Type} {s : Store} {k : Cont}
    {next : α → Config × Store × StepLabel}
    {a : α} {chain : List PanicEntry} {ps : List PickRecord} :
    deliver s k next (.ok a) chain ps = next a := rfl

@[simp] theorem deliver_panic {α : Type} {s : Store} {k : Cont}
    {next : α → Config × Store × StepLabel}
    {msg : String} {chain : List PanicEntry} {ps : List PickRecord} :
    deliver s k next (.panic msg) chain ps
      = (.panicking (chain ++ [panicEntry msg]) k, s, ⟨[], ps, []⟩) := rfl

/-- A delivered panic is the unwinding configuration over the pre-state,
with the empty trace, no output and exactly the panic path's picks. -/
theorem deliver_panic_eq {α : Type} {s : Store} {k : Cont}
    {next : α → Config × Store × StepLabel}
    {msg : String} {chain : List PanicEntry} {ps : List PickRecord}
    {c' : Config} {s' : Store} {l : StepLabel}
    (h : deliver s k next (.panic msg) chain ps = (c', s', l)) :
    c' = .panicking (chain ++ [panicEntry msg]) k ∧ s = s' ∧ l = ⟨[], ps, []⟩ := by
  simp only [deliver_panic, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1, h.2.2.symm⟩

variable (ctx)
/-- The frame-ENTRY shapes and the `(fid, args)` their next step hands
to `enterFrame` — the seven `stepFn` positions that route through
`enterFramePick` (the ordinary call with
no arguments, the last-argument arrival, the value-call callee/last-
argument arrivals, and the three deferred-call drains: normal, return,
panic-path) plus the two `go`-statement spawn positions (`spawnStep`,
Multi.lean). ONE table, consumed by the `nilValueMethodText` mirrors
(`consumesNilValueMethod` here; `CLI.stepNeeds`/`stepNeedsSeq`; the
tracer's `seqSite`) so the accountant derives the site's bound from the
machine's own analysis (`nilValueMethodWidth`) rather than a
hand-copied shape list. `none` = the step is not a frame entry. -/
def entryCallSite? : Config → Option (FuncId × List GoValue)
  | .exec (.call _ fid args) _ _ =>
      match args.toList with
      | [] => some (fid, [])
      | _ :: _ => none
  | .retV v (.callArgsK fid _ vals [] _ _) => some (fid, vals ++ [v])
  | .retV (.funcVal fid captured) (.callValCalleeK _ [] _ _) => some (fid, captured)
  | .retV v (.callValArgsK (.funcVal fid captured) _ vals [] _ _) =>
      some (fid, captured ++ vals ++ [v])
  | .next (.frame _ _ _ ((.funcVal fid captured, args) :: _) _ _) =>
      some (fid, captured ++ args)
  | .signal .ret (.frame _ _ _ ((.funcVal fid captured, args) :: _) _ _) =>
      some (fid, captured ++ args)
  | .panicking _ (.frame _ _ _ ((.funcVal fid captured, args) :: _) _ _) =>
      some (fid, captured ++ args)
  -- The `go`-statement entry (`spawnPlan` shapes, Multi.lean — the
  -- callee arrives, or its last argument arrives): `spawnStep` enters the
  -- callee's frame in the child, and its entry panic draws the same pick
  -- (audit fix F1, 2026-09-03: `go v.M()` on a nil `*T` box is in the
  -- family — gc gives the panicwrap text there).
  | .retV (.funcVal fid captured) (.goCalleeK [] _ _) => some (fid, captured ++ [])
  | .retV v (.goArgsK (.funcVal fid captured) vals [] _ _) =>
      some (fid, captured ++ (vals ++ [v]))
  | _ => none

/-- Does this configuration's next step draw the `nilValueMethodText`
pick (BUG-087)? `true` exactly at a frame entry in the wrapper family
(`nilValueMethodText?` = some — bound 2); every other shape consumes
nothing at the site. The stream-obliviousness checkers exclude exactly
this (`stepFn_oblivious`' `hnv`, `poolThreadOblivious`, `innerVecs`,
`allStreamsOk`) — a fail-closed flag like `consumesAppendSlice`. -/
def consumesNilValueMethod (c : Config) : Bool :=
  match entryCallSite? c with
  | some (fid, args) => (nilValueMethodText? ctx fid args).isSome
  | none => false

/-- Enter a receive's TARGET phase (nonempty targets; convergence
round, BUG-029): resolve the target plan and start phase 1 on the
first target's first operand. Shared verbatim by `applyChanOp` (both
dequeue arms) and `commitClause` — and by `stepFn` through them. The
malformed arms (an empty plan for nonempty targets, a zero-operand
shape) cannot arise from `targetsPlan` — fail closed, never a silent
default. -/
def enterRecvTargets (s : Store) (targets : List Assignee)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k : Cont) :
    Except Stop (Config × Store) := do
  match targetsPlan targets with
  | some ((sh, e :: ops) :: rest) =>
      return (.evalE e env (.tgtOpK sh [] ops [] rest .vals [] vals body env k), s)
  | _ => stuck "malformed receive target plan"

/-- Apply a channel statement's head to its evaluated pre-communication
operands. One step; the outcome is a configuration — `.next k` on
success, `.panicking` for the channel panics (send-on-closed /
close-of-closed / close-of-nil — REAL recoverable Go panics, D4;
messages are gc's realized strings, probes p01-p03), a `.blocked*`
shape where Go blocks (nil channel; unbuffered/full send; open-empty
receive), or — for a receive with targets — the phase-1 target entry
(`enterRecvTargets`): the COMMUNICATION happens in this step, target
OPERANDS evaluate after it, and the stores (with their nil-deref /
out-of-range panics, spec §Assignments PHASE-2 events) follow
left-to-right, exactly like the select path's step 4 (BUG-022/BUG-029;
pinned by `channels/recv-edge/*` — the drain discriminators and the
blocks-not-panics classification). Shared verbatim by rule
`Step.chanStApply` and `stepFn`'s `chanStK` apply arm.

B1 (W3.2 slice 1 stage C) / C5 (2026-09-05): every PROCEEDING outcome
opens the goroutine's post-op scheduling point — since C5 as the pool's
per-goroutine boundary FLAG (`Thread.afterStep`, Multi.lean, the envelope
statement of `ChoiceSite.postOp`), not as a wrapping configuration. A
park IS a boundary shape already; a panicking outcome opens none (the
abort window is B3, deferred — boundary-set note §2). -/
def applyChanOp (s : Store) (op : ChanStOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except Stop (Config × Store × AccessTrace) := do
  match op, vs with
  | .send elem, [chv, vv] => do
      let ch ← valueAsChan chv
      -- Normalize at the element type up front (the mapAssign discipline;
      -- for the blocked shapes the pinned value travels normalized).
      let v' ← normalizeValueForTy ctx elem vv
      match ch.base with
      | none => return (.blockedSend none v' k, s, [])
      | some loc => do
          -- THE LABEL (C1 S2c): `chansend`'s entry read of the channel object
          -- (BUG-045) opens every outcome — commit, park, panic alike; a
          -- committed buffered send then transits the next send slot
          -- (`racenotify`). A parked send's slot action is the WAKE's
          -- (`resumeThread`) or the pairing's (`applyPairing`).
          let entry := chanSendEntry loc
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [panicEntry "send on closed channel"] k, s, entry)
          else if buf.size < capacity then do
            let s' ← storeChanPayload s loc (buf.push v') capacity closed
            return (.next k, s', entry ++ [.hb (.slotOp loc.canon capacity true)])
          else
            return (.blockedSend (some loc) v' k, s, entry)
  | .recv targets elem, [chv] => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return (.blockedRecv none targets elem env k, s, [])
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          match buf[0]? with
          | some v => do
              -- FIFO dequeue; a closed channel drains its buffer
              -- with ok = true before yielding zeros (probe p06).
              -- THE LABEL: `chanrecv` is acquire-only — no channel-object
              -- access (BUG-045); the dequeue transits the next receive slot.
              let s₁ ← storeChanPayload s loc (buf.eraseIdx! 0) capacity closed
              let tr : AccessTrace := [.hb (.slotOp loc.canon capacity false)]
              match targets with
              | [] => return (.next k, s₁, tr)
              | _ :: _ => do
                  let (c', s₂) ← enterRecvTargets s₁ targets
                    (recvStores v true targets.length) (.seqn #[]) env k
                  return (c', s₂, tr)
          | none =>
              if closed then do
                -- The closed-and-empty receive acquires the closer's clock.
                let zero ← defaultValue ctx elem
                let tr : AccessTrace := [.hb (.closeAcquire loc.canon)]
                match targets with
                | [] => return (.next k, s, tr)
                | _ :: _ => do
                    let (c', s₂) ← enterRecvTargets s targets
                      (recvStores zero false targets.length) (.seqn #[]) env k
                    return (c', s₂, tr)
              else
                return (.blockedRecv (some loc) targets elem env k, s, [])
  | .close, [chv] => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return (.panicking [panicEntry "close of nil channel"] k, s, [])
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [panicEntry "close of closed channel"] k, s, [])
          else do
            let s' ← storeChanPayload s loc buf capacity true
            -- THE LABEL: `closechan`'s channel-object WRITE on the success
            -- path (BUG-045), under the pre-release clock, THEN the release.
            return (.next k, s', chanCloseWrite loc ++ [.hb (.closeOp loc.canon capacity)])
  | op, vs => stuck s!"malformed channel-operator application: {repr op} on {vs.length} operand(s)"

/-- **Apply a sync statement's head to its evaluated operands — the
sync registry entry's op semantics AND its envelope statement** (design
note §§4,6; every behavioral claim probed on go1.26.5, probe ids in
the design note).

THE ENVELOPE STATEMENT (nondeterminism doctrine, shipped with the
site): the spec and package docs say NOTHING about acquisition order
among lock/Wait/Do contenders — no fairness, no FIFO (gc realizes
semaphore-FIFO handoff WITH barging, one legal point) — so the envelope
is "any registry-granularity schedule over runnable goroutines", which
is EXACTLY the existing L1 site's envelope: an unlock/Done/complete
merely makes parked contenders wake-ready (`wakeReady`), and WHICH
contender (or barging new arrival) proceeds next is the next L1 pick.
Soundness (⊇ gc), stated at ACQUISITION-ORDER granularity (audit fix
round 2026-08-10, F1): acquisition order IS run order of the acquire
steps, and L1 admits all run orders — gc's handoff member is the
parked-waiter-picked schedule, every barging member an arrival-picked
schedule. The claim is NOT per-state successor containment: at the
RWMutex both-parked state (writer holds, a writer AND a reader are
parked) gc's Unlock deterministically releases the readers first
(rwmutex.go:206-217) while this model's `pendingW` keeps readers
excluded until the parked writer passes — the reader-first ORDER is
still admitted through the schedules that order the acquire steps
directly (design note §8 R1; pinned by sync/rwmutex-order/acquisition,
members {10, 20} ⊇ gc's realized 10). CONSEQUENCE: this apply consumes NOTHING from
the choice stream, ever — sync adds zero new consumption sites, and
single-thread sync programs are stream-transparent (sequential
conservation untouched).

Outcomes, per primitive (design note §4):
* Mutex — `lock`: unlocked → locked; locked → park. `unlock`: locked →
  unlocked; unlocked → the UNRECOVERABLE `Stop.fatal
  "sync: unlock of unlocked mutex"` (probe p01: gc's runtime `fatal`,
  recover does not catch — never a `.panicking`). No owner tracking
  (probe p09: cross-goroutine unlock is legal).
* RWMutex — `rlock`: admitted iff no writer AND no PENDING writer
  (`pendingW` — rwmutex.go's documented "a blocked Lock call excludes
  new readers"); else park. `runlock`: readers > 0 → decrement; else
  fatal "sync: RUnlock of unlocked RWMutex" (p03). `wlock`: free →
  acquire; else park AND count itself in `pendingW` (the resume
  decrements). `wunlock`: writer → release; else fatal
  "sync: Unlock of unlocked RWMutex" (p02).
* WaitGroup — `wgAdd`: the counter updates FIRST (probe p13: a
  recovered negative-counter panic leaves the counter negative), then
  new < 0 → the RECOVERABLE panic "sync: negative WaitGroup counter"
  (p04 — a real `panic()`, unlike the mutex fatals), then
  a ZEROING add resets the waiter count in the same atomic step
  (waitgroup.go:134-135; delta-review round 2 corrected this line — it
  used to list the REMOVED Add-side misuse panic as an outcome. gc
  reaches waitgroup.go:120 only through sub-op interleavings, realized
  here as the wg-sema race or clean, and gc's WAITER-side reuse panic
  (waitgroup.go:213) is a recorded §8 narrowing OUTSIDE this envelope
  — the ⊇-gc claim above carries that carve-out alongside the RWMutex
  one). `wgWait`:
  counter = 0 → proceed (the fast path still acquires — raceUpdate);
  else park, counting itself in `waiters`.
* Once — `onceBegin targets`: fresh → mark started, deliver `true`
  (run f); started ∧ done → deliver `false`; started ∧ ¬done → park
  (nested Do on one goroutine = deadlock, probe p08). Delivery rides
  `enterRecvTargets` (one fresh frontend temp). `onceComplete`: mark
  done — reached through the Once desugar's DEFER, so a panicking f
  still completes (probe p05). A complete without a begin is
  `.internal` (only the desugar emits it).

A nil receiver address panics recoverably via `valueAsLoc` (gc: the
nil-pointer deref inside the method). This is the CHOICES-FREE core
(the `applyStmtOpCore` mold): the TRY heads — the one sync op family
that draws a pick — apply through `applySyncOp` below, which threads
the stream and dispatches everything else here unchanged. Shared
verbatim (through `applySyncOp`) by rule `Step.syncStApply` and
`stepFn`'s `syncStK` apply arm. -/
def applySyncOpCore (s : Store) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except Stop (Config × Store × AccessTrace) := do
  -- THE LABEL (C1 S2c, D9): every arm emits, in gc's instruction order, the
  -- op's ENTRY word accesses (`syncEntryKinds` — the state CAS / the
  -- `race.Read(&rw.w)` / the `wg.sema` pair, with go_mem's operation kind,
  -- under the pre-op clock, commit or park alike), then on a committed op
  -- its acquire/release ACTION (the package-doc HB sentences, quoted at
  -- `SyncClocks`), then the accesses that FOLLOW the release
  -- (`syncReleaseTailKinds` — Unlock's state Add). Fatal outcomes throw
  -- (no label); a park carries its entry accesses and no action (the wake
  -- acquires, `resumeThread`); `wgAdd`'s release-merge on a negative delta
  -- precedes its panic check (waitgroup.go:81), so the panicking outcome
  -- carries it too.
  match op, vs with
  | .lock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      let entry := syncEntryKinds .lock pre 0 false loc
      match pre with
      | .mutex locked =>
          if locked then return (.blockedSync .lock loc env k, s, entry)
          else do
            let s' ← storeLoc ctx s loc (.syncData (.mutex true))
            return (.next k, s', entry ++ [.hb (.syncAcquire loc.canon false)])
      | other => stuck s!"Lock on a non-mutex sync cell: {repr other}"
  | .unlock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      match pre with
      | .mutex locked =>
          if locked then do
            let s' ← storeLoc ctx s loc (.syncData (.mutex false))
            return (.next k, s', syncEntryKinds .unlock pre 0 false loc
              ++ [.hb (.syncRelease loc.canon false)] ++ syncReleaseTailKinds .unlock pre loc)
          else throw (.fatal "sync: unlock of unlocked mutex")
      | other => stuck s!"Unlock on a non-mutex sync cell: {repr other}"
  | .rlock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      let entry := syncEntryKinds .rlock pre 0 false loc
      match pre with
      | .rwmutex writer readers pendingW =>
          if writer || pendingW > 0 then
            return (.blockedSync .rlock loc env k, s, entry)
          else do
            let s' ← storeLoc ctx s loc (.syncData (.rwmutex writer (readers + 1) pendingW))
            return (.next k, s', entry ++ [.hb (.syncAcquire loc.canon false)])
      | other => stuck s!"RLock on a non-RWMutex sync cell: {repr other}"
  | .runlock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      match pre with
      | .rwmutex writer readers pendingW =>
          match readers with
          | r + 1 => do
              let s' ← storeLoc ctx s loc (.syncData (.rwmutex writer r pendingW))
              return (.next k, s', syncEntryKinds .runlock pre 0 false loc
                ++ [.hb (.syncRelease loc.canon true)] ++ syncReleaseTailKinds .runlock pre loc)
          | 0 => throw (.fatal "sync: RUnlock of unlocked RWMutex")
      | other => stuck s!"RUnlock on a non-RWMutex sync cell: {repr other}"
  | .wlock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      let entry := syncEntryKinds .wlock pre 0 false loc
      match pre with
      | .rwmutex writer readers pendingW =>
          if !writer && readers == 0 then do
            let s' ← storeLoc ctx s loc (.syncData (.rwmutex true 0 pendingW))
            return (.next k, s', entry ++ [.hb (.syncAcquire loc.canon true)])
          else do
            -- Park AND register as a pending writer: the documented
            -- exclusion of new readers starts at the BLOCKED Lock call
            -- (rwmutex.go), so the count updates at the park.
            let s' ← storeLoc ctx s loc (.syncData (.rwmutex writer readers (pendingW + 1)))
            return (.blockedSync .wlock loc env k, s', entry)
      | other => stuck s!"write-Lock on a non-RWMutex sync cell: {repr other}"
  | .wunlock, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      match pre with
      | .rwmutex writer readers pendingW =>
          if writer then do
            let s' ← storeLoc ctx s loc (.syncData (.rwmutex false readers pendingW))
            return (.next k, s', syncEntryKinds .wunlock pre 0 false loc
              ++ [.hb (.syncRelease loc.canon false)] ++ syncReleaseTailKinds .wunlock pre loc)
          else throw (.fatal "sync: Unlock of unlocked RWMutex")
      | other => stuck s!"write-Unlock on a non-RWMutex sync cell: {repr other}"
  | .wgAdd, [av, dv] => do
      let loc ← valueAsLoc av
      let delta ← valueAsInt dv
      let pre ← syncCell ctx s loc
      match pre with
      | .waitGroup counter waiters => do
          -- gc's counter is an int32 — the high 32 bits of the uint64
          -- state word (waitgroup.go:104 `state.Add(uint64(delta) << 32)`,
          -- :109 `v := int32(state >> 32)`) — so the addition wraps mod
          -- 2^32 BEFORE the negative test (arc-end fix round 2026-08-10;
          -- divergence was real in BOTH directions, pinned by
          -- `sync/waitgroup-int32`: `Add(1 << 31)` panics in gc where the
          -- unbounded Int proceeded, `Add(-(1 << 32))` leaves the state
          -- word untouched where the unbounded Int fabricated the panic).
          -- The stored counter always lies in int32 range (starts 0,
          -- every update wraps), matching gc's bit pattern exactly.
          let counter' := (counter + delta + 2147483648).emod 4294967296 - 2147483648
          -- The ZEROING Add resets the wait count (audit fix round
          -- 2026-08-10, gc waitgroup.go:134-135: `wg.state.Store(0)`
          -- runs BEFORE the semrelease loop) — so an Add issued in the
          -- wake window, with woken waiters not yet resumed, sees
          -- w == 0 and gc's ADD side is silent (eval-pinned by the
          -- two-waiter reuse-window pin). PRECISION (delta-review
          -- round 2 — the first comment said "gc is CLEAN there",
          -- which is only the Add's half): gc's misuse detection
          -- MOVES to the WAITER, which panics "sync: WaitGroup is
          -- reused before previous Wait has returned"
          -- (waitgroup.go:207-213) when it resumes seeing nonzero
          -- state; our woken waiter stays parked instead — the §8
          -- reuse-window narrowing, recorded, misuse-only. The parked waiters stay parked-Config
          -- shapes; their resume's `waiters - 1` saturates at the
          -- already-reset 0. A NEW Wait parking after the reset counts
          -- from 0 again — which is also what keeps the first-waiter
          -- sema WRITE condition (the `.wgWait` entry row) gc-exact
          -- across reuse rounds.
          let waiters' := if counter' == 0 && waiters > 0 then 0 else waiters
          -- The update lands BEFORE any panic (probe p13).
          let s' ← storeLoc ctx s loc (.syncData (.waitGroup counter' waiters'))
          -- THE LABEL: the entry pair (the sema READ when the counter
          -- leaves 0 upward, the state RMW's write-like kind), then gc's
          -- ReleaseMerge when delta < 0 (waitgroup.go:81 — BEFORE the
          -- panic checks, so a Done whose negative-counter panic is
          -- later recovered still released; probed ordering, design
          -- note §4). No tail.
          let tr := syncEntryKinds .wgAdd pre delta false loc
            ++ (if delta < 0 then [.hb (.syncRelease loc.canon false)] else [])
          if counter' < 0 then
            -- Payload CLASS is gc-exact (arc-end fix round 2026-08-10):
            -- gc's sync package raises this with `panic("...")` — a plain
            -- string, package code — where the channel panics are runtime
            -- `plainError`s. `recover().(string)` answers true here.
            return (.panicking [⟨stringPanicValue
              "sync: negative WaitGroup counter", false⟩] k, s', tr)
          else
            -- gc's Add-side misuse panic (waitgroup.go:120, `w != 0 &&
            -- delta > 0 && v == int32(delta)`) is UNREACHABLE at
            -- registry granularity once the reset above is modeled:
            -- `waiters > 0` requires a park at counter ≠ 0, and any op
            -- that returns the counter to 0 resets the count in the
            -- same atomic step — gc reaches line 120 only through
            -- sub-op Wait/Add interleavings (a Wait registered between
            -- another Add's state update and its reset), which this
            -- machine's atomic ops realize as the wg-sema race or as
            -- clean runs. No arm is kept (no inert dead code); the
            -- audit fix round removed it with this record.
            return (.next k, s', tr)
      | other => stuck s!"Add on a non-WaitGroup sync cell: {repr other}"
  | .wgWait, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      -- The entry pair: the first-waiter sema WRITE (waitgroup.go:184-190,
      -- pre-park waiter count 0 — concurrent Waits must not race each
      -- other) and the counter read's read-like kind; a park carries no
      -- action, the wake acquires ("a call to Done 'synchronizes before'
      -- the return of any Wait call that it unblocks").
      let entry := syncEntryKinds .wgWait pre 0 false loc
      match pre with
      | .waitGroup counter waiters =>
          if counter == 0 then return (.next k, s, entry ++ [.hb (.syncAcquire loc.canon false)])
          else do
            let s' ← storeLoc ctx s loc (.syncData (.waitGroup counter (waiters + 1)))
            return (.blockedSync .wgWait loc env k, s', entry)
      | other => stuck s!"Wait on a non-WaitGroup sync cell: {repr other}"
  | .onceBegin targets, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      -- A Do observing completion is the atomic load of `o.done` and
      -- ACQUIRES (the completion release is `onceComplete`'s); every other
      -- Do is `doSlow`'s `o.m.Lock()` CAS — a fresh begin or a park carries
      -- no action.
      let entry := syncEntryKinds (.onceBegin targets) pre 0 false loc
      match pre with
      | .once started done =>
          if !started then do
            let s' ← storeLoc ctx s loc (.syncData (.once true false))
            let (c', s'') ← enterRecvTargets s' targets [.bool true] (.seqn #[]) env k
            return (c', s'', entry)
          else if done then do
            let (c', s'') ← enterRecvTargets s targets [.bool false] (.seqn #[]) env k
            return (c', s'', entry ++ [.hb (.syncAcquire loc.canon false)])
          else
            return (.blockedSync (.onceBegin targets) loc env k, s, entry)
      | other => stuck s!"Once.Do begin on a non-Once sync cell: {repr other}"
  | .onceComplete, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      match pre with
      | .once started _ =>
          if started then do
            let s' ← storeLoc ctx s loc (.syncData (.once true true))
            -- `o.done.Store(true)`, the release, then the deferred
            -- `o.m.Unlock()`'s Add (the tail).
            return (.next k, s', syncEntryKinds .onceComplete pre 0 false loc
              ++ [.hb (.syncRelease loc.canon false)] ++ syncReleaseTailKinds .onceComplete pre loc)
          else throw (.internal "onceComplete without a matching onceBegin")
      | other => stuck s!"Once.Do complete on a non-Once sync cell: {repr other}"
  -- The TRY heads never reach the core: `applySyncOp` draws their pick
  -- and applies `applyTryLock`. Named, not absorbed by the catch-all.
  | .tryLock _, _ | .tryRLock _, _ | .tryWLock _, _ =>
      throw (.internal "try-lock heads apply through applySyncOp (the choice-taking entry), never the core")
  | op, vs => stuck s!"malformed sync-operator application: {repr op} on {vs.length} operand(s)"

/-- The cell a TRY head would leave behind if it ACQUIRED — `.ok (some _)`
exactly when the op could acquire (the `tryLockWidth` = 2 condition; ONE
derivation for the apply, the width and the accountants): `TryLock` on
an unlocked Mutex → locked; `TryRLock` when no writer HOLDS → one more
reader (the `rlock` acquire — a PENDING writer does NOT force a failure,
see the envelope statement at `applyTryLock`: audit fix round F1, the R1
value-observable half); RWMutex `TryLock` when no writer and no reader
holds → the writer bit (the `wlock` immediate acquire). `.ok none` on a
held cell; a kind-mismatched cell or a
non-try head is a `stuck`/`internal` ERROR (fail closed, before any pick
matters). -/
def tryAcquire (op : SyncOp) (pre : SyncPrim) : Except Stop (Option SyncPrim) :=
  match op, pre with
  | .tryLock _, .mutex locked => pure (if locked then none else some (.mutex true))
  | .tryRLock _, .rwmutex writer readers pendingW =>
      pure (if writer then none else some (.rwmutex writer (readers + 1) pendingW))
  | .tryWLock _, .rwmutex writer readers pendingW =>
      pure (if writer || readers > 0 then none else some (.rwmutex true 0 pendingW))
  | .tryLock _, other => stuck s!"TryLock on a non-mutex sync cell: {repr other}"
  | .tryRLock _, other => stuck s!"TryRLock on a non-RWMutex sync cell: {repr other}"
  | .tryWLock _, other => stuck s!"RWMutex TryLock on a non-RWMutex sync cell: {repr other}"
  | op, _ => throw (.internal s!"tryAcquire on a non-try head: {repr op}")

/-- The width of the `tryLock` site at a TRY head's apply, from the
PRE-step cell: 2 when the op could acquire — `TryLock` on an unlocked
Mutex; `TryRLock` when no writer HOLDS (a pending writer does not force
the failure — the R1 note at `applyTryLock`); RWMutex `TryLock` when no
writer holds and no reader does (the `wlock` immediate-acquire
condition) — else 1 (the failure is forced; a bound-1 consult pops
nothing under the uniform rule). A kind-mismatched cell is
width 1 too (the apply is `stuck` there, before any pick matters). The
accountants (`CLI.stepNeeds`, `ChoiceTrace.seqSite`) recompute the bound
through THIS function. -/
def tryLockWidth (op : SyncOp) (pre : SyncPrim) : Nat :=
  match tryAcquire op pre with
  | .ok (some _) => 2
  | _ => 1

-- DELETED (C1 S2c-ii): `tryLockAcquired` — the fold's re-derivation of a TRY head's outcome from
-- the pre/post cells. `applyTryLock` KNOWS its outcome and emits it (`syncEntryKinds … acquired` and
-- the acquire action); the S2c-i audit compared the two accounts on every traced step (0 differences).

/-- A TRY head's result delivery: through `enterRecvTargets` when a target
exists (the `onceBegin` shape), else the plain continuation — success
depends on the TARGET LIST alone (`tryDeliver_ok_any`), never on the
state or the value. Every outcome is a registry-op completion (B1/C5:
the pool flags it `postOp`). -/
def tryDeliver (b : Bool) (s : Store) (targets : List Assignee)
    (env : LocalEnv) (k : Cont) : Except Stop (Config × Store) :=
  match targets with
  | [] => return (.next k, s)
  | _ :: _ => do
      let (c', s') ← enterRecvTargets s targets [.bool b] (.seqn #[]) env k
      return (c', s')

/-- **The TRY heads' apply — THE ENVELOPE STATEMENT of
`ChoiceSite.tryLock`** (Q-TRYLOCK, RULED [USER] 2026-08-31 —
`docs/2026-08-31_qrow-rulings.md` row 5; the ruling/sequencing
provenance: ledger [DL-12]; the twin-pin re-pin and the "own slice" sequencing RULED
[USER] 2026-09-03, both relayed by the [AGENT] coordinator; memo
`docs/2026-08-21_w32-qrow-memos.md` §5; implemented 2026-09-03).

THE TEXT (mem#locks, verbatim): "A successful call to l.TryLock (or
l.TryRLock) is equivalent to a call to l.Lock (or l.RLock). An
unsuccessful call has no synchronizing effect at all. As far as the
memory model is concerned, l.TryLock (or l.TryRLock) may be considered
to be able to return false even when the mutex l is unlocked." This is
spec-DECLARED latitude, not silence: at an acquirable cell the
return-value envelope is {true, false}. The always-succeeds pin (the
memo's option (B)) is OFF THE MENU PERMANENTLY by the ruling — it would
narrow a latitude the text grants by name, and gc itself realizes a
false-when-momentarily-free under contention (a lost CAS on `m.state`,
internal/sync/mutex.go:85; the starvation-mode early return, :78).

THE ENVELOPE, per head, from the pre-step cell:
* acquirable (`tryLockWidth` = 2) → ONE demonic pick at
  `ChoiceSite.tryLock`: slot 0 = ACQUIRE — the SAME state transition
  as `Lock`/`RLock`/write-`Lock`'s immediate acquire (`applySyncOpCore`)
  and, in `raceUpdate`, the same acquire edge ("equivalent to a call to
  l.Lock"); slot 1 = SPURIOUS FAILURE — deliver `false`, NO state
  change, NO HB edge ("no synchronizing effect at all"). gc exhibits
  only slot 0 in isolation (probe `muUncontended`, 20/20 at GOMAXPROCS 1
  and 8 — `docs/evidence/2026-09-03_q-trylock/`), so the spurious member
  is UNEXHIBITED-BUT-PERMITTED: the membership rows over {1, 0} carry
  it (`sync/trylock/*`), never a strict row.
* held (`tryLockWidth` = 1) → `false`, deterministically, and the site
  is consulted at bound 1 WITHOUT a pop (the uniform rule), so a
  TryLock on a held lock is stream-transparent (probes `muLocked`,
  `rwMatrix`: false 20/20). RWMutex `TryRLock` is FORCED false only while
  a writer HOLDS (`writer = true`): gc's `readerCount` goes negative at
  `readerCount.Add(-rwmutexMaxReaders)` (rwmutex.go:152), which a writer
  reaches only after `rw.w.Lock()` (:150) — a writer QUEUED behind
  `rw.w` leaves `readerCount ≥ 0`, and gc's TryRLock returns TRUE there
  (audit fix round F1: the auditor's probe 40/40, our
  `rwTryRLockQueuedWriter`), while a writer past :152 waiting for readers
  forces false (`rwTryRLockPendingWriter`: false 20/20). The model's
  `pendingW` is ONE flag for both phases (sync design §8 R1: the
  exclusion attaches to every PARKED writer, gc's only to the `rw.w`
  owner), so at (`writer = false`, `pendingW > 0`) the machine cannot
  tell them apart — the pick is therefore OFFERED there (acquirability =
  `!writer`, symmetric with RWMutex `TryLock`'s "pendingW
  notwithstanding" below): machine ⊇ gc on both phases — an [AGENT]
  widening in the safe direction, RATIFIED [USER] 2026-09-03 («TryRLock decision sounds fine», relayed by the [AGENT] coordinator); the blocking `rlock` keeps R1's exclusion (it parks
  on `pendingW > 0`), which control D shows gc's blocking RLock does not
  honor either (`rwRLockQueuedWriter`) — R1's pre-existing half, fresh
  evidence recorded there. RWMutex `TryLock` fails while readers hold
  (`readers > 0`, gc's `readerCount.CompareAndSwap(0, …)` :180) and
  succeeds otherwise — the `wlock` immediate-acquire condition, pendingW
  notwithstanding (gc holds `rw.w` for a pending writer and so fails a
  new `TryLock` in that transient window — a realized point INSIDE this
  envelope: the sync docs say nothing about a pending writer's priority
  over a TryLock, and the window closes at the writer's wake).

THE DETECTOR HALF is the apply's own LABEL (C1 S2c: `syncEntryKinds`
with the `acquired` outcome and the success-only acquire action, emitted
here; the fold moves the clocks it names).
The result is delivered through `enterRecvTargets` when a target exists
(the `onceBegin` shape — a plain write of the target AFTER the op);
with no target the value is dropped and the op still took effect (a
bare `m.TryLock()` statement acquires, gc-exact). Every proceeding
outcome is a registry-op completion (B1/C5); a TRY head never parks.

FAIRNESS / TERMINATION: a `for !m.TryLock() {}` spinner is runnable
forever under the spurious member (and under unfair schedules) —
∀-stream termination is honestly FALSE; such rows ride the membership
lane under `nonterm=` accounting with NO termination claim (row 2's
precedent, `atomics/spin`); the `Fair`-quantified claim class is
reasoning-side future work TO BE BUILT (proposal §2). -/
def applyTryLock (s : Store) (op : SyncOp) (loc : Loc) (pre : SyncPrim)
    (spurious : Bool) (targets : List Assignee) (env : LocalEnv) (k : Cont) :
    Except Stop (Config × Store × AccessTrace) := do
  -- THE LABEL (C1 S2c): `syncEntryKinds` with the TRY outcome — a failed
  -- call (forced or spurious) has «no synchronizing effect at all»
  -- (mem#locks): its realized entry accesses only; a SUCCESSFUL call is
  -- «equivalent to a call to l.Lock (or l.RLock)»: the success-only go_mem
  -- kind and the acquire action (RWMutex's write-`TryLock` acquires both
  -- clocks, the `wlock` shape).
  let alsoB : Bool := match op with
    | .tryWLock _ => true
    | .tryLock _ | .tryRLock _ => false
    | .lock | .unlock | .rlock | .runlock | .wlock | .wunlock
    | .wgAdd | .wgWait | .onceBegin _ | .onceComplete => false
  match ← tryAcquire op pre with
  | none => do
      let (c', s') ← tryDeliver false s targets env k
      return (c', s', syncEntryKinds op pre 0 false loc)
  | some post => do
      -- THE PRE-COMMIT DISCIPLINE (`applySelectCore`'s, for the ∀-streams
      -- kit): the acquired cell is stored BEFORE the pick is applied, so
      -- both members share every failure mode and apply-success is
      -- pick-independent (`applyTryLock_ok_any`); the spurious member
      -- then returns the PRE-store state — no state change, as the text
      -- demands.
      let sAcq ← storeLoc ctx s loc (.syncData post)
      if spurious then do
        let (c', s') ← tryDeliver false s targets env k
        return (c', s', syncEntryKinds op pre 0 false loc)
      else do
        let (c', s') ← tryDeliver true sAcq targets env k
        return (c', s', syncEntryKinds op pre 0 true loc ++ [.hb (.syncAcquire loc.canon alsoB)])

/-- **Apply a sync statement's head to its evaluated operands, with the
choice stream** — the sync registry entry (the `applyStmtOp` mold over
`applySyncOpCore`): the TRY heads resolve the receiver, read the cell,
draw the `tryLock` site at `tryLockWidth` (bound 1 = no pop), and apply
`applyTryLock`; every other head is `applySyncOpCore` with the stream
passed through untouched (`applySyncOp_eq_core`). Shared verbatim by
rule `Step.syncStApply` and `stepFn`'s `syncStK` apply arm. -/
def applySyncOp (s : Store) (ch : Choices) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) :
    Except Stop (Config × Store × Choices × List PickRecord × AccessTrace) := do
  match op.tryTargets?, vs with
  | some targets, [av] => do
      let loc ← valueAsLoc av
      let pre ← syncCell ctx s loc
      let (pick, ch', ps) := Choices.consumeAtE .tryLock (tryLockWidth op pre) ch
      let (c', s', tr) ← applyTryLock ctx s op loc pre (pick == 1) targets env k
      return (c', s', ch', ps, tr)
  | some _, vs => stuck s!"malformed try-lock application: {repr op} on {vs.length} operand(s)"
  | none, _ => do
      let (c', s', tr) ← applySyncOpCore ctx s op vs env k
      return (c', s', ch, [], tr)

/-- The optional store of an atomic op (`atomicCompute`'s `new?`): the
normalized integer at the op's kind, or no store at all (`load`, a
failed `cas`). -/
def atomicStore (s : Store) (loc : Loc) (kind : IntKind) :
    Option Int → Except Stop Store
  | some nv => storeLoc ctx s loc (.int nv kind)
  | none => pure s

/-- **Apply an atomic statement's head to its evaluated operands — the
atomic registry entry's op semantics AND its envelope statement**
(atomics arc wave 1; design note `docs/2026-09-03_atomics-w1-design.md`).

THE FORCED POINT (not latitude): mem#atomic — "The APIs in the
sync/atomic package are collectively 'atomic operations' that can be
used to synchronize the execution of different goroutines. If the
effect of an atomic operation A is observed by atomic operation B, then
A is synchronized before B. All the atomic operations executed in a
program behave as though executed in some sequentially consistent
order." and "The preceding definition has the same semantics as C++'s
sequentially consistent atomics and Java's volatile variables." A
conforming implementation may NOT weaken these (inventory U-6), so the
machine owes EXACTLY SC — one of the rare direct upper bounds from the
text.

THE ENVELOPE STATEMENT (nondeterminism doctrine requirement 1): the op
is ONE indivisible pool step — read, modify, write, and the result
delivery entry all in this apply, at a registry boundary — so an
execution IS an interleaving of atomic steps, and that interleaving IS
"some sequentially consistent order": ⊇ SC because any SC order of the
ops is realized by the L1 schedule that runs their steps in that order
(C1's width, `l1Sched`/`postOp`); ⊆ SC because no non-SC mixing is
expressible when every op is a single step. WHICH SC order occurs is
C1's existing scheduling latitude — this apply consumes NOTHING from
the choice stream, ever: the atomics add ZERO new consumption sites
(the census `ChoiceSite` is unchanged), and single-goroutine atomic
programs are stream-transparent (sequential conservation untouched).
The executable check that the realization is neither wide nor narrow
is the message-passing litmus `sync/atomic-frontier/mp-litmus`
(membership {0, 1, 11}; the SC-excluded 10 mechanically absent).

Outcomes: the cell's current value must be an integer AT THE OP'S KIND
(the frontend types the address `*intN`; a `.defined`-over-intN cell
carries the underlying kind — anything else is `stuck`, fail closed);
`atomicCompute` gives the store (if any) and the result; a result
target receives it through `enterRecvTargets` (the `onceBegin` delivery
shape: the phase-2 store is an ordinary plain write of the target, AFTER
the op); every proceeding outcome is a registry-op completion (B1/C5).
A nil address is gc's recoverable "invalid memory address or nil
pointer dereference" (`valueAsLoc`; probed: the intrinsic faults at
the address before any effect — no store, no HB edge, nothing recorded
by `-race`, whose `racecallatomic` touches the address first). No
alignment panic: the pinned oracle is linux/amd64, where 64-bit atomics
need no alignment; the 32-bit `unaligned 64-bit atomic operation` fatal
is outside this pin (R1's transfer caveat applies). Shared verbatim by
rule `Step.atomicStApply` and `stepFn`'s `atomicStK` apply arm. -/
def applyAtomicOp (s : Store) (op : AtomicOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except Stop (Config × Store × AccessTrace) := do
  match vs with
  | av :: operands => do
      let loc ← valueAsLoc av
      match ← loadLoc ctx s loc with
      | .int cur ck =>
          if ck != op.kind then
            stuck s!"atomic {repr op.head} at a {ck.name} cell (the op is typed {op.kind.name})"
          else do
            let (new?, result) ← atomicCompute op.head op.kind cur operands
            let s' ← atomicStore ctx s loc op.kind new?
            -- THE LABEL (C1 S2c): the op's ATOMIC-kind access at the cell and
            -- its clock action, in TSan's order (`atomicEvents`; a CAS's
            -- success is `new?`'s presence — the very outcome just applied).
            let tr := atomicEvents op.head loc new?.isSome
            match op.targets with
            | [] => return (.next k, s', tr)
            | _ :: _ => do
                let (c', s'') ← enterRecvTargets s' op.targets [result] (.seqn #[]) env k
                return (c', s'', tr)
      | other => stuck s!"atomic {repr op.head} on a non-integer cell: {repr other}"
  | [] => stuck "malformed atomic-operator application: no address operand"

/-- Commit the ONE ready clause of a `select` (spec step 3): perform its
communication, then enter the body — for a receive with targets, via
the phase-1/phase-2 delivery frames (`enterRecvTargets`; spec step 4:
LHS after the communication). A committed SEND on a closed channel
panics (probe p23 — closed counts as ready). The "unready" stuck arms
are unreachable from `applySelect` (which commits only ready clauses) —
fail closed, never a silent default.

B1 (W3.2 slice 1 stage C) / C5: a PROCEEDING commit is a registry-op
completion — the pool flags the goroutine `postOp` (`Thread.afterStep`,
the envelope statement of `ChoiceSite.postOp`) on all three commit paths
at once (the entry-path `applySelect`, the arrival-path `.commit` in
`stepThread`, and the wake path `resumeThread`); a panicking commit
opens no boundary (B3 deferred). -/
def commitClause (s : Store) (env : LocalEnv) (k : Cont) :
    EvClause → Except Stop (Config × Store × AccessTrace)
  | .sendEv chv vv elem body => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => stuck "select committed an unready send clause"
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [panicEntry "send on closed channel"] k, s, [])
          else if buf.size < capacity then do
            let v' ← normalizeValueForTy ctx elem vv
            let s' ← storeChanPayload s loc (buf.push v') capacity closed
            -- THE LABEL (C1 S2c): the committed buffered send transits the
            -- next send slot; the select's poll reads are its CALLER's
            -- (`applySelectCore`/`arrivalPoll`), never the commit's — a woken
            -- select (`resumeThread`) commits through here and re-polls nothing.
            return (.exec body env k, s', [.hb (.slotOp loc.canon capacity true)])
          else stuck "select committed an unready send clause"
  | .recvEv chv targets elem body => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => stuck "select committed an unready receive clause"
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          let (v, ok, s₁, tr) ←
            match buf[0]? with
            | some v => do
                let s₁ ← storeChanPayload s loc (buf.eraseIdx! 0) capacity closed
                pure (v, true, s₁, ([.hb (.slotOp loc.canon capacity false)] : AccessTrace))
            | none =>
                if closed then do
                  let zero ← defaultValue ctx elem
                  pure (zero, false, s, ([.hb (.closeAcquire loc.canon)] : AccessTrace))
                else stuck "select committed an unready receive clause"
          match targets with
          | [] => return (.exec body env k, s₁, tr)
          | _ :: _ => do
              let (c', s₂) ← enterRecvTargets s₁ targets
                (recvStores v ok targets.length) body env k
              return (c', s₂, tr)

/-- **The `select` READINESS step and THE L2 ENVELOPE** (spec steps
2-3; this docstring is the envelope statement, shipped with its site —
it documents the `SelectOutcome`/`applySelectCore`/`applySelect`
trio): pair the evaluated
entry operands with their clauses, compute the ready set; none ready →
`default` (consuming NOTHING) or block; exactly one ready → commit it
(consuming nothing — the singleton-ready commit is the `.done` shape,
which never consults the `l2Entry` site; the sequential/deterministic
behavior depends on that structural non-consumption). MULTIPLE ready
clauses are THE L2 SITE (`ChoiceSite.l2Entry` — the census row; design
D4, live since slice 4):

The spec's step 2 (misnumbered "step 3" here until 2026-08-22; the
pinned spec's list has the uniform-pseudo-random clause at step 2 —
launch audit D2-F3, matching inventory C6's P2 correction) — "If one
or more of the communications can proceed, a single one that can
proceed is chosen via a uniform
pseudo-random selection" — is deliberately WEAKENED to the
possibilistic "ANY entry-ready case may commit" (the nondeterminism
doctrine: no distributional claims; the membership lane is the oracle,
and gc's own runtime shuffle exercises the members). The pick is drawn
from the choice stream, bounded by the READY-CLAUSE COUNT and
consumed ONLY at width > 1. Width metadata for the enumerator /
membership lane: the site's bound is the number of ready clauses at
this apply, ≤ the clause count.

NO RE-RANDOMIZATION ON THE BLOCKED PATH (probe-pinned; D4): a select
that parks consumes NOTHING here, and its WAKE does not re-draw — a
woken select commits the FIRST wake-ready clause in clause order
(`resumeThread`), deterministically. gc's woken select commits the
case its waking event belongs to (never a fresh shuffle); every such
first-event commit is realized in this machine by the prompt-wake
schedule (the enabling op is a registry boundary, so the woken select
is schedulable immediately), and a later wake's head-commit is a
spec-legal member — at the commit moment every wake-ready clause "can
proceed". Wake-ORDER latitude is L1/L4's, not a second L2 draw.

Shared by rule `Step.selectApply` (which quantifies the stream — the
`stmtOpApply` idiom) and `stepFn`; the readiness/commit computation is
the stream-free `applySelectCore` below (`applySelect` adds only the
L2 consumption). -/
inductive SelectOutcome where
  /-- No pick consumed: default taken, park (`committed? = none`), or
  a singleton-ready commit (`committed? = some` the clause — Q2: the
  commit identity is EMITTED by the apply, so the step event and the
  detector never re-derive it from the readiness analysis). `tr` is the
  apply's LABEL (C1 S2c): the poll reads, then the commit's actions. -/
  | done (c : Config) (σ : Store) (committed? : Option EvClause) (tr : AccessTrace)
  /-- Multi-ready (≥ 2): the PRE-COMMITTED result of every ready
  clause, clause order, for the L2 pick — each paired with ITS clause
  (Q2's emitted commit identity) — `.inl` a committed configuration
  with its commit's label, `.inr` a panic message; `poll` is the
  select's entry emission, common to every pick. -/
  | picks (poll : AccessTrace) (commits : List (EvClause × Sum (Config × Store × AccessTrace) String))

/-- The stream-FREE core of `applySelect` (the `applyStmtOpCore`
precedent: choices-obliviousness of apply-SUCCESS is true by
construction — the ∀-choices kit's discipline, the mapIterNext
precedent). The multi-ready arm commits EVERY ready clause against the
same pre-state: a clause whose commit FAIL-CLOSES
(stuck/unsupported/internal — diagnostics, never Go behaviors) fails
the apply on every stream, not just when picked. Channel PANICS are Go
behaviors and stay per-pick — and on TODAY'S machine they ride `.inl`
as committed `.panicking` CONFIGURATIONS (`commitClause` never throws
`.error (.panic …)`: the send-on-closed panic is
`return (.panicking …, s)`, S4 audit correction — the earlier text
claimed `.inr` carried them). The `.inr` arm is a DEFENSIVE mirror for
any future `commitClause` panic-THROWING path: `applySelect` turns a
picked `.inr` into the same `.panicking` configuration WITH the L2
pick consumed (never a re-thrown `.error`, whose `stepFn` handler
would return the pre-consumption stream and desynchronize every later
site — the latent drop the audit found); an unpicked clause's panic is
discarded with its commit either way. -/
def applySelectCore (s : Store)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    Except Stop SelectOutcome := do
  let evs ← evalClauses clauses vs
  -- THE LABEL's head (C1 S2c): `selectgo` pass 1's channel-object read per
  -- polled send clause (BUG-046), before any commit — on EVERY outcome.
  let poll := selectPoll evs
  match ← readyClauses s evs with
  | [] =>
      -- NO ready clause: neither arm is a registry-op COMPLETION, so
      -- neither is wrapped in `.opDone` — B1 scopes post-op boundaries
      -- to select COMMITS (`docs/2026-08-20_w32-boundary-set.md` §B1,
      -- "select commits (entry path `applySelect`, arrival path
      -- `commitClause`)"), and a default-take commits nothing.
      -- ENVELOPE-NEUTRAL, on the passive-partner argument's pattern
      -- (§B1's fourth bullet: wrapping adds a no-op step and no
      -- latitude): taking the default changes no channel or sync
      -- state and wakes nobody, so no other goroutine's futures depend
      -- on a boundary placed AFTER it — the goroutine continues into
      -- `d`, whose own next registry op emits its own `.opDone`. The
      -- latitude that decides WHETHER this select sees a ready clause
      -- is consumed before this step, at the other goroutines'
      -- boundaries; a point here would only re-offer the same
      -- successor set. The park arm needs none either — a park IS a
      -- boundary shape already (§B1's "NOT wrapped" note).
      match default? with
      | some d => return .done (.exec d env k) s none poll
      | none => return .done (.blockedSelect evs env k) s none poll
  | [c] => do
      let (c', s', tr) ← commitClause ctx s env k c
      return .done c' s' (some c) (poll ++ tr)
  | ready => do
      let commits ← ready.mapM fun cl =>
        (match commitClause ctx s env k cl with
        | .ok r => .ok (cl, .inl r)
        | .error (.panic msg) => .ok (cl, .inr msg)
        | .error e => .error e :
          Except Stop (EvClause × Sum (Config × Store × AccessTrace) String))
      return .picks poll commits

@[inherit_doc applySelectCore]
def applySelect (s : Store) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (vs : List GoValue) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    Except Stop (Config × Store × Choices × List PickRecord × Option EvClause × AccessTrace) := do
  -- The 4th component is the L2 consultation's record (`consumeAtE`;
  -- step-label reshape 2026-09-28), the 5th Q2's emitted commit identity
  -- (`none` = default taken or parked): the sequential `stepFn` arm
  -- PROJECTS the identity away; the pool's select interception
  -- (`stepThread`) carries it into the step event. The 6th is the
  -- apply's memory trace (C1 S2c): the poll reads and the picked
  -- commit's actions.
  match ← applySelectCore ctx s clauses default? vs env k with
  | .done c' s' cl? tr => return (c', s', ch, [], cl?, tr)
  | .picks poll commits =>
      -- THE L2 CONSUMPTION (envelope statement in the docstring
      -- above): bound = the ready-clause count, ≥ 2 by construction
      -- (`.picks` arises only from a multi-ready analysis).
      let (idx, ch', ps) := Choices.consumeAtE .l2Entry commits.length ch
      match commits[idx]? with
      | some (cl, .inl (c', s', tr)) => return (c', s', ch', ps, some cl, poll ++ tr)
      | some (cl, .inr msg) =>
          -- Defensive arm (unreachable today — docstring above): the
          -- picked clause's panic becomes a `.panicking` configuration
          -- with the pick CONSUMED, exactly like the `.inl` route; the
          -- label is the poll alone (a panicking commit performs no action).
          return (.panicking [panicEntry msg] k, s, ch', ps, some cl, poll)
      | none => throw (.internal "select ready-clause pick out of range")

/-! ## The consumption projection (design-hygiene wave (iii), B8, 2026-09-04)

WHERE the sequential machine consults the choice stream, and at what
bound — computed by the machine's OWN functions, once, instead of the
three hand-written mirrors that used to live in `CLI.stepNeeds`/
`stepNeedsSeq` and `ChoiceTrace.seqSite`/`poolSite` (review U10). The
theorem `stepFn_consumption` (MachineSound) is the guarantee: `none` ⇒
the step is stream-oblivious; `some (site, b)` ⇒ the step's stream is
`(Choices.consumeAt site b ch).2` and the step depends on the stream only
through that pick. The pool layer's projection is `poolConsumption`
(Multi.lean). -/

/-- The spill decision of an `appendSlice` apply, from the operands and
the state alone — EVERY test `applyStmtOp`'s append arm performs before
it consults the stream, in the arm's order (operand shapes, slice
validation, the visible element read, the target address, the capacity
test, the R16 `growslice` refusal — a recoverable panic raised BEFORE the
consult — and the old-element read); `some (appendSpillWidth …)` exactly
when the arm reaches the consult, `none` whenever it refuses, panics or
stores in place before it (audit fix F1: `some` ⇔ the consult happens). -/
def appendSpill? (s : Store) (elem : Ty) (vs : List GoValue) : Option Nat :=
  match vs with
  | [tv, sliceV, elemsV] =>
      match valueAsSlice sliceV, valueAsSlice elemsV with
      | .ok slice, .ok elems =>
          match validateSlice slice, validateSlice elems, Mem.loadSlice ctx s elems, valueAsLoc tv with
          | .ok _, .ok _, .ok (elemValues, _), .ok _ =>
              let newLen := slice.len + elemValues.size
              if newLen ≤ slice.cap then none
              else
                match tySizeBytes ctx.types elem with
                | .ok elemSize =>
                    if newLen ≥ intExclusiveUpperBound || newLen * elemSize > maxAllocBytes then none
                    else
                      match Mem.loadSlice ctx s slice with
                      | .ok _ => some (appendSpillWidth slice.cap newLen)
                      | .error _ => none
                | .error _ => none
          | _, _, _, _ => none
      | _, _ => none
  | _ => none

/-- The TRY heads' consult width at a sync apply (`applySyncOp`): the
receiver cell's `tryLockWidth`, `none` unless it pops (width 2). -/
def tryLockConsult? (s : Store) (op : SyncOp) (vs : List GoValue) : Option Nat :=
  match op.tryTargets?, vs with
  | some _, [av] =>
      match valueAsLoc av with
      | .ok loc =>
          match syncCell ctx s loc with
          | .ok pre => if tryLockWidth op pre ≤ 1 then none else some (tryLockWidth op pre)
          | .error _ => none
      | .error _ => none
  | _, _ => none

/-- The range frame's consult: `mapIter` at width candidates + stop
(`stepFn`'s own `mapIterCandidates` / `mapIterMandatoryRemains`) when
that width is ≥ 2; nothing at an empty candidate set, and nothing at
width 1 — the last MANDATORY candidate, a forced pick that pops nothing
under the uniform rule (G-U; before it this site popped at width 1). -/
def mapIterConsult? (σ : Store) (keyTy valTy : Ty) (base : Option Loc)
    (produced start : Array Nat) : Option (ChoiceSite × Nat) :=
  match mapIterCandidates ctx σ keyTy valTy base produced with
  | .ok (cands, _) =>
      if cands.isEmpty then none
      else
        let w := cands.size + (if mapIterMandatoryRemains cands start then 0 else 1)
        if w ≤ 1 then none else some (.mapIter, w)
  | .error _ => none

/-- The wide-statement apply's consult: only a SPILLING `appendSlice`
draws (`appendSpill?`). -/
def stmtConsult? (σ : Store) (op : StmtOp) (vs : List GoValue) : Option (ChoiceSite × Nat) :=
  match op with
  | .appendSlice elem => (appendSpill? ctx σ elem vs).map (.appendSpill, ·)
  | _ => none

/-- The select apply's consult: the L2 pick at a multi-ready analysis
(`applySelectCore`'s `.picks`), nothing at `.done` or a refusal. -/
def selectConsult? (σ : Store) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    Option (ChoiceSite × Nat) :=
  match applySelectCore ctx σ clauses default? vs env k with
  | .ok (.picks _ commits) => some (.l2Entry, commits.length)
  | _ => none

/-- The sync apply's consult: a TRY head at an acquirable cell (`tryLockConsult?`). -/
def syncConsult? (σ : Store) (op : SyncOp) (vs : List GoValue) : Option (ChoiceSite × Nat) :=
  (tryLockConsult? ctx σ op vs).map (.tryLock, ·)

/-- The frame entry's consult: `nilValueMethodText` at width 2 (the wrapper
family) when `enterFrame` PANICS — the pick is drawn on the panic path only
(`enterFramePick`); nothing at width 1 or at a successful entry. -/
def entryConsult? (σ : Store) (fid : FuncId) (args : List GoValue) : Option (ChoiceSite × Nat) :=
  if nilValueMethodWidth ctx fid args ≤ 1 then none
  else match enterFrame ctx σ fid args with
    | .error (.panic _) => some (.nilValueMethodText, nilValueMethodWidth ctx fid args)
    | _ => none

/-- Does this configuration's next step draw the `unseqPanic` pick (E13
option (b), `e13-b`)? `true` exactly at a panic that has reached an
unsequenced-operand probe frame — `.panicking _ (.probeK _)`, bound 2,
always a pop. The obliviousness checkers exclude exactly this
(`stepFn_oblivious`' `hnu`, `poolThreadOblivious`) — a fail-closed flag
like `consumesAppendSlice`; the certified dedup engine ENUMERATES it
instead since Stage D (`innerVecs` N-PICK: the vectors `[0]`, `[1]`, the
same `stepFn`-path shape as `unseqNext` — `stepThread_pick_run`). Retires
with the legacy lowering at Stage E. -/
def consumesUnseqPanic : Config → Bool
  | .panicking _ (.probeK _) => true
  | _ => false

/-- Does this configuration's next step draw the `unseqNext` pick (the
`unseq` scheduler's step, Stage B)? `true` at EVERY pick position
`.next (.unseqK … .pick _)` — conservative, like `consumesSelect`: the
sequential obliviousness checker (`stepFn_oblivious`' `hnn`) refuses the
shape whether or not the ready set is wide. The POOL checkers read the
bound off the frame (`unseqNextBound`, below — route α of v2.1 §3.6,
Stage D): `poolThreadOblivious` is `true` exactly at a bound-≤-1 pick (a
consult that pops nothing, G-U) and the certified dedup engine's
`innerVecs` enumerates a wide pick's `|ready|` branches
(`stepThread_pick_run`). `seqConsumption` reports the EXACT bound. -/
def consumesUnseqNext : Config → Bool
  | .next (.unseqK _ _ _ _ _ .pick _) => true
  | _ => false

/-- **The `unseqNext` pick's BOUND, read off the configuration alone**
(route α, Stage D): `|ready|` at a pick position, `0` elsewhere. The ONE
`ready` computation (Unseq.lean, review R5) — `seqConsumption`'s arm below
reports exactly this when it is ≥ 2 (`seqConsumption_unseqNext`,
MachineSound), and the dedup checker's branch vectors enumerate exactly
`[0, unseqNextBound c)` (`innerVecs`, EnumDedupCheck). It reads NO store
and NO other goroutine: the scheduler's pick depends on the stepping
thread's own frame only, which is what makes the branch-vector
construction configuration-determined (the pool coverage lemma
`stepThread_total_covered` needs nothing about the rest of the pool). -/
def unseqNextBound : Config → Nat
  | .next (.unseqK g _ st _ _ .pick _) => (g.ready st).length
  | _ => 0

/-- Does this configuration's abort draw the `repanicCollapse` pick
(BUG-004 item 1, landing chunk L3)? `true` exactly at an abort
(`Config.abort?`) whose head is recovered with an equal successor payload
— `repanicCollapseWidth = 2`; every other abort consults at bound 1 and
pops nothing. The stream-obliviousness checkers exclude exactly this
(`stepFn_oblivious`' `hnr`, `poolThreadOblivious`, `innerVecs`) — a
fail-closed flag like `consumesUnseqPanic`. -/
def consumesRepanicCollapse (c : Config) : Bool :=
  match c.abort? with
  | some (first, rest) => repanicEqualNext first rest
  | none => false

/-- **The sequential consumption projection**: the site and bound the next
`stepFn` step draws — `some` exactly when the consult POPS (a bound-≤-1
consult is `none` at every site — the uniform rule, G-U). Eight sites, one
consult function each: `mapIter` at a live range frame, `appendSpill` at
a spilling append, `l2Entry` at a multi-ready select, `tryLock` at an
acquirable TRY head, `nilValueMethodText` at a panicking frame entry in
the wrapper family, `unseqPanic` at a panic that reached an
unsequenced-operand probe frame (bound 2, constant), `repanicCollapse` at
an ABORT whose head is recovered with an equal successor payload (bound 2
there, `repanicCollapseWidth`; the abort's step is the `panic` terminal,
so this is the one projection arm whose step never returns `.ok`), and
`unseqNext` at an `unseq` sweep frame's pick position with ≥ 2 ready
occurrences (Stage B; bound = the ready count exactly). -/
def seqConsumption (σ : Store) (c : Config) : Option (ChoiceSite × Nat) :=
  match c with
  | .next (.mapIterK _ _ keyTy valTy _ base produced start _ _) =>
      mapIterConsult? ctx σ keyTy valTy base produced start
  | .panicking _ (.probeK _) => some (.unseqPanic, 2)
  -- The `unseq` scheduler's pick (Stage B): EXACTLY the number of ready
  -- occurrences when it is ≥ 2 (the one `ready` computation, Unseq.lean);
  -- a singleton ready set is a bound-1 consult that pops nothing.
  | .next (.unseqK g _ st _ _ .pick _) =>
      if 2 ≤ (g.ready st).length then some (.unseqNext, (g.ready st).length) else none
  | .panicking (first :: rest) .stop =>
      if repanicEqualNext first rest then some (.repanicCollapse, 2) else none
  | c =>
    match c.applyPos with
    | some (.stmt op _, vs, _, _) => stmtConsult? ctx σ op vs
    | some (.select clauses default?, vs, env, k) => selectConsult? ctx σ clauses default? vs env k
    | some (.sync op, vs, _, _) => syncConsult? ctx σ op vs
    | some (.strict _, _, _, _) | some (.chan _, _, _, _) | some (.atomic _, _, _, _)
    | some (.rhs _ _ _, _, _, _) => none
    | none =>
      match entryCallSite? c with
      | some (fid, args) => entryConsult? ctx σ fid args
      | none => none

variable {ctx}
/-- What a `none` entry consult says: outside the wrapper family, or an
entry that does not panic. -/
theorem entryConsult?_none {σ : Store} {fid : FuncId} {args : List GoValue}
    (h : entryConsult? ctx σ fid args = none) :
    (nilValueMethodText? ctx fid args).isSome = false
      ∨ ∀ msg, enterFrame ctx σ fid args ≠ .error (.panic msg) := by
  unfold entryConsult? at h
  split at h
  · left
    rename_i hle
    unfold nilValueMethodWidth at hle
    split at hle
    · omega
    · exact Bool.eq_false_iff.mpr ‹_›
  · right
    intro msg hp
    rw [hp] at h
    simp at h

/-- What a `some` entry consult says: the family's width 2 and a panicking entry. -/
theorem entryConsult?_some {σ : Store} {fid : FuncId} {args : List GoValue}
    {site : ChoiceSite} {b : Nat} (h : entryConsult? ctx σ fid args = some (site, b)) :
    site = .nilValueMethodText ∧ b = nilValueMethodWidth ctx fid args
      ∧ 1 < nilValueMethodWidth ctx fid args
      ∧ ∃ msg, enterFrame ctx σ fid args = .error (.panic msg) := by
  unfold entryConsult? at h
  split at h
  · cases h
  · rename_i hgt
    split at h
    · rename_i msg hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, Nat.lt_of_not_le hgt, msg, hp⟩
    · cases h

/-! ## The read's narrowing by its continuation (moved from `Race.lean`, C1 S2a) -/

variable (ctx)
/-- Narrow a whole-cell read through the chain of PROJECTIONS its
continuation will immediately apply: when the value a read produces is
delivered straight into single-operand `fieldGet` frames, only the
projected FIELD PATH is semantically read (Go compiles `p.a` to a
single field load; the rest of the struct is discarded unobserved).
This is what keeps disjoint-field READ/WRITE pairs race-free at the
detector (S3 audit: the free lane's read/write direction) for both the
local (`evalVar` under a `fieldGet` frame) and pointer (`deref` under a
`fieldGet` frame) forms. Since C1 S2a the CALLER of the module's
`Mem.loadFor` (for a variable, its root-only twin `Mem.loadBindingFor`) names this leaf — `Step.evalVar`/`stepFn`'s `.var` arm and
the strict apply's `leafOf` for `.deref` — a semantic statement about
what Go reads here, never an emission of its own.

**Q-RACEPATH — CONSTANT-index narrowing (RULED [USER] 2026-08-31,
`docs/2026-08-31_qrow-rulings.md` row 4; implemented 2026-09-02, the
Tier-4 detector-soundness lane).** The chain also passes through an
`indexGet` frame whose pending index operand is a CONSTANT literal
(`Expr.intLit` — go/types constant-folds every constant index
expression to one, and a constant index is compile-time bounds-checked,
so the element path is fully determined before the projection applies)
PROVIDED the cell the read produces is an ARRAY: element paths live
under the array's own `Loc`, exactly where element STORES land
(`storeTarget` resolves `a[1] = v` to `.index base 1`), so a
constant-index read and a disjoint-element write are disjoint paths.
gc compiles `a[1]` to a single element load, and mem#restrictions
licenses the per-sub-value decomposition of composite reads verbatim
(quoted at inventory C10) — the narrowed footprint is the faithful
one. A SLICE or STRING variable's cell is a HEADER whose elements live
elsewhere: its read stays whole-cell (the element read is the
`indexGet` apply's own `Mem.load`), which is why the narrowing is
gated on the loaded cell being `.array` — never on the frame shape
alone (the root check is a PEEK). The chain composes in either order
(`a[1].x` and `s.arr[1]`). DYNAMIC indices (any non-literal index
expression — a variable, a call, an arithmetic form go/types could not
fold) are NOT narrowed and remain the recorded whole-cell
over-approximation: O1's RESIDUAL, red-pinned by
`race/free/array-dyn-index-read-write` (BUG-041), with its re-open
trigger recorded in O1. -/
def projChainTarget (s : Store) : Cont → Loc → Loc
  | .strictK (.fieldGet tid f) [] [] _ k', loc =>
      projChainTarget s k' (.field loc tid f)
  | .strictK .indexGet [] [.intLit i _] _ k', loc =>
      match loadLoc ctx s loc with
      | .ok (.array _) => projChainTarget s k' (.index loc i)
      | _ => loc
  | _, loc => loc

/-! ## The step relation -/

/-- One machine step over `(control, state)` pairs, LABELLED by its full
event label (C1 S2a, D5; widened by the step-label reshape, 2026-09-28,
`docs/2026-09-28_step-label.md`): the fifth index is the step's
`StepLabel` — the memory-model `trace`, the kept tape consultations
`picks` (bound > 1, as `Choices.consumeAtE` returns them; the rules that
choose an index state them with `PickRecord.ofPick`), and the `print`
bytes `out`. Pure control steps carry `⟨[], [], []⟩`, every
helper-bearing rule carries what its operations emitted, a delivered
panic no trace and no output. No rule applies to
malformed or unmodeled configurations: they are stuck (fail closed). A
panic step starts UNWINDING (`.panicking` carries the chain and the
continuation): defers run on the panic path, `recover` in a panic-run
deferred call cancels the unwind, and an unrecovered chain reaching
`.stop` is the abort — a configuration with NO rule (B4: `Config.abort?`;
the drivers raise the `panic` terminal there). Nondeterministic steps (map
iteration order, append capacity) arrive at S2 with their statements. -/
inductive Step : Config → Store → Config → Store → StepLabel → Prop where
  -- Every APPLY/ENTRY rule below is "apply, then deliver" (B2): the
  -- helper's outcome is classified once (`toResult` — a value or a
  -- recoverable panic; refusals and the unrecoverable terminals have no
  -- successor and stay relation-silent) and `deliver` turns it into the
  -- successor configuration: the value's continuation, or the unwinding
  -- `.panicking [panicEntry msg] k` over the pre-apply state.
  -- Expression entry
  | evalVar {id loc v tr env k s} :
      LocalEnv.lookup env id = some loc →
      -- The variable read, recorded at the leaf its continuation projects
      -- (`projChainTarget`): the caller names the leaf, the module emits.
      Mem.loadBindingFor ctx s loc (projChainTarget ctx s k loc) = .ok (v, tr) →
      Step (.evalE (.var id) env k) s (.retV v k) s ⟨tr, [], []⟩
  | evalIntLit {value kind env k s} :
      Step (.evalE (.intLit value kind) env k) s
        (.retV (.int (kind.normalize value) kind) k) s ⟨[], [], []⟩
  | evalBoolLit {value env k s} :
      Step (.evalE (.boolLit value) env k) s (.retV (.bool value) k) s ⟨[], [], []⟩
  | evalStringLit {value env k s} :
      Step (.evalE (.stringLit value) env k) s (.retV (.string value) k) s ⟨[], [], []⟩
  | evalRef {id loc env k s} :
      LocalEnv.lookup env id = some loc →
      Step (.evalE (.ref id) env k) s (.retV (.addr loc) k) s ⟨[], [], []⟩
  /-- A global's address is its index, provided the cell exists (A4). -/
  | evalGlobal {gid env k s} :
      gid < s.heap.size →
      Step (.evalE (.global gid) env k) s (.retV (.addr (.base ⟨gid⟩)) k) s ⟨[], [], []⟩
  /-- Enter a strict form with at least one operand: evaluate the first
  under the generic frame. -/
  | evalStrict {e op e₁ rest env k s} :
      strictPlan e = some (op, e₁ :: rest) →
      Step (.evalE e env k) s (.evalE e₁ env (.strictK op [] rest env k)) s ⟨[], [], []⟩
  /-- A nullary strict form applies immediately: apply, then deliver (a
  value is returned to `k`; a recoverable panic unwinds under `k`). -/
  | evalStrictNullary {e op r env k s c' s' l} :
      strictPlan e = some (op, []) →
      toResult (applyStrictOp ctx s (projChainTarget ctx s k) op []) = .ok r →
      deliver s k (fun (v, s', tr) => (.retV v k, s', ⟨tr, [], []⟩)) r = (c', s', l) →
      Step (.evalE e env k) s c' s' l
  /-- `recover()`: the walk-and-mark is one deterministic function of the
  continuation (arc doc §A1); never stuck. -/
  | evalRecover {env k v k' s} :
      recoverResult k = (v, k') →
      Step (.evalE .recoverCall env k) s (.retV v k') s ⟨[], [], []⟩
  | evalAnd {l r env k s} :
      Step (.evalE (.and l r) env k) s (.evalE l env (.andK r env k)) s ⟨[], [], []⟩
  | evalOr {l r env k s} :
      Step (.evalE (.or l r) env k) s (.evalE l env (.orK r env k)) s ⟨[], [], []⟩
  -- Strict-operator frame
  | strictShift {op done e rest v env k s} :
      Step (.retV v (.strictK op done (e :: rest) env k)) s
        (.evalE e env (.strictK op (v :: done) rest env k)) s ⟨[], [], []⟩
  | strictApply {op done v r env k s c' s' l} :
      toResult (applyStrictOp ctx s (projChainTarget ctx s k) op (v :: done).reverse) = .ok r →
      deliver s k (fun (out, s', tr) => (.retV out k, s', ⟨tr, [], []⟩)) r = (c', s', l) →
      Step (.retV v (.strictK op done [] env k)) s c' s' l
  -- Short-circuit frames
  | andTrue {r env k s} :
      Step (.retV (.bool true) (.andK r env k)) s (.evalE r env (.boolK k)) s ⟨[], [], []⟩
  | andFalse {r env k s} :
      Step (.retV (.bool false) (.andK r env k)) s (.retV (.bool false) k) s ⟨[], [], []⟩
  | orTrue {r env k s} :
      Step (.retV (.bool true) (.orK r env k)) s (.retV (.bool true) k) s ⟨[], [], []⟩
  | orFalse {r env k s} :
      Step (.retV (.bool false) (.orK r env k)) s (.evalE r env (.boolK k)) s ⟨[], [], []⟩
  | boolCoerce {b k s} :
      Step (.retV (.bool b) (.boolK k)) s (.retV (.bool b) k) s ⟨[], [], []⟩
  -- Sequencing (unchanged from the old relation)
  | seqn {ss env k s} :
      Step (.exec (.seqn ss) env k) s (.next (seqCont ss.toList env k)) s ⟨[], [], []⟩
  | seqNext {t rest env k s} :
      Step (.next (.seq (t :: rest) env k)) s (.exec t env (.seq rest env k)) s ⟨[], [], []⟩
  | seqDone {env k s} :
      Step (.next (.seq [] env k)) s (.next k) s ⟨[], [], []⟩
  /-- **The signal rules** (B4): a control-transfer statement RAISES its
  signal (`Stmt.signal?`), and a signal in flight steps by the
  frame×signal table (`signalStep`) — pass, catch, or no rule. The one
  state-touching catch, `ret` at a call frame, is the frame-exit rule
  family below (`frameReturn*`, the `.next` exit rules' twins). -/
  | signalStmt {stmt sg env k s} :
      stmt.signal? = some sg →
      Step (.exec stmt env k) s (.signal sg k) s ⟨[], [], []⟩
  | signal {sg k c' s} :
      signalStep sg k = some c' →
      Step (.signal sg k) s c' s ⟨[], [], []⟩
  -- Blocks and declarations
  | block {decls ss env env' k s s'} :
      allocDecls ctx env.pushScope s decls.toList = .ok (env', s') →
      Step (.exec (.block decls ss) env k) s (.next (.seq ss.toList env' k)) s' ⟨[], [], []⟩
  | initialization {p v loc rest env k s s'} :
      defaultValue ctx p.typ = .ok v →
      Store.alloc ctx s v p.typ = .ok (loc, s') →
      Step (.exec (.initialization p) env (.seq rest env k)) s
        (.next (.seq rest (env.declare p.id loc) k)) s' ⟨[], [], []⟩
  -- Assignment (round 4, BUG-037): the SINGLE assignment rides the
  -- phase-split spine as a one-target multi-assign — the RHS is
  -- phase 1, the target chain's checks fire at the store (phase 2).
  -- Rules appended at the END of the inductive with their spine
  -- siblings.
  -- Conditionals
  | ifStmt {c t e env k s} :
      Step (.exec (.ifThenElse c t e) env k) s (.evalE c env (.ifK t e env k)) s ⟨[], [], []⟩
  | ifTrue {t e env k s} :
      Step (.retV (.bool true) (.ifK t e env k)) s (.exec t env k) s ⟨[], [], []⟩
  | ifFalse {t e env k s} :
      Step (.retV (.bool false) (.ifK t e env k)) s (.exec e env k) s ⟨[], [], []⟩
  -- Loops
  | whileStmt {c b env k s} :
      Step (.exec (.while c b) env k) s (.evalE c env (.whileK c b env k)) s ⟨[], [], []⟩
  | whileTrue {c b env k s} :
      Step (.retV (.bool true) (.whileK c b env k)) s
        (.exec b env (.loop c b env k)) s ⟨[], [], []⟩
  | whileFalse {c b env k s} :
      Step (.retV (.bool false) (.whileK c b env k)) s (.next k) s ⟨[], [], []⟩
  | loopNext {c b env k s} :
      Step (.next (.loop c b env k)) s (.exec (.while c b) env k) s ⟨[], [], []⟩
  -- Breakable scopes (switch/select bodies): `break` exits the scope
  -- (the table's `breakableK` row), everything else unwinds past it.
  | breakableEnter {b env k s} :
      Step (.exec (.breakable b) env k) s (.exec b env (.breakableK k)) s ⟨[], [], []⟩
  | breakableDone {k s} :
      Step (.next (.breakableK k)) s (.next k) s ⟨[], [], []⟩
  -- (Control transfer — `return`/`break`/`continue`/`break L`/`continue L`
  -- — is the `signalStmt` rule; the per-frame handling is `signal`.)
  | inertLabel {name env k s} :
      Step (.exec (.inertLabel name) env k) s (.next k) s ⟨[], [], []⟩
  -- Labeled statements (control-flow slice,
  -- docs/2026-08-04_control-flow-design.md). The label scope's handling
  -- of every signal — catching `brkTo` at a match, passing the bare
  -- signals, never being `contTo`'s target (a MATCHING label not guarded
  -- by a loop head has no rule: statically impossible in Go — fail
  -- closed) — is the table's `labelK` row; `contTo` is caught by a loop
  -- whose immediate continuation is the matching label (`contHeadLabel`
  -- — the frontend's placement invariant), the table's `loop`/`mapIterK`
  -- rows.
  | labeledEnter {name b env k s} :
      Step (.exec (.labeled name b) env k) s (.exec b env (.labelK name k)) s ⟨[], [], []⟩
  | labelDone {name k s} :
      Step (.next (.labelK name k)) s (.next k) s ⟨[], [], []⟩
  -- Calls (BUG-025 spine migration; ORDER pinned at the S1 audit,
  -- BUG-052): the CALL evaluates first — arguments left-to-right, then
  -- frame entry — and the caller-target PLANS ride the frame untouched.
  -- Target OPERANDS evaluate at frame EXIT (post-call, through the
  -- tgtOpK spine — the receive path's exact shape), each target
  -- completing into a store-ready `TargetRef` with its outer check
  -- deferred to its own `storeK` store.
  --
  -- THE PINNED LATITUDE (deterministic pin of spec-unordered order —
  -- record per the nondeterminism doctrine's deterministic-latitude
  -- precedent, panic identity / hidden-dep init order): spec §Order of
  -- evaluation — "when evaluating the operands of an expression,
  -- assignment, or return statement, all function calls, method calls,
  -- receive operations, and binary logical operations are evaluated in
  -- lexical left-to-right order"; and, of the spec's own
  -- `y[f()], ok = g(z || h(), i()+x[j()], <-c), k()` example:
  -- "However, the order of those events compared to the evaluation
  -- and indexing of x and the evaluation of y and z is not specified,
  -- except as required lexically." The `lhs..., x = f(...)` class sits
  -- squarely in that carve-out ON GOCORE'S EXPR SURFACE: the frontend
  -- hoists every nested call/receive out of target operands (A-normal
  -- form), so by the time this rule fires the left-hand operand reads
  -- are call-free and receive-free — nothing the "except as required
  -- lexically" qualifier orders remains among them, and their order
  -- against the RHS call is exactly the unspecified residue.
  -- gc REALIZES call-first: the left-hand operands (index operands, a
  -- deref target's pointer, an index target's slice-header base) are
  -- read AFTER the call returns — probed go1.26.5 (the BUG-052 matrix:
  -- missed/spurious index panic, global index, deref target,
  -- slice-header base; multi-assign/call-write-back-order{,-value}/*).
  -- The machine consumes NO Choices here, so it pins gc's point; a
  -- future gc that realizes the other order revisits this pin, not the
  -- spec claim. SCOPE: the pin covers ONLY the call-vs-operand axis.
  -- The INTER-TARGET operand order (which target's operands evaluate
  -- first) is a SEPARATE spec-unordered axis this pin does NOT cover:
  -- gc's realization there is compiler-internal (2 targets: the
  -- second's operand panic wins; 3: the middle's — go1.26.5, stable
  -- under -N -l) and therefore unpinnable; the machine's left-to-right
  -- is OUR spec-legal realization, recorded as OPEN latitude in
  -- BUG-026's unordered-panic-envelope amendment (docs/BUGS.md).
  | callStart {targets fid args plans a rest env k s} :
      targetsPlan targets.toList = some plans →
      args.toList = a :: rest →
      Step (.exec (.call targets fid args) env k) s
        (.evalE a env (.callArgsK fid plans [] rest env k)) s ⟨[], [], []⟩
  -- Frame ENTRY rules (B2): `enterFramePick` classifies the entry
  -- (`enterFrame`'s recoverable panic — dynamic dispatch on a nil
  -- interface, the auto-deref of a nil pointer box — is an ordinary
  -- RECOVERABLE panic in Go, pinned by `interfaces/recover-nil-dispatch/*`)
  -- and draws the BUG-087 text pick on the panic path; the rule
  -- quantifies the stream (`ch`/`ch'`, the `stmtOpApply` idiom) and
  -- delivers: an entered frame runs the body, a panic unwinds under the
  -- caller's continuation.
  | callImmediate {targets fid args plans r env k s ch ch' ps c' s' l} :
      targetsPlan targets.toList = some plans →
      args.toList = [] →
      enterFramePick ctx s fid [] ch = .ok (r, ch', ps) →
      deliver s k (fun (e, s', tr) => (e.callConfig plans env k, s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.exec (.call targets fid args) env k) s c' s' l
  | callArgNext {v fid plans vals a rest env k s} :
      Step (.retV v (.callArgsK fid plans vals (a :: rest) env k)) s
        (.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k)) s ⟨[], [], []⟩
  | callArgsDoneEnter {v fid plans vals r env k s ch ch' ps c' s' l} :
      enterFramePick ctx s fid (vals ++ [v]) ch = .ok (r, ch', ps) →
      deliver s k (fun (e, s', tr) => (e.callConfig plans env k, s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.retV v (.callArgsK fid plans vals [] env k)) s c' s' l
  -- Wide statements (S2): one generic operand-plan frame; targets are
  -- checked as their addresses arrive (interpreter order), and the final
  -- state update is one `applyStmtOp` step. The `ch`/`ch'` choice streams
  -- are rule variables: a step under ANY choice stream is a legal step
  -- (the relation over-approximates the nondeterminism the executable
  -- resolves via `Choices`).
  | stmtOpFirst {stmt op nt e rest env k s} :
      stmtPlan stmt = some (op, nt, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.stmtOpK op nt [] rest env k)) s ⟨[], [], []⟩
  | stmtOpShiftTarget {op nt done v r e rest env k s c' s' l} :
      done.length < nt →
      toResult (valueAsLoc v) = .ok r →
      deliver s k (fun _ => (.evalE e env (.stmtOpK op nt (v :: done) rest env k), s, ⟨[], [], []⟩)) r
        = (c', s', l) →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s c' s' l
  | stmtOpShiftPlain {op nt done v e rest env k s} :
      nt ≤ done.length →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s
        (.evalE e env (.stmtOpK op nt (v :: done) rest env k)) s ⟨[], [], []⟩
  -- (The target check is restricted to a nonempty pending list: at the
  -- apply position the same nil-target panic surfaces through
  -- `applyStmtOp`'s per-arm `valueAsLoc` checks, delivered by
  -- `stmtOpApply` — keeping the rules in one-to-one correspondence with
  -- `stepFn`'s arms.)
  | stmtOpApply {op nt done v r env k s ch c' s' l} :
      toResult (applyStmtOp ctx s ch op nt (v :: done).reverse) = .ok r →
      deliver s k (fun (s', _, ps, tr) =>
        (.next k, s', ⟨tr, ps, stmtOpOut op (v :: done).reverse⟩)) r = (c', s', l) →
      Step (.retV v (.stmtOpK op nt done [] env k)) s c' s' l
  -- Map iteration — LIVE (BUG-005 (L) surgery, ruled 2026-08-19; the
  -- snapshot rules are retired) over entry-identity stamps (B1): start
  -- records the base cell and the START-ID set; each pick LOADS the
  -- live cell, filters candidates by the produced-ID set, and either
  -- picks ANY candidate (the nondeterministic order latitude + the
  -- created-entries latitude) or STOPS, the stop legal only when no
  -- never-removed start entry remains a candidate (the spec-forced
  -- traversal clause; `mapIterMandatoryRemains` is pure). The envelope
  -- statement lives on `Cont.mapIterK`'s docstring; the executable
  -- consumes one choice of width `candidates + stop`, stop LAST — the
  -- zero stream IS the canonical member, by definition.
  | mapRange {keyVar valVar mapExpr keyTy valTy body env k s} :
      Step (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) s
        (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k)) s ⟨[], [], []⟩
  | mapRangeStart {v base start tr keyVar valVar keyTy valTy body env k s} :
      mapRangeStartSets s v = .ok (base, start, tr) →
      Step (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body base #[] start env k)) s ⟨tr, [], []⟩
  | mapIterDone {keyVar valVar keyTy valTy body base produced start env k s tr} :
      mapIterCandidates ctx s keyTy valTy base produced = .ok (#[], tr) →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next k) s ⟨tr, [], []⟩
  | mapIterNext {keyVar valVar keyTy valTy body base produced start cands idx env env' k s s' tr}
      (hidx : idx < cands.size) :
      mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr) →
      -- (The mandatory test is pure since B1, so it needs no success
      -- premise here: the pick width is a total function of `cands`.)
      bindIterVars ctx env.pushScope s keyVar valVar keyTy valTy
        cands[idx].2.1 cands[idx].2.2 = .ok (env', s') →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.exec body env' (.mapIterK keyVar valVar keyTy valTy body
          base (produced.push cands[idx].1) start env k)) s'
        ⟨tr, PickRecord.ofPick .mapIter
          (cands.size + if mapIterMandatoryRemains cands start then 0 else 1) idx, []⟩
  | mapIterStop {keyVar valVar keyTy valTy body base produced start cands env k s tr} :
      mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr) →
      cands.size ≠ 0 →
      mapIterMandatoryRemains cands start = false →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next k) s ⟨tr, [⟨.mapIter, cands.size + 1, cands.size⟩], []⟩
  -- (`break`/`continue`/`return` at the range frame: the table's
  -- `mapIterK` row, rule `signal`.)
  -- Call through a function VALUE (§8): targets, then the callee, then the
  -- arguments; frame entry prepends the closure's captured values, which is
  -- the whole lambda-lifting protocol. `enterFrame` is reused verbatim.
  -- Call through a value (§8), same BUG-052 order pin: callee, then
  -- arguments, then frame entry — the caller-target plans ride to the
  -- frame; target operands evaluate at frame exit.
  | callValueStart {targets callee args plans env k s} :
      targetsPlan targets.toList = some plans →
      Step (.exec (.callValue targets callee args) env k) s
        (.evalE callee env (.callValCalleeK plans args.toList env k)) s ⟨[], [], []⟩
  /-- The callee value arrives (funcVal or nil); start the arguments. Go
  evaluates the callee and ALL arguments before the nil check fires. -/
  | callValCalleeArg {cv plans a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.callValCalleeK plans (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv plans [] rest env k)) s ⟨[], [], []⟩
  /-- Nullary call through a value: enter directly with the captures. -/
  | callValCalleeEnter {fid captured plans r env k s ch ch' ps c' s' l} :
      enterFramePick ctx s fid captured ch = .ok (r, ch', ps) →
      deliver s k (fun (e, s', tr) => (e.callConfig plans env k, s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k)) s c' s' l
  /-- Nullary call of a nil function value: nothing to evaluate, panic. -/
  | callValCalleeNil {plans env k s} :
      Step (.retV .nil (.callValCalleeK plans [] env k)) s
        (.panicking [panicEntry nilDerefPanicText] k) s ⟨[], [], []⟩
  | callValArgNext {v cv plans vals a rest env k s} :
      Step (.retV v (.callValArgsK cv plans vals (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv plans (vals ++ [v]) rest env k)) s ⟨[], [], []⟩
  | callValArgsEnter {v fid captured plans vals r env k s ch ch' ps c' s' l} :
      enterFramePick ctx s fid (captured ++ vals ++ [v]) ch = .ok (r, ch', ps) →
      deliver s k (fun (e, s', tr) => (e.callConfig plans env k, s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k)) s c' s' l
  /-- All arguments evaluated, callee is nil: NOW the invocation panics. -/
  | callValArgsNil {v plans vals env k s} :
      Step (.retV v (.callValArgsK .nil plans vals [] env k)) s
        (.panicking [panicEntry nilDerefPanicText] k) s ⟨[], [], []⟩
  -- Frame exit (BUG-025 spine migration; ORDER pinned per BUG-052):
  -- explicit return and fall-through perform the same pinned-location
  -- result read. A TARGETLESS frame resumes the caller in one step
  -- (behavior unchanged — every expression-position call the frontend
  -- hoists takes this shape); a frame WITH caller-target PLANS reads
  -- the results and enters the tgtOpK spine POST-CALL (the post-call
  -- point is gc's realized order — the BUG-052 pin, which covers ONLY
  -- the call-vs-operand axis; the spine is the receive path's exact
  -- delivery shape): phase 1 evaluates the target operands
  -- left-to-right in the CALLER's environment — OUR spec-legal
  -- realization of the INTER-TARGET order, an axis gc realizes
  -- compiler-internally and this pin deliberately leaves OPEN (the
  -- BUG-026 envelope amendment) — each target completing into a
  -- store-ready TargetRef with its outer check deferred; phase 2
  -- (`storeK`) stores
  -- left-to-right one per step, checks firing at the store after
  -- earlier stores landed — spec §Assignments' example, on the call
  -- write-back path.
  -- (Targetless + resultless — the void-call and deferred-inner-frame
  -- shape — resumes in one step, state untouched, exactly as before. A
  -- targetless frame with PINNED results has no rule: the frontend
  -- always supplies targets — `$callres` temps or blank discards — for
  -- result-bearing calls, and the machine stays stuck-closed on the
  -- malformed shape as it always was.)
  | frameReturn {tenv k fr s} :
      Step (.signal .ret (.frame [] tenv [] [] k fr)) s (.next k) s ⟨[], [], []⟩
  | frameFall {tenv k fr s} :
      Step (.next (.frame [] tenv [] [] k fr)) s (.next k) s ⟨[], [], []⟩
  | frameReturnTargets {sh e ops rest tenv results k fr s vs tr} :
      loadResults ctx s results = .ok (vs, tr) →
      Step (.signal .ret (.frame ((sh, e :: ops) :: rest) tenv results [] k fr)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩
  | frameFallTargets {sh e ops rest tenv results k fr s vs tr} :
      loadResults ctx s results = .ok (vs, tr) →
      Step (.next (.frame ((sh, e :: ops) :: rest) tenv results [] k fr)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩
  -- Draining the defer chain: one deferred call per step, each in its own
  -- frame whose continuation is this frame with the rest of the chain, so
  -- both exit paths converge on the rules above once the chain is empty.
  -- The inner frame has NO targets and NO results: a deferred call's
  -- results are discarded in Go (`defer/defer-function-result-discard`).
  -- An ENTRY panic is the deferred INVOCATION's panic (audit F1+F5,
  -- 2026-08-05 — the class the `.nil`-callee drain rules model, pinned by
  -- `defer/deferred-dispatch-entry-panic/*`): on the normal drains it
  -- starts unwinding AT THIS FRAME with its remaining defers (the
  -- delivery continuation is the draining frame).
  | frameDeferFall {targets tenv results fid captured args ds k fr s r ch ch' ps c' s' l} :
      enterFramePick ctx s fid (captured ++ args) ch = .ok (r, ch', ps) →
      deliver s (.frame targets tenv results ds k fr) (fun (e, s', tr) =>
        (e.drainConfig (.frame targets tenv results ds k fr)
          (fun cv => .next (.frame targets tenv results ((cv, []) :: ds) k fr)), s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.next (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k fr)) s c' s' l
  | frameDeferReturn {targets tenv results fid captured args ds k fr s r ch ch' ps c' s' l} :
      enterFramePick ctx s fid (captured ++ args) ch = .ok (r, ch', ps) →
      deliver s (.frame targets tenv results ds k fr) (fun (e, s', tr) =>
        (e.drainConfig (.frame targets tenv results ds k fr)
          (fun cv => .next (.frame targets tenv results ((cv, []) :: ds) k fr)), s', ⟨tr, [], []⟩)) r [] ps
        = (c', s', l) →
      Step (.signal .ret (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k fr)) s c' s' l
  /-- Invoking a nil deferred call panics at DRAIN time (Go: registration
  succeeded; the panic belongs to the invocation). The panic starts
  unwinding AT THIS FRAME with its remaining defers — which run, and may
  recover (`defer/defer-nil-function-recover-order` pins the order). -/
  | frameDeferNilFall {targets tenv results args ds k fr s} :
      Step (.next (.frame targets tenv results ((.nil, args) :: ds) k fr)) s
        (.panicking [panicEntry nilDerefPanicText] (.frame targets tenv results ds k fr)) s ⟨[], [], []⟩
  | frameDeferNilReturn {targets tenv results args ds k fr s} :
      Step (.signal .ret (.frame targets tenv results ((.nil, args) :: ds) k fr)) s
        (.panicking [panicEntry nilDerefPanicText] (.frame targets tenv results ds k fr)) s ⟨[], [], []⟩
  -- Registering a deferred call: callee, then arguments, evaluated NOW.
  | deferStmt {callee args env k s} :
      Step (.exec (.deferCall callee args) env k) s
        (.evalE callee env (.deferCalleeK args.toList env k)) s ⟨[], [], []⟩
  | deferCalleeArg {cv a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.deferCalleeK (a :: rest) env k)) s
        (.evalE a env (.deferArgsK cv [] rest env k)) s ⟨[], [], []⟩
  | deferCalleeNoArgs {cv env k k' s} :
      deferrableCallee cv = true →
      pushDefer (cv, []) k = some k' →
      Step (.retV cv (.deferCalleeK [] env k)) s (.next k') s ⟨[], [], []⟩
  | deferArgNext {v cv vals a rest env k s} :
      Step (.retV v (.deferArgsK cv vals (a :: rest) env k)) s
        (.evalE a env (.deferArgsK cv (vals ++ [v]) rest env k)) s ⟨[], [], []⟩
  | deferArgsDone {v cv vals env k k' s} :
      pushDefer (cv, vals ++ [v]) k = some k' →
      Step (.retV v (.deferArgsK cv vals [] env k)) s (.next k') s ⟨[], [], []⟩
  -- The unwinding arc (`docs/2026-07-25_unwinding-arc.md` §A1): panic as
  -- a travelling configuration.
  /-- `panic(v)`: evaluate the payload (already `any`-converted by the
  lowering), then start unwinding. -/
  | panicStmt {e env k s} :
      Step (.exec (.panicStmt e) env k) s (.evalE e env (.panicArgK k)) s ⟨[], [], []⟩
  | panicArgValue {v k s} :
      Step (.retV v (.panicArgK k)) s (.panicking [⟨panicPayload v, false⟩] k) s ⟨[], [], []⟩
  /-- Unwinding strips every non-frame, non-marker continuation. -/
  | panicUnwind {chain k k' s} :
      panicPassthrough k = some k' →
      Step (.panicking chain k) s (.panicking chain k') s ⟨[], [], []⟩
  /-- Unwinding past a frame with no (remaining) defers: results are NOT
  read — the call did not return. -/
  | panicFrameEmpty {chain targets tenv results k fr s} :
      Step (.panicking chain (.frame targets tenv results [] k fr)) s
        (.panicking chain k) s ⟨[], [], []⟩
  /-- Defers RUN on the panic path: the deferred call executes above a
  `panicResumeK` carrying the suspended chain — the shape `recover`'s
  walk detects. Results discarded, as on the normal drain. An ENTRY panic
  JOINS the suspended chain newest-last (`deliver`'s `chain`; audit
  F1+F5 — Go appends the new panic and `recover` answers the newest
  entry, which `chainNewestRecovered` implements; the `during-panic` pin
  discriminates newest-vs-original by asserting the recovered value) and
  draining continues — the `.nil`-callee mirror below. -/
  | panicFrameDefer {chain targets tenv results fid captured args ds k fr s r ch ch' ps c' s' l} :
      enterFramePick ctx s fid (captured ++ args) ch = .ok (r, ch', ps) →
      deliver s (.frame targets tenv results ds k fr) (fun (e, s', tr) =>
        (e.drainConfig (.panicResumeK chain (.frame targets tenv results ds k fr))
          (fun cv => .panicking chain (.frame targets tenv results ((cv, []) :: ds) k fr)),
          s', ⟨tr, [], []⟩)) r chain ps
        = (c', s', l) →
      Step (.panicking chain (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k fr))
        s c' s' l
  /-- A nil deferred callee invoked DURING unwinding: the invocation's
  nil-dereference panic joins the chain (newest last) and this frame's
  remaining defers keep draining. -/
  | panicFrameDeferNil {chain targets tenv results args ds k fr s} :
      Step (.panicking chain (.frame targets tenv results ((.nil, args) :: ds) k fr)) s
        (.panicking (chain ++ [panicEntry nilDerefPanicText])
          (.frame targets tenv results ds k fr)) s ⟨[], [], []⟩
  /-- A NEW panic unwinding through a suspended chain's marker merges
  behind it — this single rule produces Go's chained abort output
  (`panic: first ⏎ panic: second`, `… [recovered] ⏎ …`). -/
  | panicResumeMerge {chain suspended k s} :
      Step (.panicking chain (.panicResumeK suspended k)) s
        (.panicking (suspended ++ chain) k) s ⟨[], [], []⟩
  /-- A panic-path deferred call completed and the newest chain entry was
  recovered: the unwind is cancelled, the whole chain discarded, and the
  frame below resumes its NORMAL exit path (drain remaining defers, then
  read pinned results — Go's "the surrounding function returns
  normally"). -/
  | panicResumeRecovered {chain k s} :
      chainNewestRecovered chain = true →
      Step (.next (.panicResumeK chain k)) s (.next k) s ⟨[], [], []⟩
  /-- …not recovered: unwinding resumes below. -/
  | panicResumeContinue {chain k s} :
      chainNewestRecovered chain = false →
      Step (.next (.panicResumeK chain k)) s (.panicking chain k) s ⟨[], [], []⟩
  -- (An unrecovered chain at `.stop` — the abort — has NO rule since B4:
  -- `Config.abort?`; the sequential driver raises the `panic` terminal
  -- there and the pool records the goroutine's `aborted` tombstone, both
  -- through `abortMsg`. The former `panicAbort` step to the k-less
  -- `.panicked` is gone with that constructor.)
  -- (The seven `*Panic`/`*EnterPanic` frame-entry twins that lived here
  -- were folded into their entry rules by B2 — `enterFramePick` +
  -- `deliver`; the BUG-087 entry-panic TEXT is now the pick the rule's
  -- quantified stream draws: on the wrapper family the two-member set
  -- {nil-dereference text, gc's `panicwrap` text}, elsewhere `msg`. The
  -- deleted docstrings' history: ledger [DL-20].)
  /-- Channel statements (channels arc slice 1; receive reordered at the
  audit response, BUG-022): pre-communication operand entry, plain
  shifts, one apply step — the apply's outcome a full CONFIGURATION
  (`applyChanOp`: next / panicking / blocked / a receive's phase-1
  target entry — targets evaluate AFTER the communication, then store
  left-to-right, spec §Assignments via BUG-029's split phases, the
  select path's shape). Appended at the
  END of the inductive so the correspondence proofs' positional case
  tags stay stable. The blocked configurations these can step TO have no
  outgoing rules (relation-silent): pairing is the slice-2 pool's job,
  and the sequential driver classifies them as the deadlocked run. -/
  | chanStFirst {stmt op e rest env k s} :
      chanPlan stmt = some (op, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.chanStK op [] rest env k)) s ⟨[], [], []⟩
  | chanStShift {op done v e rest env k s} :
      Step (.retV v (.chanStK op done (e :: rest) env k)) s
        (.evalE e env (.chanStK op (v :: done) rest env k)) s ⟨[], [], []⟩
  | chanStApply {op done v r env k s c' s' l} :
      toResult (applyChanOp ctx s op (v :: done).reverse env k) = .ok r →
      -- Channel traffic is SYNCHRONIZATION (no `.data` access); the label
      -- is the apply's own emission (C1 S2c): the channel-object read/write
      -- gc instruments and the slot / close actions.
      deliver s k (fun (c', s', tr) => (c', s', ⟨tr, [], []⟩)) r = (c', s', l) →
      Step (.retV v (.chanStK op done [] env k)) s c' s' l
  -- `select` (spec's five steps): entry evaluates the clause operands in
  -- source order under `selectOpsK` (step 1); the apply step computes
  -- readiness and commits (steps 2-3, `applySelect` — one ready clause
  -- or default deterministically; MULTI-READY draws the L2 clause pick
  -- from the choice stream, live since slice 4 — the envelope statement
  -- is `applySelect`'s docstring); a selected receive's targets evaluate
  -- after the communication (step 4, the `tgtOpK`/`storeK` phases); the
  -- body enters
  -- under the plain continuation (step 5 — the frontend wraps the whole
  -- select in `.breakable`, so `break` needs no select-side rule).
  | selectFirst {clauses default? e rest env k s} :
      selectOperands clauses.toList = e :: rest →
      Step (.exec (.selectStmt clauses default?) env k) s
        (.evalE e env (.selectOpsK clauses.toList default? [] rest env k)) s ⟨[], [], []⟩
  | selectNoClausesDefault {clauses d env k s} :
      selectOperands clauses.toList = [] →
      Step (.exec (.selectStmt clauses (some d)) env k) s (.exec d env k) s ⟨[], [], []⟩
  /-- `select {}` (and the degenerate no-clause, no-default form): blocks
  forever (spec: "a select with ... no default case blocks forever"). -/
  | selectNoClausesBlock {clauses env k s} :
      selectOperands clauses.toList = [] →
      Step (.exec (.selectStmt clauses none) env k) s
        (.blockedSelect [] env k) s ⟨[], [], []⟩
  | selectOpsShift {clauses default? done v e rest env k s} :
      Step (.retV v (.selectOpsK clauses default? done (e :: rest) env k)) s
        (.evalE e env (.selectOpsK clauses default? (v :: done) rest env k)) s ⟨[], [], []⟩
  -- The apply rules quantify the CHOICE STREAM (`stmtOpApply`'s idiom):
  -- multi-ready readiness draws the L2 clause pick from it (slice 4 —
  -- the envelope statement is `applySelect`'s docstring), so any
  -- ready clause's commit is a legal step.
  | selectApply {clauses default? done v r env k s ch c' s' l} :
      -- The rule quantifies the stream; the apply's emitted commit
      -- identity (Q2's 4th component — instrumentation, not semantics)
      -- and its stream are projected away by the delivery: the
      -- successor configuration is what the rule relates.
      toResult (applySelect ctx s clauses default? (v :: done).reverse env k ch) = .ok r →
      deliver s k (fun (c', s', _, ps, _, tr) => (c', s', ⟨tr, ps, []⟩)) r = (c', s', l) →
      Step (.retV v (.selectOpsK clauses default? done [] env k)) s c' s' l
  -- Receive delivery, phases SPLIT (convergence round, BUG-029): phase
  -- 1 (`tgtOpK`) evaluates every target's OPERANDS left-to-right,
  -- resolving each target to a store-ready `TargetRef` with its outer
  -- nil/bounds check DEFERRED; phase 2 (`storeK`, `.next`-driven)
  -- stores left-to-right, ONE step per target, store-time panics
  -- firing after earlier stores landed.
  | tgtOpShift {sh ops v e pending refs targets rop rhs vals body env k s} :
      Step (.retV v (.tgtOpK sh ops (e :: pending) refs targets rop rhs vals body env k)) s
        (.evalE e env (.tgtOpK sh (v :: ops) pending refs targets rop rhs vals body env k)) s ⟨[], [], []⟩
  | tgtOpNext {sh ops v r sh' e ops' targets refs rop rhs vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: targets) rop rhs vals body env k)) s
        (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) targets rop rhs vals body env k)) s ⟨[], [], []⟩
  | tgtOpStores {sh ops v r refs rop vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs [] rop [] vals body env k)) s
        (.next (.storeK (refs ++ [r]) vals body env k)) s ⟨[], [], []⟩
  -- Spine-riding assignments (BUG-025; single form and comma-ok
  -- sources round 4, BUG-034/BUG-037): phase 1 resolves the targets,
  -- the RHS evaluates left-to-right (`rhsK`), the value source
  -- applies (`applyRhsOp` — identity / map lookup / type assert),
  -- phase 2 stores one step per target with the chain's checks firing
  -- at the store.
  | tgtOpRhs {sh ops v r refs rop e rest vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals body env k)) s
        (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k)) s ⟨[], [], []⟩
  | rhsShift {rop refs done v e rest body env k s} :
      Step (.retV v (.rhsK rop refs done (e :: rest) body env k)) s
        (.evalE e env (.rhsK rop refs (v :: done) rest body env k)) s ⟨[], [], []⟩
  | rhsStores {rop refs done v r body env k s c' s' l} :
      toResult (applyRhsOp ctx s rop (v :: done).reverse) = .ok r →
      deliver s k (fun (vals, tr) => (.next (.storeK refs vals body env k), s, ⟨tr, [], []⟩)) r
        = (c', s', l) →
      Step (.retV v (.rhsK rop refs done [] body env k)) s c' s' l
  | assignManyFirst {left right sh e ops rest env k s} :
      left.size = right.size →
      targetsPlan left.toList = some ((sh, e :: ops) :: rest) →
      Step (.exec (.assignMany left right) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k)) s ⟨[], [], []⟩
  | assignFirst {lhs rhs sh e ops env k s} :
      targetPlan lhs = some (sh, e :: ops) →
      Step (.exec (.assign lhs rhs) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k)) s ⟨[], [], []⟩
  | mapLookupFirst {t okT base index keyTy valueTy sh e ops rest env k s} :
      targetsPlan [t, okT] = some ((sh, e :: ops) :: rest) →
      Step (.exec (.mapLookup t okT base index keyTy valueTy) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy)
          [base, index] [] (.seqn #[]) env k)) s ⟨[], [], []⟩
  | typeAssertFirst {t okT expr targetTy sh e ops rest env k s} :
      targetsPlan [t, okT] = some ((sh, e :: ops) :: rest) →
      Step (.exec (.typeAssert t okT expr targetTy) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest (.typeAssert targetTy)
          [expr] [] (.seqn #[]) env k)) s ⟨[], [], []⟩
  | storeStep {ref rs val vals r body env k s c' s' l} :
      toResult (storeTarget ctx s ref val) = .ok r →
      deliver s k (fun (s', tr) => (.next (.storeK rs vals body env k), s', ⟨tr, [], []⟩)) r
        = (c', s', l) →
      Step (.next (.storeK (ref :: rs) (val :: vals) body env k)) s c' s' l
  | storeDone {body env k s} :
      Step (.next (.storeK [] [] body env k)) s (.exec body env k) s ⟨[], [], []⟩
  -- `go` statements (channels arc slice 2): callee then arguments,
  -- evaluated NOW in the spawning goroutine (spec §Go statements) — the
  -- defer registration's eval-now shape. The completed SPAWN position
  -- (`goCalleeK []` / `goArgsK … []`) is deliberately RELATION-SILENT
  -- here: spawning appends a thread, which the per-goroutine relation
  -- cannot express — the spawn is a rule of the spawn-extended `StepE`
  -- (Multi.lean) and a pool step of `StepM`; `stepFn` fails closed at
  -- the spawn position, which keeps `go` in `$pkginit` refused.
  | goStmtEntry {callee args env k s} :
      Step (.exec (.goStmt callee args) env k) s
        (.evalE callee env (.goCalleeK args.toList env k)) s ⟨[], [], []⟩
  | goCalleeArg {cv a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.goCalleeK (a :: rest) env k)) s
        (.evalE a env (.goArgsK cv [] rest env k)) s ⟨[], [], []⟩
  | goArgNext {v cv vals a rest env k s} :
      Step (.retV v (.goArgsK cv vals (a :: rest) env k)) s
        (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k)) s ⟨[], [], []⟩
  -- Sync statements (spec-parity slice 2, design note §§4,6): the
  -- `chanStK` shape verbatim — operand entry/shift, then ONE apply
  -- step (`applySyncOp`: next / panicking / blocked / an onceBegin
  -- delivery entry). The FATAL outcomes (unlock-of-unlocked etc.) are
  -- `Except.error (.fatal …)` from the apply and therefore
  -- RELATION-SILENT, like the diagnostic errors — an unrecoverable
  -- abort has no successor configuration. The blocked shape
  -- `.blockedSync` has no outgoing per-goroutine rule (the pool wakes
  -- it). The apply QUANTIFIES THE CHOICE STREAM (the `stmtOpApply`
  -- idiom): only the TRY heads draw from it (`ChoiceSite.tryLock`, the
  -- envelope statement at `applyTryLock`); every other head passes it
  -- through untouched (`applySyncOpCore`'s envelope statement).
  | syncStFirst {stmt op e rest env k s} :
      syncPlan stmt = some (op, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.syncStK op [] rest env k)) s ⟨[], [], []⟩
  | syncStShift {op done v e rest env k s} :
      Step (.retV v (.syncStK op done (e :: rest) env k)) s
        (.evalE e env (.syncStK op (v :: done) rest env k)) s ⟨[], [], []⟩
  | syncStApply {op done v r env k s ch c' s' l} :
      toResult (applySyncOp ctx s ch op (v :: done).reverse env k) = .ok r →
      -- Sync traffic is the primitive's state transition (no `.data`
      -- access); the label is the apply's own emission (C1 S2c): the
      -- sync-word accesses and the acquire/release action.
      deliver s k (fun (c', s', _, ps, tr) => (c', s', ⟨tr, ps, []⟩)) r = (c', s', l) →
      Step (.retV v (.syncStK op done [] env k)) s c' s' l
  -- (The completion marker's strip `opDoneStrip` LEFT this relation at
  -- C5: the boundary is a per-goroutine flag of the pool (`Thread`), and
  -- its clear is a POOL step (`StepM.strip`), never a `Config` step.)
  -- sync/atomic statements (atomics arc wave 1): the `syncStK` shape
  -- verbatim — operand entry/shift, then ONE apply step
  -- (`applyAtomicOp`: next / a result delivery entry / panicking on a
  -- nil address). Diagnostic outcomes are relation-silent like every
  -- other apply's; the apply consumes NO choices (its envelope
  -- statement). Appended at the END so positional case tags stay
  -- stable.
  | atomicStFirst {stmt op e rest env k s} :
      atomicPlan stmt = some (op, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.atomicStK op [] rest env k)) s ⟨[], [], []⟩
  | atomicStShift {op done v e rest env k s} :
      Step (.retV v (.atomicStK op done (e :: rest) env k)) s
        (.evalE e env (.atomicStK op (v :: done) rest env k)) s ⟨[], [], []⟩
  | atomicStApply {op done v r env k s c' s' l} :
      toResult (applyAtomicOp ctx s op (v :: done).reverse env k) = .ok r →
      -- The atomic op's own access at the cell (its ATOMIC kind) and its
      -- clock action are the apply's emission (C1 S2c); no plain `.data`
      -- access here.
      deliver s k (fun (c', s', tr) => (c', s', ⟨tr, [], []⟩)) r = (c', s', l) →
      Step (.retV v (.atomicStK op done [] env k)) s c' s' l
  -- The unsequenced-operand probe (latitude E13 option (b), lane `e13-b`
  -- 2026-09-05, RULED [USER] relayed; envelope statement at
  -- `Stmt.unseqProbe`): evaluate the operand under the probe frame; a
  -- value is discarded; a PANIC reaching the frame has TWO successors —
  -- nondeterminism where Go has it (spec#Order_of_evaluation orders
  -- neither the operand nor the sibling event first). Appended at the END
  -- so positional case tags stay stable.
  --
  -- REACHABILITY INVARIANT (the reason the four rules below are the ONLY
  -- rules at a `probeK` frame): a `probeK` frame is created by exactly one
  -- rule (`unseqProbe`, under `.evalE`), and expression evaluation reaches
  -- a statement-level configuration only through `retV` (a value) or
  -- `panicking` (a panic) — a `.signal sg _` (B4's one control form for
  -- break/continue/return and their labelled forms) arises from `.exec` of
  -- a statement, and no statement executes under a probe (the probed
  -- operand is an `Expr`; a func literal called inside it runs in its OWN
  -- frame, whose signals stop at that `.frame`). So `.signal _ (.probeK _)`
  -- and `.next (.probeK _)` are unreachable from a well-formed
  -- configuration; `stepFn` refuses them through `signalRefusal`'s
  -- expression-frame arm and the `.next` catch-all ("break/continue/return/
  -- completion delivered to expression continuation" — Machine.lean's
  -- `signalRefusal`, StepFn.lean's `.signal`/`.next` arms; each site's
  -- comment names `probeK` among the frames it covers), never a silent
  -- default (`signalStep` has no `probeK` row: `none` there). The fix round
  -- did NOT add explicit `.probeK` arms (every added arm shifts
  -- `MachineSound`'s positional case tags) — e13-b audit fix round R12;
  -- wording corrected at the re-audit (R1'-6: the earlier text claimed a
  -- `stuck` naming `probeK` that does not exist) and restated over B4's
  -- `Signal` at the round-17 rebase ([AGENT]).
  | unseqProbe {e env k s} :
      Step (.exec (.unseqProbe e) env k) s (.evalE e env (.probeK k)) s ⟨[], [], []⟩
  | probeValue {v k s} :
      Step (.retV v (.probeK k)) s (.next k) s ⟨[], [], []⟩
  /-- DEFER (slot 0): the early panic is not raised here; the operand is
  re-evaluated at its residual position after the sibling events. -/
  | probeDefer {chain k s} :
      Step (.panicking chain (.probeK k)) s (.next k) s ⟨[], [⟨.unseqPanic, 2, 0⟩], []⟩
  /-- RAISE (slot 1): the panic propagates now, ahead of the sibling events. -/
  | probeRaise {chain k s} :
      Step (.panicking chain (.probeK k)) s (.panicking chain k) s ⟨[], [⟨.unseqPanic, 2, 1⟩], []⟩
  -- **The `unseq` construct** (evaluation-order model v2.1 §3.3; Stage B,
  -- lane `core/unseq-scheduler-b-0916`, 2026-09-16; the mechanism RULED
  -- [USER] Mike 2026-09-16 relayed — «the Cerberus model is the correct
  -- one»). ENTER allocates the binder cells in the source scope (the
  -- `.initialization` idiom: the enclosing `.seq` frame's environment is
  -- extended in place, so `thenB`'s source declarations survive); the
  -- graph's static shape is checked BY NAME (`UnseqGraph.wellFormed?`).
  -- PICK (review R2's three cases): (i) no active occurrence → phase 2 —
  -- the stores ride the existing `storeK` spine, then `thenB` runs in the
  -- source scope; (ii) ANY ready occurrence may run next — nondeterminism
  -- where Go has it (spec#Order_of_evaluation: the order of the events
  -- against the evaluation of the other operands «is not specified,
  -- except as required lexically»; the graph's edges ARE the lexical
  -- requirements — the design note's §1 table); (iii) active work with no
  -- ready occurrence has NO rule (a named malformed-graph refusal in
  -- `stepFn`), as has a value dependency on a skipped region's binder
  -- (`skippedDep?`) and a completion whose stores or `thenB` would consume
  -- a binder never produced (`unproducedConsumer?`, audit F1) — refusals
  -- are not steps. RUN dispatches on the body: a value head evaluates
  -- under the frame (`.wait i`; its value is stored into the binder cell by
  -- `unseqValue`), an invocation runs `callValue` with the binder cells as
  -- targets (its completion is `unseqStmtDone`), a checked load / target
  -- plan / guard is ONE step. A failure anywhere unwinds through the frame
  -- (`panicUnwind`: `exprGlue`) — the sweep's first failure with the effect
  -- prefix so far. Appended at the END so positional case tags stay stable.
  | unseqEnter {g thenB rest env env' k s s'} :
      g.wellFormed? = none →
      allocDecls ctx env s g.cells = .ok (env', s') →
      Step (.exec (.unseq g thenB) env (.seq rest env k)) s
        (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env' k))) s' ⟨[], [], []⟩
  /-- Case (ii): the `j`-th READY occurrence (canonical rank order) runs
  next — the `ChoiceSite.unseqNext` pick; `j` is free (every ready
  occurrence is a legal choice). -/
  | unseqPick {g thenB st tg env k s} {j i : Nat} :
      g.skippedDep? st = none →
      (g.ready st)[j]? = some i →
      Step (.next (.unseqK g thenB st tg env .pick k)) s
        (.next (.unseqK g thenB st tg env (.run i) k)) s
        ⟨[], PickRecord.ofPick .unseqNext (g.ready st).length j, []⟩
  /-- Case (i): nothing active → phase 2 (the stores, then `thenB`). Every
  binder the stores and `thenB` consume was PRODUCED (`unproducedConsumer?`;
  audit F1, 2026-09-16 — a skipped producer's cell is never consumed as a
  value; the refusal is `stepFn`'s, by name). -/
  | unseqComplete {g thenB st tg env k s refs vals} :
      g.skippedDep? st = none →
      g.allSettled st = true →
      g.unproducedConsumer? st thenB = none →
      unseqStorePlan ctx s env tg g.stores = .ok (refs, vals) →
      Step (.next (.unseqK g thenB st tg env .pick k)) s
        (.next (.storeK refs vals thenB env k)) s ⟨[], [], []⟩
  | unseqRunEval {g thenB st tg env k s o bind head} {i : Nat} :
      g.occs[i]? = some o → o.body = .eval bind head →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.evalE head env (.unseqK g thenB st tg env (.wait i) k)) s ⟨[], [], []⟩
  | unseqRunInvoke {g thenB st tg env k s o binds callee args} {i : Nat} :
      g.occs[i]? = some o → o.body = .invoke binds callee args →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.exec (unseqInvokeStmt binds callee args) env
          (.unseqK g thenB st tg env (.wait i) k)) s ⟨[], [], []⟩
  /-- Stage E E3: a RECEIVE occurrence runs `chanRecv` with the binder cells
  as targets under the wait frame (its completion is `unseqRecvDone`); a
  receive that would block is the statement's own `blockedRecv`. -/
  | unseqRunRecv {g thenB st tg env k s o binds ch elem} {i : Nat} :
      g.occs[i]? = some o → o.body = .recv binds ch elem →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.exec (unseqRecvStmt binds ch elem) env
          (.unseqK g thenB st tg env (.wait i) k)) s ⟨[], [], []⟩
  /-- Stage E E4: an ALLOCATION occurrence runs its hoisted statement with the
  binder cell as its target under the wait frame (its completion is
  `unseqAllocDone`); a `make` whose size is out of range panics as the
  statement's own panic. -/
  | unseqRunAlloc {g thenB st tg env k s o bind spec} {i : Nat} :
      g.occs[i]? = some o → o.body = .allocate bind spec →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.exec (unseqAllocStmt bind spec) env
          (.unseqK g thenB st tg env (.wait i) k)) s ⟨[], [], []⟩
  /-- Stage E5 E5a: a WIDE built-in occurrence (`append`, `copy`) runs its
  hoisted statement with the binder cells as its targets under the wait frame
  (its completion is `unseqWideDone`); its own panics (an append past the
  address space, a copy through a nil slice's element) are the statement's. -/
  | unseqRunWide {g thenB st tg env k s o binds spec} {i : Nat} :
      g.occs[i]? = some o → o.body = .wide binds spec →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.exec (unseqWideStmt binds spec) env
          (.unseqK g thenB st tg env (.wait i) k)) s ⟨[], [], []⟩
  /-- The checked access through a frozen plan: apply, then deliver — a
  bounds panic unwinds through the frame over the pre-state. -/
  | unseqRunLoad {g thenB st tg env k s o bind tgt r c' s' l} {i : Nat} :
      g.occs[i]? = some o → o.body = .load bind tgt →
      toResult (unseqLoad ctx s env tg bind tgt) = .ok r →
      deliver s (.unseqK g thenB st tg env .pick k)
        (fun (s', tr) => (.next (.unseqK g thenB (st.set i .done) tg env .pick k), s', ⟨tr, [], []⟩)) r
        = (c', s', l) →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s c' s' l
  | unseqRunTarget {g thenB st tg env k s o bind lhs r tr} {i : Nat} :
      g.occs[i]? = some o → o.body = .target bind lhs →
      unseqTargetPlan ctx s env lhs = .ok (r, tr) →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.next (.unseqK g thenB (st.set i .done) (tg ++ [(bind, r)]) env .pick k)) s ⟨tr, [], []⟩
  | unseqRunGuard {g thenB st tg env k s o test w out st' s' tr} {i : Nat} :
      g.occs[i]? = some o → o.body = .guard test w out →
      unseqGuard ctx s g env st i test w out = .ok (st', s', tr) →
      Step (.next (.unseqK g thenB st tg env (.run i) k)) s
        (.next (.unseqK g thenB st' tg env .pick k)) s' ⟨tr, [], []⟩
  /-- A value head's result is WRITTEN into its predeclared binder cell
  (normalized at the cell's declared type) and the occurrence is DONE. -/
  | unseqValue {g thenB st tg env k s o bind head v loc s' tr} {i : Nat} :
      g.occs[i]? = some o → o.body = .eval bind head →
      unseqCellLoc env bind = .ok loc →
      Mem.store ctx s loc v = .ok (s', tr) →
      Step (.retV v (.unseqK g thenB st tg env (.wait i) k)) s
        (.next (.unseqK g thenB (st.set i .done) tg env .pick k)) s' ⟨tr, [], []⟩
  /-- An invocation's statement completed (its results already stored by
  the call's own phase-2 stores): the occurrence is DONE. -/
  | unseqStmtDone {g thenB st tg env k s o binds callee args} {i : Nat} :
      g.occs[i]? = some o → o.body = .invoke binds callee args →
      Step (.next (.unseqK g thenB st tg env (.wait i) k)) s
        (.next (.unseqK g thenB (st.set i .done) tg env .pick k)) s ⟨[], [], []⟩
  /-- Stage E E3: a receive's statement completed (its value already stored
  by the receive's own delivery): the occurrence is DONE. -/
  | unseqRecvDone {g thenB st tg env k s o binds ch elem} {i : Nat} :
      g.occs[i]? = some o → o.body = .recv binds ch elem →
      Step (.next (.unseqK g thenB st tg env (.wait i) k)) s
        (.next (.unseqK g thenB (st.set i .done) tg env .pick k)) s ⟨[], [], []⟩
  /-- Stage E E4: an allocation's statement completed (the fresh object already
  bound by the statement's own store): the occurrence is DONE. -/
  | unseqAllocDone {g thenB st tg env k s o bind spec} {i : Nat} :
      g.occs[i]? = some o → o.body = .allocate bind spec →
      Step (.next (.unseqK g thenB st tg env (.wait i) k)) s
        (.next (.unseqK g thenB (st.set i .done) tg env .pick k)) s ⟨[], [], []⟩
  /-- Stage E5 E5a: a wide built-in's statement completed (its results already
  stored by the statement's own phase-2 stores): the occurrence is DONE. -/
  | unseqWideDone {g thenB st tg env k s o binds spec} {i : Nat} :
      g.occs[i]? = some o → o.body = .wide binds spec →
      Step (.next (.unseqK g thenB st tg env (.wait i) k)) s
        (.next (.unseqK g thenB (st.set i .done) tg env .pick k)) s ⟨[], [], []⟩

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Config → Store → Config → Store → Prop where
  | refl (c : Config) (s : Store) : Steps c s c s
  -- The closure ERASES the labels (the run's trace is the drivers' fold).
  | tail {a sa b sb c sc tr} : Steps a sa b sb → Step ctx b sb c sc tr → Steps a sa c sc

variable {ctx}
theorem Steps.single {a b : Config} {sa sb : Store} {l : StepLabel} (h : Step ctx a sa b sb l) :
    Steps ctx a sa b sb :=
  .tail (.refl a sa) h

theorem Steps.trans {a b c : Config} {sa sb sc : Store} :
    Steps ctx a sa b sb → Steps ctx b sb c sc → Steps ctx a sa c sc := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

variable (ctx)
/-- A configuration the sequential machine considers FINISHED. The
blocked configurations (channels arc slice 1) are deliberately NOT here
(audit S12): they are relation-terminal in the per-goroutine relation
(no outgoing rule — `step_blocked*_elim`) and the sequential driver
classifies them as the deadlocked run, but they are not "finished" —
slice 2's pool machine steps them (pairing/wake), so extending this
predicate would be the wrong edit. Its only current consumer is the
`go_adequacy` scope prose. -/
def Config.terminal : Config → Prop
  | .next .stop => True
  | _ => False

variable {ctx}
/-- **The direct path is unchanged** (design note
`docs/2026-09-28_gp-method-promotion-design.md` §3 `enterFrame_declared`;
window charter row 3 — the logic team's `MaybeUpdate` pilot uses ordinary
call rules): for a callee that is a DECLARED `Func` and not an interface
anchor (every plain function and every concrete method — `methodInfoByFuncId?`
answers `none` or a non-interface receiver), whose arity the call meets, the
entry IS the function-call rule: bind the parameters, declare the results,
pin their cells, run `func`'s body in a frame naming `func.id`; no memory
access. No promotion record, no dispatch is consulted. -/
theorem enterFrame_declared {s : Store} {fid : FuncId} {argVals : List GoValue} {func : Func}
    (hf : findFunctionIn? ctx.functions fid = some func)
    (hanchor : ∀ m, methodInfoByFuncId? ctx func.id = some m → methodRecvInterfaceName? m = none)
    (harity : func.args.size = argVals.length) :
    enterFrame ctx s fid argVals = (do
      let (argsEnv, s₁) ← bindParams ctx [] s func.args.toList argVals
      let (frameEnv, s₂) ← allocDecls ctx argsEnv s₁ func.results.toList
      let resultLocs ← pinResultLocs frameEnv func.results.toList
      return (.run func frameEnv resultLocs, s₂, [])) := by
  have hdd : dynamicDispatch? ctx s func argVals.toArray = .ok (none, []) := by
    unfold dynamicDispatch?
    cases hm : methodInfoByFuncId? ctx func.id with
    | none => rfl
    | some m => simp [hanchor m hm, pure, Except.pure]
  unfold enterFrame enterFrame.plan callee?
  simp [hf, hdd, harity, Bind.bind, Except.bind, pure, Except.pure]

/-- **A frame exit reads «`fid` returned `vs`»** ([USER] Mike 2026-09-28 «Agree
on (1)» — the logic team's request 6, option 1; relayed by the [AGENT]
coordinator, cite as relayed): the frame running `fid`'s body, at its exit —
whether the body FELL OFF ITS END or RETURNED — reads its pinned result cells
as `vs` and resumes the caller on its target plans with exactly those values
(`frameFallTargets`/`frameReturnTargets`; the frame's `fid` field is
representation only: no rule reads it, the label is the result read's). A
targetless, resultless frame resumes the caller directly (`frameFall`/
`frameReturn`). -/
theorem frame_exit_returns {sh : TargetShape} {e : Expr} {ops : List Expr}
    {rest : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc} {k : Cont}
    {fid : FuncId} {s : Store} {vs : List GoValue} {tr : AccessTrace}
    (hload : loadResults ctx s results = .ok (vs, tr)) :
    Step ctx (.next (.frame ((sh, e :: ops) :: rest) tenv results [] k fid)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩
      ∧ Step ctx (.signal .ret (.frame ((sh, e :: ops) :: rest) tenv results [] k fid)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s ⟨tr, [], []⟩ :=
  ⟨.frameFallTargets hload, .frameReturnTargets hload⟩
variable (ctx)

end GoLean.GoCore.Machine
