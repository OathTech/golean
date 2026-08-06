import GoLean.GoCore.Ops

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
  (where `recover` can cancel it), and only at `.stop` becomes the
  terminal `.panicked` abort line. The old per-operator
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
statements (`assignMany`, `newValue`, make/assign/lookup for maps and
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

/-! ## Assignee desugaring -/

/-- The expression an assignment target denotes: evaluating it yields the
target *address* (`.var id` is exactly `.ref id`; `.addr e` is `e`).
`none` for unsupported assignees — the machine is silent there. -/
def assigneeExpr : Assignee → Option Expr
  | .var id => some (.ref id)
  | .addr e => some e
  | .unsupported _ => none

def assigneesExprs (targets : List Assignee) : Option (List Expr) :=
  targets.mapM assigneeExpr

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
  deriving Repr, BEq

/-- Classify an expression as a strict-operator application: the head and
the operand list, in evaluation order. `none` for the forms with their own
rules (`var`/literals/`ref`/`locLit`, short-circuit `and`/`or`) and for
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
  | _ => none

/-- Slice-expression application, after all operands are values (base, low,
high, optional max already as `Int`). Transcribed from the interpreter's
`.slice` arm. -/
def applySlice (s : ExecState) (b : GoValue) (lowValue highValue : Int)
    (maxValue : Option Int) : Except GoError (GoValue × ExecState) := do
  match b with
  | .string value => return ((← stringSlice value lowValue highValue maxValue), s)
  | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), s)
  | .addr baseLoc =>
      match ← loadLoc s baseLoc with
      | .array values =>
          return ((← sliceFromArray baseLoc values.size lowValue highValue maxValue), s)
      | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), s)
      | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
  | .array values =>
      unsupported s!"slice expression over non-addressable array value of length {values.size}"
  | other => stuck s!"expected array or slice value for slice expression, got {repr other}"

/-- Apply a strict operator to its (already evaluated, in evaluation order)
operand values. The single op table shared by the relation (as a rule
premise) and the executable `stepFn`: transcribed arm-by-arm from the
big-step interpreter's `evalExpr`, minus the recursion. Panics are Go
behavior (`.panic`); `.stuck`/`.unsupported` mean no relation rule matches
(fail closed). The catch-all arm covers head/arity mismatches unreachable
via `strictPlan`. -/
def applyStrictOp (s : ExecState) : StrictOp → List GoValue → Except GoError (GoValue × ExecState)
  | .add, [l, r] =>
      match l, r with
      | .int .., .int .. => do return ((← intBinaryResult "+" (· + ·) l r), s)
      | .float .., .float .. => do
          return ((← floatBinaryResult "+" FloatBits.fadd64 FloatBits.fadd32 l r), s)
      | .string lv, .string rv => return (.string (GoString.append lv rv), s)
      | _, _ => stuck s!"mismatched + operands: {repr l} and {repr r}"
  | .sub, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "-" FloatBits.fsub64 FloatBits.fsub32 l r), s)
      | _, _ => do return ((← intBinaryResult "-" (· - ·) l r), s)
  | .mul, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "*" FloatBits.fmul64 FloatBits.fmul32 l r), s)
      | _, _ => do return ((← intBinaryResult "*" (· * ·) l r), s)
  | .div, [l, r] =>
      match l, r with
      -- Float division dispatches BEFORE the integer divide-by-zero
      -- check: it NEVER panics — IEEE ±Inf/NaN results (design note
      -- §3.2, an envelope narrowing matching gc everywhere; pinned by
      -- floats/division-specials).
      | .float .., .float .. => do
          return ((← floatBinaryResult "/" FloatBits.fdiv64 FloatBits.fdiv32 l r), s)
      | _, _ => do
          let divisor ← valueAsInt r
          if divisor == 0 then
            panic "runtime error: integer divide by zero"
          return ((← intBinaryResult "/" Int.tdiv l r), s)
  | .mod, [l, r] => do
      let divisor ← valueAsInt r
      if divisor == 0 then
        panic "runtime error: integer divide by zero"
      return ((← intBinaryResult "%" Int.tmod l r), s)
  | .shiftLeft, [l, r] => do return ((← intShiftLeftResult l r), s)
  | .shiftRight, [l, r] => do return ((← intShiftRightResult l r), s)
  | .bitAnd, [l, r] => do return ((← intBitwiseBinaryResult "&" Nat.land l r), s)
  | .bitOr, [l, r] => do return ((← intBitwiseBinaryResult "|" Nat.lor l r), s)
  | .bitXor, [l, r] => do return ((← intBitwiseBinaryResult "^" Nat.xor l r), s)
  | .bitClear, [l, r] => do return ((← intBitClearResult l r), s)
  | .bitNeg, [v] => do return ((← intBitNegResult v), s)
  | .neg, [v] =>
      match v with
      | .int value kind => return (.int (kind.normalize (0 - value)) kind, s)
      -- IEEE negation is the sign-bit flip, never 0 - x (wrong at +0).
      | .float bits kind => return (.float (kind.normalizeBits (kind.negBits bits)) kind, s)
      | other => stuck s!"mismatched unary - operand: {repr other}"
  | .floatLit num den kind, [] =>
      -- Malformed rationals fail closed at the decoder; defensive here.
      if den == 0 then stuck "malformed float literal: zero denominator"
      else return (.float (kind.normalizeBits (kind.ratToBits num den)) kind, s)
  | .not, [v] => do return (.bool (!(← valueAsBool v)), s)
  | .eqCmp ty, [l, r] => do return (.bool (← valueEq s ty l r), s)
  | .neqCmp ty, [l, r] => do return (.bool (!(← valueEq s ty l r)), s)
  | .atMostCmp, [l, r] => do return (.bool (← valueAtMost l r), s)
  | .atLeastCmp, [l, r] => do return (.bool (← valueAtLeast l r), s)
  | .lessCmp, [l, r] => do return (.bool (← valueLess l r), s)
  | .greaterCmp, [l, r] => do return (.bool (← valueGreater l r), s)
  | .convert ty, [v] => do return ((← convertValueToTy s ty v), s)
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
      | .string value =>
          let bytes := value.bytes.map (fun b => GoValue.int (Int.ofNat b.toNat) .uint8)
          let (base, s') := s.alloc (.array bytes) (some (.array bytes.size (.int .uint8)))
          return (.slice { base := some base, offset := 0, len := bytes.size, cap := bytes.size }, s')
      | other => stuck s!"expected string operand for []byte conversion, got {repr other}"
  | .stringFromByteSlice, [v] => do
      let slice ← valueAsSlice v
      let values ← sliceVisibleValues s slice
      let mut bytes := #[]
      for value in values do
        match value with
        | .int byte .uint8 =>
            if byte < 0 || byte > 255 then
              stuck s!"malformed uint8 byte value in string conversion: {byte}"
            bytes := bytes.push (UInt8.ofNat byte.toNat)
        | other => stuck s!"expected uint8 element in string conversion, got {repr other}"
      return (.string { bytes := bytes }, s)
  | .stringFromRune, [v] => do
      return (.string (GoString.fromCodePoint (← valueAsInt v)), s)
  | .deref _, [v] => do return ((← loadLoc s (← valueAsLoc v)), s)
  | .fieldGet typeId fieldName, [v] => do
      match v with
      | .struct actualType fields =>
          if actualType != typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return (value, s)
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct value for field access, got {repr other}"
  | .fieldAddr typeId fieldName, [v] => do
      return (.addr (.field (← valueAsLoc v) typeId fieldName), s)
  | .structLit ty, vs => do return ((← buildStructValue s ty vs.toArray), s)
  | .arrayLit n elem keys, vs => do
      if keys.length != vs.length then
        stuck s!"array literal expected {keys.length} element value(s), got {vs.length}"
      return ((← buildArrayValue s n elem (keys.zip vs).toArray), s)
  | .toInterface _ dynamic, [v] => do
      -- Box with the CANONICAL dynamic type (S3): aliases resolved,
      -- identity kept, fail closed on unsupported leaves. An
      -- interface-typed source is an interface→interface conversion:
      -- the existing box (or nil) passes through unchanged — Go never
      -- double-boxes.
      let dynTy ← canonicalDynamicTy s dynamic
      match dynTy with
      | .interface _ => return (v, s)
      | _ => return (.interface dynTy v, s)
  | .typeAssert targetTy sourceTy, [v] => do
      let result ← typeAssertValue s v targetTy
      if result.2 then
        return (result.1, s)
      else
        -- Go names the first UNMET requirement when the target is an
        -- interface; a nil operand has none to report.
        let missing ←
          match resolveDefinedAliases s targetTy, v with
          | .interface interfaceName, .interface dynTy _ =>
              firstUnsatisfiedMethod? s dynTy interfaceName
          | _, _ => pure none
        panic (typeAssertPanicMessage s v targetTy sourceTy missing)
  | .indexGet, [b, i] => do
      let indexValue ← valueAsInt i
      match b with
      | .array values => return ((← arrayGet values indexValue), s)
      | .string value => return ((← stringByteGet value indexValue), s)
      | .slice slice =>
          return ((← loadLoc s (← sliceIndexLoc slice indexValue)), s)
      | other => stuck s!"expected array, slice, or string value for index access, got {repr other}"
  | .indexAddr, [b, i] => do
      let indexValue ← valueAsInt i
      match b with
      | .slice slice => return (.addr (← sliceIndexLoc slice indexValue), s)
      | .addr baseLoc =>
          match ← loadLoc s baseLoc with
          | .array values =>
              let _ ← arrayIndexNat values indexValue
              return (.addr (.index baseLoc indexValue), s)
          | .slice slice => return (.addr (← sliceIndexLoc slice indexValue), s)
          | other => stuck s!"expected array or slice base for index address, got {repr other}"
      | other => stuck s!"expected array or slice base for index address, got {repr other}"
  | .mapGet keyTy valueTy, [b, i] => do
      let map ← valueAsMap b
      let key ← normalizeValueForTy s keyTy i
      match map.base with
      -- A NIL map still hashes the key before returning the zero value.
      | none => do
          checkKeyHashable s key (isInsert := false) (nonEmpty := false)
          return ((← defaultValue s valueTy), s)
      | some baseLoc =>
          match ← loadLoc s baseLoc with
          | .mapData entries =>
              match ← mapEntryIndex? s keyTy entries key with
              | some idx =>
                  match entries[idx]? with
                  | some (_, value) => return (value, s)
                  | none => stuck s!"missing map entry at index {idx}"
              | none => return ((← defaultValue s valueTy), s)
          | other => stuck s!"expected map data, got {repr other}"
  | .sliceExpr false, [b, lo, hi] => do
      applySlice s b (← valueAsInt lo) (← valueAsInt hi) none
  | .sliceExpr true, [b, lo, hi, m] => do
      applySlice s b (← valueAsInt lo) (← valueAsInt hi) (some (← valueAsInt m))
  | .lengthOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) => return (.int n, s)
      | _ =>
          match v with
          | .array values => return (.int values.size, s)
          | .addr baseLoc =>
              match ← loadLoc s baseLoc with
              | .array values => return (.int values.size, s)
              | other => unsupported s!"len for non-array pointer value {repr other}"
          | .string value => return (.int value.length, s)
          | .slice slice =>
              validateSlice slice *> return (.int slice.len, s)
          | .map map =>
              match map.base with
              | none => return (.int 0, s)
              | some baseLoc =>
                  match ← loadLoc s baseLoc with
                  | .mapData entries => return (.int entries.size, s)
                  | other => stuck s!"expected map data, got {repr other}"
          -- len(ch) = elements queued in the buffer; nil channel = 0
          -- (spec §Length and capacity). Never panics, never blocks.
          | .chan ch =>
              match ch.base with
              | none => return (.int 0, s)
              | some baseLoc =>
                  match ← loadLoc s baseLoc with
                  | .chanData buf _ _ => return (.int buf.size, s)
                  | other => stuck s!"expected channel data, got {repr other}"
          | other => unsupported s!"len for non-array/slice/map value {repr other}"
  | .capacityOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) => return (.int n, s)
      | _ =>
          match v with
          | .array values => return (.int values.size, s)
          | .addr baseLoc =>
              match ← loadLoc s baseLoc with
              | .array values => return (.int values.size, s)
              | other => unsupported s!"cap for non-array pointer value {repr other}"
          | .slice slice =>
              validateSlice slice *> return (.int slice.cap, s)
          -- cap(ch) = buffer capacity; nil channel = 0.
          | .chan ch =>
              match ch.base with
              | none => return (.int 0, s)
              | some baseLoc =>
                  match ← loadLoc s baseLoc with
                  | .chanData _ capacity _ => return (.int capacity, s)
                  | other => stuck s!"expected channel data, got {repr other}"
          | other => unsupported s!"cap for non-array/slice value {repr other}"
  | .funcValOf fid, vs => return (.funcVal fid vs, s)
  | .minOf, v :: vs =>
      -- Float min/max stays FAIL-CLOSED (design note §9): Go's builtin
      -- is NaN-propagating with -0 < +0 — a valueLess fold would get
      -- NaN silently wrong, and no corpus case pins it yet.
      if anyFloatOperand (v :: vs) then
        unsupported "min builtin over float operands"
      else do
        let mut best := v
        for w in vs do
          if ← valueLess w best then
            best := w
        return (best, s)
  | .maxOf, v :: vs =>
      if anyFloatOperand (v :: vs) then
        unsupported "max builtin over float operands"
      else do
        let mut best := v
        for w in vs do
          if ← valueLess best w then
            best := w
        return (best, s)
  | .runeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (decodeRuneAt str off.toNat).1 .int32, s)
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | .runeSizeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (Int.ofNat (decodeRuneAt str off.toNat).2) .int, s)
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | .defaultValueOf ty, [] => do return ((← defaultValue s ty), s)
  | .nilLit typ, [] =>
      match typ with
      | none => return (.nil, s)
      | some ty =>
          match ty with
          | .slice _ => do return ((← defaultValue s ty), s)
          | .map _ _ => do return ((← defaultValue s ty), s)
          | .chan _ _ => do return ((← defaultValue s ty), s)
          | .pointer _ => return (.nil, s)
          | .unsupported feature => unsupported s!"nil literal for {feature}"
          | other => stuck s!"nil literal for non-nilable type {repr other}"
  | op, vs => stuck s!"malformed strict-operator application: {repr op} on {vs.length} operand(s)"

/-! ## Shared list operations (env-threading; used as rule premises and by
`stepFn`) -/

/-- Declare typed locals: allocate each at its default value, extending the
environment (the functional form of the old `DeclsR`). -/
def allocDecls : LocalEnv → ExecState → List Param → Except GoError (LocalEnv × ExecState)
  | env, s, [] => return (env, s)
  | env, s, p :: rest => do
      let v ← defaultValue s p.typ
      let (loc, s₁) := s.alloc v (some p.typ)
      allocDecls (env.declare p.id loc) s₁ rest

/-- Bind call parameters into a frame environment, normalized at declared
type (the functional form of the old `BindParamsR`). Arity is checked by
`enterFrame` before this runs. -/
def bindParams : LocalEnv → ExecState → List Param → List GoValue → Except GoError (LocalEnv × ExecState)
  | env, s, [], [] => return (env, s)
  | env, s, p :: ps, v :: vs => do
      let v' ← normalizeValueForTy s p.typ v
      let (loc, s₁) := s.alloc v' (some p.typ)
      bindParams (env.declare p.id loc) s₁ ps vs
  | _, _, [], _ :: _ => stuck "extra argument value"
  | _, _, _ :: _, [] => stuck "missing argument"

/-- Resolve freshly declared result names to their frame locations, at call
time (the functional form of the old `LookupsR`; D2-proper result pinning). -/
def pinResultLocs (env : LocalEnv) : List Param → Except GoError (List Loc)
  | [] => return []
  | p :: ps =>
      match env.lookup p.id with
      | some loc => do return loc :: (← pinResultLocs env ps)
      | none => stuck s!"unbound GoCore result variable: {p.id}"

/-- Load a list of locations (frame-exit result reads; old `LoadsR`). -/
def loadMany (s : ExecState) : List Loc → Except GoError (List GoValue)
  | [] => return []
  | loc :: locs => do return (← loadLoc s loc) :: (← loadMany s locs)

/-- Store values to locations pairwise (frame-exit target writes; old
`StoreManyR`). -/
def storeMany : ExecState → List Loc → List GoValue → Except GoError ExecState
  | s, [], [] => return s
  | s, loc :: locs, v :: vs => do storeMany (← storeLoc s loc v) locs vs
  | _, [], _ :: _ => stuck "extra GoCore assignment value"
  | _, _ :: _, [] => stuck "missing GoCore assignment value"

/-- Function lookup, arity check, dynamic method dispatch, parameter
binding, result declaration, and result-location pinning — everything
between "arguments are values" and "executing the callee body". One step in
the machine (frame entry). The two arity checks mirror the interpreter's
(pre-dispatch in `execFunctionCallWithLocs`, post-dispatch in
`execFunctionWithValues`). -/
def enterFrame (s : ExecState) (fid : FuncId) (argVals : List GoValue) :
    Except GoError (Func × LocalEnv × List Loc × ExecState) := do
  let func ←
    match findFunctionIn? s.functions fid with
    | some func => pure func
    | none => stuck s!"GoCore function not found: {fid.key}"
  if func.args.size != argVals.length then
    stuck s!"function {fid.key} expected {func.args.size} argument(s), got {argVals.length}"
  let (func, argVals) ←
    match ← dynamicDispatch? s func argVals.toArray with
    | some (targetFunc, targetArgs) => pure (targetFunc, targetArgs.toList)
    | none => pure (func, argVals)
  if func.args.size != argVals.length then
    stuck s!"function {func.id.key} expected {func.args.size} argument(s), got {argVals.length}"
  let (argsEnv, s₁) ← bindParams [] s func.args.toList argVals
  let (frameEnv, s₂) ← allocDecls argsEnv s₁ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  return (func, frameEnv, resultLocs, s₂)

/-! ## Wide statements: the statement-op table -/

/-- Head of a wide statement: evaluate the operand plan (targets first, as
addresses, then the value operands), then perform the state update in one
`applyStmtOp` step. -/
inductive StmtOp where
  | assignMany
  | newValue (typ : Option Ty)
  | makeSlice (elem : Ty) (hasCap : Bool)
  | makeMap (hasSpace : Bool)
  /-- `make(chan T[, n])` (channels arc slice 1): allocate an empty
  `chanData` cell (the `makeMap` shape; the cell is untyped, like
  `mapData`). Negative capacity ⇒ the recoverable run-time panic
  `makechan: size out of range` (probe p21). -/
  | makeChan (hasCap : Bool)
  | mapAssign (keyTy valueTy : Ty)
  | mapLookup (keyTy valueTy : Ty)
  | typeAssertStmt (targetTy : Ty)
  | appendSlice (elem : Ty)
  | copySlice
  | mapDelete (keyTy : Ty)
  | clearMap
  | clearSlice (elem : Ty)
  | sortSlice (elem : Ty)
  deriving Repr, BEq

/-- Classify a wide statement: the head, how many leading operands are
target addresses, and the operand expressions in evaluation order (the
interpreter's order: all targets, then the value operands). `none` for
statements with their own rules, for unsupported assignees, and for
`assignMany` arity mismatch (the executable reports those with the
interpreter's messages). -/
def stmtPlan : Stmt → Option (StmtOp × Nat × List Expr)
  | .assignMany left right => do
      if left.size != right.size then none else
      let tes ← assigneesExprs left.toList
      return (.assignMany, left.size, tes ++ right.toList)
  | .newValue target value typ => do
      let te ← assigneeExpr target
      return (.newValue typ, 1, [te, value])
  | .makeSlice target elem len cap => do
      let te ← assigneeExpr target
      return (.makeSlice elem cap.isSome, 1, [te, len] ++ cap.toList)
  | .makeMap target _ _ space => do
      let te ← assigneeExpr target
      return (.makeMap space.isSome, 1, [te] ++ space.toList)
  | .makeChan target _ capacity => do
      let te ← assigneeExpr target
      return (.makeChan capacity.isSome, 1, [te] ++ capacity.toList)
  | .mapAssign base index value keyTy valueTy =>
      return (.mapAssign keyTy valueTy, 0, [base, index, value])
  | .mapLookup target okTarget base index keyTy valueTy => do
      let te ← assigneeExpr target
      let oke ← assigneeExpr okTarget
      return (.mapLookup keyTy valueTy, 2, [te, oke, base, index])
  | .typeAssert target okTarget expr targetTy => do
      let te ← assigneeExpr target
      let oke ← assigneeExpr okTarget
      return (.typeAssertStmt targetTy, 2, [te, oke, expr])
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
  | _ => none

/-- Extract target locations from already-checked address values. -/
def locsOf : List GoValue → Except GoError (List Loc)
  | [] => return []
  | v :: vs => do return (← valueAsLoc v) :: (← locsOf vs)

/-- The choices-FREE core of `applyStmtOp`: every wide-op arm except
`appendSlice` (whose spill path consumes a capacity choice; its arm HERE
is an unreachable fail-closed `.internal` — real dispatch happens in the
wrapper, and the wrapper never routes `appendSlice` here). Extracted at
the sem-adequacy arc's notions slice (2026-08-03) so that
choices-obliviousness of wide-op success is TRUE BY CONSTRUCTION — the
correspondence kit's `∀ choices` lemmas dispatch through this core rather
than a per-arm congruence bash. Arms are verbatim from the old
`applyStmtOp` minus the trailing `choices` threading.
-/
def applyStmtOpCore (s : ExecState) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : Except GoError ExecState := do
  match op with
  | .assignMany => do
      let locs ← locsOf (vs.take nt)
      return ((← storeMany s locs (vs.drop nt)))
  | .newValue typ =>
      match vs with
      | [tv, value] => do
          let loc ← valueAsLoc tv
          let (nloc, s₁) := s.alloc value typ
          return ((← storeLoc s₁ loc (.addr nloc)))
      | _ => stuck "malformed newValue operands"
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
      let len ← natFromNonnegativeInt "runtime error: makeslice: len out of range" lenValue
      let cap ← natFromNonnegativeInt "runtime error: makeslice: cap out of range" capValue
      if cap < len then
        panic "runtime error: makeslice: cap out of range"
      let backing ← buildDefaultArrayValue s cap elem
      let (base, s₁) := s.alloc backing (some (.array cap elem))
      let loc ← valueAsLoc tv
      return ((← storeLoc s₁ loc (.slice { base := some base, offset := 0, len, cap })))
  | .makeMap hasSpace => do
      let (tv, spaceV?) ←
        match vs, hasSpace with
        | [tv], false => pure (tv, none)
        | [tv, spaceV], true => pure (tv, some spaceV)
        | _, _ => stuck "malformed makeMap operands"
      match spaceV? with
      | none => pure ()
      | some spaceV => do
          let size ← valueAsInt spaceV
          let _ ← natFromNonnegativeInt "makemap: size out of range" size
      let (base, s₁) := s.alloc (.mapData #[])
      let loc ← valueAsLoc tv
      return ((← storeLoc s₁ loc (.map { base := some base })))
  | .makeChan hasCap => do
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
            -- repo's existing makemap/makeslice narrowing.
            natFromNonnegativeInt "makechan: size out of range" size
      let (base, s₁) := s.alloc (.chanData #[] capacity false)
      let loc ← valueAsLoc tv
      return ((← storeLoc s₁ loc (.chan { base := some base })))
  | .mapAssign keyTy valueTy =>
      match vs with
      | [baseV, keyV, valueV] => do
          let map ← valueAsMap baseV
          let key ← normalizeValueForTy s keyTy keyV
          let value ← normalizeValueForTy s valueTy valueV
          match ← mapEntries s map with
          | none => panic "assignment to entry in nil map"
          | some (baseLoc, entries) =>
              let entries ←
                match ← mapEntryIndex? s keyTy entries key (isInsert := true) with
                | some i => pure (entries.set! i (key, value))
                | none => pure (entries.push (key, value))
              return ((← storeLoc s baseLoc (.mapData entries)))
      | _ => stuck "malformed mapAssign operands"
  | .mapLookup keyTy valueTy =>
      match vs with
      | [tv, okv, baseV, keyV] => do
          let map ← valueAsMap baseV
          let key ← normalizeValueForTy s keyTy keyV
          let pair ← mapLookupValue s map key keyTy valueTy
          let tloc ← valueAsLoc tv
          let okloc ← valueAsLoc okv
          let s₁ ← storeLoc s tloc pair.1
          return ((← storeLoc s₁ okloc (.bool pair.2)))
      | _ => stuck "malformed mapLookup operands"
  | .typeAssertStmt targetTy =>
      match vs with
      | [tv, okv, value] => do
          let result ← typeAssertValue s value targetTy
          let tloc ← valueAsLoc tv
          let okloc ← valueAsLoc okv
          let s₁ ← storeLoc s tloc result.1
          return ((← storeLoc s₁ okloc (.bool result.2)))
      | _ => stuck "malformed typeAssert operands"
  | .mapDelete keyTy =>
      match vs with
      | [baseV, keyV] => do
          let map ← valueAsMap baseV
          let key ← normalizeValueForTy s keyTy keyV
          match ← mapEntries s map with
          -- Nil map: no-op (the key evaluated) — but Go still HASHES the
          -- key, so an unhashable one panics here too (probed 2026-07-31).
          | none => do
              checkKeyHashable s key (isInsert := false) (nonEmpty := false)
              return (s)
          | some (baseLoc, entries) =>
              match ← mapEntryIndex? s keyTy entries key with
              | some i =>
                  return ((← storeLoc s baseLoc (.mapData (entries.eraseIdx! i))))
              | none => return (s)
      | _ => stuck "malformed mapDelete operands"
  | .clearMap =>
      match vs with
      | [baseV] => do
          let map ← valueAsMap baseV
          match ← mapEntries s map with
          | none => return (s) -- nil map: no-op
          | some (baseLoc, _) =>
              return ((← storeLoc s baseLoc (.mapData #[])))
      | _ => stuck "malformed clearMap operands"
  | .clearSlice elem =>
      -- Multi-cell in one apply step, like copySlice: a granularity-ledger
      -- entry to re-audit before any concurrency claim mentions it (R4).
      match vs with
      | [baseV] => do
          let slice ← valueAsSlice baseV
          validateSlice slice
          let zero ← defaultValue s elem
          let mut current := s
          for i in [:slice.len] do
            current ← storeLoc current (← sliceIndexLoc slice (Int.ofNat i)) zero
          return (current)
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
      -- back. Non-int
      -- elements fail closed — the frontend only emits this at integer
      -- element kinds.
      match vs with
      | [baseV] => do
          let slice ← valueAsSlice baseV
          validateSlice slice
          let mut loaded : Array (Int × IntKind) := #[]
          let mut current := s
          for i in [:slice.len] do
            match ← loadLoc current (← sliceIndexLoc slice (Int.ofNat i)) with
            | .int v kind => loaded := loaded.push (v, kind)
            | other => stuck s!"sortSlice expected int element, got {repr other}"
          -- `sortLe`, not `List.mergeSort`: the latter is WF-compiled and
          -- kernel-irreducible (de-WF, 2026-08-03; output provably agrees).
          let sorted := (sortLe (fun a b => a.1 ≤ b.1) loaded.toList).toArray
          for i in [:slice.len] do
            match sorted[i]? with
            | some (v, kind) =>
                current ← storeLoc current (← sliceIndexLoc slice (Int.ofNat i)) (.int v kind)
            | none => stuck "sortSlice element count mismatch"
          return (current)
      | _ => stuck "malformed sortSlice operands"
  | .copySlice =>
      match vs with
      | [tv, dstV, srcV] => do
          let dstSlice ← valueAsSlice dstV
          let srcSlice ← valueAsSlice srcV
          validateSlice dstSlice
          validateSlice srcSlice
          let count := Nat.min dstSlice.len srcSlice.len
          let mut values := #[]
          for i in [:count] do
            values := values.push (← loadLoc s (← sliceIndexLoc srcSlice (Int.ofNat i)))
          let mut current := s
          let mut i := 0
          for value in values do
            current ← storeLoc current (← sliceIndexLoc dstSlice (Int.ofNat i)) value
            i := i + 1
          let tloc ← valueAsLoc tv
          return ((← storeLoc current tloc (.int (Int.ofNat count))))
      | _ => stuck "malformed copySlice operands"
  | .appendSlice _ =>
      throw (.internal "applyStmtOpCore: appendSlice dispatches through applyStmtOp")

/-- Apply a wide statement's head to its evaluated operands (`nt` leading
target addresses, then values). One state-update step. `appendSlice`'s
spill path consumes a capacity choice — the second nondeterministic point
— and is the ONLY arm that touches the stream; everything else dispatches
to the choices-free `applyStmtOpCore`. -/
def applyStmtOp (s : ExecState) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : Except GoError (ExecState × Choices) := do
  match op with
  | .appendSlice elem =>
      match vs with
      | [tv, sliceV, elemsV] => do
          let slice ← valueAsSlice sliceV
          let elems ← valueAsSlice elemsV
          validateSlice slice
          validateSlice elems
          let elemValues ← sliceVisibleValues s elems
          let newLen := slice.len + elemValues.size
          let tloc ← valueAsLoc tv
          if newLen <= slice.cap then
            let mut current := s
            let mut i := 0
            for value in elemValues do
              match slice.base with
              | some base =>
                  current ← storeLoc current
                    (.index base (Int.ofNat (slice.offset + slice.len + i))) value
                  i := i + 1
              | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place"
            return ((← storeLoc current tloc (.slice { slice with len := newLen })), choices)
          else
            let oldValues ← sliceVisibleValues s slice
            -- The capacity ENVELOPE is [newLen, appendSpillUpper] (the
            -- statement and containment argument live on
            -- `appendSpillUpper`, Ops.lean — arc-final audit F2 /
            -- BUG-021, replacing growth+[0,8), which go1.26.5 escapes
            -- in both directions). The choice is offset so the EMPTY
            -- stream (extra = 0) keeps the growth-formula point — the
            -- strict lane's deterministic behavior is unchanged — while
            -- extra ranges bijectively over the whole envelope.
            let width := appendSpillWidth slice.cap newLen
            let (extra, choices) := choices.consume width
            let newCap := newLen +
              ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            let backing ← buildAppendBackingValue s elem oldValues elemValues newCap
            let (base, current) := s.alloc backing (some (.array newCap elem))
            return ((← storeLoc current tloc
              (.slice { base := some base, offset := 0, len := newLen, cap := newCap })), choices)
      | _ => stuck "malformed appendSlice operands"
  | op => do return ((← applyStmtOpCore s op nt vs), choices)

/-- The entries a `mapRange` iterates: snapshot of the map's data cell
(empty for a nil map). -/
def mapRangeEntries (s : ExecState) (v : GoValue) :
    Except GoError (Array (GoValue × GoValue)) := do
  let map ← valueAsMap v
  match map.base with
  | none => return #[]
  | some base =>
      match ← loadLoc s base with
      | .mapData es => return es
      | other => stuck s!"expected map data for range, got {repr other}"

/-- Are all entries of a `mapRange` snapshot self-normalized at the range
key/value types — keys at `keyTy`, values at `valTy`? The pick-free
typing check the snapshot step fails closed on (sem-adequacy arc slice 3,
2026-08-04): `mapAssign` only ever stores normalized keys AND values, so
every legitimate snapshot passes identically (differential-validated),
while an ill-typed entry — which would make `mapIterNext`'s per-pick
`bindIterVars` normalization succeed at one pick and fail at another —
is rejected before any pick exists. Structural over the entry list;
kernel-reducible (`isNormalForTyFuel`'s contract). Note the recorded
design named only the KEYS; the value check is forced by the same
obstruction one constructor over — `bindIterVars` normalizes the VALUE
at `valTy` whenever a value variable is bound, so key-only validation
leaves iteration success pick-dependent through the values. -/
def snapshotEntriesSelfNormalizedList (types : TypeEnv) (keyTy valTy : Ty) :
    List (GoValue × GoValue) → Bool
  | [] => true
  | (k, v) :: rest =>
      isNormalForTy types keyTy k && isNormalForTy types valTy v
        && snapshotEntriesSelfNormalizedList types keyTy valTy rest

@[inherit_doc snapshotEntriesSelfNormalizedList]
def snapshotEntriesSelfNormalized (types : TypeEnv) (keyTy valTy : Ty)
    (entries : Array (GoValue × GoValue)) : Bool :=
  snapshotEntriesSelfNormalizedList types keyTy valTy entries.toList

/-- The validated snapshot step's premise function, shared VERBATIM by
`stepFn`'s `mapRangeK` arm and rule `Step.mapRangeSnapshot`: read the
ranged map's entries, then fail CLOSED unless every entry is
self-normalized at the range key/value types. -/
def mapRangeSnapshotEntries (s : ExecState) (keyTy valTy : Ty) (v : GoValue) :
    Except GoError (Array (GoValue × GoValue)) := do
  let entries ← mapRangeEntries s v
  if snapshotEntriesSelfNormalized s.types keyTy valTy entries then
    return entries
  else
    throw (.stuck s!"map range snapshot entry not self-normalized at range \
key/value types ({repr keyTy}, {repr valTy})")

/-- Declare a `mapRange` iteration's key/value variables in a fresh scope
(normalized at the range types), mirroring the interpreter's per-iteration
`declareLocal`s. -/
def bindIterVars (env : LocalEnv) (s : ExecState) (keyVar valVar : Option String)
    (keyTy valTy : Ty) (key value : GoValue) :
    Except GoError (LocalEnv × ExecState) := do
  let (env, s) ←
    match keyVar with
    | some name => do
        let kv ← normalizeValueForTy s keyTy key
        let (loc, s') := s.alloc kv (some keyTy)
        pure (env.declare name loc, s')
    | none => pure (env, s)
  match valVar with
  | some name => do
      let vv ← normalizeValueForTy s valTy value
      let (loc, s') := s.alloc vv (some valTy)
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

/-- Head of a channel statement (send/receive/close). `elem` is the
element type: sends normalize the value at it (the `mapAssign` key/value
discipline, so buffered values are self-normalized); receives build the
closed-channel zero value from it. -/
inductive ChanStOp where
  | send (elem : Ty)
  | recv (elem : Ty)
  | close
  deriving Repr, BEq

/-- Classify a channel statement: op head, leading target-address count,
operands in evaluation order — channel THEN value for a send (pinned by
`ordinary-send-eval-order`), target addresses THEN channel for a receive
(Go's assignment operand order, pinned by `ordinary-receive-eval-order`).
`none` for unsupported assignees and >2 receive targets (fail closed). -/
def chanPlan : Stmt → Option (ChanStOp × Nat × List Expr)
  | .chanSend ch value elem => some (.send elem, 0, [ch, value])
  | .chanRecv targets ch elem => do
      if targets.size > 2 then none else
      let tes ← assigneesExprs targets.toList
      return (.recv elem, targets.size, tes ++ [ch])
  | .closeChan ch => some (.close, 0, [ch])
  | _ => none

/-- The channel-statement plan and the wide-statement plan classify
DISJOINT statements: a statement `chanPlan` recognizes is never one
`stmtPlan` recognizes. `step_det`'s rule-disjointness sweep cites this
(as a conditional simp lemma) to refute the generic-statement cross
pairs without casing the statement. -/
theorem stmtPlan_of_chanPlan {stmt : Stmt} {p : ChanStOp × Nat × List Expr}
    (h : chanPlan stmt = some p) : stmtPlan stmt = none := by
  cases stmt <;> simp_all [chanPlan, stmtPlan]

/-- Load a channel's data cell: (buffer, capacity, closed). -/
def chanCell (s : ExecState) (loc : Loc) :
    Except GoError (Array GoValue × Nat × Bool) := do
  match ← loadLoc s loc with
  | .chanData buf capacity closed => return (buf, capacity, closed)
  | other => stuck s!"expected channel data, got {repr other}"

/-- The values a receive delivers to its target list: the received value,
plus the comma-ok Bool when the form has two targets. -/
def recvStores (v : GoValue) (ok : Bool) : Nat → List GoValue
  | 2 => [v, .bool ok]
  | 1 => [v]
  | _ => []

/-- One `select` clause with its entry-time operands EVALUATED (spec
§Select statements, step 1): the channel value (and send value) are
pinned; receive targets stay as their assignee expressions — evaluated
only after selection (step 4). The payload of the readiness step and of
the `.blockedSelect` configuration. -/
inductive EvClause where
  | sendEv (chv v : GoValue) (elem : Ty) (body : Stmt)
  | recvEv (chv : GoValue) (targets : List Expr) (elem : Ty) (body : Stmt)
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
    Except GoError (List EvClause)
  | [], [] => return []
  | (.send _ _ elem, body) :: rest, chv :: vv :: vs => do
      return .sendEv chv vv elem body :: (← evalClauses rest vs)
  | (.recv targets _ elem, body) :: rest, chv :: vs => do
      match assigneesExprs targets.toList with
      | some tes => return .recvEv chv tes elem body :: (← evalClauses rest vs)
      | none => throw (.unsupported "unsupported select receive target assignee")
  | _, _ => stuck "malformed select operand values"

/-- Clause readiness — a pure function of the channel cells (spec step 2
"can proceed", with one runtime-pinned subtlety: a SEND on a closed
channel counts as READY and panics when selected — probe p23;
`select.go`'s pass-1 send check tests closed first). A nil channel is
never ready. -/
def clauseReady (s : ExecState) : EvClause → Except GoError Bool
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
def readyClauses (s : ExecState) : List EvClause → Except GoError (List EvClause)
  | [] => return []
  | c :: rest => do
      let tail ← readyClauses s rest
      if ← clauseReady s c then return c :: tail else return tail

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
  .interface (.defined runtimeErrorTypeId) (.string (GoString.fromLeanString msg))

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

/-- Constructive ASCII decode for abort rendering. Core's
`String.fromUTF8?` depends on `Classical.choice` (its validation proofs),
and the machine-correspondence theorems are pinned constructive
(`proofs/Audit.lean`) — so abort rendering covers single-line ASCII
payloads and fails closed on any byte ≥ 0x80 AND on an embedded newline
(Go routes string payloads through `printindented`, so its FIRST abort
line stops at a `\n` — a multi-line payload has no one-line rendering to
pin; pre-merge audit 2026-07-25, BUG-004): a rejected payload aborting is
a visible unsupported, never a wrong message. -/
def asciiString? (bytes : Array UInt8) : Option String :=
  bytes.foldl
    (fun acc b => acc.bind fun out =>
      if b < 0x80 && b != 0x0A then some (out.push (Char.ofNat b.toNat)) else none)
    (some "")

/-- Does `dynTy` carry `name() string` — the shape of BOTH interfaces Go's
`preprintpanics` consults (`error`'s `Error() string` and `stringer`'s
`String() string`)? Checked against the METHOD SET directly rather than
through a wire interface declaration: those two interfaces are built into
the runtime, so the rewrite applies whether or not the program ever
mentions `error`/`fmt.Stringer`. -/
def hasNoArgStringMethod (state : ExecState) (dynTy : Ty) (name : String) : Bool :=
  match concreteMethodForDynamic? state dynTy name with
  | some (info, _) =>
      match concreteMethodSignature? state info with
      | some (params, results, variadic) =>
          params.isEmpty && results == #[Ty.string] && !variadic
      | none => false
  | none => false

/-- The payload rewrite Go performs before printing: `v.Error()` for an
`error`, `v.String()` for a `fmt.Stringer`. -/
def panicPayloadIsRewritten (state : ExecState) (dynTy : Ty) : Bool :=
  hasNoArgStringMethod state dynTy "Error" || hasNoArgStringMethod state dynTy "String"

/-- Render a panic payload as Go's first abort line renders it (after
`panic: `).

Go's `preprintpanics` REWRITES the payload to `v.Error()` / `v.String()`
before `printpanicval` runs, so `printanycustomtype`'s `main.T(v)` shape
applies only to a defined type with NEITHER method. The rewritten form
would require CALLING a method at abort time — which the terminal rule
cannot do — so a payload whose dynamic type implements either interface
fails CLOSED here (pre-merge audit 2026-07-31, finding 3; the unconditional
`main.T(v)` arm this replaces was a fail-closed → wrong-answer regression).
Everything else not pinned is `none` for the same reason. -/
def renderPanicPayload (state : ExecState) : GoValue → Option String
  | .nil => some "nil"
  | .interface (.defined id) (.string s) =>
      if id == runtimeErrorTypeId then asciiString? s.bytes else none
  | .interface .string (.string s) => asciiString? s.bytes
  | .interface (.int dkind) (.int v kind) =>
      if dkind == kind then some (toString v) else none
  | .interface .bool (.bool b) => some (if b then "true" else "false")
  -- A DEFINED-type payload renders qualified with Go's
  -- `printanycustomtype` shape: `main.Code(7)` (BUG-004 item 2 — the
  -- identity is modeled since the interfaces campaign; the KEY is
  -- package-qualified by the frontend, so it renders verbatim). Only
  -- the int-underlying form is pinned; other underlyings stay closed.
  | .interface (.defined name) (.int v _) =>
      if name == runtimeErrorTypeId then
        none
      else if panicPayloadIsRewritten state (.defined name) then
        none -- Error()/String() would have to be CALLED: fail closed
      else
        some s!"{name.key}({v})"
  | _ => none

/-- Go's first abort line for a panic chain. The `[recovered, repanicked]`
collapse is decided by the runtime via eface IDENTITY — a bitwise compare
of the interface's type word AND data pointer (`preprintpanics`,
runtime/panic.go), NOT semantic equality (pre-merge audit 2026-07-25;
the §A3 probe that suggested otherwise was constant-folded — `"or"+"ig"`
shares a static eface, `mk("or","ig")` at runtime does not). Value-level
state decides only one direction: structurally UNEQUAL payloads can never
share a box, so ` [recovered]` is certain there; structurally EQUAL
payloads may or may not collapse (`panic(recover())` and constant
literals do, runtime-computed equal values do not) — fail closed
(BUG-004). -/
def renderPanicHead (state : ExecState) (first : PanicEntry) (rest : List PanicEntry) :
    Option String :=
  (renderPanicPayload state first.value).bind fun base =>
    if first.recovered then
      match rest with
      | e :: _ =>
          if e.value == first.value then
            none -- boxing identity unmodeled: collapse undecidable (BUG-004)
          else
            some (base ++ " [recovered]")
      | [] => some (base ++ " [recovered]")
    else
      some base

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
  `wrapper` marks a frame entered through a
  compiler-SYNTHESIZED promotion wrapper (wire flag `"wrapper": true`,
  design note 2026-08-05 D1.3): gc marks the same frames
  `abi.FuncIDWrapper`, and its recover walk skips them ("there must be
  exactly one non-wrapper frame between gopanic and gorecover",
  runtime/panic.go) — `recoverResult` is the ONLY consumer; every other
  rule treats a wrapper frame as an ordinary frame (BUG-015, arc-final
  audit F1, 2026-08-06). Defaults to `false` so hand-built programs and
  user-code frames are unmarked; call entries pass the resolved
  callee's flag. Positioned after `k` so the default applies at every
  pre-existing construction site. -/
  | frame (targets : List Loc) (results : List Loc)
      (defers : List (GoValue × List GoValue)) (k : Cont) (wrapper : Bool := false)
  /-- Awaiting a deferred call's callee value. -/
  | deferCalleeK (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting a deferred call's arguments; they are evaluated AT DEFER
  TIME (Go), then the pending call — the callee VALUE plus argument
  values — is prepended to the innermost frame's chain. A nil callee
  REGISTERS fine and panics only at invocation (pre-merge audit
  2026-07-25; Go's rule). -/
  | deferArgsK (callee : GoValue) (vals : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Breakable scope (`Stmt.breakable`): catches `breaking`, passes
  `continuing`/`returning` through. -/
  | breakableK (k : Cont)
  /-- Label scope (`Stmt.labeled`, control-flow slice): catches
  `breakingTo` at a matching label; a `loop`/`mapIterK` whose IMMEDIATE
  continuation is a matching `labelK` is the labeled loop `continuingTo`
  targets (`contHeadLabel`). Bare `breaking`/`continuing`/`returning`
  pass through — a bare break targets the innermost for/switch
  regardless of labels. -/
  | labelK (label : String) (k : Cont)
  /-- Call-through-value (§8): awaiting a target address; then remaining
  targets, then the callee expression. -/
  | callValTargetsK (callee : Expr) (locs : List Loc) (pending : List Expr)
      (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting the CALLEE value (a `funcVal`, or `nil` → panic). -/
  | callValCalleeK (locs : List Loc) (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting an argument of a value call. Carries the callee VALUE: a
  funcVal's captures are prepended at frame entry; a nil callee evaluates
  every argument first and panics at the invocation step (Go's order —
  pre-merge audit 2026-07-25). -/
  | callValArgsK (callee : GoValue) (locs : List Loc)
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
  /-- Awaiting an assignment target address; the RHS is not yet evaluated
  (Go's order: target location first, then value). -/
  | assignTargetK (rhs : Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting an assignment RHS value; the store to `loc` is the next
  step. -/
  | assignStoreK (loc : Loc) (k : Cont)
  /-- Awaiting a call target address; then remaining targets, then
  arguments, then frame entry. -/
  | callTargetsK (fid : FuncId) (locs : List Loc) (pending : List Expr)
      (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting a call argument value; then remaining arguments, then frame
  entry. -/
  | callArgsK (fid : FuncId) (locs : List Loc) (vals : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Wide-statement operand evaluation: the leading `ntargets` operands are
  target addresses (checked as they arrive); `done` holds evaluated
  operands most recent first. Ends in one `applyStmtOp` step. -/
  | stmtOpK (op : StmtOp) (ntargets : Nat) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting the `mapRange` map value; the snapshot step follows. -/
  | mapRangeK (keyVar valVar : Option String) (keyTy valTy : Ty)
      (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- `mapRange` iteration context: `remaining` is the unconsumed snapshot.
  The pick-next step is nondeterministic (any in-range index); `break`
  finishes the range, `continue` proceeds, `return` unwinds. The
  per-iteration scope is the entered body's environment; this frame carries
  the *original* `env` for subsequent iterations (scope exit by discard,
  as everywhere in the CEK design). -/
  | mapIterK (keyVar valVar : Option String) (keyTy valTy : Ty) (body : Stmt)
      (remaining : Array (GoValue × GoValue)) (env : LocalEnv) (k : Cont)
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
  `stmtOpK` discipline — leading `ntargets` operands are target
  addresses, checked as they arrive — ending in one `applyChanOp` step
  whose outcome may be next / panicking / blocked. Appended at the END
  of the inductive (with its two select siblings) so positional case
  tags in the correspondence proofs stay stable. -/
  | chanStK (op : ChanStOp) (ntargets : Nat) (done : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- `select` entry-time operand evaluation (spec step 1, source order);
  ends in one `applySelect` readiness/commit step. -/
  | selectOpsK (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
      (done : List GoValue) (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- A selected receive clause's target evaluation (spec step 4: LHS
  evaluated only AFTER the communication committed): the received value
  and ok flag are pinned; target addresses accumulate; the final step
  stores and enters the clause body. -/
  | selectRecvK (v : GoValue) (ok : Bool) (locs : List Loc)
      (pending : List Expr) (body : Stmt) (env : LocalEnv) (k : Cont)

/-- The continuation for entering a `.seqn`: under a same-env governing
sequence, SPLICE the statements into it (D1) — Go statement lists splice
and only blocks scope. Any other continuation wraps in a fresh seq node. -/
def seqCont (ss : List Stmt) (env : LocalEnv) : Cont → Cont
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

/-- The label carried by the HEAD of a continuation, if it is a `labelK`.
The labeled-loop test for `continuingTo`: the frontend attaches
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
(LIFO). Statement-shaped continuations are walked through; a `defer`
outside any frame (or under an expression frame, which cannot contain a
statement) has no rule — fail closed. -/
def pushDefer (d : GoValue × List GoValue) : Cont → Option Cont
  | .frame t r ds k w => some (.frame t r (d :: ds) k w)
  | .seq rest env k => (pushDefer d k).map (Cont.seq rest env)
  | .loop c b env k => (pushDefer d k).map (Cont.loop c b env)
  | .breakableK k => (pushDefer d k).map Cont.breakableK
  | .labelK name k => (pushDefer d k).map (Cont.labelK name)
  | .mapIterK kv vv kt vt b rem env k =>
      (pushDefer d k).map (Cont.mapIterK kv vv kt vt b rem env)
  | _ => none

/-- One unwinding step through a continuation frame: every frame that is
not a call frame, a suspended-chain marker, or `.stop` is stripped with
the chain unchanged — statement glue AND expression frames (a panic can
surface mid-expression, unlike `break`/`continue`/`return`). The three
`none` heads each have their own unwinding rules. -/
def panicPassthrough : Cont → Option Cont
  | .seq _ _ k => some k
  | .loop _ _ _ k => some k
  | .breakableK k => some k
  | .labelK _ k => some k
  | .mapIterK _ _ _ _ _ _ _ k => some k
  | .strictK _ _ _ _ k => some k
  | .andK _ _ k => some k
  | .orK _ _ k => some k
  | .boolK k => some k
  | .ifK _ _ _ k => some k
  | .whileK _ _ _ k => some k
  | .assignTargetK _ _ k => some k
  | .assignStoreK _ k => some k
  | .callTargetsK _ _ _ _ _ k => some k
  | .callArgsK _ _ _ _ _ k => some k
  | .stmtOpK _ _ _ _ _ k => some k
  | .mapRangeK _ _ _ _ _ _ k => some k
  | .callValTargetsK _ _ _ _ _ k => some k
  | .callValCalleeK _ _ _ k => some k
  | .callValArgsK _ _ _ _ _ k => some k
  | .deferCalleeK _ _ k => some k
  | .deferArgsK _ _ _ _ k => some k
  | .panicArgK k => some k
  | .chanStK _ _ _ _ _ k => some k
  | .selectOpsK _ _ _ _ _ k => some k
  | .selectRecvK _ _ _ _ _ _ k => some k
  | .frame _ _ _ _ _ => none
  | .panicResumeK _ _ => none
  | .stop => none

/-- Below the ONE non-wrapper frame of the recover walk: statement glue
and WRAPPER frames are transparent on the way down to the
suspended-chain marker (`recoverResult`'s docstring has the rule). A
non-wrapper frame or `.stop` refutes; `.panicResumeK` resolves. Returns
the payload and the rebuilt continuation with the newest entry marked.
Glue must be skipped here because a wrapper's BODY glue sits between the
promoted method's frame and the wrapper's frame; for wrapper-free
continuations this arm is only ever reached with the marker DIRECTLY
below (the panic-drain rule constructs the deferred frame on the marker,
and nothing inserts glue below an entered frame), so behavior on
wrapper-free programs is unchanged. -/
def recoverThroughWrappers : Cont → Option (GoValue × Cont)
  | .panicResumeK chain k =>
      (markNewestRecovered chain).map (fun (v, chain') => (v, .panicResumeK chain' k))
  | .frame t r ds k true =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .frame t r ds k' true))
  | .frame _ _ _ _ false => none
  | .stop => none
  | .seq a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .seq a b k'))
  | .loop a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .loop a b c k'))
  | .breakableK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .breakableK k'))
  | .labelK a k => (recoverThroughWrappers k).map (fun (v, k') => (v, .labelK a k'))
  | .mapIterK a b c d e f g k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .mapIterK a b c d e f g k'))
  | .strictK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .strictK a b c d k'))
  | .andK a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .andK a b k'))
  | .orK a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .orK a b k'))
  | .boolK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .boolK k'))
  | .ifK a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .ifK a b c k'))
  | .whileK a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .whileK a b c k'))
  | .assignTargetK a b k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .assignTargetK a b k'))
  | .assignStoreK a k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .assignStoreK a k'))
  | .callTargetsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callTargetsK a b c d e k'))
  | .callArgsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callArgsK a b c d e k'))
  | .stmtOpK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .stmtOpK a b c d e k'))
  | .mapRangeK a b c d e f k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .mapRangeK a b c d e f k'))
  | .callValTargetsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callValTargetsK a b c d e k'))
  | .callValCalleeK a b c k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callValCalleeK a b c k'))
  | .callValArgsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callValArgsK a b c d e k'))
  | .deferCalleeK a b k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .deferCalleeK a b k'))
  | .deferArgsK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .deferArgsK a b c d k'))
  | .panicArgK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .panicArgK k'))
  | .chanStK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .chanStK a b c d e k'))
  | .selectOpsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .selectOpsK a b c d e k'))
  | .selectRecvK a b c d e f k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .selectRecvK a b c d e f k'))

/-- The `recover()` builtin (arc doc §A1; wrapper transparency added at
the arc-final audit F1/BUG-015, 2026-08-06): walk the continuation to the
first NON-WRAPPER call frame — gc's rule, verbatim from runtime/panic.go
(`gorecover`): "there must be exactly one non-wrapper frame between
gopanic and gorecover", with compiler-synthesized wrapper frames
(`abi.FuncIDWrapper`; our wire's `"wrapper": true` promotion wrappers)
skipped. Recover applies exactly when that frame sits on a `panicResumeK`
whose newest entry is not yet recovered, with only glue and wrapper
frames between — the shape the panic-drain rule builds (directly, or
through the wrapper's forwarding call). Returns the recovered payload and
the continuation with the entry marked, or `.nil` and the continuation
unchanged (never stuck: `recover` outside a panic-run deferred function
is a defined no-op in Go). A wrapper frame ABOVE the walk's start cannot
occur from lowered Go (`recover()` never appears textually inside a
synthesized wrapper); for totality it is transparent there too. -/
def recoverResult : Cont → GoValue × Cont
  | .frame t r ds k false =>
      (match recoverThroughWrappers k with
       | some (v, k') => (v, .frame t r ds k' false)
       | none => (.nil, .frame t r ds k false))
  | .frame t r ds k true =>
      let (v, k') := recoverResult k
      (v, .frame t r ds k' true)
  | k@.stop => (.nil, k)
  | k@(.panicResumeK _ _) => (.nil, k)
  | .seq a b k => let (v, k') := recoverResult k; (v, .seq a b k')
  | .loop a b c k => let (v, k') := recoverResult k; (v, .loop a b c k')
  | .breakableK k => let (v, k') := recoverResult k; (v, .breakableK k')
  | .labelK a k => let (v, k') := recoverResult k; (v, .labelK a k')
  | .mapIterK a b c d e f g k =>
      let (v, k') := recoverResult k; (v, .mapIterK a b c d e f g k')
  | .strictK a b c d k => let (v, k') := recoverResult k; (v, .strictK a b c d k')
  | .andK a b k => let (v, k') := recoverResult k; (v, .andK a b k')
  | .orK a b k => let (v, k') := recoverResult k; (v, .orK a b k')
  | .boolK k => let (v, k') := recoverResult k; (v, .boolK k')
  | .ifK a b c k => let (v, k') := recoverResult k; (v, .ifK a b c k')
  | .whileK a b c k => let (v, k') := recoverResult k; (v, .whileK a b c k')
  | .assignTargetK a b k => let (v, k') := recoverResult k; (v, .assignTargetK a b k')
  | .assignStoreK a k => let (v, k') := recoverResult k; (v, .assignStoreK a k')
  | .callTargetsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callTargetsK a b c d e k')
  | .callArgsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callArgsK a b c d e k')
  | .stmtOpK a b c d e k => let (v, k') := recoverResult k; (v, .stmtOpK a b c d e k')
  | .mapRangeK a b c d e f k =>
      let (v, k') := recoverResult k; (v, .mapRangeK a b c d e f k')
  | .callValTargetsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callValTargetsK a b c d e k')
  | .callValCalleeK a b c k =>
      let (v, k') := recoverResult k; (v, .callValCalleeK a b c k')
  | .callValArgsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callValArgsK a b c d e k')
  | .deferCalleeK a b k => let (v, k') := recoverResult k; (v, .deferCalleeK a b k')
  | .deferArgsK a b c d k =>
      let (v, k') := recoverResult k; (v, .deferArgsK a b c d k')
  | .panicArgK k => let (v, k') := recoverResult k; (v, .panicArgK k')
  | .chanStK a b c d e k =>
      let (v, k') := recoverResult k; (v, .chanStK a b c d e k')
  | .selectOpsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .selectOpsK a b c d e k')
  | .selectRecvK a b c d e f k =>
      let (v, k') := recoverResult k; (v, .selectRecvK a b c d e f k')

/-- Control configurations (the Iris `Expr` projection; the `ExecState` is
the paired `Step` component, as before). New over the old relation:
`evalE` (expression under evaluation) and `retV` (value delivery). The
terminal remains `.next .stop`; `retV` never reaches `.stop` because an
expression always evaluates under at least one frame. -/
inductive Config where
  | exec (stmt : Stmt) (env : LocalEnv) (k : Cont)
  | evalE (e : Expr) (env : LocalEnv) (k : Cont)
  | retV (v : GoValue) (k : Cont)
  | next (k : Cont)
  | breaking (k : Cont)
  | continuing (k : Cont)
  | returning (k : Cont)
  /-- `break L` travelling outward to the `labelK` for `L` (control-flow
  slice). Strips statement frames like `.breaking`, but is caught only by
  the MATCHING label; never crosses a call frame (`go/types` guarantees
  enclosure — the machine fails closed there). -/
  | breakingTo (label : String) (k : Cont)
  /-- `continue L` travelling outward to the loop labeled `L`: caught by a
  `loop`/`mapIterK` whose immediate continuation is the matching
  `labelK` (`contHeadLabel`). -/
  | continuingTo (label : String) (k : Cont)
  /-- Unwinding: a panic (chain, arc doc §A1) travelling outward through
  the continuation. Frames strip; call frames run their defers (which is
  where `recover` can catch it); `.stop` renders the terminal abort. -/
  | panicking (chain : List PanicEntry) (k : Cont)
  /-- The terminal abort: Go's first `panic: ` line. No outgoing rule —
  which is exactly what keeps `Progress`'s statement meaning "verified ⇒
  no UNRECOVERED panic" (the unwinding arc retired panic-as-teleport;
  `.panicking` is the recoverable, non-terminal form). -/
  | panicked (msg : String)
  -- Blocked configurations (channels arc slice 1, design of record D7:
  -- "blocked goroutines are blocked-Config shapes; NO waiter queues in
  -- channel state"). NO outgoing rules in the per-goroutine relation — in
  -- slice 2's ThreadPool the PAIRING/wake steps live at the pool level,
  -- and per-goroutine relation-silence here is what makes that extension
  -- additive. In this zero-scheduler slice the driver classifies any
  -- blocked configuration as the deadlocked run (`GoError.deadlock`):
  -- one blocked goroutine with no siblings IS Go's "all goroutines are
  -- asleep" state. Payloads carry what a future pairing step needs
  -- (channel identity, in-flight value, delivery targets); `ch = none` is
  -- the nil channel (blocks forever — no partner can exist).
  | blockedSend (ch : Option Loc) (v : GoValue) (k : Cont)
  | blockedRecv (ch : Option Loc) (locs : List Loc) (elem : Ty) (k : Cont)
  | blockedSelect (clauses : List EvClause) (env : LocalEnv) (k : Cont)

/-- Apply a channel statement's head to its evaluated operands (`nt`
leading target addresses, then values; the receive's channel operand is
LAST). One step; the outcome is a configuration — `.next k` on success,
`.panicking` for the channel panics (send-on-closed / close-of-closed /
close-of-nil — REAL recoverable Go panics, D4; messages are gc's realized
strings, probes p01-p03), or a `.blocked*` shape where Go blocks (nil
channel; unbuffered/full send; open-empty receive). Shared verbatim by
rule `Step.chanStApply` and `stepFn`'s `chanStK` apply arm. An `.error
(.panic msg)` result (a nil TARGET address surfacing through `locsOf`)
becomes `.panicking` at the caller, mirroring `stmtOpApplyPanic`. -/
def applyChanOp (s : ExecState) (op : ChanStOp) (nt : Nat) (vs : List GoValue)
    (k : Cont) : Except GoError (Config × ExecState) := do
  match op, vs with
  | .send elem, [chv, vv] => do
      let ch ← valueAsChan chv
      -- Normalize at the element type up front (the mapAssign discipline;
      -- for the blocked shapes the pinned value travels normalized).
      let v' ← normalizeValueForTy s elem vv
      match ch.base with
      | none => return (.blockedSend none v' k, s)
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [⟨runtimeErrorValue "send on closed channel", false⟩] k, s)
          else if buf.size < capacity then do
            let s' ← storeLoc s loc (.chanData (buf.push v') capacity closed)
            return (.next k, s')
          else
            return (.blockedSend (some loc) v' k, s)
  | .recv elem, vs => do
      let locs ← locsOf (vs.take nt)
      match vs.drop nt with
      | [chv] => do
          let ch ← valueAsChan chv
          match ch.base with
          | none => return (.blockedRecv none locs elem k, s)
          | some loc => do
              let (buf, capacity, closed) ← chanCell s loc
              match buf[0]? with
              | some v => do
                  -- FIFO dequeue; a closed channel drains its buffer
                  -- with ok = true before yielding zeros (probe p06).
                  let s₁ ← storeLoc s loc (.chanData (buf.eraseIdx! 0) capacity closed)
                  let s₂ ← storeMany s₁ locs (recvStores v true locs.length)
                  return (.next k, s₂)
              | none =>
                  if closed then do
                    let zero ← defaultValue s elem
                    let s₁ ← storeMany s locs (recvStores zero false locs.length)
                    return (.next k, s₁)
                  else
                    return (.blockedRecv (some loc) locs elem k, s)
      | _ => stuck "malformed chanRecv operands"
  | .close, [chv] => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return (.panicking [⟨runtimeErrorValue "close of nil channel", false⟩] k, s)
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [⟨runtimeErrorValue "close of closed channel", false⟩] k, s)
          else do
            let s' ← storeLoc s loc (.chanData buf capacity true)
            return (.next k, s')
  | op, vs => stuck s!"malformed channel-operator application: {repr op} on {vs.length} operand(s)"

/-- Commit the ONE ready clause of a `select` (spec step 3): perform its
communication, then enter the body — for a receive with targets, via the
`selectRecvK` target-evaluation frames (spec step 4: LHS after the
communication). A committed SEND on a closed channel panics (probe p23 —
closed counts as ready). The "unready" stuck arms are unreachable from
`applySelect` (which commits only ready clauses) — fail closed, never a
silent default. -/
def commitClause (s : ExecState) (env : LocalEnv) (k : Cont) :
    EvClause → Except GoError (Config × ExecState)
  | .sendEv chv vv elem body => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => stuck "select committed an unready send clause"
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          if closed then
            return (.panicking [⟨runtimeErrorValue "send on closed channel", false⟩] k, s)
          else if buf.size < capacity then do
            let v' ← normalizeValueForTy s elem vv
            let s' ← storeLoc s loc (.chanData (buf.push v') capacity closed)
            return (.exec body env k, s')
          else stuck "select committed an unready send clause"
  | .recvEv chv targets elem body => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => stuck "select committed an unready receive clause"
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          let (v, ok, s₁) ←
            match buf[0]? with
            | some v => do
                let s₁ ← storeLoc s loc (.chanData (buf.eraseIdx! 0) capacity closed)
                pure (v, true, s₁)
            | none =>
                if closed then do
                  let zero ← defaultValue s elem
                  pure (zero, false, s)
                else stuck "select committed an unready receive clause"
          match targets with
          | [] => return (.exec body env k, s₁)
          | te :: rest =>
              return (.evalE te env (.selectRecvK v ok [] rest body env k), s₁)

/-- The `select` READINESS step (spec step 2, deterministic slice): pair
the evaluated entry operands with their clauses, compute the ready set;
none ready → `default` (consuming NOTHING) or block; exactly one ready →
commit it. MULTIPLE ready clauses FAIL CLOSED (`.unsupported`) — the
spec's "uniform pseudo-random" choice is the L2 envelope, a `Choices`
site deliberately deferred to the scheduler arc (slice 4); refusing here
keeps this slice free of new nondeterminism-consumption sites. Shared by
rule `Step.selectApply` and `stepFn`. -/
def applySelect (s : ExecState) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    Except GoError (Config × ExecState) := do
  let evs ← evalClauses clauses vs
  match ← readyClauses s evs with
  | [] =>
      match default? with
      | some d => return (.exec d env k, s)
      | none => return (.blockedSelect evs env k, s)
  | [c] => commitClause s env k c
  | _ :: _ :: _ =>
      throw (.unsupported
        "select with multiple ready cases (deterministic slice; the choice envelope is the scheduler arc's slice 4)")

/-! ## The step relation -/

/-- One machine step over `(control, state)` pairs. No rule applies to
malformed or unmodeled configurations: they are stuck (fail closed). A
panic step starts UNWINDING (`.panicking` carries the chain and the
continuation): defers run on the panic path, `recover` in a panic-run
deferred call cancels the unwind, and only an unrecovered chain reaching
`.stop` becomes the terminal `.panicked`. Nondeterministic steps (map
iteration order, append capacity) arrive at S2 with their statements. -/
inductive Step : Config → ExecState → Config → ExecState → Prop where
  -- Expression entry
  | evalVar {id loc v env k s} :
      LocalEnv.lookup env id = some loc →
      loadLoc s loc = .ok v →
      Step (.evalE (.var id) env k) s (.retV v k) s
  | evalIntLit {value kind env k s} :
      Step (.evalE (.intLit value kind) env k) s
        (.retV (.int (kind.normalize value) kind) k) s
  | evalBoolLit {value env k s} :
      Step (.evalE (.boolLit value) env k) s (.retV (.bool value) k) s
  | evalStringLit {value env k s} :
      Step (.evalE (.stringLit value) env k) s (.retV (.string value) k) s
  | evalRef {id loc env k s} :
      LocalEnv.lookup env id = some loc →
      Step (.evalE (.ref id) env k) s (.retV (.addr loc) k) s
  | evalLocLit {l env k s} :
      Step (.evalE (.locLit l) env k) s (.retV (.addr l) k) s
  /-- Enter a strict form with at least one operand: evaluate the first
  under the generic frame. -/
  | evalStrict {e op e₁ rest env k s} :
      strictPlan e = some (op, e₁ :: rest) →
      Step (.evalE e env k) s (.evalE e₁ env (.strictK op [] rest env k)) s
  /-- A nullary strict form applies immediately. -/
  | evalStrictNullary {e op v env k s s'} :
      strictPlan e = some (op, []) →
      applyStrictOp s op [] = .ok (v, s') →
      Step (.evalE e env k) s (.retV v k) s'
  | evalStrictNullaryPanic {e op msg env k s} :
      strictPlan e = some (op, []) →
      applyStrictOp s op [] = .error (.panic msg) →
      Step (.evalE e env k) s (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  /-- `recover()`: the walk-and-mark is one deterministic function of the
  continuation (arc doc §A1); never stuck. -/
  | evalRecover {env k v k' s} :
      recoverResult k = (v, k') →
      Step (.evalE .recoverCall env k) s (.retV v k') s
  | evalAnd {l r env k s} :
      Step (.evalE (.and l r) env k) s (.evalE l env (.andK r env k)) s
  | evalOr {l r env k s} :
      Step (.evalE (.or l r) env k) s (.evalE l env (.orK r env k)) s
  -- Strict-operator frame
  | strictShift {op done e rest v env k s} :
      Step (.retV v (.strictK op done (e :: rest) env k)) s
        (.evalE e env (.strictK op (v :: done) rest env k)) s
  | strictApply {op done v out env k s s'} :
      applyStrictOp s op (v :: done).reverse = .ok (out, s') →
      Step (.retV v (.strictK op done [] env k)) s (.retV out k) s'
  | strictApplyPanic {op done v msg env k s} :
      applyStrictOp s op (v :: done).reverse = .error (.panic msg) →
      Step (.retV v (.strictK op done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- Short-circuit frames
  | andTrue {r env k s} :
      Step (.retV (.bool true) (.andK r env k)) s (.evalE r env (.boolK k)) s
  | andFalse {r env k s} :
      Step (.retV (.bool false) (.andK r env k)) s (.retV (.bool false) k) s
  | orTrue {r env k s} :
      Step (.retV (.bool true) (.orK r env k)) s (.retV (.bool true) k) s
  | orFalse {r env k s} :
      Step (.retV (.bool false) (.orK r env k)) s (.evalE r env (.boolK k)) s
  | boolCoerce {b k s} :
      Step (.retV (.bool b) (.boolK k)) s (.retV (.bool b) k) s
  -- Sequencing (unchanged from the old relation)
  | seqn {ss env k s} :
      Step (.exec (.seqn ss) env k) s (.next (seqCont ss.toList env k)) s
  | seqNext {t rest env k s} :
      Step (.next (.seq (t :: rest) env k)) s (.exec t env (.seq rest env k)) s
  | seqDone {env k s} :
      Step (.next (.seq [] env k)) s (.next k) s
  | seqBreak {rest env k s} :
      Step (.breaking (.seq rest env k)) s (.breaking k) s
  | seqContinue {rest env k s} :
      Step (.continuing (.seq rest env k)) s (.continuing k) s
  | seqReturn {rest env k s} :
      Step (.returning (.seq rest env k)) s (.returning k) s
  -- Blocks and declarations
  | block {decls ss env env' k s s'} :
      allocDecls env.pushScope s decls.toList = .ok (env', s') →
      Step (.exec (.block decls ss) env k) s (.next (.seq ss.toList env' k)) s'
  | initialization {p v loc rest env k s s'} :
      defaultValue s p.typ = .ok v →
      s.alloc v (some p.typ) = (loc, s') →
      Step (.exec (.initialization p) env (.seq rest env k)) s
        (.next (.seq rest (env.declare p.id loc) k)) s'
  -- Assignment: target address, then RHS, then the store — three separate
  -- steps around the operand evaluations.
  | assign {lhs te rhs env k s} :
      assigneeExpr lhs = some te →
      Step (.exec (.assign lhs rhs) env k) s
        (.evalE te env (.assignTargetK rhs env k)) s
  | assignTargetLoc {v loc rhs env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.assignTargetK rhs env k)) s
        (.evalE rhs env (.assignStoreK loc k)) s
  | assignTargetPanic {v msg rhs env k s} :
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.assignTargetK rhs env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | assignStore {v loc k s s'} :
      storeLoc s loc v = .ok s' →
      Step (.retV v (.assignStoreK loc k)) s (.next k) s'
  | assignStorePanic {v loc msg k s} :
      storeLoc s loc v = .error (.panic msg) →
      Step (.retV v (.assignStoreK loc k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- Conditionals
  | ifStmt {c t e env k s} :
      Step (.exec (.ifThenElse c t e) env k) s (.evalE c env (.ifK t e env k)) s
  | ifTrue {t e env k s} :
      Step (.retV (.bool true) (.ifK t e env k)) s (.exec t env k) s
  | ifFalse {t e env k s} :
      Step (.retV (.bool false) (.ifK t e env k)) s (.exec e env k) s
  -- Loops
  | whileStmt {c b env k s} :
      Step (.exec (.while c b) env k) s (.evalE c env (.whileK c b env k)) s
  | whileTrue {c b env k s} :
      Step (.retV (.bool true) (.whileK c b env k)) s
        (.exec b env (.loop c b env k)) s
  | whileFalse {c b env k s} :
      Step (.retV (.bool false) (.whileK c b env k)) s (.next k) s
  | loopNext {c b env k s} :
      Step (.next (.loop c b env k)) s (.exec (.while c b) env k) s
  | loopContinue {c b env k s} :
      Step (.continuing (.loop c b env k)) s (.exec (.while c b) env k) s
  | loopBreak {c b env k s} :
      Step (.breaking (.loop c b env k)) s (.next k) s
  | loopReturn {c b env k s} :
      Step (.returning (.loop c b env k)) s (.returning k) s
  -- Breakable scopes (switch/select bodies): `break` exits the scope,
  -- everything else unwinds past it unchanged.
  | breakableEnter {b env k s} :
      Step (.exec (.breakable b) env k) s (.exec b env (.breakableK k)) s
  | breakableDone {k s} :
      Step (.next (.breakableK k)) s (.next k) s
  | breakableBreak {k s} :
      Step (.breaking (.breakableK k)) s (.next k) s
  | breakableContinue {k s} :
      Step (.continuing (.breakableK k)) s (.continuing k) s
  | breakableReturn {k s} :
      Step (.returning (.breakableK k)) s (.returning k) s
  -- Control transfer
  | returnStmt {env k s} :
      Step (.exec .returnStmt env k) s (.returning k) s
  | breakStmt {env k s} :
      Step (.exec .breakStmt env k) s (.breaking k) s
  | continueStmt {env k s} :
      Step (.exec .continueStmt env k) s (.continuing k) s
  | label {name env k s} :
      Step (.exec (.label name) env k) s (.next k) s
  -- Labeled statements and labeled break/continue (control-flow slice,
  -- docs/2026-08-04_control-flow-design.md). The label scope catches
  -- `breakingTo` at a match; bare signals pass through it; `continuingTo`
  -- is caught by a loop whose immediate continuation is the matching
  -- label (`contHeadLabel` — the frontend's placement invariant).
  | labeledEnter {name b env k s} :
      Step (.exec (.labeled name b) env k) s (.exec b env (.labelK name k)) s
  | breakToStmt {name env k s} :
      Step (.exec (.breakTo name) env k) s (.breakingTo name k) s
  | continueToStmt {name env k s} :
      Step (.exec (.continueTo name) env k) s (.continuingTo name k) s
  | labelDone {name k s} :
      Step (.next (.labelK name k)) s (.next k) s
  | labelBreak {name k s} :
      Step (.breaking (.labelK name k)) s (.breaking k) s
  | labelContinue {name k s} :
      Step (.continuing (.labelK name k)) s (.continuing k) s
  | labelReturn {name k s} :
      Step (.returning (.labelK name k)) s (.returning k) s
  | breakToSeq {L rest env k s} :
      Step (.breakingTo L (.seq rest env k)) s (.breakingTo L k) s
  | breakToLoop {L c b env k s} :
      Step (.breakingTo L (.loop c b env k)) s (.breakingTo L k) s
  | breakToBreakable {L k s} :
      Step (.breakingTo L (.breakableK k)) s (.breakingTo L k) s
  | breakToMapIter {L keyVar valVar keyTy valTy body remaining env k s} :
      Step (.breakingTo L (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.breakingTo L k) s
  | breakToLabelMatch {L name k s} :
      name = L →
      Step (.breakingTo L (.labelK name k)) s (.next k) s
  | breakToLabelSkip {L name k s} :
      name ≠ L →
      Step (.breakingTo L (.labelK name k)) s (.breakingTo L k) s
  | continueToSeq {L rest env k s} :
      Step (.continuingTo L (.seq rest env k)) s (.continuingTo L k) s
  | continueToBreakable {L k s} :
      Step (.continuingTo L (.breakableK k)) s (.continuingTo L k) s
  /-- A `labelK` reached by `continuingTo` is never the target: `continue
  L` targets a LOOP labeled `L`, caught one frame earlier at the loop
  whose head is the matching label. A non-matching label is stripped; a
  MATCHING one not guarded by a loop head has no rule (statically
  impossible in Go — fail closed). -/
  | continueToLabelSkip {L name k s} :
      name ≠ L →
      Step (.continuingTo L (.labelK name k)) s (.continuingTo L k) s
  | continueToLoopMatch {L c b env k s} :
      contHeadLabel k = some L →
      Step (.continuingTo L (.loop c b env k)) s (.exec (.while c b) env k) s
  | continueToLoopSkip {L c b env k s} :
      contHeadLabel k ≠ some L →
      Step (.continuingTo L (.loop c b env k)) s (.continuingTo L k) s
  | continueToMapIterMatch {L keyVar valVar keyTy valTy body remaining env k s} :
      contHeadLabel k = some L →
      Step (.continuingTo L (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
  | continueToMapIterSkip {L keyVar valVar keyTy valTy body remaining env k s} :
      contHeadLabel k ≠ some L →
      Step (.continuingTo L (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.continuingTo L k) s
  -- Calls: resolve target addresses left-to-right (each an evaluated
  -- expression via `assigneeExpr`), then arguments left-to-right, then
  -- frame entry — Go's order, one machine step per operand plus one per
  -- memory operation inside the operand evaluations.
  | callFirstTarget {targets fid args te rest env k s} :
      assigneesExprs targets.toList = some (te :: rest) →
      Step (.exec (.call targets fid args) env k) s
        (.evalE te env (.callTargetsK fid [] rest args.toList env k)) s
  | callFirstArg {targets fid args a rest env k s} :
      assigneesExprs targets.toList = some [] →
      args.toList = a :: rest →
      Step (.exec (.call targets fid args) env k) s
        (.evalE a env (.callArgsK fid [] [] rest env k)) s
  | callImmediate {targets fid args func frameEnv resultLocs env k s s'} :
      assigneesExprs targets.toList = some [] →
      args.toList = [] →
      enterFrame s fid [] = .ok (func, frameEnv, resultLocs, s') →
      Step (.exec (.call targets fid args) env k) s
        (.exec func.body frameEnv (.frame [] resultLocs [] k func.wrapper)) s'
  | callTargetLoc {v loc fid locs te rest args env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.callTargetsK fid locs (te :: rest) args env k)) s
        (.evalE te env (.callTargetsK fid (locs ++ [loc]) rest args env k)) s
  | callTargetsDoneArg {v loc fid locs a rest env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.callTargetsK fid locs [] (a :: rest) env k)) s
        (.evalE a env (.callArgsK fid (locs ++ [loc]) [] rest env k)) s
  | callTargetsDoneEnter {v loc fid locs func frameEnv resultLocs env k s s'} :
      valueAsLoc v = .ok loc →
      enterFrame s fid [] = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callTargetsK fid locs [] [] env k)) s
        (.exec func.body frameEnv (.frame (locs ++ [loc]) resultLocs [] k func.wrapper)) s'
  | callTargetPanic {v msg fid locs pending args env k s} :
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.callTargetsK fid locs pending args env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callArgNext {v fid locs vals a rest env k s} :
      Step (.retV v (.callArgsK fid locs vals (a :: rest) env k)) s
        (.evalE a env (.callArgsK fid locs (vals ++ [v]) rest env k)) s
  | callArgsDoneEnter {v fid locs vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callArgsK fid locs vals [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k func.wrapper)) s'
  -- Wide statements (S2): one generic operand-plan frame; targets are
  -- checked as their addresses arrive (interpreter order), and the final
  -- state update is one `applyStmtOp` step. The `ch`/`ch'` choice streams
  -- are rule variables: a step under ANY choice stream is a legal step
  -- (the relation over-approximates the nondeterminism the executable
  -- resolves via `Choices`).
  | stmtOpFirst {stmt op nt e rest env k s} :
      stmtPlan stmt = some (op, nt, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.stmtOpK op nt [] rest env k)) s
  | stmtOpNullary {stmt op nt env k s s' ch ch'} :
      stmtPlan stmt = some (op, nt, []) →
      applyStmtOp s ch op nt [] = .ok (s', ch') →
      Step (.exec stmt env k) s (.next k) s'
  | stmtOpShiftTarget {op nt done v loc e rest env k s} :
      done.length < nt →
      valueAsLoc v = .ok loc →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s
        (.evalE e env (.stmtOpK op nt (v :: done) rest env k)) s
  | stmtOpShiftPlain {op nt done v e rest env k s} :
      nt ≤ done.length →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s
        (.evalE e env (.stmtOpK op nt (v :: done) rest env k)) s
  -- (Restricted to a nonempty pending list: at the apply position the same
  -- nil-target panic surfaces through `applyStmtOp`'s `locsOf` — rule
  -- `stmtOpApplyPanic` — keeping the rules in one-to-one correspondence
  -- with `stepFn`'s arms.)
  | stmtOpTargetPanic {op nt done v msg e rest env k s} :
      done.length < nt →
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | stmtOpApply {op nt done v env k s s' ch ch'} :
      applyStmtOp s ch op nt (v :: done).reverse = .ok (s', ch') →
      Step (.retV v (.stmtOpK op nt done [] env k)) s (.next k) s'
  | stmtOpApplyPanic {op nt done v msg env k s ch} :
      applyStmtOp s ch op nt (v :: done).reverse = .error (.panic msg) →
      Step (.retV v (.stmtOpK op nt done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- Map iteration (S2): snapshot, then nondeterministic pick-next — any
  -- in-range index is a legal step (the executable instantiates the pick
  -- from `Choices`, one choice per remaining entry).
  | mapRange {keyVar valVar mapExpr keyTy valTy body env k s} :
      Step (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) s
        (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k)) s
  | mapRangeSnapshot {v entries keyVar valVar keyTy valTy body env k s} :
      mapRangeSnapshotEntries s keyTy valTy v = .ok entries →
      Step (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body entries env k)) s
  | mapIterDone {keyVar valVar keyTy valTy body env k s} :
      Step (.next (.mapIterK keyVar valVar keyTy valTy body #[] env k)) s
        (.next k) s
  | mapIterNext {keyVar valVar keyTy valTy body remaining idx env env' k s s'}
      (hidx : idx < remaining.size) :
      bindIterVars env.pushScope s keyVar valVar keyTy valTy
        remaining[idx].1 remaining[idx].2 = .ok (env', s') →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.exec body env' (.mapIterK keyVar valVar keyTy valTy body
          (remaining.eraseIdx idx hidx) env k)) s'
  | mapIterContinue {keyVar valVar keyTy valTy body remaining env k s} :
      Step (.continuing (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
  | mapIterBreak {keyVar valVar keyTy valTy body remaining env k s} :
      Step (.breaking (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.next k) s
  | mapIterReturn {keyVar valVar keyTy valTy body remaining env k s} :
      Step (.returning (.mapIterK keyVar valVar keyTy valTy body remaining env k)) s
        (.returning k) s
  -- Call through a function VALUE (§8): targets, then the callee, then the
  -- arguments; frame entry prepends the closure's captured values, which is
  -- the whole lambda-lifting protocol. `enterFrame` is reused verbatim.
  | callValueFirstTarget {targets callee args te rest env k s} :
      assigneesExprs targets.toList = some (te :: rest) →
      Step (.exec (.callValue targets callee args) env k) s
        (.evalE te env (.callValTargetsK callee [] rest args.toList env k)) s
  | callValueNoTargets {targets callee args env k s} :
      assigneesExprs targets.toList = some [] →
      Step (.exec (.callValue targets callee args) env k) s
        (.evalE callee env (.callValCalleeK [] args.toList env k)) s
  | callValTargetLoc {v loc callee locs te rest args env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.callValTargetsK callee locs (te :: rest) args env k)) s
        (.evalE te env (.callValTargetsK callee (locs ++ [loc]) rest args env k)) s
  | callValTargetsDone {v loc callee locs args env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.callValTargetsK callee locs [] args env k)) s
        (.evalE callee env (.callValCalleeK (locs ++ [loc]) args env k)) s
  | callValTargetPanic {v msg callee locs pending args env k s} :
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.callValTargetsK callee locs pending args env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  /-- The callee value arrives (funcVal or nil); start the arguments. Go
  evaluates the callee and ALL arguments before the nil check fires. -/
  | callValCalleeArg {cv locs a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.callValCalleeK locs (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv locs [] rest env k)) s
  /-- Nullary call through a value: enter directly with the captures. -/
  | callValCalleeEnter {fid captured locs func frameEnv resultLocs env k s s'} :
      enterFrame s fid captured = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV (.funcVal fid captured) (.callValCalleeK locs [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k func.wrapper)) s'
  /-- Nullary call of a nil function value: nothing to evaluate, panic. -/
  | callValCalleeNil {locs env k s} :
      Step (.retV .nil (.callValCalleeK locs [] env k)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩] k) s
  | callValArgNext {v cv locs vals a rest env k s} :
      Step (.retV v (.callValArgsK cv locs vals (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv locs (vals ++ [v]) rest env k)) s
  | callValArgsEnter {v fid captured locs vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (captured ++ vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callValArgsK (.funcVal fid captured) locs vals [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k func.wrapper)) s'
  /-- All arguments evaluated, callee is nil: NOW the invocation panics. -/
  | callValArgsNil {v locs vals env k s} :
      Step (.retV v (.callValArgsK .nil locs vals [] env k)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩] k) s
  -- Frame exit: explicit return and fall-through perform the same
  -- pinned-location result read and caller-target stores.
  | frameReturn {targets results k w s vs s'} :
      loadMany s results = .ok vs →
      storeMany s targets vs = .ok s' →
      Step (.returning (.frame targets results [] k w)) s (.next k) s'
  | frameFall {targets results k w s vs s'} :
      loadMany s results = .ok vs →
      storeMany s targets vs = .ok s' →
      Step (.next (.frame targets results [] k w)) s (.next k) s'
  -- Draining the defer chain: one deferred call per step, each in its own
  -- frame whose continuation is this frame with the rest of the chain, so
  -- both exit paths converge on the rules above once the chain is empty.
  -- The inner frame has NO targets and NO results: a deferred call's
  -- results are discarded in Go (`defer/defer-function-result-discard`).
  | frameDeferFall {targets results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.next (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] (.frame targets results ds k w) func.wrapper)) s'
  | frameDeferReturn {targets results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.returning (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] (.frame targets results ds k w) func.wrapper)) s'
  /-- Invoking a nil deferred call panics at DRAIN time (Go: registration
  succeeded; the panic belongs to the invocation). The panic starts
  unwinding AT THIS FRAME with its remaining defers — which run, and may
  recover (`defer/defer-nil-function-recover-order` pins the order). -/
  | frameDeferNilFall {targets results args ds k w s} :
      Step (.next (.frame targets results ((.nil, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩]
          (.frame targets results ds k w)) s
  | frameDeferNilReturn {targets results args ds k w s} :
      Step (.returning (.frame targets results ((.nil, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩]
          (.frame targets results ds k w)) s
  -- Registering a deferred call: callee, then arguments, evaluated NOW.
  | deferStmt {callee args env k s} :
      Step (.exec (.deferCall callee args) env k) s
        (.evalE callee env (.deferCalleeK args.toList env k)) s
  | deferCalleeArg {cv a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.deferCalleeK (a :: rest) env k)) s
        (.evalE a env (.deferArgsK cv [] rest env k)) s
  | deferCalleeNoArgs {cv env k k' s} :
      deferrableCallee cv = true →
      pushDefer (cv, []) k = some k' →
      Step (.retV cv (.deferCalleeK [] env k)) s (.next k') s
  | deferArgNext {v cv vals a rest env k s} :
      Step (.retV v (.deferArgsK cv vals (a :: rest) env k)) s
        (.evalE a env (.deferArgsK cv (vals ++ [v]) rest env k)) s
  | deferArgsDone {v cv vals env k k' s} :
      pushDefer (cv, vals ++ [v]) k = some k' →
      Step (.retV v (.deferArgsK cv vals [] env k)) s (.next k') s
  -- The unwinding arc (`docs/2026-07-25_unwinding-arc.md` §A1): panic as
  -- a travelling configuration.
  /-- `panic(v)`: evaluate the payload (already `any`-converted by the
  lowering), then start unwinding. -/
  | panicStmt {e env k s} :
      Step (.exec (.panicStmt e) env k) s (.evalE e env (.panicArgK k)) s
  | panicArgValue {v k s} :
      Step (.retV v (.panicArgK k)) s (.panicking [⟨panicPayload v, false⟩] k) s
  /-- Unwinding strips every non-frame, non-marker continuation. -/
  | panicUnwind {chain k k' s} :
      panicPassthrough k = some k' →
      Step (.panicking chain k) s (.panicking chain k') s
  /-- Unwinding past a frame with no (remaining) defers: results are NOT
  read — the call did not return. -/
  | panicFrameEmpty {chain targets results k w s} :
      Step (.panicking chain (.frame targets results [] k w)) s
        (.panicking chain k) s
  /-- Defers RUN on the panic path: the deferred call executes above a
  `panicResumeK` carrying the suspended chain — the shape `recover`'s
  walk detects. Results discarded, as on the normal drain. -/
  | panicFrameDefer {chain targets results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.panicking chain (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] (.panicResumeK chain (.frame targets results ds k w)) func.wrapper)) s'
  /-- A nil deferred callee invoked DURING unwinding: the invocation's
  nil-dereference panic joins the chain (newest last) and this frame's
  remaining defers keep draining. -/
  | panicFrameDeferNil {chain targets results args ds k w s} :
      Step (.panicking chain (.frame targets results ((.nil, args) :: ds) k w)) s
        (.panicking (chain ++ [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩])
          (.frame targets results ds k w)) s
  /-- A NEW panic unwinding through a suspended chain's marker merges
  behind it — this single rule produces Go's chained abort output
  (`panic: first ⏎ panic: second`, `… [recovered] ⏎ …`). -/
  | panicResumeMerge {chain suspended k s} :
      Step (.panicking chain (.panicResumeK suspended k)) s
        (.panicking (suspended ++ chain) k) s
  /-- A panic-path deferred call completed and the newest chain entry was
  recovered: the unwind is cancelled, the whole chain discarded, and the
  frame below resumes its NORMAL exit path (drain remaining defers, then
  read pinned results — Go's "the surrounding function returns
  normally"). -/
  | panicResumeRecovered {chain k s} :
      chainNewestRecovered chain = true →
      Step (.next (.panicResumeK chain k)) s (.next k) s
  /-- …not recovered: unwinding resumes below. -/
  | panicResumeContinue {chain k s} :
      chainNewestRecovered chain = false →
      Step (.next (.panicResumeK chain k)) s (.panicking chain k) s
  /-- An unrecovered chain at `.stop`: the terminal abort, rendered as
  Go's first `panic: ` line (arc doc §A3). Chains whose head payload has
  no pinned rendering have no rule — fail closed. -/
  | panicAbort {first rest msg s} :
      renderPanicHead s first rest = some msg →
      Step (.panicking (first :: rest) .stop) s (.panicked msg) s
  /-- Frame-ENTRY panics are ordinary recoverable panics (2026-08-05,
  slice-2 stage 5: dynamic dispatch on a nil interface or the auto-deref
  of a nil pointer box raises inside `enterFrame`; Go recovers these like
  any other panic — pinned by `interfaces/recover-nil-dispatch/*`). One
  twin per ordinary call-entry rule, appended at the END of the inductive
  so existing positional case tags in the correspondence proofs keep
  their numbering. DEFERRED-call entry has its own twins further below
  (`frameDeferFallEnterPanic` and friends — audit F1+F5, 2026-08-05;
  the original narrowing here was scoped too widely). -/
  | callImmediatePanic {targets fid args msg env k s} :
      assigneesExprs targets.toList = some [] →
      args.toList = [] →
      enterFrame s fid [] = .error (.panic msg) →
      Step (.exec (.call targets fid args) env k) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callTargetsDoneEnterPanic {v loc fid locs msg env k s} :
      valueAsLoc v = .ok loc →
      enterFrame s fid [] = .error (.panic msg) →
      Step (.retV v (.callTargetsK fid locs [] [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callArgsDoneEnterPanic {v fid locs vals msg env k s} :
      enterFrame s fid (vals ++ [v]) = .error (.panic msg) →
      Step (.retV v (.callArgsK fid locs vals [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callValCalleeEnterPanic {fid captured locs msg env k s} :
      enterFrame s fid captured = .error (.panic msg) →
      Step (.retV (.funcVal fid captured) (.callValCalleeK locs [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callValArgsEnterPanic {v fid captured locs vals msg env k s} :
      enterFrame s fid (captured ++ vals ++ [v]) = .error (.panic msg) →
      Step (.retV v (.callValArgsK (.funcVal fid captured) locs vals [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  /-- DEFERRED-call frame-ENTRY panics (audit F1+F5, 2026-08-05): a
  dispatch panic entering a deferred call is a panic of the deferred
  INVOCATION — exactly the class the `.nil`-callee drain rules already
  model (differentially pinned by `defer/defer-nil-function-recover-order`
  there and `defer/deferred-dispatch-entry-panic/*` here). On the normal
  drains it starts unwinding AT THIS FRAME with its remaining defers
  (mirror of `frameDeferNilFall`/`frameDeferNilReturn`); DURING an
  unwinding panic it JOINS the chain newest-last and draining continues
  (mirror of `panicFrameDeferNil` — Go appends the new panic and
  `recover` answers the newest entry, which `chainNewestRecovered`
  implements; the `during-panic` pin discriminates newest-vs-original by
  asserting the recovered value). Appended at the END of the inductive
  so the correspondence proofs' positional case tags stay stable. -/
  | frameDeferFallEnterPanic {targets results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.next (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] (.frame targets results ds k w)) s
  | frameDeferReturnEnterPanic {targets results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.returning (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] (.frame targets results ds k w)) s
  | panicFrameDeferEnterPanic {chain targets results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.panicking chain (.frame targets results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking (chain ++ [⟨runtimeErrorValue msg, false⟩])
          (.frame targets results ds k w)) s
  /-- Channel statements (channels arc slice 1): the `stmtOpK` rule shape
  — operand-plan entry, target-checked shifts, one apply step — with the
  apply's outcome a full CONFIGURATION (`applyChanOp`: next / panicking /
  blocked). Appended at the END of the inductive so the correspondence
  proofs' positional case tags stay stable. The blocked configurations
  these can step TO have no outgoing rules (relation-silent): pairing is
  the slice-2 pool's job, and the sequential driver classifies them as
  the deadlocked run. -/
  | chanStFirst {stmt op nt e rest env k s} :
      chanPlan stmt = some (op, nt, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.chanStK op nt [] rest env k)) s
  | chanStShiftTarget {op nt done v loc e rest env k s} :
      done.length < nt →
      valueAsLoc v = .ok loc →
      Step (.retV v (.chanStK op nt done (e :: rest) env k)) s
        (.evalE e env (.chanStK op nt (v :: done) rest env k)) s
  | chanStShiftPlain {op nt done v e rest env k s} :
      nt ≤ done.length →
      Step (.retV v (.chanStK op nt done (e :: rest) env k)) s
        (.evalE e env (.chanStK op nt (v :: done) rest env k)) s
  | chanStTargetPanic {op nt done v msg e rest env k s} :
      done.length < nt →
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.chanStK op nt done (e :: rest) env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | chanStApply {op nt done v c' env k s s'} :
      applyChanOp s op nt (v :: done).reverse k = .ok (c', s') →
      Step (.retV v (.chanStK op nt done [] env k)) s c' s'
  | chanStApplyPanic {op nt done v msg env k s} :
      applyChanOp s op nt (v :: done).reverse k = .error (.panic msg) →
      Step (.retV v (.chanStK op nt done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- `select` (spec's five steps): entry evaluates the clause operands in
  -- source order under `selectOpsK` (step 1); the apply step computes
  -- readiness and commits (steps 2-3, `applySelect` — deterministic in
  -- this slice: one ready clause or default; multi-ready is
  -- relation-silent/unsupported); a selected receive's targets evaluate
  -- after the communication (step 4, `selectRecvK`); the body enters
  -- under the plain continuation (step 5 — the frontend wraps the whole
  -- select in `.breakable`, so `break` needs no select-side rule).
  | selectFirst {clauses default? e rest env k s} :
      selectOperands clauses.toList = e :: rest →
      Step (.exec (.selectStmt clauses default?) env k) s
        (.evalE e env (.selectOpsK clauses.toList default? [] rest env k)) s
  | selectNoClausesDefault {clauses d env k s} :
      selectOperands clauses.toList = [] →
      Step (.exec (.selectStmt clauses (some d)) env k) s (.exec d env k) s
  /-- `select {}` (and the degenerate no-clause, no-default form): blocks
  forever (spec: "a select with ... no default case blocks forever"). -/
  | selectNoClausesBlock {clauses env k s} :
      selectOperands clauses.toList = [] →
      Step (.exec (.selectStmt clauses none) env k) s
        (.blockedSelect [] env k) s
  | selectOpsShift {clauses default? done v e rest env k s} :
      Step (.retV v (.selectOpsK clauses default? done (e :: rest) env k)) s
        (.evalE e env (.selectOpsK clauses default? (v :: done) rest env k)) s
  | selectApply {clauses default? done v c' env k s s'} :
      applySelect s clauses default? (v :: done).reverse env k = .ok (c', s') →
      Step (.retV v (.selectOpsK clauses default? done [] env k)) s c' s'
  | selectApplyPanic {clauses default? done v msg env k s} :
      applySelect s clauses default? (v :: done).reverse env k = .error (.panic msg) →
      Step (.retV v (.selectOpsK clauses default? done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | selectRecvTargetLoc {v0 ok locs v loc e rest body env k s} :
      valueAsLoc v = .ok loc →
      Step (.retV v (.selectRecvK v0 ok locs (e :: rest) body env k)) s
        (.evalE e env (.selectRecvK v0 ok (locs ++ [loc]) rest body env k)) s
  | selectRecvTargetPanic {v0 ok locs v msg pending body env k s} :
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.selectRecvK v0 ok locs pending body env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | selectRecvFinish {v0 ok locs v loc body env k s s'} :
      valueAsLoc v = .ok loc →
      storeMany s (locs ++ [loc]) (recvStores v0 ok (locs ++ [loc]).length) = .ok s' →
      Step (.retV v (.selectRecvK v0 ok locs [] body env k)) s
        (.exec body env k) s'

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Config → ExecState → Config → ExecState → Prop where
  | refl (c : Config) (s : ExecState) : Steps c s c s
  | tail {a sa b sb c sc} : Steps a sa b sb → Step b sb c sc → Steps a sa c sc

theorem Steps.single {a b : Config} {sa sb : ExecState} (h : Step a sa b sb) :
    Steps a sa b sb :=
  .tail (.refl a sa) h

theorem Steps.trans {a b c : Config} {sa sb sc : ExecState} :
    Steps a sa b sb → Steps b sb c sc → Steps a sa c sc := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

/-- A configuration the sequential machine considers finished. -/
def Config.terminal : Config → Prop
  | .next .stop => True
  | .panicked _ => True
  | _ => False

end GoLean.GoCore.Machine
