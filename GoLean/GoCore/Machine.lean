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
statements (`newValue`, make/assign/lookup for maps and
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

/-- The element location of an index-addressed target: bounds-checked
against the base. Shared verbatim between the `indexAddr` strict op
(address in expression position — the check fires at evaluation) and
`storeTarget` (an assignment's OWN index target — spec §Assignments
defers the check to the STORE, phase 2; convergence round BUG-029,
pinned by `channels/recv-edge/oob-second-target-stores-first`). -/
def indexTargetLoc (s : ExecState) (b i : GoValue) : Except GoError Loc := do
  let indexValue ← valueAsInt i
  match b with
  | .slice slice => sliceIndexLoc slice indexValue
  -- A nil pointer-to-array base is gc's recoverable nil-pointer
  -- dereference, at exactly this point (round 4, BUG-038 — the
  -- `valueAsLoc` convention; previously a wrongly-stuck fall-through).
  | .nil => panic "runtime error: invalid memory address or nil pointer dereference"
  | .addr baseLoc =>
      match ← loadLoc s baseLoc with
      | .array values => do
          let _ ← arrayIndexNat values indexValue
          return .index baseLoc indexValue
      | .slice slice => sliceIndexLoc slice indexValue
      | other => stuck s!"expected array or slice base for index address, got {repr other}"
  | other => stuck s!"expected array or slice base for index address, got {repr other}"

/-- Store into a map element: normalize key and value at the map's
types, insert-or-overwrite; a NIL map is the run-time panic. Shared
verbatim between the `mapAssign` wide op and `storeTarget`'s
map-element arm (convergence round BUG-030 — a map-element receive
target's store is a phase-2 event like any other). -/
def mapAssignValue (s : ExecState) (keyTy valueTy : Ty)
    (baseV keyV valueV : GoValue) : Except GoError ExecState := do
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
      storeLoc s baseLoc (.mapData entries)

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
  -- `&*p` (BUG-056): the nil check consumes the pointer VALUE already
  -- in hand — `.addr` passes through, `.nil` panics via `valueAsLoc`'s
  -- runtime-error arm, anything else is stuck. It reads and writes NO
  -- memory cell (gc: a bare TESTB nil-probe, no pointee load — memo
  -- §2), so it has no race-footprint arm on purpose (Race.lean's
  -- call-site inventory records the decision).
  | .addrOfDeref, [v] => do return (.addr (← valueAsLoc v), s)
  | .fieldGet typeId fieldName, [v] => do
      match v with
      | .struct actualType fields =>
          -- Tag-convertible mint tags are accepted (triage L7): the
          -- pointer conversion aliases the cell, whose tag stays.
          if actualType != typeId && !structTagCompatible s actualType typeId then
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
      -- Pointer-to-array base in READ position (triage L5;
      -- spec#Index_expressions: for `a` of pointer to array type,
      -- `a[x]` is shorthand for `(*a)[x]`): the read sibling of
      -- BUG-038's write-path `.addr` arm in `indexTargetLoc`. Only an
      -- ARRAY pointee is accepted — Go's index auto-deref applies to
      -- pointer-to-array alone; the write path's slice-pointee arm
      -- exists because assignment TARGETS carry the base cell's
      -- address, a shape read position never produces.
      | .addr baseLoc =>
          match ← loadLoc s baseLoc with
          | .array values => return ((← arrayGet values indexValue), s)
          | other => stuck s!"expected array pointee for index access, got {repr other}"
      -- A nil pointer-to-array base is gc's recoverable nil-pointer
      -- dereference (triage L6; BUG-038's entry names this case as the
      -- deferred read-position sibling).
      | .nil => panic "runtime error: invalid memory address or nil pointer dereference"
      | other => stuck s!"expected array, slice, or string value for index access, got {repr other}"
  | .indexAddr, [b, i] => do
      return (.addr (← indexTargetLoc s b i), s)
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
      -- Float operands take the IEEE fold (triage L3, spec#Min_and_max:
      -- NaN propagates, min(-0,+0) = -0) over the softfloat comparison
      -- kernel — never valueLess, whose unordered `<` is false at NaN
      -- in BOTH directions and would silently make the first operand
      -- win. Left-associative like gc's lowering.
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax true best w
        return (best, s)
      else do
        let mut best := v
        for w in vs do
          if ← valueLess w best then
            best := w
        return (best, s)
  | .maxOf, v :: vs =>
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax false best w
        return (best, s)
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
      | .string value =>
          let runes := (runesOfString value).map
            (fun r => GoValue.int r .int32)
          let (base, s') := s.alloc (.array runes)
            (some (.array runes.size (.int .int32)))
          return (.slice { base := some base, offset := 0,
                           len := runes.size, cap := runes.size }, s')
      | other => stuck s!"expected string operand for []rune conversion, got {repr other}"
  -- `string(rs)` over a rune slice (triage L1): concatenate the UTF-8
  -- encodings of the individual rune values (spec §Conversions to and
  -- from a string type) — values outside the valid code-point range
  -- (negative, surrogate, > U+10FFFF) encode U+FFFD via the same
  -- `fromCodePoint` kernel `string(int)` uses.
  | .stringFromRuneSlice, [v] => do
      let slice ← valueAsSlice v
      let values ← sliceVisibleValues s slice
      let mut str := GoString.empty
      for value in values do
        match value with
        | .int r .int32 => str := str.append (GoString.fromCodePoint r)
        | other => stuck s!"expected rune element in string conversion, got {repr other}"
      return (.string str, s)
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
  | newValue (typ : Option Ty)
  | makeSlice (elem : Ty) (hasCap : Bool)
  | makeMap (hasSpace : Bool)
  /-- `make(chan T[, n])` (channels arc slice 1): allocate an empty
  `chanData` cell (the `makeMap` shape; the cell is untyped, like
  `mapData`). Negative capacity ⇒ the recoverable run-time panic
  `makechan: size out of range` (probe p21). -/
  | makeChan (hasCap : Bool)
  | mapAssign (keyTy valueTy : Ty)
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
statements with their own rules and for unsupported assignees.
`assignMany` no longer rides this plan: the convergence round (BUG-025)
moved it onto the phase-split delivery machinery (`tgtOpK`/`rhsK`/
`storeK`), whose per-store phase 2 the one-shot `applyStmtOp` cannot
express. -/
def stmtPlan : Stmt → Option (StmtOp × Nat × List Expr)
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
def applyStmtOpCore (s : ExecState) (op : StmtOp) (_nt : Nat)
    (vs : List GoValue) : Except GoError ExecState := do
  match op with
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
      | [baseV, keyV, valueV] => mapAssignValue s keyTy valueTy baseV keyV valueV
      | _ => stuck "malformed mapAssign operands"
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
            let (extra, choices) := Choices.consumeAt .appendSpill width choices
            let newCap := newLen +
              ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            let backing ← buildAppendBackingValue s elem oldValues elemValues newCap
            let (base, current) := s.alloc backing (some (.array newCap elem))
            return ((← storeLoc current tloc
              (.slice { base := some base, offset := 0, len := newLen, cap := newCap })), choices)
      | _ => stuck "malformed appendSlice operands"
  | op => do return ((← applyStmtOpCore s op nt vs), choices)

/-- Range START (BUG-005 (L) surgery, replacing the retired snapshot):
the ranged map's base cell and its START-KEY set — the keys present
when the range begins (keys only, never values: values are read LIVE
at production, the spec's forced production-table clause). Shared
verbatim by rule `Step.mapRangeStart` and `stepFn`'s `mapRangeK` arm.
The load here is a real heap read (the footprint's `mapRangeK` arm). -/
def mapRangeStartSets (s : ExecState) (v : GoValue) :
    Except GoError (Option Loc × Array GoValue) := do
  let map ← valueAsMap v
  match map.base with
  | none => return (none, #[])
  | some base =>
      match ← loadLoc s base with
      | .mapData es => return (some base, es.map (·.1))
      | other => stuck s!"expected map data for range, got {repr other}"

/-- The LIVE entries of an in-flight range's map cell (`none` base =
nil map = no entries). Every `mapIterNext` pick — including the final
done-check — performs this read (gc's exhausted `mapIterNext` still
reads; the U1-closing footprint arm records it). -/
def mapIterLiveEntries (s : ExecState) (base : Option Loc) :
    Except GoError (Array (GoValue × GoValue)) := do
  match base with
  | none => return #[]
  | some l =>
      match ← loadLoc s l with
      | .mapData es => return es
      | other => stuck s!"expected map data for range, got {repr other}"

/-- Is `key` a member of `keys` under Go map-key equality at `keyTy`
(the same `valueEq` the map ops use)? Structural on the list — the
de-WF recipe, so the candidate/mandatory lemmas induct cleanly. -/
def keyInKeyList (s : ExecState) (keyTy : Ty) (key : GoValue) :
    List GoValue → Except GoError Bool
  | [] => return false
  | p :: rest => do
      if ← valueEq s keyTy p key then
        return true
      else
        keyInKeyList s keyTy key rest

@[inherit_doc keyInKeyList]
def keyInKeys (s : ExecState) (keyTy : Ty) (keys : Array GoValue)
    (key : GoValue) : Except GoError Bool :=
  keyInKeyList s keyTy key keys.toList

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

/-- The PICK-TIME candidates (BUG-005 (L) surgery): the live entries
whose key is not yet in `produced`, VALIDATED self-normalized at the
range key/value types — fail closed otherwise. The validation is the
sem-adequacy obstruction's guard, moved from the retired snapshot step
to the pick: an ill-typed live entry would make `bindIterVars` succeed
at one pick and fail at another, so it is rejected BEFORE any choice
is consumed, keeping pick success choices-independent
(`step_complete_any_wf`'s mapIterNext case rests on exactly this).
Shared VERBATIM by the `Step.mapIter*` rules and `stepFn`. -/
def filterCandidateList (s : ExecState) (keyTy : Ty)
    (produced : Array GoValue) :
    List (GoValue × GoValue) → Except GoError (List (GoValue × GoValue))
  | [] => return []
  | (k, v) :: rest => do
      let inProduced ← keyInKeys s keyTy produced k
      let tail ← filterCandidateList s keyTy produced rest
      if inProduced then
        return tail
      else
        return (k, v) :: tail

/-- The PICK-TIME candidates (docstring above `filterCandidateList`'s
block comment — see the surgery note there). -/
def mapIterCandidates (s : ExecState) (keyTy valTy : Ty)
    (base : Option Loc) (produced : Array GoValue) :
    Except GoError (Array (GoValue × GoValue)) := do
  let entries ← mapIterLiveEntries s base
  let out := (← filterCandidateList s keyTy produced entries.toList).toArray
  if snapshotEntriesSelfNormalized s.types keyTy valTy out then
    return out
  else
    throw (.stuck s!"map range live entry not self-normalized at range \
key/value types ({repr keyTy}, {repr valTy})")

/-- Does a MANDATORY candidate remain — a candidate whose key is a
never-removed start key? While `true`, the STOP slot is illegal: the
spec's production table traverses every surviving entry ("For each
iteration, iteration values are produced …"), so an entry neither
removed nor created must be produced before iteration may end. Shared
verbatim by rule `Step.mapIterStop` and `stepFn`. -/
def mandatoryInList (s : ExecState) (keyTy : Ty) (start : Array GoValue) :
    List (GoValue × GoValue) → Except GoError Bool
  | [] => return false
  | (k, _) :: rest => do
      if ← keyInKeys s keyTy start k then
        return true
      else
        mandatoryInList s keyTy start rest

@[inherit_doc mandatoryInList]
def mapIterMandatoryRemains (s : ExecState) (keyTy : Ty)
    (candidates : Array (GoValue × GoValue)) (start : Array GoValue) :
    Except GoError Bool :=
  mandatoryInList s keyTy start candidates.toList

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
def resolveChain (s : ExecState) : GoValue → List TargetStep → List GoValue →
    Except GoError GoValue
  | cur, [], [] => return cur
  | cur, .index :: steps, i :: idxs => do
      resolveChain s (.addr (← indexTargetLoc s cur i)) steps idxs
  | cur, .field tid f :: steps, idxs => do
      resolveChain s (.addr (.field (← valueAsLoc cur) tid f)) steps idxs
  | _, _, _ => stuck "malformed target chain"

/-- Phase 2, one target, one step: the store, with the target chain's
OWN checks — nil address (`valueAsLoc`), bounds (`indexTargetLoc`),
nil field bases, nil map — firing HERE (spec §Assignments: "the
assignments are carried out in left-to-right order"). -/
def storeTarget (s : ExecState) (r : TargetRef) (v : GoValue) : Except GoError ExecState := do
  match r with
  | .chain anchor idxs steps =>
      storeLoc s (← valueAsLoc (← resolveChain s anchor steps idxs)) v
  | .mapElem b k kt vt => mapAssignValue s kt vt b k v

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
Shared verbatim by rule `Step.rhsStores`/`rhsStoresPanic` and
`stepFn`'s `rhsK` finish arm. -/
def applyRhsOp (s : ExecState) : RhsOp → List GoValue → Except GoError (List GoValue)
  | .vals, vs => return vs
  | .mapLookup keyTy valueTy, [baseV, keyV] => do
      let map ← valueAsMap baseV
      let key ← normalizeValueForTy s keyTy keyV
      let pair ← mapLookupValue s map key keyTy valueTy
      return [pair.1, .bool pair.2]
  | .typeAssert targetTy, [value] => do
      let result ← typeAssertValue s value targetTy
      return [result.1, .bool result.2]
  | _, _ => stuck "malformed comma-ok source operands"

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

/-- The channel-statement plan and the wide-statement plan classify
DISJOINT statements: a statement `chanPlan` recognizes is never one
`stmtPlan` recognizes. `step_det`'s rule-disjointness sweep cites this
(as a conditional simp lemma) to refute the generic-statement cross
pairs without casing the statement. -/
theorem stmtPlan_of_chanPlan {stmt : Stmt} {p : ChanStOp × List Expr}
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

/-! ## Sync-package primitives (spec-parity slice 2,
`docs/2026-08-09_sync-package-design.md`)

THE REGISTRY ENTRY (the channels-arc D2+D3 growth contract exercised as
designed — one registration, nothing revises): each sync op's APPLY
position is (a) a SCHEDULING POINT — it joins `Config.atBoundary`, so
the EXISTING L1 scheduler site is consulted there (consumed only at
|runnable| > 1; sync adds ZERO new `Choices` sites — see the envelope
statement at `applySyncOp`) — and (b) an HB EDGE SOURCE — `raceUpdate`
(Multi.lean) classifies sync applies/wakes and advances the per-cell
sync clocks (`RaceState.syncAcquire`/`syncRelease`, Race.lean; the
package-doc sentences quoted there). Blocked ops are the ONE new
blocked-Config shape `.blockedSync`; wake is CELL-based (`wakeReady`),
and which contender acquires next is pure L1 latitude — sync needs no
arrival intercept, no pairing step, and no L4-analogue waiter pick,
because nothing transfers between goroutines except through the cell. -/

/-- Machine-level sync operation: the `SyncStmtOp` head with the
`onceBegin` target payload validated in (the `ChanStOp.recv` shape). -/
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
  deriving Repr, BEq

/-- Classify a sync statement: op head plus the operands evaluated
before the apply — the receiver ADDRESS expression, plus the delta for
`wgAdd`. Fails closed (`none`) on arity drift, on targets anywhere but
`onceBegin`, on a target count ≠ 1 for `onceBegin`, and on unsupported
target assignees (the `chanPlan` discipline). -/
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
  | _ => none

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

/-- Load a sync primitive's cell. A non-sync cell is `stuck` (fail
closed — the frontend types every receiver). -/
def syncCell (s : ExecState) (loc : Loc) : Except GoError SyncPrim := do
  match ← loadLoc s loc with
  | .syncData p => return p
  | other => stuck s!"expected sync primitive data, got {repr other}"

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
    Except GoError (List EvClause)
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
      else if !dynamicMethodSetRecorded state (.defined name) then
        -- BUG-053 class, renderer consumer (contract note §4,
        -- 2026-08-10): with no method-set record,
        -- `panicPayloadIsRewritten`'s "no Error()/String()" below would
        -- be an answer from absence — gc may well rewrite the payload
        -- through a method we never saw. Fail closed to an unrenderable
        -- abort, never a fabricated `main.T(v)`. (`Error`/`String` are
        -- exported names, so an `exported`-coverage record suffices to
        -- decide honestly.)
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
  | frame (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
      (results : List Loc)
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
  /-- `mapRange` iteration context — LIVE iteration (BUG-005 (L)
  surgery, ruled 2026-08-19; the snapshot design is retired). The frame
  carries the ranged map's `base` cell (`none` = nil map), the
  `produced` KEY set (keys already bound, in production order) and the
  `start` KEY set (keys present when the range began). Each pick-next
  step LOADS the live cell (the U1-closing race footprint), takes
  `candidates` = live entries whose key ∉ produced (removed entries
  drop out by absence — the spec's forced removal clause; values come
  live — the forced production-table clause), and consumes ONE choice
  of width `candidates.size + stop`, where the trailing STOP slot is
  legal only when no candidate key remains in `start` (a surviving
  never-removed start key is MANDATORY — spec-forced traversal). A
  `mapDelete`/`clearMap` step prunes the deleted key(s) from `produced`
  AND `start` in every in-flight frame over the same base
  (`contAfterStmtOp`): a deleted-then-re-created key is a NEW entry —
  the adopted reading, `docs/spec-interpretations.md` I-1 /
  ledger L-012. `break` finishes the range, `continue` proceeds,
  `return` unwinds. The per-iteration scope is the entered body's
  environment; this frame carries the *original* `env` for subsequent
  iterations (scope exit by discard, as everywhere in the CEK design).

  ENVELOPE STATEMENT (doctrine requirement 1, SPEC class —
  spec#For_statements, range clause, maps): "The iteration order over
  maps is not specified …. If a map entry that has not yet been
  reached is removed during iteration, the corresponding iteration
  value will not be produced. If a map entry is created during
  iteration, that entry may be produced during the iteration or may be
  skipped. The choice may vary for each entry created and from one
  iteration to the next." The realized set: any interleaved
  production order over live entries; removal exact (absent at pick
  time ⇒ not a candidate; checked live, so a re-created key is a
  candidate again); values live at production; created entries — any
  subset produced, each at any interleaved position, re-creations
  re-producible (the FULL literal envelope: the 2026-08-19 ruling
  REJECTED the at-most-once-per-key and re-created-start-keys-
  mandatory narrowings). Consequences carried deliberately:
  self-inserting loops have genuinely unbounded trace sets
  (∀-streams certification fails closed on them — membership lane
  territory), and the CANONICAL member is BY DEFINITION the machine at
  the zero choice stream (index 0 = first candidate in cell order,
  stop ordered LAST), so mutation-free ranges keep the
  first-remaining-in-insertion-order pick sequence and self-inserting
  loops fuel-out VISIBLY on the strict lane — correct behavior.
  Residual narrowing, recorded: the delete-prune walks the DELETING
  goroutine's own continuation, so a DRF cross-goroutine delete
  (synchronized mid-range) does not prune other goroutines' in-flight
  produced/start sets — re-production of a cross-goroutine
  deleted-then-re-created key is not realized. Recorded at inventory
  E9 with a re-envelope obligation; every same-goroutine shape (all
  probes, all pinned cases) is exact. -/
  | mapIterK (keyVar valVar : Option String) (keyTy valTy : Ty) (body : Stmt)
      (base : Option Loc) (produced : Array GoValue)
      (start : Array GoValue) (env : LocalEnv) (k : Cont)
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
  | .frame t te r ds k w => some (.frame t te r (d :: ds) k w)
  | .seq rest env k => (pushDefer d k).map (Cont.seq rest env)
  | .loop c b env k => (pushDefer d k).map (Cont.loop c b env)
  | .breakableK k => (pushDefer d k).map Cont.breakableK
  | .labelK name k => (pushDefer d k).map (Cont.labelK name)
  | .mapIterK kv vv kt vt b base prod st env k =>
      (pushDefer d k).map (Cont.mapIterK kv vv kt vt b base prod st env)
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
  | .mapIterK _ _ _ _ _ _ _ _ _ k => some k
  | .strictK _ _ _ _ k => some k
  | .andK _ _ k => some k
  | .orK _ _ k => some k
  | .boolK k => some k
  | .ifK _ _ _ k => some k
  | .whileK _ _ _ k => some k
  | .callArgsK _ _ _ _ _ k => some k
  | .stmtOpK _ _ _ _ _ k => some k
  | .mapRangeK _ _ _ _ _ _ k => some k
  | .callValCalleeK _ _ _ k => some k
  | .callValArgsK _ _ _ _ _ k => some k
  | .deferCalleeK _ _ k => some k
  | .deferArgsK _ _ _ _ k => some k
  | .panicArgK k => some k
  | .chanStK _ _ _ _ k => some k
  | .selectOpsK _ _ _ _ _ k => some k
  | .tgtOpK _ _ _ _ _ _ _ _ _ _ k => some k
  | .rhsK _ _ _ _ _ _ k => some k
  | .storeK _ _ _ _ k => some k
  | .goCalleeK _ _ k => some k
  | .goArgsK _ _ _ _ k => some k
  | .syncStK _ _ _ _ k => some k
  | .frame _ _ _ _ _ _ => none
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
  | .frame t te r ds k true =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .frame t te r ds k' true))
  | .frame _ _ _ _ _ false => none
  | .stop => none
  | .seq a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .seq a b k'))
  | .loop a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .loop a b c k'))
  | .breakableK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .breakableK k'))
  | .labelK a k => (recoverThroughWrappers k).map (fun (v, k') => (v, .labelK a k'))
  | .mapIterK a b c d e f g h i k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .mapIterK a b c d e f g h i k'))
  | .strictK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .strictK a b c d k'))
  | .andK a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .andK a b k'))
  | .orK a b k => (recoverThroughWrappers k).map (fun (v, k') => (v, .orK a b k'))
  | .boolK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .boolK k'))
  | .ifK a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .ifK a b c k'))
  | .whileK a b c k => (recoverThroughWrappers k).map (fun (v, k') => (v, .whileK a b c k'))
  | .callArgsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callArgsK a b c d e k'))
  | .stmtOpK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .stmtOpK a b c d e k'))
  | .mapRangeK a b c d e f k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .mapRangeK a b c d e f k'))
  | .callValCalleeK a b c k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callValCalleeK a b c k'))
  | .callValArgsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .callValArgsK a b c d e k'))
  | .deferCalleeK a b k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .deferCalleeK a b k'))
  | .deferArgsK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .deferArgsK a b c d k'))
  | .panicArgK k => (recoverThroughWrappers k).map (fun (v, k') => (v, .panicArgK k'))
  | .chanStK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .chanStK a b c d k'))
  | .selectOpsK a b c d e k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .selectOpsK a b c d e k'))
  | .tgtOpK a b c d e f g h i j k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .tgtOpK a b c d e f g h i j k'))
  | .rhsK a b c d e f k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .rhsK a b c d e f k'))
  | .storeK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .storeK a b c d k'))
  | .goCalleeK a b k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .goCalleeK a b k'))
  | .goArgsK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .goArgsK a b c d k'))
  | .syncStK a b c d k =>
      (recoverThroughWrappers k).map (fun (v, k') => (v, .syncStK a b c d k'))

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
  | .frame t te r ds k false =>
      (match recoverThroughWrappers k with
       | some (v, k') => (v, .frame t te r ds k' false)
       | none => (.nil, .frame t te r ds k false))
  | .frame t te r ds k true =>
      let (v, k') := recoverResult k
      (v, .frame t te r ds k' true)
  | k@.stop => (.nil, k)
  | k@(.panicResumeK _ _) => (.nil, k)
  | .seq a b k => let (v, k') := recoverResult k; (v, .seq a b k')
  | .loop a b c k => let (v, k') := recoverResult k; (v, .loop a b c k')
  | .breakableK k => let (v, k') := recoverResult k; (v, .breakableK k')
  | .labelK a k => let (v, k') := recoverResult k; (v, .labelK a k')
  | .mapIterK a b c d e f g h i k =>
      let (v, k') := recoverResult k; (v, .mapIterK a b c d e f g h i k')
  | .strictK a b c d k => let (v, k') := recoverResult k; (v, .strictK a b c d k')
  | .andK a b k => let (v, k') := recoverResult k; (v, .andK a b k')
  | .orK a b k => let (v, k') := recoverResult k; (v, .orK a b k')
  | .boolK k => let (v, k') := recoverResult k; (v, .boolK k')
  | .ifK a b c k => let (v, k') := recoverResult k; (v, .ifK a b c k')
  | .whileK a b c k => let (v, k') := recoverResult k; (v, .whileK a b c k')
  | .callArgsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callArgsK a b c d e k')
  | .stmtOpK a b c d e k => let (v, k') := recoverResult k; (v, .stmtOpK a b c d e k')
  | .mapRangeK a b c d e f k =>
      let (v, k') := recoverResult k; (v, .mapRangeK a b c d e f k')
  | .callValCalleeK a b c k =>
      let (v, k') := recoverResult k; (v, .callValCalleeK a b c k')
  | .callValArgsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .callValArgsK a b c d e k')
  | .deferCalleeK a b k => let (v, k') := recoverResult k; (v, .deferCalleeK a b k')
  | .deferArgsK a b c d k =>
      let (v, k') := recoverResult k; (v, .deferArgsK a b c d k')
  | .panicArgK k => let (v, k') := recoverResult k; (v, .panicArgK k')
  | .chanStK a b c d k =>
      let (v, k') := recoverResult k; (v, .chanStK a b c d k')
  | .selectOpsK a b c d e k =>
      let (v, k') := recoverResult k; (v, .selectOpsK a b c d e k')
  | .tgtOpK a b c d e f g h i j k =>
      let (v, k') := recoverResult k; (v, .tgtOpK a b c d e f g h i j k')
  | .rhsK a b c d e f k =>
      let (v, k') := recoverResult k; (v, .rhsK a b c d e f k')
  | .storeK a b c d k =>
      let (v, k') := recoverResult k; (v, .storeK a b c d k')
  | .goCalleeK a b k =>
      let (v, k') := recoverResult k; (v, .goCalleeK a b k')
  | .goArgsK a b c d k =>
      let (v, k') := recoverResult k; (v, .goArgsK a b c d k')
  | .syncStK a b c d k =>
      let (v, k') := recoverResult k; (v, .syncStK a b c d k')

/-- Remove every occurrence of `key` (Go map-key equality at `keyTy`)
from a key list — the delete-prune's set subtraction. Structural. -/
def removeKeyList (s : ExecState) (keyTy : Ty) (key : GoValue) :
    List GoValue → Except GoError (List GoValue)
  | [] => return []
  | p :: rest => do
      let tail ← removeKeyList s keyTy key rest
      if ← valueEq s keyTy p key then
        return tail
      else
        return (p :: tail)

/-- Prune one DELETED key out of every in-flight `mapIterK` frame over
`delBase` (BUG-005 (L) surgery): the key leaves the frame's
`produced` set AND its mandatory `start` set — a
deleted-then-re-created key is a NEW entry (adopted reading,
`docs/spec-interpretations.md` I-1 / ledger L-012), so it must be a
candidate again if re-created, and its mandatory status is gone
forever. Key comparison is Go map-key equality at the FRAME's own
key type (the same `valueEq` the map ops use), so the walk is
`Except`-monadic and fails closed on an ill-formed comparison. The
walk crosses every frame (a range body may delete through a call);
it covers the DELETING goroutine's continuation — the cross-goroutine
residual is recorded at inventory E9. -/
def pruneIterFramesKey (s : ExecState) (delBase : Loc) (key : GoValue) :
    Cont → Except GoError Cont
  | .stop => return .stop
  | .seq a b k => do return .seq a b (← pruneIterFramesKey s delBase key k)
  | .loop a b c k => do return .loop a b c (← pruneIterFramesKey s delBase key k)
  | .frame a b c d k w => do return .frame a b c d (← pruneIterFramesKey s delBase key k) w
  | .deferCalleeK a b k => do return .deferCalleeK a b (← pruneIterFramesKey s delBase key k)
  | .deferArgsK a b c d k => do return .deferArgsK a b c d (← pruneIterFramesKey s delBase key k)
  | .breakableK k => do return .breakableK (← pruneIterFramesKey s delBase key k)
  | .labelK a k => do return .labelK a (← pruneIterFramesKey s delBase key k)
  | .callValCalleeK a b c k => do return .callValCalleeK a b c (← pruneIterFramesKey s delBase key k)
  | .callValArgsK a b c d e k => do return .callValArgsK a b c d e (← pruneIterFramesKey s delBase key k)
  | .strictK a b c d k => do return .strictK a b c d (← pruneIterFramesKey s delBase key k)
  | .andK a b k => do return .andK a b (← pruneIterFramesKey s delBase key k)
  | .orK a b k => do return .orK a b (← pruneIterFramesKey s delBase key k)
  | .boolK k => do return .boolK (← pruneIterFramesKey s delBase key k)
  | .ifK a b c k => do return .ifK a b c (← pruneIterFramesKey s delBase key k)
  | .whileK a b c k => do return .whileK a b c (← pruneIterFramesKey s delBase key k)
  | .callArgsK a b c d e k => do return .callArgsK a b c d e (← pruneIterFramesKey s delBase key k)
  | .stmtOpK a b c d e k => do return .stmtOpK a b c d e (← pruneIterFramesKey s delBase key k)
  | .mapRangeK a b c d e f k => do return .mapRangeK a b c d e f (← pruneIterFramesKey s delBase key k)
  | .mapIterK kv vv keyTy valTy body base produced start env k => do
      let k' ← pruneIterFramesKey s delBase key k
      if base == some delBase then
        let produced' := (← removeKeyList s keyTy key produced.toList).toArray
        let start' := (← removeKeyList s keyTy key start.toList).toArray
        return .mapIterK kv vv keyTy valTy body base produced' start' env k'
      else
        return .mapIterK kv vv keyTy valTy body base produced start env k'
  | .panicArgK k => do return .panicArgK (← pruneIterFramesKey s delBase key k)
  | .panicResumeK a k => do return .panicResumeK a (← pruneIterFramesKey s delBase key k)
  | .chanStK a b c d k => do return .chanStK a b c d (← pruneIterFramesKey s delBase key k)
  | .selectOpsK a b c d e k => do return .selectOpsK a b c d e (← pruneIterFramesKey s delBase key k)
  | .tgtOpK a b c d e f g h i j k => do return .tgtOpK a b c d e f g h i j (← pruneIterFramesKey s delBase key k)
  | .rhsK a b c d e f k => do return .rhsK a b c d e f (← pruneIterFramesKey s delBase key k)
  | .storeK a b c d k => do return .storeK a b c d (← pruneIterFramesKey s delBase key k)
  | .goCalleeK a b k => do return .goCalleeK a b (← pruneIterFramesKey s delBase key k)
  | .goArgsK a b c d k => do return .goArgsK a b c d (← pruneIterFramesKey s delBase key k)
  | .syncStK a b c d k => do return .syncStK a b c d (← pruneIterFramesKey s delBase key k)

/-- `clear(m)`'s prune: EVERY key of every in-flight `mapIterK` frame
over `delBase` leaves both sets (all entries were deleted). Pure — no
key comparison is needed to empty a set. -/
def pruneIterFramesAll (delBase : Loc) : Cont → Cont
  | .stop => .stop
  | .seq a b k => .seq a b (pruneIterFramesAll delBase k)
  | .loop a b c k => .loop a b c (pruneIterFramesAll delBase k)
  | .frame a b c d k w => .frame a b c d (pruneIterFramesAll delBase k) w
  | .deferCalleeK a b k => .deferCalleeK a b (pruneIterFramesAll delBase k)
  | .deferArgsK a b c d k => .deferArgsK a b c d (pruneIterFramesAll delBase k)
  | .breakableK k => .breakableK (pruneIterFramesAll delBase k)
  | .labelK a k => .labelK a (pruneIterFramesAll delBase k)
  | .callValCalleeK a b c k => .callValCalleeK a b c (pruneIterFramesAll delBase k)
  | .callValArgsK a b c d e k => .callValArgsK a b c d e (pruneIterFramesAll delBase k)
  | .strictK a b c d k => .strictK a b c d (pruneIterFramesAll delBase k)
  | .andK a b k => .andK a b (pruneIterFramesAll delBase k)
  | .orK a b k => .orK a b (pruneIterFramesAll delBase k)
  | .boolK k => .boolK (pruneIterFramesAll delBase k)
  | .ifK a b c k => .ifK a b c (pruneIterFramesAll delBase k)
  | .whileK a b c k => .whileK a b c (pruneIterFramesAll delBase k)
  | .callArgsK a b c d e k => .callArgsK a b c d e (pruneIterFramesAll delBase k)
  | .stmtOpK a b c d e k => .stmtOpK a b c d e (pruneIterFramesAll delBase k)
  | .mapRangeK a b c d e f k => .mapRangeK a b c d e f (pruneIterFramesAll delBase k)
  | .mapIterK kv vv keyTy valTy body base produced start env k =>
      if base == some delBase then
        .mapIterK kv vv keyTy valTy body base #[] #[] env
          (pruneIterFramesAll delBase k)
      else
        .mapIterK kv vv keyTy valTy body base produced start env
          (pruneIterFramesAll delBase k)
  | .panicArgK k => .panicArgK (pruneIterFramesAll delBase k)
  | .panicResumeK a k => .panicResumeK a (pruneIterFramesAll delBase k)
  | .chanStK a b c d k => .chanStK a b c d (pruneIterFramesAll delBase k)
  | .selectOpsK a b c d e k => .selectOpsK a b c d e (pruneIterFramesAll delBase k)
  | .tgtOpK a b c d e f g h i j k => .tgtOpK a b c d e f g h i j (pruneIterFramesAll delBase k)
  | .rhsK a b c d e f k => .rhsK a b c d e f (pruneIterFramesAll delBase k)
  | .storeK a b c d k => .storeK a b c d (pruneIterFramesAll delBase k)
  | .goCalleeK a b k => .goCalleeK a b (pruneIterFramesAll delBase k)
  | .goArgsK a b c d k => .goArgsK a b c d (pruneIterFramesAll delBase k)
  | .syncStK a b c d k => .syncStK a b c d (pruneIterFramesAll delBase k)

/-- The continuation AFTER a wide-statement apply (BUG-005 (L)
surgery): `mapDelete` prunes the deleted key from every in-flight
iteration over the same map; `clearMap` prunes everything; every other
op leaves the continuation untouched (`.ok k` by `rfl` per op — the
existing wide-statement laws keep their shape at any concrete op).
Shared VERBATIM by rule `stmtOpApply` and `stepFn`'s apply arm. The
nullary rule (`stmtOpNullary`) deliberately does NOT thread it: no
nullary op is a pruning op — `mapDelete` carries two operands and
`clearMap` one — so it would be the identity there (docstring
corrected at the audit fix round, reviewer A nit: it used to claim
the nullary rule shares this function, under a rule name —
`stmtOpStart` — that does not exist). The state argument is the
POST-apply state (key comparison consults `types` only, which no wide
op mutates). -/
def contAfterStmtOp (s : ExecState) (op : StmtOp) (vs : List GoValue)
    (k : Cont) : Except GoError Cont :=
  match op with
  | .mapDelete keyTy =>
      match vs with
      | [baseV, keyV] => do
          let map ← valueAsMap baseV
          match map.base with
          | none => return k
          | some l =>
              pruneIterFramesKey s l (← normalizeValueForTy s keyTy keyV) k
      | _ => return k
  | .clearMap =>
      match vs with
      | [baseV] => do
          let map ← valueAsMap baseV
          match map.base with
          | none => return k
          | some l => return pruneIterFramesAll l k
      | _ => return k
  | _ => return k

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
  | blockedRecv (ch : Option Loc) (targets : List Assignee) (elem : Ty) (env : LocalEnv) (k : Cont)
  | blockedSelect (clauses : List EvClause) (env : LocalEnv) (k : Cont)
  -- The POST-SPAWN completion marker (channels arc slice 4, BUG-040):
  -- the spawn step leaves the PARENT here instead of at `.next k`, and
  -- the pool treats it as a registry boundary — so the scheduling
  -- decision "who runs after the fork" exists as its own registry op
  -- (the child now CAN preempt a sync-free parent segment; without
  -- this the child-first interleaving of the exit-no-sync class was
  -- outside the L1 envelope on every stream). Its only step is the
  -- pool-level strip to `.next k` (`stepThread`; rule
  -- `StepM.spawned`). Pool-only: the sequential machine never
  -- constructs it (`stepFn` fails closed `.internal`), and it is
  -- relation-silent in the per-goroutine `Step` like the blocked
  -- shapes.
  | spawned (k : Cont)
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

/-- Enter a receive's TARGET phase (nonempty targets; convergence
round, BUG-029): resolve the target plan and start phase 1 on the
first target's first operand. Shared verbatim by `applyChanOp` (both
dequeue arms) and `commitClause` — and by `stepFn` through them. The
malformed arms (an empty plan for nonempty targets, a zero-operand
shape) cannot arise from `targetsPlan` — fail closed, never a silent
default. -/
def enterRecvTargets (s : ExecState) (targets : List Assignee)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k : Cont) :
    Except GoError (Config × ExecState) := do
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
`Step.chanStApply` and `stepFn`'s `chanStK` apply arm. -/
def applyChanOp (s : ExecState) (op : ChanStOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except GoError (Config × ExecState) := do
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
  | .recv targets elem, [chv] => do
      let ch ← valueAsChan chv
      match ch.base with
      | none => return (.blockedRecv none targets elem env k, s)
      | some loc => do
          let (buf, capacity, closed) ← chanCell s loc
          match buf[0]? with
          | some v => do
              -- FIFO dequeue; a closed channel drains its buffer
              -- with ok = true before yielding zeros (probe p06).
              let s₁ ← storeLoc s loc (.chanData (buf.eraseIdx! 0) capacity closed)
              match targets with
              | [] => return (.next k, s₁)
              | _ :: _ =>
                  enterRecvTargets s₁ targets (recvStores v true targets.length)
                    (.seqn #[]) env k
          | none =>
              if closed then do
                let zero ← defaultValue s elem
                match targets with
                | [] => return (.next k, s)
                | _ :: _ =>
                    enterRecvTargets s targets (recvStores zero false targets.length)
                      (.seqn #[]) env k
              else
                return (.blockedRecv (some loc) targets elem env k, s)
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
  unlocked; unlocked → the UNRECOVERABLE `GoError.fatal
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
nil-pointer deref inside the method). Shared verbatim by rule
`Step.syncStApply` and `stepFn`'s `syncStK` apply arm. -/
def applySyncOp (s : ExecState) (op : SyncOp) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) : Except GoError (Config × ExecState) := do
  match op, vs with
  | .lock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .mutex locked =>
          if locked then return (.blockedSync .lock loc env k, s)
          else do
            let s' ← storeLoc s loc (.syncData (.mutex true))
            return (.next k, s')
      | other => stuck s!"Lock on a non-mutex sync cell: {repr other}"
  | .unlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .mutex locked =>
          if locked then do
            let s' ← storeLoc s loc (.syncData (.mutex false))
            return (.next k, s')
          else throw (.fatal "sync: unlock of unlocked mutex")
      | other => stuck s!"Unlock on a non-mutex sync cell: {repr other}"
  | .rlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .rwmutex writer readers pendingW =>
          if writer || pendingW > 0 then
            return (.blockedSync .rlock loc env k, s)
          else do
            let s' ← storeLoc s loc (.syncData (.rwmutex writer (readers + 1) pendingW))
            return (.next k, s')
      | other => stuck s!"RLock on a non-RWMutex sync cell: {repr other}"
  | .runlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .rwmutex writer readers pendingW =>
          match readers with
          | r + 1 => do
              let s' ← storeLoc s loc (.syncData (.rwmutex writer r pendingW))
              return (.next k, s')
          | 0 => throw (.fatal "sync: RUnlock of unlocked RWMutex")
      | other => stuck s!"RUnlock on a non-RWMutex sync cell: {repr other}"
  | .wlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .rwmutex writer readers pendingW =>
          if !writer && readers == 0 then do
            let s' ← storeLoc s loc (.syncData (.rwmutex true 0 pendingW))
            return (.next k, s')
          else do
            -- Park AND register as a pending writer: the documented
            -- exclusion of new readers starts at the BLOCKED Lock call
            -- (rwmutex.go), so the count updates at the park.
            let s' ← storeLoc s loc (.syncData (.rwmutex writer readers (pendingW + 1)))
            return (.blockedSync .wlock loc env k, s')
      | other => stuck s!"write-Lock on a non-RWMutex sync cell: {repr other}"
  | .wunlock, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .rwmutex writer readers pendingW =>
          if writer then do
            let s' ← storeLoc s loc (.syncData (.rwmutex false readers pendingW))
            return (.next k, s')
          else throw (.fatal "sync: Unlock of unlocked RWMutex")
      | other => stuck s!"write-Unlock on a non-RWMutex sync cell: {repr other}"
  | .wgAdd, [av, dv] => do
      let loc ← valueAsLoc av
      let delta ← valueAsInt dv
      match ← syncCell s loc with
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
          -- sema WRITE condition (raceUpdate's `.wgWait` arm) gc-exact
          -- across reuse rounds.
          let waiters' := if counter' == 0 && waiters > 0 then 0 else waiters
          -- The update lands BEFORE any panic (probe p13).
          let s' ← storeLoc s loc (.syncData (.waitGroup counter' waiters'))
          if counter' < 0 then
            -- Payload CLASS is gc-exact (arc-end fix round 2026-08-10):
            -- gc's sync package raises this with `panic("...")` — a plain
            -- string, package code — where the channel panics are runtime
            -- `plainError`s. `recover().(string)` answers true here.
            return (.panicking [⟨stringPanicValue
              "sync: negative WaitGroup counter", false⟩] k, s')
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
            return (.next k, s')
      | other => stuck s!"Add on a non-WaitGroup sync cell: {repr other}"
  | .wgWait, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .waitGroup counter waiters =>
          if counter == 0 then return (.next k, s)
          else do
            let s' ← storeLoc s loc (.syncData (.waitGroup counter (waiters + 1)))
            return (.blockedSync .wgWait loc env k, s')
      | other => stuck s!"Wait on a non-WaitGroup sync cell: {repr other}"
  | .onceBegin targets, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .once started done =>
          if !started then do
            let s' ← storeLoc s loc (.syncData (.once true false))
            enterRecvTargets s' targets [.bool true] (.seqn #[]) env k
          else if done then
            enterRecvTargets s targets [.bool false] (.seqn #[]) env k
          else
            return (.blockedSync (.onceBegin targets) loc env k, s)
      | other => stuck s!"Once.Do begin on a non-Once sync cell: {repr other}"
  | .onceComplete, [av] => do
      let loc ← valueAsLoc av
      match ← syncCell s loc with
      | .once started _ =>
          if started then do
            let s' ← storeLoc s loc (.syncData (.once true true))
            return (.next k, s')
          else throw (.internal "onceComplete without a matching onceBegin")
      | other => stuck s!"Once.Do complete on a non-Once sync cell: {repr other}"
  | op, vs => stuck s!"malformed sync-operator application: {repr op} on {vs.length} operand(s)"

/-- Commit the ONE ready clause of a `select` (spec step 3): perform its
communication, then enter the body — for a receive with targets, via
the phase-1/phase-2 delivery frames (`enterRecvTargets`; spec step 4:
LHS after the communication). A committed SEND on a closed channel
panics (probe p23 — closed counts as ready). The "unready" stuck arms
are unreachable from `applySelect` (which commits only ready clauses) —
fail closed, never a silent default. -/
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
          | _ :: _ =>
              enterRecvTargets s₁ targets (recvStores v ok targets.length) body env k

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

The spec's step 3 — "If one or more of the communications can
proceed, a single one that can proceed is chosen via a uniform
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
  detector never re-derive it from the readiness analysis). -/
  | done (c : Config) (σ : ExecState) (committed? : Option EvClause)
  /-- Multi-ready (≥ 2): the PRE-COMMITTED result of every ready
  clause, clause order, for the L2 pick — each paired with ITS clause
  (Q2's emitted commit identity) — `.inl` a committed configuration,
  `.inr` a panic message. -/
  | picks (commits : List (EvClause × Sum (Config × ExecState) String))

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
def applySelectCore (s : ExecState)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
    (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    Except GoError SelectOutcome := do
  let evs ← evalClauses clauses vs
  match ← readyClauses s evs with
  | [] =>
      match default? with
      | some d => return .done (.exec d env k) s none
      | none => return .done (.blockedSelect evs env k) s none
  | [c] => do
      let (c', s') ← commitClause s env k c
      return .done c' s' (some c)
  | ready => do
      let commits ← ready.mapM fun cl =>
        (match commitClause s env k cl with
        | .ok r => .ok (cl, .inl r)
        | .error (.panic msg) => .ok (cl, .inr msg)
        | .error e => .error e :
          Except GoError (EvClause × Sum (Config × ExecState) String))
      return .picks commits

@[inherit_doc applySelectCore]
def applySelect (s : ExecState) (clauses : List (SelectClauseHead × Stmt))
    (default? : Option Stmt) (vs : List GoValue) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    Except GoError (Config × ExecState × Choices × Option EvClause) := do
  -- The 4th component is Q2's emitted commit identity (`none` =
  -- default taken or parked): the sequential `stepFn` arm PROJECTS it
  -- away; the pool's select interception (`stepThread`) carries it
  -- into the step event so the race detector folds it instead of
  -- replaying the readiness analysis and the stream.
  match ← applySelectCore s clauses default? vs env k with
  | .done c' s' cl? => return (c', s', ch, cl?)
  | .picks commits =>
      -- THE L2 CONSUMPTION (envelope statement in the docstring
      -- above): bound = the ready-clause count, ≥ 2 by construction
      -- (`.picks` arises only from a multi-ready analysis).
      let (idx, ch') := Choices.consumeAt .l2Entry commits.length ch
      match commits[idx]? with
      | some (cl, .inl (c', s')) => return (c', s', ch', some cl)
      | some (cl, .inr msg) =>
          -- Defensive arm (unreachable today — docstring above): the
          -- picked clause's panic becomes a `.panicking` configuration
          -- with the pick CONSUMED, exactly like the `.inl` route.
          return (.panicking [⟨runtimeErrorValue msg, false⟩] k, s, ch', some cl)
      | none => throw (.internal "select ready-clause pick out of range")

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
  -- Assignment (round 4, BUG-037): the SINGLE assignment rides the
  -- phase-split spine as a one-target multi-assign — the RHS is
  -- phase 1, the target chain's checks fire at the store (phase 2).
  -- Rules appended at the END of the inductive with their spine
  -- siblings.
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
  | breakToMapIter {L keyVar valVar keyTy valTy body base produced start env k s} :
      Step (.breakingTo L (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
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
  | continueToMapIterMatch {L keyVar valVar keyTy valTy body base produced start env k s} :
      contHeadLabel k = some L →
      Step (.continuingTo L (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
  | continueToMapIterSkip {L keyVar valVar keyTy valTy body base produced start env k s} :
      contHeadLabel k ≠ some L →
      Step (.continuingTo L (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.continuingTo L k) s
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
        (.evalE a env (.callArgsK fid plans [] rest env k)) s
  | callImmediate {targets fid args plans func frameEnv resultLocs env k s s'} :
      targetsPlan targets.toList = some plans →
      args.toList = [] →
      enterFrame s fid [] = .ok (func, frameEnv, resultLocs, s') →
      Step (.exec (.call targets fid args) env k) s
        (.exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper)) s'
  | callArgNext {v fid plans vals a rest env k s} :
      Step (.retV v (.callArgsK fid plans vals (a :: rest) env k)) s
        (.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k)) s
  | callArgsDoneEnter {v fid plans vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callArgsK fid plans vals [] env k)) s
        (.exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper)) s'
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
  -- nil-target panic surfaces through `applyStmtOp`'s per-arm
  -- `valueAsLoc` checks — rule `stmtOpApplyPanic` — keeping the rules
  -- in one-to-one correspondence with `stepFn`'s arms.)
  | stmtOpTargetPanic {op nt done v msg e rest env k s} :
      done.length < nt →
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | stmtOpApply {op nt done v env k k' s s' ch ch'} :
      applyStmtOp s ch op nt (v :: done).reverse = .ok (s', ch') →
      contAfterStmtOp s' op (v :: done).reverse k = .ok k' →
      Step (.retV v (.stmtOpK op nt done [] env k)) s (.next k') s'
  | stmtOpApplyPanic {op nt done v msg env k s ch} :
      applyStmtOp s ch op nt (v :: done).reverse = .error (.panic msg) →
      Step (.retV v (.stmtOpK op nt done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- Map iteration — LIVE (BUG-005 (L) surgery, ruled 2026-08-19; the
  -- snapshot rules are retired): start records the base cell and the
  -- START-KEY set; each pick LOADS the live cell, filters candidates
  -- by the produced-key set, and either picks ANY candidate (the
  -- nondeterministic order latitude + the created-entries latitude) or
  -- STOPS, the stop legal only when no never-removed start key remains
  -- a candidate (the spec-forced traversal clause). The envelope
  -- statement lives on `Cont.mapIterK`'s docstring; the executable
  -- consumes one choice of width `candidates + stop`, stop LAST — the
  -- zero stream IS the canonical member, by definition.
  | mapRange {keyVar valVar mapExpr keyTy valTy body env k s} :
      Step (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) s
        (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k)) s
  | mapRangeStart {v base start keyVar valVar keyTy valTy body env k s} :
      mapRangeStartSets s v = .ok (base, start) →
      Step (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body base #[] start env k)) s
  | mapIterDone {keyVar valVar keyTy valTy body base produced start env k s} :
      mapIterCandidates s keyTy valTy base produced = .ok #[] →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next k) s
  | mapIterNext {keyVar valVar keyTy valTy body base produced start cands mand idx env env' k s s'}
      (hidx : idx < cands.size) :
      mapIterCandidates s keyTy valTy base produced = .ok cands →
      -- The mandatory computation must SUCCEED (its value is free): the
      -- executable computes the pick width from it on every nonempty
      -- pick, so completeness (`step_complete`) needs its success as a
      -- rule premise — an error there is a stuck step on both sides.
      mapIterMandatoryRemains s keyTy cands start = .ok mand →
      bindIterVars env.pushScope s keyVar valVar keyTy valTy
        cands[idx].1 cands[idx].2 = .ok (env', s') →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.exec body env' (.mapIterK keyVar valVar keyTy valTy body
          base (produced.push cands[idx].1) start env k)) s'
  | mapIterStop {keyVar valVar keyTy valTy body base produced start cands env k s} :
      mapIterCandidates s keyTy valTy base produced = .ok cands →
      cands.size ≠ 0 →
      mapIterMandatoryRemains s keyTy cands start = .ok false →
      Step (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next k) s
  | mapIterContinue {keyVar valVar keyTy valTy body base produced start env k s} :
      Step (.continuing (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
  | mapIterBreak {keyVar valVar keyTy valTy body base produced start env k s} :
      Step (.breaking (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.next k) s
  | mapIterReturn {keyVar valVar keyTy valTy body base produced start env k s} :
      Step (.returning (.mapIterK keyVar valVar keyTy valTy body base produced start env k)) s
        (.returning k) s
  -- Call through a function VALUE (§8): targets, then the callee, then the
  -- arguments; frame entry prepends the closure's captured values, which is
  -- the whole lambda-lifting protocol. `enterFrame` is reused verbatim.
  -- Call through a value (§8), same BUG-052 order pin: callee, then
  -- arguments, then frame entry — the caller-target plans ride to the
  -- frame; target operands evaluate at frame exit.
  | callValueStart {targets callee args plans env k s} :
      targetsPlan targets.toList = some plans →
      Step (.exec (.callValue targets callee args) env k) s
        (.evalE callee env (.callValCalleeK plans args.toList env k)) s
  /-- The callee value arrives (funcVal or nil); start the arguments. Go
  evaluates the callee and ALL arguments before the nil check fires. -/
  | callValCalleeArg {cv plans a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.callValCalleeK plans (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv plans [] rest env k)) s
  /-- Nullary call through a value: enter directly with the captures. -/
  | callValCalleeEnter {fid captured plans func frameEnv resultLocs env k s s'} :
      enterFrame s fid captured = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k)) s
        (.exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper)) s'
  /-- Nullary call of a nil function value: nothing to evaluate, panic. -/
  | callValCalleeNil {plans env k s} :
      Step (.retV .nil (.callValCalleeK plans [] env k)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩] k) s
  | callValArgNext {v cv plans vals a rest env k s} :
      Step (.retV v (.callValArgsK cv plans vals (a :: rest) env k)) s
        (.evalE a env (.callValArgsK cv plans (vals ++ [v]) rest env k)) s
  | callValArgsEnter {v fid captured plans vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (captured ++ vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k)) s
        (.exec func.body frameEnv (.frame plans env resultLocs [] k func.wrapper)) s'
  /-- All arguments evaluated, callee is nil: NOW the invocation panics. -/
  | callValArgsNil {v plans vals env k s} :
      Step (.retV v (.callValArgsK .nil plans vals [] env k)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩] k) s
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
  | frameReturn {tenv k w s} :
      Step (.returning (.frame [] tenv [] [] k w)) s (.next k) s
  | frameFall {tenv k w s} :
      Step (.next (.frame [] tenv [] [] k w)) s (.next k) s
  | frameReturnTargets {sh e ops rest tenv results k w s vs} :
      loadMany s results = .ok vs →
      Step (.returning (.frame ((sh, e :: ops) :: rest) tenv results [] k w)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s
  | frameFallTargets {sh e ops rest tenv results k w s vs} :
      loadMany s results = .ok vs →
      Step (.next (.frame ((sh, e :: ops) :: rest) tenv results [] k w)) s
        (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k)) s
  -- Draining the defer chain: one deferred call per step, each in its own
  -- frame whose continuation is this frame with the rest of the chain, so
  -- both exit paths converge on the rules above once the chain is empty.
  -- The inner frame has NO targets and NO results: a deferred call's
  -- results are discarded in Go (`defer/defer-function-result-discard`).
  | frameDeferFall {targets tenv results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.next (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] [] (.frame targets tenv results ds k w) func.wrapper)) s'
  | frameDeferReturn {targets tenv results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.returning (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] [] (.frame targets tenv results ds k w) func.wrapper)) s'
  /-- Invoking a nil deferred call panics at DRAIN time (Go: registration
  succeeded; the panic belongs to the invocation). The panic starts
  unwinding AT THIS FRAME with its remaining defers — which run, and may
  recover (`defer/defer-nil-function-recover-order` pins the order). -/
  | frameDeferNilFall {targets tenv results args ds k w s} :
      Step (.next (.frame targets tenv results ((.nil, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩]
          (.frame targets tenv results ds k w)) s
  | frameDeferNilReturn {targets tenv results args ds k w s} :
      Step (.returning (.frame targets tenv results ((.nil, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩]
          (.frame targets tenv results ds k w)) s
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
  | panicFrameEmpty {chain targets tenv results k w s} :
      Step (.panicking chain (.frame targets tenv results [] k w)) s
        (.panicking chain k) s
  /-- Defers RUN on the panic path: the deferred call executes above a
  `panicResumeK` carrying the suspended chain — the shape `recover`'s
  walk detects. Results discarded, as on the normal drain. -/
  | panicFrameDefer {chain targets tenv results fid captured args ds k w s func frameEnv resultLocs s'} :
      enterFrame s fid (captured ++ args) = .ok (func, frameEnv, resultLocs, s') →
      Step (.panicking chain (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.exec func.body frameEnv
          (.frame [] [] [] [] (.panicResumeK chain (.frame targets tenv results ds k w)) func.wrapper)) s'
  /-- A nil deferred callee invoked DURING unwinding: the invocation's
  nil-dereference panic joins the chain (newest last) and this frame's
  remaining defers keep draining. -/
  | panicFrameDeferNil {chain targets tenv results args ds k w s} :
      Step (.panicking chain (.frame targets tenv results ((.nil, args) :: ds) k w)) s
        (.panicking (chain ++ [⟨runtimeErrorValue
          "runtime error: invalid memory address or nil pointer dereference", false⟩])
          (.frame targets tenv results ds k w)) s
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
  | callImmediatePanic {targets fid args plans msg env k s} :
      targetsPlan targets.toList = some plans →
      args.toList = [] →
      enterFrame s fid [] = .error (.panic msg) →
      Step (.exec (.call targets fid args) env k) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callArgsDoneEnterPanic {v fid plans vals msg env k s} :
      enterFrame s fid (vals ++ [v]) = .error (.panic msg) →
      Step (.retV v (.callArgsK fid plans vals [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callValCalleeEnterPanic {fid captured plans msg env k s} :
      enterFrame s fid captured = .error (.panic msg) →
      Step (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | callValArgsEnterPanic {v fid captured plans vals msg env k s} :
      enterFrame s fid (captured ++ vals ++ [v]) = .error (.panic msg) →
      Step (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k)) s
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
  | frameDeferFallEnterPanic {targets tenv results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.next (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] (.frame targets tenv results ds k w)) s
  | frameDeferReturnEnterPanic {targets tenv results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.returning (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] (.frame targets tenv results ds k w)) s
  | panicFrameDeferEnterPanic {chain targets tenv results fid captured args ds k w s msg} :
      enterFrame s fid (captured ++ args) = .error (.panic msg) →
      Step (.panicking chain (.frame targets tenv results ((.funcVal fid captured, args) :: ds) k w)) s
        (.panicking (chain ++ [⟨runtimeErrorValue msg, false⟩])
          (.frame targets tenv results ds k w)) s
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
      Step (.exec stmt env k) s (.evalE e env (.chanStK op [] rest env k)) s
  | chanStShift {op done v e rest env k s} :
      Step (.retV v (.chanStK op done (e :: rest) env k)) s
        (.evalE e env (.chanStK op (v :: done) rest env k)) s
  | chanStApply {op done v c' env k s s'} :
      applyChanOp s op (v :: done).reverse env k = .ok (c', s') →
      Step (.retV v (.chanStK op done [] env k)) s c' s'
  | chanStApplyPanic {op done v msg env k s} :
      applyChanOp s op (v :: done).reverse env k = .error (.panic msg) →
      Step (.retV v (.chanStK op done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
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
  -- The apply rules quantify the CHOICE STREAM (`stmtOpApply`'s idiom):
  -- multi-ready readiness draws the L2 clause pick from it (slice 4 —
  -- the envelope statement is `applySelect`'s docstring), so any
  -- ready clause's commit is a legal step.
  | selectApply {clauses default? done v c' env k s s' ch ch' cl?} :
      -- The rule quantifies the stream AND the apply's emitted commit
      -- identity (Q2's 4th component — instrumentation, not semantics;
      -- the successor configuration is what the rule relates).
      applySelect s clauses default? (v :: done).reverse env k ch = .ok (c', s', ch', cl?) →
      Step (.retV v (.selectOpsK clauses default? done [] env k)) s c' s'
  | selectApplyPanic {clauses default? done v msg env k s ch} :
      applySelect s clauses default? (v :: done).reverse env k ch = .error (.panic msg) →
      Step (.retV v (.selectOpsK clauses default? done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  -- Receive delivery, phases SPLIT (convergence round, BUG-029): phase
  -- 1 (`tgtOpK`) evaluates every target's OPERANDS left-to-right,
  -- resolving each target to a store-ready `TargetRef` with its outer
  -- nil/bounds check DEFERRED; phase 2 (`storeK`, `.next`-driven)
  -- stores left-to-right, ONE step per target, store-time panics
  -- firing after earlier stores landed.
  | tgtOpShift {sh ops v e pending refs targets rop rhs vals body env k s} :
      Step (.retV v (.tgtOpK sh ops (e :: pending) refs targets rop rhs vals body env k)) s
        (.evalE e env (.tgtOpK sh (v :: ops) pending refs targets rop rhs vals body env k)) s
  | tgtOpNext {sh ops v r sh' e ops' targets refs rop rhs vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: targets) rop rhs vals body env k)) s
        (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) targets rop rhs vals body env k)) s
  | tgtOpStores {sh ops v r refs rop vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs [] rop [] vals body env k)) s
        (.next (.storeK (refs ++ [r]) vals body env k)) s
  -- Spine-riding assignments (BUG-025; single form and comma-ok
  -- sources round 4, BUG-034/BUG-037): phase 1 resolves the targets,
  -- the RHS evaluates left-to-right (`rhsK`), the value source
  -- applies (`applyRhsOp` — identity / map lookup / type assert),
  -- phase 2 stores one step per target with the chain's checks firing
  -- at the store.
  | tgtOpRhs {sh ops v r refs rop e rest vals body env k s} :
      completeTargetRef sh (v :: ops).reverse = some r →
      Step (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals body env k)) s
        (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k)) s
  | rhsShift {rop refs done v e rest body env k s} :
      Step (.retV v (.rhsK rop refs done (e :: rest) body env k)) s
        (.evalE e env (.rhsK rop refs (v :: done) rest body env k)) s
  | rhsStores {rop refs done v vals body env k s} :
      applyRhsOp s rop (v :: done).reverse = .ok vals →
      Step (.retV v (.rhsK rop refs done [] body env k)) s
        (.next (.storeK refs vals body env k)) s
  | rhsStoresPanic {rop refs done v msg body env k s} :
      applyRhsOp s rop (v :: done).reverse = .error (.panic msg) →
      Step (.retV v (.rhsK rop refs done [] body env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | assignManyFirst {left right sh e ops rest env k s} :
      left.size = right.size →
      targetsPlan left.toList = some ((sh, e :: ops) :: rest) →
      Step (.exec (.assignMany left right) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k)) s
  | assignFirst {lhs rhs sh e ops env k s} :
      targetPlan lhs = some (sh, e :: ops) →
      Step (.exec (.assign lhs rhs) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k)) s
  | mapLookupFirst {t okT base index keyTy valueTy sh e ops rest env k s} :
      targetsPlan [t, okT] = some ((sh, e :: ops) :: rest) →
      Step (.exec (.mapLookup t okT base index keyTy valueTy) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy)
          [base, index] [] (.seqn #[]) env k)) s
  | typeAssertFirst {t okT expr targetTy sh e ops rest env k s} :
      targetsPlan [t, okT] = some ((sh, e :: ops) :: rest) →
      Step (.exec (.typeAssert t okT expr targetTy) env k) s
        (.evalE e env (.tgtOpK sh [] ops [] rest (.typeAssert targetTy)
          [expr] [] (.seqn #[]) env k)) s
  | storeStep {r rs val vals body env k s s'} :
      storeTarget s r val = .ok s' →
      Step (.next (.storeK (r :: rs) (val :: vals) body env k)) s
        (.next (.storeK rs vals body env k)) s'
  | storeStepPanic {r rs val vals msg body env k s} :
      storeTarget s r val = .error (.panic msg) →
      Step (.next (.storeK (r :: rs) (val :: vals) body env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s
  | storeDone {body env k s} :
      Step (.next (.storeK [] [] body env k)) s (.exec body env k) s
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
        (.evalE callee env (.goCalleeK args.toList env k)) s
  | goCalleeArg {cv a rest env k s} :
      deferrableCallee cv = true →
      Step (.retV cv (.goCalleeK (a :: rest) env k)) s
        (.evalE a env (.goArgsK cv [] rest env k)) s
  | goArgNext {v cv vals a rest env k s} :
      Step (.retV v (.goArgsK cv vals (a :: rest) env k)) s
        (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k)) s
  -- Sync statements (spec-parity slice 2, design note §§4,6): the
  -- `chanStK` shape verbatim — operand entry/shift, then ONE apply
  -- step (`applySyncOp`: next / panicking / blocked / an onceBegin
  -- delivery entry). The FATAL outcomes (unlock-of-unlocked etc.) are
  -- `Except.error (.fatal …)` from the apply and therefore
  -- RELATION-SILENT, like the diagnostic errors — an unrecoverable
  -- abort has no successor configuration. The blocked shape
  -- `.blockedSync` has no outgoing per-goroutine rule (the pool wakes
  -- it); the apply consumes NO choices (the envelope statement at
  -- `applySyncOp`).
  | syncStFirst {stmt op e rest env k s} :
      syncPlan stmt = some (op, e :: rest) →
      Step (.exec stmt env k) s (.evalE e env (.syncStK op [] rest env k)) s
  | syncStShift {op done v e rest env k s} :
      Step (.retV v (.syncStK op done (e :: rest) env k)) s
        (.evalE e env (.syncStK op (v :: done) rest env k)) s
  | syncStApply {op done v c' env k s s'} :
      applySyncOp s op (v :: done).reverse env k = .ok (c', s') →
      Step (.retV v (.syncStK op done [] env k)) s c' s'
  | syncStApplyPanic {op done v msg env k s} :
      applySyncOp s op (v :: done).reverse env k = .error (.panic msg) →
      Step (.retV v (.syncStK op done [] env k)) s
        (.panicking [⟨runtimeErrorValue msg, false⟩] k) s

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
  | .panicked _ => True
  | _ => False

end GoLean.GoCore.Machine
