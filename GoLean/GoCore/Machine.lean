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
- **Panic propagation is free**: a panic step abandons the whole
  continuation (`.panicked` is terminal), so the old per-operator
  `binPanicLeft/Right`-style propagation rules have no analogue here.
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
  | typeAssert (target : Ty)
  | indexGet | indexAddr
  | mapGet (keyTy valueTy : Ty)
  | sliceExpr (hasMax : Bool)
  | lengthOf (typ : Option Ty)
  | capacityOf (typ : Option Ty)
  | defaultValueOf (ty : Ty)
  | nilLit (typ : Option Ty)
  /-- Build a closure value from its captured operands (§8). -/
  | funcValOf (fid : FuncId)
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
  | .typeAssert e target => some (.typeAssert target, [e])
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
      | .string lv, .string rv => return (.string (GoString.append lv rv), s)
      | _, _ => stuck s!"mismatched + operands: {repr l} and {repr r}"
  | .sub, [l, r] => do return ((← intBinaryResult "-" (· - ·) l r), s)
  | .mul, [l, r] => do return ((← intBinaryResult "*" (· * ·) l r), s)
  | .div, [l, r] => do
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
  | .not, [v] => do return (.bool (!(← valueAsBool v)), s)
  | .eqCmp ty, [l, r] => do return (.bool (← valueEq s ty l r), s)
  | .neqCmp ty, [l, r] => do return (.bool (!(← valueEq s ty l r)), s)
  | .atMostCmp, [l, r] => do return (.bool (← valueAtMost l r), s)
  | .atLeastCmp, [l, r] => do return (.bool (← valueAtLeast l r), s)
  | .lessCmp, [l, r] => do return (.bool (← valueLess l r), s)
  | .greaterCmp, [l, r] => do return (.bool (← valueGreater l r), s)
  | .convert ty, [v] => do return ((← convertValueToTy s ty v), s)
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
  | .toInterface _ dynamic, [v] =>
      match dynamicTypeName? s dynamic with
      | some dynamicName => return (.interface dynamicName v, s)
      | none => unsupported s!"interface conversion for dynamic type {repr dynamic}"
  | .typeAssert targetTy, [v] => do
      let result ← typeAssertValue s v targetTy
      if result.2 then
        return (result.1, s)
      else
        panic (typeAssertPanicMessage s v targetTy)
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
      | none => return ((← defaultValue s valueTy), s)
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
          | other => unsupported s!"cap for non-array/slice value {repr other}"
  | .funcValOf fid, vs => return (.funcVal fid vs, s)
  | .defaultValueOf ty, [] => do return ((← defaultValue s ty), s)
  | .nilLit typ, [] =>
      match typ with
      | none => return (.nil, s)
      | some ty =>
          match ty with
          | .slice _ => do return ((← defaultValue s ty), s)
          | .map _ _ => do return ((← defaultValue s ty), s)
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
  | mapAssign (keyTy valueTy : Ty)
  | mapLookup (keyTy valueTy : Ty)
  | typeAssertStmt (targetTy : Ty)
  | appendSlice (elem : Ty)
  | copySlice
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
  | _ => none

/-- Extract target locations from already-checked address values. -/
def locsOf : List GoValue → Except GoError (List Loc)
  | [] => return []
  | v :: vs => do return (← valueAsLoc v) :: (← locsOf vs)

/-- Apply a wide statement's head to its evaluated operands (`nt` leading
target addresses, then values). One state-update step; transcribed from the
big-step interpreter's exec helpers minus the operand recursion.
`appendSlice`'s spill path consumes a capacity choice — the second
nondeterministic point, threaded exactly as the interpreter does. -/
def applyStmtOp (s : ExecState) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : Except GoError (ExecState × Choices) := do
  match op with
  | .assignMany => do
      let locs ← locsOf (vs.take nt)
      return ((← storeMany s locs (vs.drop nt)), choices)
  | .newValue typ =>
      match vs with
      | [tv, value] => do
          let loc ← valueAsLoc tv
          let (nloc, s₁) := s.alloc value typ
          return ((← storeLoc s₁ loc (.addr nloc)), choices)
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
      return ((← storeLoc s₁ loc (.slice { base := some base, offset := 0, len, cap })), choices)
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
      return ((← storeLoc s₁ loc (.map { base := some base })), choices)
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
                match ← mapEntryIndex? s keyTy entries key with
                | some i => pure (entries.set! i (key, value))
                | none => pure (entries.push (key, value))
              return ((← storeLoc s baseLoc (.mapData entries)), choices)
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
          return ((← storeLoc s₁ okloc (.bool pair.2)), choices)
      | _ => stuck "malformed mapLookup operands"
  | .typeAssertStmt targetTy =>
      match vs with
      | [tv, okv, value] => do
          let result ← typeAssertValue s value targetTy
          let tloc ← valueAsLoc tv
          let okloc ← valueAsLoc okv
          let s₁ ← storeLoc s tloc result.1
          return ((← storeLoc s₁ okloc (.bool result.2)), choices)
      | _ => stuck "malformed typeAssert operands"
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
            let (extra, choices) := choices.consume 8
            let newCap := appendGrowthCap slice.cap newLen + extra
            let backing ← buildAppendBackingValue s elem oldValues elemValues newCap
            let (base, current) := s.alloc backing (some (.array newCap elem))
            return ((← storeLoc current tloc
              (.slice { base := some base, offset := 0, len := newLen, cap := newCap })), choices)
      | _ => stuck "malformed appendSlice operands"
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
          return ((← storeLoc current tloc (.int (Int.ofNat count))), choices)
      | _ => stuck "malformed copySlice operands"

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
  mutation of a named result observable (W3 §9). -/
  | frame (targets : List Loc) (results : List Loc)
      (defers : List (FuncId × List GoValue)) (k : Cont)
  /-- Awaiting a deferred call's callee value. -/
  | deferCalleeK (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting a deferred call's arguments; they are evaluated AT DEFER
  TIME (Go), then the call is prepended to the innermost frame's chain. -/
  | deferArgsK (fid : FuncId) (captured : List GoValue) (vals : List GoValue)
      (pending : List Expr) (env : LocalEnv) (k : Cont)
  /-- Breakable scope (`Stmt.breakable`): catches `breaking`, passes
  `continuing`/`returning` through. -/
  | breakableK (k : Cont)
  /-- Call-through-value (§8): awaiting a target address; then remaining
  targets, then the callee expression. -/
  | callValTargetsK (callee : Expr) (locs : List Loc) (pending : List Expr)
      (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting the CALLEE value (a `funcVal`, or `nil` → panic). -/
  | callValCalleeK (locs : List Loc) (args : List Expr) (env : LocalEnv) (k : Cont)
  /-- Awaiting an argument of a value call; `captured` are the closure's
  captured values, prepended to the arguments at frame entry. -/
  | callValArgsK (fid : FuncId) (captured : List GoValue) (locs : List Loc)
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

/-- The continuation for entering a `.seqn`: under a same-env governing
sequence, SPLICE the statements into it (D1) — Go statement lists splice
and only blocks scope. Any other continuation wraps in a fresh seq node. -/
def seqCont (ss : List Stmt) (env : LocalEnv) : Cont → Cont
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

/-- Prepend a pending call onto the innermost enclosing frame's defer chain
(LIFO). Statement-shaped continuations are walked through; a `defer`
outside any frame (or under an expression frame, which cannot contain a
statement) has no rule — fail closed. -/
def pushDefer (d : FuncId × List GoValue) : Cont → Option Cont
  | .frame t r ds k => some (.frame t r (d :: ds) k)
  | .seq rest env k => (pushDefer d k).map (Cont.seq rest env)
  | .loop c b env k => (pushDefer d k).map (Cont.loop c b env)
  | .breakableK k => (pushDefer d k).map Cont.breakableK
  | .mapIterK kv vv kt vt b rem env k =>
      (pushDefer d k).map (Cont.mapIterK kv vv kt vt b rem env)
  | _ => none

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
  | panicked (msg : String)

/-! ## The step relation -/

/-- One machine step over `(control, state)` pairs. No rule applies to
malformed or unmodeled configurations: they are stuck (fail closed). A
panic step abandons the continuation — `.panicked` is terminal, so panic
propagation needs no rules. Nondeterministic steps (map iteration order,
append capacity) arrive at S2 with their statements. -/
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
      Step (.evalE e env k) s (.panicked msg) s
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
      Step (.retV v (.strictK op done [] env k)) s (.panicked msg) s
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
      Step (.retV v (.assignTargetK rhs env k)) s (.panicked msg) s
  | assignStore {v loc k s s'} :
      storeLoc s loc v = .ok s' →
      Step (.retV v (.assignStoreK loc k)) s (.next k) s'
  | assignStorePanic {v loc msg k s} :
      storeLoc s loc v = .error (.panic msg) →
      Step (.retV v (.assignStoreK loc k)) s (.panicked msg) s
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
        (.exec func.body frameEnv (.frame [] resultLocs [] k)) s'
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
        (.exec func.body frameEnv (.frame (locs ++ [loc]) resultLocs [] k)) s'
  | callTargetPanic {v msg fid locs pending args env k s} :
      valueAsLoc v = .error (.panic msg) →
      Step (.retV v (.callTargetsK fid locs pending args env k)) s
        (.panicked msg) s
  | callArgNext {v fid locs vals a rest env k s} :
      Step (.retV v (.callArgsK fid locs vals (a :: rest) env k)) s
        (.evalE a env (.callArgsK fid locs (vals ++ [v]) rest env k)) s
  | callArgsDoneEnter {v fid locs vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callArgsK fid locs vals [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k)) s'
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
      Step (.retV v (.stmtOpK op nt done (e :: rest) env k)) s (.panicked msg) s
  | stmtOpApply {op nt done v env k s s' ch ch'} :
      applyStmtOp s ch op nt (v :: done).reverse = .ok (s', ch') →
      Step (.retV v (.stmtOpK op nt done [] env k)) s (.next k) s'
  | stmtOpApplyPanic {op nt done v msg env k s ch} :
      applyStmtOp s ch op nt (v :: done).reverse = .error (.panic msg) →
      Step (.retV v (.stmtOpK op nt done [] env k)) s (.panicked msg) s
  -- Map iteration (S2): snapshot, then nondeterministic pick-next — any
  -- in-range index is a legal step (the executable instantiates the pick
  -- from `Choices`, one choice per remaining entry).
  | mapRange {keyVar valVar mapExpr keyTy valTy body env k s} :
      Step (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) s
        (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k)) s
  | mapRangeSnapshot {v entries keyVar valVar keyTy valTy body env k s} :
      mapRangeEntries s v = .ok entries →
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
        (.panicked msg) s
  /-- The callee value arrives; start the arguments. -/
  | callValCalleeArg {fid captured locs a rest env k s} :
      Step (.retV (.funcVal fid captured) (.callValCalleeK locs (a :: rest) env k)) s
        (.evalE a env (.callValArgsK fid captured locs [] rest env k)) s
  /-- Nullary call through a value: enter directly with the captures. -/
  | callValCalleeEnter {fid captured locs func frameEnv resultLocs env k s s'} :
      enterFrame s fid captured = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV (.funcVal fid captured) (.callValCalleeK locs [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k)) s'
  /-- Calling a nil function value panics (Go). -/
  | callValCalleeNil {locs args env k s} :
      Step (.retV .nil (.callValCalleeK locs args env k)) s
        (.panicked "runtime error: invalid memory address or nil pointer dereference") s
  | callValArgNext {v fid captured locs vals a rest env k s} :
      Step (.retV v (.callValArgsK fid captured locs vals (a :: rest) env k)) s
        (.evalE a env (.callValArgsK fid captured locs (vals ++ [v]) rest env k)) s
  | callValArgsEnter {v fid captured locs vals func frameEnv resultLocs env k s s'} :
      enterFrame s fid (captured ++ vals ++ [v]) = .ok (func, frameEnv, resultLocs, s') →
      Step (.retV v (.callValArgsK fid captured locs vals [] env k)) s
        (.exec func.body frameEnv (.frame locs resultLocs [] k)) s'
  -- Frame exit: explicit return and fall-through perform the same
  -- pinned-location result read and caller-target stores.
  | frameReturn {targets results k s vs s'} :
      loadMany s results = .ok vs →
      storeMany s targets vs = .ok s' →
      Step (.returning (.frame targets results [] k)) s (.next k) s'
  | frameFall {targets results k s vs s'} :
      loadMany s results = .ok vs →
      storeMany s targets vs = .ok s' →
      Step (.next (.frame targets results [] k)) s (.next k) s'
  -- Draining the defer chain: one deferred call per step, each in its own
  -- frame whose continuation is this frame with the rest of the chain, so
  -- both exit paths converge on the rules above once the chain is empty.
  -- The inner frame has NO targets and NO results: a deferred call's
  -- results are discarded in Go (`defer/defer-function-result-discard`).
  | frameDeferFall {targets results fid vals ds k s func frameEnv resultLocs s'} :
      enterFrame s fid vals = .ok (func, frameEnv, resultLocs, s') →
      Step (.next (.frame targets results ((fid, vals) :: ds) k)) s
        (.exec func.body frameEnv
          (.frame [] [] [] (.frame targets results ds k))) s'
  | frameDeferReturn {targets results fid vals ds k s func frameEnv resultLocs s'} :
      enterFrame s fid vals = .ok (func, frameEnv, resultLocs, s') →
      Step (.returning (.frame targets results ((fid, vals) :: ds) k)) s
        (.exec func.body frameEnv
          (.frame [] [] [] (.frame targets results ds k))) s'
  -- Registering a deferred call: callee, then arguments, evaluated NOW.
  | deferStmt {callee args env k s} :
      Step (.exec (.deferCall callee args) env k) s
        (.evalE callee env (.deferCalleeK args.toList env k)) s
  | deferCalleeArg {fid captured a rest env k s} :
      Step (.retV (.funcVal fid captured) (.deferCalleeK (a :: rest) env k)) s
        (.evalE a env (.deferArgsK fid captured [] rest env k)) s
  | deferCalleeNoArgs {fid captured env k k' s} :
      pushDefer (fid, captured) k = some k' →
      Step (.retV (.funcVal fid captured) (.deferCalleeK [] env k)) s (.next k') s
  | deferCalleeNil {args env k s} :
      Step (.retV .nil (.deferCalleeK args env k)) s
        (.panicked "runtime error: invalid memory address or nil pointer dereference") s
  | deferArgNext {v fid captured vals a rest env k s} :
      Step (.retV v (.deferArgsK fid captured vals (a :: rest) env k)) s
        (.evalE a env (.deferArgsK fid captured (vals ++ [v]) rest env k)) s
  | deferArgsDone {v fid captured vals env k k' s} :
      pushDefer (fid, captured ++ vals ++ [v]) k = some k' →
      Step (.retV v (.deferArgsK fid captured vals [] env k)) s (.next k') s

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
