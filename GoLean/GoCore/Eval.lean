import GoLean.GoCore.Ops

namespace GoLean.GoCore

open GoLean

abbrev EvalResult := GoValue × ExecState
abbrev LocResult := Loc × ExecState
abbrev LocsResult := Array Loc × ExecState

def intBinaryResult (opName : String) (op : Int → Int → Int) (left right : GoValue) :
    Except GoError GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let (rightValue, rightKind) ← valueAsIntValue right
  let kind ←
    match IntKind.compatibleResult leftKind rightKind with
    | some kind => pure kind
    | none => stuck s!"mismatched {opName} integer kinds: {leftKind.name} and {rightKind.name}"
  return .int (kind.normalize (op leftValue rightValue)) kind

def intKindBitWidth (opName : String) (kind : IntKind) : Except GoError Nat := do
  match kind.bits? with
  | some bits => return bits
  | none => unsupported s!"{opName} for unbounded integer kind {kind.name}"

def intKindUnsignedNat (kind : IntKind) (value : Int) : Except GoError Nat := do
  let bits ← intKindBitWidth "bitwise operator" kind
  let modulus : Int := (2 : Int) ^ bits
  return (value % modulus).toNat

def intBitwiseBinaryResult (opName : String) (op : Nat → Nat → Nat) (left right : GoValue) :
    Except GoError GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let (rightValue, rightKind) ← valueAsIntValue right
  let kind ←
    match IntKind.compatibleResult leftKind rightKind with
    | some kind => pure kind
    | none => stuck s!"mismatched {opName} integer kinds: {leftKind.name} and {rightKind.name}"
  let leftBits ← intKindUnsignedNat kind leftValue
  let rightBits ← intKindUnsignedNat kind rightValue
  return .int (kind.normalize (Int.ofNat (op leftBits rightBits))) kind

def intBitClearResult (left right : GoValue) : Except GoError GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let (rightValue, rightKind) ← valueAsIntValue right
  let kind ←
    match IntKind.compatibleResult leftKind rightKind with
    | some kind => pure kind
    | none => stuck s!"mismatched &^ integer kinds: {leftKind.name} and {rightKind.name}"
  let bits ← intKindBitWidth "&^" kind
  let mask := (2 ^ bits) - 1
  let leftBits ← intKindUnsignedNat kind leftValue
  let rightBits ← intKindUnsignedNat kind rightValue
  return .int (kind.normalize (Int.ofNat (Nat.land leftBits (Nat.xor rightBits mask)))) kind

def intBitNegResult (value : GoValue) : Except GoError GoValue := do
  let (intValue, kind) ← valueAsIntValue value
  let bits ← intKindBitWidth "^" kind
  let mask := (2 ^ bits) - 1
  let valueBits ← intKindUnsignedNat kind intValue
  return .int (kind.normalize (Int.ofNat (Nat.xor valueBits mask))) kind

def shiftCountNat (count : GoValue) : Except GoError Nat := do
  let count ← valueAsInt count
  if count < 0 then
    panic "runtime error: negative shift amount"
  return count.toNat

def arithmeticShiftRight (value : Int) (count : Nat) : Int :=
  let divisor : Int := (2 : Int) ^ count
  if value < 0 then
    -Int.tdiv ((-value) + divisor - 1) divisor
  else
    Int.tdiv value divisor

def intShiftLeftResult (left right : GoValue) : Except GoError GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let count ← shiftCountNat right
  return .int (leftKind.normalize (leftValue * ((2 : Int) ^ count))) leftKind

def intShiftRightResult (left right : GoValue) : Except GoError GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let count ← shiftCountNat right
  let shifted :=
    if leftKind.signed then
      arithmeticShiftRight leftValue count
    else
      Int.tdiv leftValue ((2 : Int) ^ count)
  return .int (leftKind.normalize shifted) leftKind

mutual
  def evalExpr (state : ExecState) : Expr → Except GoError EvalResult
    | .var id => return (← lookup state id, state)
    | .nil none => return (.nil, state)
    | .nil (some typ) =>
        match typ with
        | .slice _ => return (← defaultValue state typ, state)
        | .map _ _ => return (← defaultValue state typ, state)
        | .pointer _ => return (.nil, state)
        | .unsupported feature => unsupported s!"nil literal for {feature}"
        | other => stuck s!"nil literal for non-nilable type {repr other}"
    | .intLit value kind => return (.int (kind.normalize value) kind, state)
    | .stringLit value => return (.string value, state)
    | .boolLit value => return (.bool value, state)
    | .convert typ operand => do
        let pair ← evalExpr state operand
        return (← convertValueToTy pair.2 typ pair.1, pair.2)
    | .bytesFromString operand => do
        let pair ← evalExpr state operand
        match pair.1 with
        | .string value =>
            let bytes := value.bytes.map (fun b => GoValue.int (Int.ofNat b.toNat) .uint8)
            let (base, current) := pair.2.alloc (.array bytes) (some (.array bytes.size (.int .uint8)))
            return (.slice { base := some base, offset := 0, len := bytes.size, cap := bytes.size }, current)
        | other => stuck s!"expected string operand for []byte conversion, got {repr other}"
    | .stringFromByteSlice operand => do
        let pair ← evalExpr state operand
        let slice ← valueAsSlice pair.1
        let values ← sliceVisibleValues pair.2 slice
        let mut bytes := #[]
        for value in values do
          match value with
          | .int byte .uint8 =>
              if byte < 0 || byte > 255 then
                stuck s!"malformed uint8 byte value in string conversion: {byte}"
              bytes := bytes.push (UInt8.ofNat byte.toNat)
          | other => stuck s!"expected uint8 element in string conversion, got {repr other}"
        return (.string { bytes := bytes }, pair.2)
    | .stringFromRune operand => do
        let pair ← evalExpr state operand
        let codePoint ← valueAsInt pair.1
        return (.string (GoString.fromCodePoint codePoint), pair.2)
    | .add left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        match leftPair.1, rightPair.1 with
        | .int .., .int .. => return (← intBinaryResult "+" (· + ·) leftPair.1 rightPair.1, rightPair.2)
        | .string leftValue, .string rightValue =>
            return (.string (GoString.append leftValue rightValue), rightPair.2)
        | leftValue, rightValue => stuck s!"mismatched + operands: {repr leftValue} and {repr rightValue}"
    | .sub left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBinaryResult "-" (· - ·) leftPair.1 rightPair.1, rightPair.2)
    | .mul left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBinaryResult "*" (· * ·) leftPair.1 rightPair.1, rightPair.2)
    | .div left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        let divisor ← valueAsInt rightPair.1
        if divisor == 0 then
          panic "runtime error: integer divide by zero"
        return (← intBinaryResult "/" Int.tdiv leftPair.1 rightPair.1, rightPair.2)
    | .mod left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        let divisor ← valueAsInt rightPair.1
        if divisor == 0 then
          panic "runtime error: integer divide by zero"
        return (← intBinaryResult "%" Int.tmod leftPair.1 rightPair.1, rightPair.2)
    | .shiftLeft left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intShiftLeftResult leftPair.1 rightPair.1, rightPair.2)
    | .shiftRight left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intShiftRightResult leftPair.1 rightPair.1, rightPair.2)
    | .bitAnd left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBitwiseBinaryResult "&" Nat.land leftPair.1 rightPair.1, rightPair.2)
    | .bitOr left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBitwiseBinaryResult "|" Nat.lor leftPair.1 rightPair.1, rightPair.2)
    | .bitXor left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBitwiseBinaryResult "^" Nat.xor leftPair.1 rightPair.1, rightPair.2)
    | .bitClear left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (← intBitClearResult leftPair.1 rightPair.1, rightPair.2)
    | .bitNeg operand => do
        let pair ← evalExpr state operand
        return (← intBitNegResult pair.1, pair.2)
    | .eqCmp typ left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueEq rightPair.2 typ leftPair.1 rightPair.1), rightPair.2)
    | .neqCmp typ left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (!(← valueEq rightPair.2 typ leftPair.1 rightPair.1)), rightPair.2)
    | .atMostCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueAtMost leftPair.1 rightPair.1), rightPair.2)
    | .atLeastCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueAtLeast leftPair.1 rightPair.1), rightPair.2)
    | .lessCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueLess leftPair.1 rightPair.1), rightPair.2)
    | .greaterCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueGreater leftPair.1 rightPair.1), rightPair.2)
    | .and left right => do
        let leftPair ← evalExpr state left
        if ← valueAsBool leftPair.1 then
          let rightPair ← evalExpr leftPair.2 right
          return (.bool (← valueAsBool rightPair.1), rightPair.2)
        else
          return (.bool false, leftPair.2)
    | .or left right => do
        let leftPair ← evalExpr state left
        if ← valueAsBool leftPair.1 then
          return (.bool true, leftPair.2)
        else
          let rightPair ← evalExpr leftPair.2 right
          return (.bool (← valueAsBool rightPair.1), rightPair.2)
    | .not operand => do
        let pair ← evalExpr state operand
        return (.bool (!(← valueAsBool pair.1)), pair.2)
    | .ref id => return (.addr (← lookupLoc state id), state)
    | .locLit l => return (.addr l, state)
    | .deref ptr _typ => do
        let pair ← evalExpr state ptr
        return (← loadLoc pair.2 (← valueAsLoc pair.1), pair.2)
    | .structLit typ args => do
        let (values, current) ← evalExprSeq state args.toList
        return (← buildStructValue current typ values, current)
    | .fieldGet recv typeName fieldName => do
        let pair ← evalExpr state recv
        match pair.1 with
        | .struct actualType fields =>
            if actualType != typeName then
              stuck s!"expected struct {typeName.key}, got struct {actualType.key}"
            match StructFields.lookup fields fieldName with
            | some value => return (value, pair.2)
            | none => stuck s!"unknown GoCore struct field: {fieldName}"
        | other => stuck s!"expected struct value for field access, got {repr other}"
    | .fieldAddr base typeName fieldName => do
        let pair ← evalExpr state base
        return (.addr (.field (← valueAsLoc pair.1) typeName fieldName), pair.2)
    | .arrayLit length elem args => do
        let (values, current) ← evalExprKeyedSeq state args.toList
        return (← buildArrayValue current length elem values, current)
    | .defaultValue typ => return (← defaultValue state typ, state)
    | .toInterface _target dynamic operand => do
        let pair ← evalExpr state operand
        match dynamicTypeName? pair.2 dynamic with
        | some dynamicName => return (.interface dynamicName pair.1, pair.2)
        | none => unsupported s!"interface conversion for dynamic type {repr dynamic}"
    | .typeAssert operand targetTy => do
        let pair ← evalExpr state operand
        let result ← typeAssertValue pair.2 pair.1 targetTy
        if result.2 then
          return (result.1, pair.2)
        else
          panic (typeAssertPanicMessage pair.2 pair.1 targetTy)
    | .indexGet base index => do
        let basePair ← evalExpr state base
        let indexPair ← evalExpr basePair.2 index
        let indexValue ← valueAsInt indexPair.1
        match basePair.1 with
        | .array values => return (← arrayGet values indexValue, indexPair.2)
        | .string value => return (← stringByteGet value indexValue, indexPair.2)
        | .slice slice => do
            let loc ← sliceIndexLoc slice indexValue
            return (← loadLoc indexPair.2 loc, indexPair.2)
        | other => stuck s!"expected array, slice, or string value for index access, got {repr other}"
    | .mapGet base index keyTy valueTy => do
        let basePair ← evalExpr state base
        let map ← valueAsMap basePair.1
        let keyPair ← evalExpr basePair.2 index
        let key ← normalizeValueForTy keyPair.2 keyTy keyPair.1
        match map.base with
        | none => return (← defaultValue keyPair.2 valueTy, keyPair.2)
        | some baseLoc =>
            match ← loadLoc keyPair.2 baseLoc with
            | .mapData entries =>
                match ← mapEntryIndex? keyPair.2 keyTy entries key with
                | some i =>
                    match entries[i]? with
                    | some (_, value) => return (value, keyPair.2)
                    | none => stuck s!"missing map entry at index {i}"
                | none => return (← defaultValue keyPair.2 valueTy, keyPair.2)
            | other => stuck s!"expected map data, got {repr other}"
    | .indexAddr base index => do
        let basePair ← evalExpr state base
        let indexPair ← evalExpr basePair.2 index
        let indexValue ← valueAsInt indexPair.1
        match basePair.1 with
        | .slice slice => return (.addr (← sliceIndexLoc slice indexValue), indexPair.2)
        | .addr baseLoc =>
            match ← loadLoc indexPair.2 baseLoc with
            | .array values =>
                let _ ← arrayIndexNat values indexValue
                return (.addr (.index baseLoc indexValue), indexPair.2)
            | .slice slice => return (.addr (← sliceIndexLoc slice indexValue), indexPair.2)
            | other => stuck s!"expected array or slice base for index address, got {repr other}"
        | other => stuck s!"expected array or slice base for index address, got {repr other}"
    | .slice base low high max => do
        let basePair ← evalExpr state base
        let lowPair ← evalExpr basePair.2 low
        let highPair ← evalExpr lowPair.2 high
        let lowValue ← valueAsInt lowPair.1
        let highValue ← valueAsInt highPair.1
        let mut current := highPair.2
        let mut maxValue : Option Int := none
        match max with
        | none => pure ()
        | some max => do
            let maxPair ← evalExpr current max
            maxValue := some (← valueAsInt maxPair.1)
            current := maxPair.2
        match basePair.1 with
        | .string value => return (← stringSlice value lowValue highValue maxValue, current)
        | .slice slice => return (← sliceFromSlice slice lowValue highValue maxValue, current)
        | .addr baseLoc =>
            match ← loadLoc current baseLoc with
            | .array values => return (← sliceFromArray baseLoc values.size lowValue highValue maxValue, current)
            | .slice slice => return (← sliceFromSlice slice lowValue highValue maxValue, current)
            | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
        | .array values =>
            unsupported s!"slice expression over non-addressable array value of length {values.size}"
        | other => stuck s!"expected array or slice value for slice expression, got {repr other}"
    | .length operand typ => do
        let pair ← evalExpr state operand
        match typ with
        | some (.pointer (.array length _)) => return (.int length, pair.2)
        | _ =>
            match pair.1 with
            | .array values => return (.int values.size, pair.2)
            | .addr baseLoc =>
                match ← loadLoc pair.2 baseLoc with
                | .array values => return (.int values.size, pair.2)
                | other => unsupported s!"len for non-array pointer value {repr other}"
            | .string value => return (.int value.length, pair.2)
            | .slice slice => do
                validateSlice slice
                return (.int slice.len, pair.2)
            | .map map => do
                match map.base with
                | none => return (.int 0, pair.2)
                | some baseLoc =>
                    match ← loadLoc pair.2 baseLoc with
                    | .mapData entries => return (.int entries.size, pair.2)
                    | other => stuck s!"expected map data, got {repr other}"
            | other => unsupported s!"len for non-array/slice/map value {repr other}"
    | .capacity operand typ => do
        let pair ← evalExpr state operand
        match typ with
        | some (.pointer (.array length _)) => return (.int length, pair.2)
        | _ =>
            match pair.1 with
            | .array values => return (.int values.size, pair.2)
            | .addr baseLoc =>
                match ← loadLoc pair.2 baseLoc with
                | .array values => return (.int values.size, pair.2)
                | other => unsupported s!"cap for non-array pointer value {repr other}"
            | .slice slice => do
                validateSlice slice
                return (.int slice.cap, pair.2)
            | other => unsupported s!"cap for non-array/slice value {repr other}"
    | .unsupported feature => unsupported feature

  /-- Evaluate a sequence of expressions left-to-right, threading state (Go
  evaluation order). Structural on the list so `evalExpr`'s recursion on the
  element expressions stays visible to the termination checker. -/
  def evalExprSeq (state : ExecState) : List Expr → Except GoError (Array GoValue × ExecState)
    | [] => return (#[], state)
    | arg :: rest => do
        let pair ← evalExpr state arg
        let (tailValues, finalState) ← evalExprSeq pair.2 rest
        return (#[pair.1] ++ tailValues, finalState)

  /-- Like `evalExprSeq`, but each expression is paired with a literal index
  key (array-literal element positions), threading state left-to-right. -/
  def evalExprKeyedSeq (state : ExecState) :
      List (Int × Expr) → Except GoError (Array (Int × GoValue) × ExecState)
    | [] => return (#[], state)
    | (key, arg) :: rest => do
        let pair ← evalExpr state arg
        let (tailValues, finalState) ← evalExprKeyedSeq pair.2 rest
        return (#[(key, pair.1)] ++ tailValues, finalState)

  def evalAssigneeLoc (state : ExecState) : Assignee → Except GoError LocResult
    | .var id => return (← lookupLoc state id, state)
    | .addr locExpr => do
        let pair ← evalExpr state locExpr
        return (← valueAsLoc pair.1, pair.2)
    | .unsupported feature => unsupported feature

  def evalAssigneeLocs (state : ExecState) (targets : Array Assignee) :
      Except GoError LocsResult := do
    let mut current := state
    let mut locs := #[]
    for target in targets do
      let pair ← evalAssigneeLoc current target
      locs := locs.push pair.1
      current := pair.2
    return (locs, current)

  def assignLoc (state : ExecState) (loc : Loc) (value : GoValue) :
      Except GoError ExecState := do
    storeLoc state loc value

  def assignAssignee (state : ExecState) (assignee : Assignee) (value : GoValue) :
      Except GoError ExecState := do
    let pair ← evalAssigneeLoc state assignee
    assignLoc pair.2 pair.1 value

  def assignLocs (state : ExecState) (targets : Array Loc)
      (values : Array GoValue) : Except GoError ExecState := do
    if targets.size != values.size then
      stuck s!"expected {targets.size} call result value(s), got {values.size}"
    let mut current := state
    let mut i := 0
    for target in targets do
      match values[i]? with
      | some value =>
          current ← assignLoc current target value
          i := i + 1
      | none => stuck s!"missing call result value {i}"
    return current

  def assignAssignees (state : ExecState) (targets : Array Assignee)
      (values : Array GoValue) : Except GoError ExecState := do
    let pair ← evalAssigneeLocs state targets
    assignLocs pair.2 pair.1 values

  def execAssignMany (state : ExecState) (left : Array Assignee) (right : Array Expr) :
      Except GoError ExecState := do
    if left.size != right.size then
      stuck s!"multi-assignment expected {left.size} value(s), got {right.size}"
    let locPair ← evalAssigneeLocs state left
    let mut current := locPair.2
    let mut values := #[]
    for expr in right do
      let pair ← evalExpr current expr
      values := values.push pair.1
      current := pair.2
    assignLocs current locPair.1 values

  def execNewValue (state : ExecState) (target : Assignee) (valueExpr : Expr)
      (typ : Option Ty) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let valuePair ← evalExpr targetPair.2 valueExpr
    let (loc, current) := valuePair.2.alloc valuePair.1 typ
    assignLoc current targetPair.1 (.addr loc)

  def execMakeMap (state : ExecState) (target : Assignee) (_key _value : Ty)
      (initialSpace : Option Expr) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let mut current := targetPair.2
    match initialSpace with
    | none => pure ()
    | some expr =>
        let pair ← evalExpr current expr
        let size ← valueAsInt pair.1
        let _ ← natFromNonnegativeInt "makemap: size out of range" size
        current := pair.2
    let allocated := current.alloc (.mapData #[])
    let base := allocated.1
    let afterAlloc := allocated.2
    assignLoc afterAlloc targetPair.1 (.map { base := some base })

  def mapEntries (state : ExecState) (map : MapValue) :
      Except GoError (Option (Loc × Array (GoValue × GoValue))) := do
    match map.base with
    | none => return none
    | some baseLoc =>
        match ← loadLoc state baseLoc with
        | .mapData entries => return some (baseLoc, entries)
        | other => stuck s!"expected map data, got {repr other}"

  def mapLookupValue (state : ExecState) (map : MapValue) (key : GoValue)
      (keyTy valueTy : Ty) : Except GoError (GoValue × Bool) := do
    match ← mapEntries state map with
    | none => return (← defaultValue state valueTy, false)
    | some (_, entries) =>
        match ← mapEntryIndex? state keyTy entries key with
        | some i =>
            match entries[i]? with
            | some (_, value) => return (value, true)
            | none => stuck s!"missing map entry at index {i}"
        | none => return (← defaultValue state valueTy, false)

  def execMapAssign (state : ExecState) (baseExpr keyExpr valueExpr : Expr) (keyTy valueTy : Ty) :
      Except GoError ExecState := do
    let basePair ← evalExpr state baseExpr
    let map ← valueAsMap basePair.1
    let keyPair ← evalExpr basePair.2 keyExpr
    let valuePair ← evalExpr keyPair.2 valueExpr
    let key ← normalizeValueForTy valuePair.2 keyTy keyPair.1
    let value ← normalizeValueForTy valuePair.2 valueTy valuePair.1
    match ← mapEntries valuePair.2 map with
    | none => panic "assignment to entry in nil map"
    | some (baseLoc, entries) =>
        let entries ←
          match ← mapEntryIndex? valuePair.2 keyTy entries key with
          | some i => pure (entries.set! i (key, value))
          | none => pure (entries.push (key, value))
        storeLoc valuePair.2 baseLoc (.mapData entries)

  def execMapLookup (state : ExecState) (target okTarget : Assignee)
      (baseExpr keyExpr : Expr) (keyTy valueTy : Ty) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let okPair ← evalAssigneeLoc targetPair.2 okTarget
    let basePair ← evalExpr okPair.2 baseExpr
    let map ← valueAsMap basePair.1
    let keyPair ← evalExpr basePair.2 keyExpr
    let key ← normalizeValueForTy keyPair.2 keyTy keyPair.1
    let pair ← mapLookupValue keyPair.2 map key keyTy valueTy
    let value := pair.1
    let ok := pair.2
    let current ← assignLoc keyPair.2 targetPair.1 value
    assignLoc current okPair.1 (.bool ok)

  def execTypeAssert (state : ExecState) (target okTarget : Assignee)
      (expr : Expr) (targetTy : Ty) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let okPair ← evalAssigneeLoc targetPair.2 okTarget
    let valuePair ← evalExpr okPair.2 expr
    let result ← typeAssertValue valuePair.2 valuePair.1 targetTy
    let current ← assignLoc valuePair.2 targetPair.1 result.1
    assignLoc current okPair.1 (.bool result.2)

  def sliceVisibleValues (state : ExecState) (slice : SliceValue) :
      Except GoError (Array GoValue) := do
    validateSlice slice
    let mut values := #[]
    for i in [:slice.len] do
      values := values.push (← loadLoc state (← sliceIndexLoc slice (Int.ofNat i)))
    return values

  def execCopySlice (state : ExecState) (target : Assignee) (dstExpr srcExpr : Expr) :
      Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let dstPair ← evalExpr targetPair.2 dstExpr
    let dstSlice ← valueAsSlice dstPair.1
    let srcPair ← evalExpr dstPair.2 srcExpr
    let srcSlice ← valueAsSlice srcPair.1
    validateSlice dstSlice
    validateSlice srcSlice
    let count := Nat.min dstSlice.len srcSlice.len
    let mut values := #[]
    for i in [:count] do
      values := values.push (← loadLoc srcPair.2 (← sliceIndexLoc srcSlice (Int.ofNat i)))
    let mut current := srcPair.2
    let mut i := 0
    for value in values do
      current ← storeLoc current (← sliceIndexLoc dstSlice (Int.ofNat i)) value
      i := i + 1
    assignLoc current targetPair.1 (.int (Int.ofNat count))

  def appendGrowthCap (oldCap newLen : Nat) : Nat :=
    if newLen <= oldCap then
      oldCap
    else if oldCap == 0 then
      max 4 newLen
    else if newLen > oldCap + oldCap then
      newLen
    else if oldCap < 256 then
      oldCap + oldCap
    else
      let rec loop (cap : Nat) : Nat :=
        if cap >= newLen then
          cap
        else
          loop (cap + (cap + 3 * 256) / 4)
      loop oldCap

  def buildAppendBackingValue (state : ExecState) (elem : Ty)
      (oldValues elemValues : Array GoValue) (newCap : Nat) : Except GoError GoValue := do
    let mut values := #[]
    for value in oldValues ++ elemValues do
      values := values.push (← normalizeValueForTy state elem value)
    if values.size > newCap then
      stuck s!"append backing capacity {newCap} smaller than length {values.size}"
    for _ in [:newCap - values.size] do
      values := values.push (← defaultValue state elem)
    return .array values

  def execAppendSlice (state : ExecState) (target : Assignee) (elem : Ty)
      (sliceExpr elemsExpr : Expr) (choices : Choices) : Except GoError (ExecState × Choices) := do
    let targetPair ← evalAssigneeLoc state target
    let slicePair ← evalExpr targetPair.2 sliceExpr
    let slice ← valueAsSlice slicePair.1
    let elemsPair ← evalExpr slicePair.2 elemsExpr
    let elems ← valueAsSlice elemsPair.1
    validateSlice slice
    validateSlice elems
    let elemValues ← sliceVisibleValues elemsPair.2 elems
    let newLen := slice.len + elemValues.size
    if newLen <= slice.cap then
      let mut current := elemsPair.2
      let mut i := 0
      for value in elemValues do
        match slice.base with
        | some base =>
            current ← storeLoc current (.index base (Int.ofNat (slice.offset + slice.len + i))) value
            i := i + 1
        | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place"
      return (← assignLoc current targetPair.1 (.slice { slice with len := newLen }), choices)
    else
      let oldValues ← sliceVisibleValues elemsPair.2 slice
      -- Go does not specify post-reallocation capacity; any cap >= newLen is
      -- valid. The oracle chooses one: the default (0) reproduces the
      -- Go-matching growth formula for differential testing, and other choices
      -- explore additional valid capacities so cap-observing programs are
      -- revealed as nondeterministic by the invariance check.
      let (extra, choices) := choices.consume 8
      let newCap := appendGrowthCap slice.cap newLen + extra
      let backing ← buildAppendBackingValue elemsPair.2 elem oldValues elemValues newCap
      let (base, current) := elemsPair.2.alloc backing (some (.array newCap elem))
      return (← assignLoc current targetPair.1 (.slice { base := some base, offset := 0, len := newLen, cap := newCap }), choices)

  def execMakeSlice (state : ExecState) (target : Assignee) (elem : Ty)
      (lenExpr : Expr) (capExpr : Option Expr) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let lenPair ← evalExpr targetPair.2 lenExpr
    let lenValue ← valueAsInt lenPair.1
    let mut current := lenPair.2
    let mut capValue := lenValue
    match capExpr with
    | none => pure ()
    | some capExpr => do
        let capPair ← evalExpr current capExpr
        capValue := (← valueAsInt capPair.1)
        current := capPair.2
    let len ← natFromNonnegativeInt "runtime error: makeslice: len out of range" lenValue
    let cap ← natFromNonnegativeInt "runtime error: makeslice: cap out of range" capValue
    if cap < len then
      panic "runtime error: makeslice: cap out of range"
    let backing ← buildDefaultArrayValue current cap elem
    let allocated := current.alloc backing (some (.array cap elem))
    let base := allocated.1
    let afterAlloc := allocated.2
    assignLoc afterAlloc targetPair.1 (.slice { base := some base, offset := 0, len, cap })

  def dynamicDispatch? (state : ExecState) (func : Func) (argValues : Array GoValue) :
      Except GoError (Option (Func × Array GoValue)) := do
    match methodInfoByFuncId? state func.id with
    | none => return none
    | some method =>
        match methodRecvInterfaceName? state method with
        | none => return none
        | some _ =>
            match argValues[0]? with
            | some (GoValue.interface dynamicName inner) =>
                match concreteMethodForDynamic? state dynamicName method.name with
                | some concrete =>
                    let targetFunc ←
                      match findFunctionIn? state.functions concrete.funcId with
                      | some func => pure func
                      | none => stuck s!"GoCore dynamic method target not found: {concrete.funcId.key}"
                    return some (targetFunc, argValues.set! 0 inner)
                | none => stuck s!"dynamic type {dynamicName} has no method {method.name}"
            | _ => return none
end

-- Fuel'd upper cluster: function calls and loops recurse on `fuel` (the lower
-- structural cluster above is already total and never calls back into this one).
mutual
  partial def execFunctionWithValues (fuel : Nat) (state : ExecState) (targets : Array Loc)
      (func : Func) (argValues : Array GoValue) (choices : Choices) :
      Except GoError (ExecState × Choices) := do
    if fuel == 0 then
      stuck "GoCore execution fuel exhausted"
    if func.args.size != argValues.size then
      stuck s!"function {func.id.key} expected {func.args.size} argument(s), got {argValues.size}"
    let current := state
    let callerLocals := current.locals
    let mut callState : ExecState := { current with locals := [] }
    let mut i := 0
    for param in func.args do
      match argValues[i]? with
      | some value =>
          callState := callState.declareLocal param.id (some param.typ) (← normalizeValueForTy callState param.typ value)
          i := i + 1
      | none => stuck s!"missing argument {i}"
    for result in func.results do
      callState := callState.declareLocal result.id (some result.typ) (← defaultValue callState result.typ)
    let (outcome, choices) ← execStmt (fuel - 1) callState choices func.body
    let finalState ←
      match outcome with
      | .normal nextState => pure nextState
      | .returned nextState => pure nextState
      | .broke _ => stuck s!"function {func.id.key} body escaped with break"
      | .continued _ => stuck s!"function {func.id.key} body escaped with continue"
    let mut resultValues := #[]
    for result in func.results do
      resultValues := resultValues.push (← lookup finalState result.id)
    let callerState : ExecState := { finalState with locals := callerLocals }
    return (← assignLocs callerState targets resultValues, choices)

  partial def execFunctionCallWithLocs (fuel : Nat) (state : ExecState) (targets : Array Loc)
      (id : FuncId) (args : Array Expr) (choices : Choices) :
      Except GoError (ExecState × Choices) := do
    let func ←
      match findFunctionIn? state.functions id with
      | some func => pure func
      | none => stuck s!"GoCore function not found: {id.key}"
    if func.args.size != args.size then
      stuck s!"function {id.key} expected {func.args.size} argument(s), got {args.size}"
    let mut current := state
    let mut argValues := #[]
    for arg in args do
      let pair ← evalExpr current arg
      argValues := argValues.push pair.1
      current := pair.2
    match ← dynamicDispatch? current func argValues with
    | some (targetFunc, targetArgs) => execFunctionWithValues fuel current targets targetFunc targetArgs choices
    | none => execFunctionWithValues fuel current targets func argValues choices

  partial def execFunctionCall (fuel : Nat) (state : ExecState) (targets : Array Assignee)
      (id : FuncId) (args : Array Expr) (choices : Choices) :
      Except GoError (ExecState × Choices) := do
    let targetPair ← evalAssigneeLocs state targets
    execFunctionCallWithLocs fuel targetPair.2 targetPair.1 id args choices

  partial def execDecl (state : ExecState) (param : Param) : Except GoError ExecState := do
    return state.declareLocal param.id (some param.typ) (← defaultValue state param.typ)

  partial def execDecls (state : ExecState) (decls : Array Param) : Except GoError ExecState := do
    let mut current := state
    for decl in decls do
      current ← execDecl current decl
    return current

  partial def execStmts (fuel : Nat) (state : ExecState) (stmts : Array Stmt)
      (choices : Choices) : Except GoError (ExecOutcome × Choices) :=
    execStmtList fuel state choices stmts.toList

  /-- Execute statements in order, short-circuiting on the first non-normal
  outcome. Structural on the list so `execStmt`'s recursion stays visible to the
  termination checker. -/
  partial def execStmtList (fuel : Nat) (state : ExecState) (choices : Choices) :
      List Stmt → Except GoError (ExecOutcome × Choices)
    | [] => return (.normal state, choices)
    | stmt :: rest => do
        match ← execStmt fuel state choices stmt with
        | (.normal nextState, choices) => execStmtList fuel nextState choices rest
        | (outcome, choices) => return (outcome, choices)

  partial def execStmt (fuel : Nat) (state : ExecState) (choices : Choices) :
      Stmt → Except GoError (ExecOutcome × Choices)
    | .seqn stmts => execStmts fuel state stmts choices
    | .block decls stmts => do
        let entered := { state with locals := state.locals.pushScope }
        let (outcome, choices) ← execStmts fuel (← execDecls entered decls) stmts choices
        let exitScope (s : ExecState) : ExecState :=
          { s with locals := s.locals.popScope }
        return (match outcome with
        | .normal s => .normal (exitScope s)
        | .returned s => .returned (exitScope s)
        | .broke s => .broke (exitScope s)
        | .continued s => .continued (exitScope s), choices)
    | .initialization var => return (.normal (← execDecl state var), choices)
    | .assign left right => do
        let locPair ← evalAssigneeLoc state left
        let valuePair ← evalExpr locPair.2 right
        return (.normal (← assignLoc valuePair.2 locPair.1 valuePair.1), choices)
    | .assignMany left right => return (.normal (← execAssignMany state left right), choices)
    | .newValue target value typ => return (.normal (← execNewValue state target value typ), choices)
    | .makeSlice target elem len cap => return (.normal (← execMakeSlice state target elem len cap), choices)
    | .makeMap target key value initialSpace =>
        return (.normal (← execMakeMap state target key value initialSpace), choices)
    | .mapAssign base index value keyTy valueTy =>
        return (.normal (← execMapAssign state base index value keyTy valueTy), choices)
    | .mapLookup target okTarget base index keyTy valueTy =>
        return (.normal (← execMapLookup state target okTarget base index keyTy valueTy), choices)
    | .typeAssert target okTarget expr targetTy =>
        return (.normal (← execTypeAssert state target okTarget expr targetTy), choices)
    | .appendSlice target elem slice elems => do
        let (s, choices) ← execAppendSlice state target elem slice elems choices
        return (.normal s, choices)
    | .copySlice target dst src => return (.normal (← execCopySlice state target dst src), choices)
    | .call targets funcId args => do
        let (s, choices) ← execFunctionCall fuel state targets funcId args choices
        return (.normal s, choices)
    | .ifThenElse cond thenBranch elseBranch => do
        let condPair ← evalExpr state cond
        if ← valueAsBool condPair.1 then
          execStmt fuel condPair.2 choices thenBranch
        else
          execStmt fuel condPair.2 choices elseBranch
    | .while cond body => do
        if fuel == 0 then
          stuck "GoCore execution fuel exhausted"
        let condPair ← evalExpr state cond
        if ← valueAsBool condPair.1 then
          match ← execStmt fuel condPair.2 choices body with
          | (.normal bodyState, choices) => execStmt (fuel - 1) bodyState choices (.while cond body)
          | (.continued bodyState, choices) => execStmt (fuel - 1) bodyState choices (.while cond body)
          | (.broke bodyState, choices) => return (.normal bodyState, choices)
          | (.returned bodyState, choices) => return (.returned bodyState, choices)
        else
          return (.normal condPair.2, choices)
    | .mapRange keyVar valVar mapExpr keyTy valTy body => do
        let mapPair ← evalExpr state mapExpr
        let map ← valueAsMap mapPair.1
        let entries ←
          match map.base with
          | none => pure #[]
          | some base =>
              match ← loadLoc mapPair.2 base with
              | .mapData es => pure es
              | other => stuck s!"expected map data for range, got {repr other}"
        execMapRangeLoop fuel mapPair.2 keyVar valVar keyTy valTy body entries choices
    | .returnStmt => return (.returned state, choices)
    | .breakStmt => return (.broke state, choices)
    | .continueStmt => return (.continued state, choices)
    | .label _ => return (.normal state, choices)
    | .unsupported feature => unsupported feature

  /-- Iterate the snapshotted map entries in an oracle-chosen order: at each
  step consume a choice bounded by the number of remaining entries to pick the
  next one, bind the range variables in a fresh per-iteration scope, and run
  the body. The default oracle (0) yields the stored order. -/
  partial def execMapRangeLoop (fuel : Nat) (state : ExecState)
      (keyVar valVar : Option String) (keyTy valTy : Ty) (body : Stmt)
      (remaining : Array (GoValue × GoValue)) (choices : Choices) :
      Except GoError (ExecOutcome × Choices) := do
    if remaining.isEmpty then
      return (.normal state, choices)
    let (idx, choices) := choices.consume remaining.size
    match remaining[idx]? with
    | none => return (.normal state, choices)
    | some (key, value) =>
        let rest := remaining.eraseIdx! idx
        let mut iterState : ExecState := { state with locals := state.locals.pushScope }
        match keyVar with
        | some name => iterState := iterState.declareLocal name (some keyTy) (← normalizeValueForTy iterState keyTy key)
        | none => pure ()
        match valVar with
        | some name => iterState := iterState.declareLocal name (some valTy) (← normalizeValueForTy iterState valTy value)
        | none => pure ()
        let popScope (s : ExecState) : ExecState := { s with locals := s.locals.popScope }
        match ← execStmt fuel iterState choices body with
        | (.normal s, choices) => execMapRangeLoop fuel (popScope s) keyVar valVar keyTy valTy body rest choices
        | (.continued s, choices) => execMapRangeLoop fuel (popScope s) keyVar valVar keyTy valTy body rest choices
        | (.broke s, choices) => return (.normal (popScope s), choices)
        | (.returned s, choices) => return (.returned (popScope s), choices)
end

def bindParams (state : ExecState) (params : Array Param) (args : Array GoValue) :
    Except GoError ExecState := do
  if params.size != args.size then
    stuck s!"expected {params.size} argument(s), got {args.size}"
  let mut state := state
  let mut i := 0
  for param in params do
    match args[i]? with
    | some value =>
        state := state.declareLocal param.id (some param.typ) (← normalizeValueForTy state param.typ value)
        i := i + 1
    | none => stuck s!"missing argument {i}"
  return state

def initResults (state : ExecState) (results : Array Param) : Except GoError ExecState := do
  let mut state := state
  for result in results do
    state := state.declareLocal result.id (some result.typ) (← defaultValue state result.typ)
  return state

def collectResults (state : ExecState) (results : Array Param) :
    Except GoError (Array GoValue) := do
  let mut values := #[]
  for result in results do
    values := values.push (← lookup state result.id)
  return values

def runFunctionWithContext (fuel : Nat) (types : TypeEnv) (functions : Array Func)
    (func : Func) (args : Array GoValue) (methods : Array MethodInfo := #[])
    (choices : Choices := []) :
    Except GoError Result := do
  let state ← bindParams { types := types, functions := functions, methods := methods } func.args args
  let state ← initResults state func.results
  let (outcome, _) ← execStmt fuel state choices func.body
  let state ←
    match outcome with
    | .normal state => pure state
    | .returned state => pure state
    | .broke _ => stuck s!"function {func.id.key} body escaped with break"
    | .continued _ => stuck s!"function {func.id.key} body escaped with continue"
  return { values := (← collectResults state func.results) }

def runFunctionWithTypes (fuel : Nat) (types : TypeEnv) (func : Func) (args : Array GoValue) :
    Except GoError Result :=
  runFunctionWithContext fuel types #[func] func args

def runFunction (fuel : Nat) (func : Func) (args : Array GoValue) : Except GoError Result :=
  runFunctionWithTypes fuel [] func args

/-- Lookup by canonical function name. This is the user-facing entry point
(CLI subject-function selection); it constructs the `FuncId` from the
canonical source-level name, which is exactly what the symbol map assigns to
plain functions. -/
def findFunction? (program : Program) (name : String) : Option Func :=
  findFunctionIn? program.funcs ⟨name⟩

def runNamedFunction (fuel : Nat) (program : Program) (name : String) (args : Array GoValue)
    (choices : List Nat := []) :
    Except GoError Result := do
  let func ←
    match findFunction? program name with
    | some func => pure func
    | none => stuck s!"GoCore function not found: {name}"
  runFunctionWithContext fuel program.typeDefs.toList program.funcs func args program.methods choices

def runNamedFunctionInts (fuel : Nat) (program : Program) (name : String) (args : Array Int)
    (choices : List Nat := []) :
    Except GoError Result :=
  runNamedFunction fuel program name (args.map GoValue.int) choices


end GoLean.GoCore
