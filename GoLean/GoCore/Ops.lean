import GoLean.GoCore.State

namespace GoLean.GoCore

open GoLean

def arrayIndexNat (values : Array GoValue) (index : Int) : Except GoError Nat := do
  if index < 0 then
    panic "index out of range"
  let i := index.toNat
  if i < values.size then
    return i
  else
    panic "index out of range"

def arrayGet (values : Array GoValue) (index : Int) : Except GoError GoValue := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some value => return value
  | none => panic "index out of range"

def arraySet (values : Array GoValue) (index : Int) (value : GoValue) :
    Except GoError (Array GoValue) := do
  let i ← arrayIndexNat values index
  return values.set! i value

def natFromNonnegativeInt (context : String) (value : Int) : Except GoError Nat := do
  if value < 0 then
    panic context
  return value.toNat

def validateSlice (slice : SliceValue) : Except GoError Unit := do
  if slice.len > slice.cap then
    stuck s!"malformed GoCore slice: len {slice.len} > cap {slice.cap}"
  match slice.base with
  | some _ => return ()
  | none =>
      if slice.offset == 0 && slice.len == 0 && slice.cap == 0 then
        return ()
      else
        stuck s!"malformed GoCore nil slice: {repr slice}"

def sliceIndexLoc (slice : SliceValue) (index : Int) : Except GoError Loc := do
  validateSlice slice
  let i ← natFromNonnegativeInt "slice index out of bounds" index
  if i < slice.len then
    match slice.base with
    | some base => return .index base (Int.ofNat (slice.offset + i))
    | none => stuck s!"malformed GoCore nil slice with length {slice.len}"
  else
    panic "slice index out of bounds"

def sliceFromSlice (slice : SliceValue) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  validateSlice slice
  let low ← natFromNonnegativeInt "slice bounds out of range" low
  let high ← natFromNonnegativeInt "slice bounds out of range" high
  match max with
  | none =>
      if low <= high && high <= slice.cap then
        return .slice {
          base := slice.base,
          offset := slice.offset + low,
          len := high - low,
          cap := slice.cap - low
        }
      else
        panic "slice bounds out of range"
  | some max =>
      let max ← natFromNonnegativeInt "slice bounds out of range" max
      if low <= high && high <= max && max <= slice.cap then
        return .slice {
          base := slice.base,
          offset := slice.offset + low,
          len := high - low,
          cap := max - low
        }
      else
        panic "slice bounds out of range"

def sliceFromArray (base : Loc) (length : Nat) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  let low ← natFromNonnegativeInt "slice bounds out of range" low
  let high ← natFromNonnegativeInt "slice bounds out of range" high
  match max with
  | none =>
      if low <= high && high <= length then
        return .slice {
          base := some base,
          offset := low,
          len := high - low,
          cap := length - low
        }
      else
        panic "slice bounds out of range"
  | some max =>
      let max ← natFromNonnegativeInt "slice bounds out of range" max
      if low <= high && high <= max && max <= length then
        return .slice {
          base := some base,
          offset := low,
          len := high - low,
          cap := max - low
        }
      else
        panic "slice bounds out of range"

mutual
  partial def loadLoc (state : ExecState) : Loc → Except GoError GoValue
    | loc@(.base _) =>
        match Heap.lookup state.heap loc with
        | some value => return value
        | none => stuck s!"unbound GoCore heap location: {repr loc}"
    | .field base typeName fieldName => do
        match ← loadLoc state base with
        | .struct actualType fields =>
            if actualType != typeName then
              stuck s!"expected struct {typeName}, got struct {actualType}"
            match StructFields.lookup fields fieldName with
            | some value => return value
            | none => stuck s!"unknown GoCore struct field: {fieldName}"
        | other => stuck s!"expected struct base for field load, got {repr other}"
    | .index base index => do
        match ← loadLoc state base with
        | .array values => arrayGet values index
        | other => stuck s!"expected array base for index load, got {repr other}"

  partial def storeLoc (state : ExecState) : Loc → GoValue → Except GoError ExecState
    | loc@(.base _), value =>
        return { state with heap := Heap.set state.heap loc value }
    | .field base typeName fieldName, value => do
        match ← loadLoc state base with
        | .struct actualType fields =>
            if actualType != typeName then
              stuck s!"expected struct {typeName}, got struct {actualType}"
            let updated ← StructFields.set fields fieldName value
            storeLoc state base (.struct actualType updated)
        | other => stuck s!"expected struct base for field store, got {repr other}"
    | .index base index, value => do
        match ← loadLoc state base with
        | .array values => storeLoc state base (.array (← arraySet values index value))
        | other => stuck s!"expected array base for index store, got {repr other}"
end

def lookup (state : ExecState) (name : String) : Except GoError GoValue := do
  loadLoc state (← lookupLoc state name)

mutual
  partial def defaultValue (state : ExecState) : Ty → Except GoError GoValue
    | .bool => return .bool false
    | .int => return .int 0
    | .string => return .string ""
    | .array length elem => do
        let mut values := #[]
        for _ in [:length] do
          values := values.push (← defaultValue state elem)
        return .array values
    | .slice _ => return .slice { base := none, offset := 0, len := 0, cap := 0 }
    | .map _ _ => return .map { base := none }
    | .pointer _ => return .nil
    | .defined name => do
        match TypeEnv.lookup state.types name with
        | some (.struct fields) =>
            let mut values := #[]
            for field in fields do
              values := values.push (field.name, (← defaultValue state field.typ))
            return .struct name values
        | some (.alias target) => defaultValue state target
        | some (.unsupported feature) => unsupported s!"default value for {feature}"
        | none => unsupported s!"default value for unknown defined type {name}"
    | .unsupported feature => unsupported s!"default value for {feature}"

  partial def buildStructValue (state : ExecState) (typ : Ty) (args : Array GoValue) :
      Except GoError GoValue := do
    match typ with
    | .defined name =>
        match TypeEnv.lookup state.types name with
        | some (.struct fields) =>
            if fields.size != args.size then
              stuck s!"struct {name} literal expected {fields.size} field value(s), got {args.size}"
            let mut values := #[]
            let mut i := 0
            for field in fields do
              match args[i]? with
              | some value =>
                  values := values.push (field.name, value)
                  i := i + 1
              | none => stuck s!"missing struct field literal value {i}"
            return .struct name values
        | some (.alias target) => buildStructValue state target args
        | some (.unsupported feature) => unsupported s!"struct literal for {feature}"
        | none => unsupported s!"struct literal for unknown defined type {name}"
    | .unsupported feature => unsupported s!"struct literal for {feature}"
    | other => unsupported s!"struct literal for non-defined type {repr other}"

  partial def buildArrayValue (state : ExecState) (length : Nat) (elem : Ty)
      (args : Array (Int × GoValue)) : Except GoError GoValue := do
    let mut values := #[]
    for _ in [:length] do
      values := values.push (← defaultValue state elem)
    let mut seen : Array Int := #[]
    for (key, value) in args do
      if seen.contains key then
        stuck s!"duplicate GoCore array literal index: {key}"
      seen := seen.push key
      if key < 0 then
        stuck s!"negative GoCore array literal index: {key}"
      match values[key.toNat]? with
      | some _ => values := values.set! key.toNat value
      | none => stuck s!"GoCore array literal index out of range: {key}"
    return .array values
end

def buildDefaultArrayValue (state : ExecState) (length : Nat) (elem : Ty) :
    Except GoError GoValue :=
  buildArrayValue state length elem #[]

def valueAsInt : GoValue → Except GoError Int
  | .int value => return value
  | other => stuck s!"expected int value, got {repr other}"

def valueAsBool : GoValue → Except GoError Bool
  | .bool value => return value
  | other => stuck s!"expected bool value, got {repr other}"

def valueAsSlice : GoValue → Except GoError SliceValue
  | .slice value => return value
  | other => stuck s!"expected slice value, got {repr other}"

def valueAsMap : GoValue → Except GoError MapValue
  | .map value => return value
  | other => stuck s!"expected map value, got {repr other}"

def valueAsLoc : GoValue → Except GoError Loc
  | .addr loc => return loc
  | .nil => panic "nil pointer dereference"
  | other => stuck s!"expected address value, got {repr other}"

partial def valueEq : GoValue → GoValue → Except GoError Bool
  | .bool left, .bool right => return left == right
  | .int left, .int right => return left == right
  | .string left, .string right => return left == right
  | .addr left, .addr right => return left == right
  | .nil, .nil => return true
  | .addr _, .nil => return false
  | .nil, .addr _ => return false
  | .slice left, .nil => do
      validateSlice left
      return left.base.isNone
  | .nil, .slice right => do
      validateSlice right
      return right.base.isNone
  | .map left, .nil => return left.base.isNone
  | .nil, .map right => return right.base.isNone
  | .map left, .map right =>
      match left.base, right.base with
      | none, none => return true
      | none, some _ => return false
      | some _, none => return false
      | some _, some _ => stuck "non-nil maps are not comparable"
  | .slice left, .slice right => do
      validateSlice left
      validateSlice right
      match left.base, right.base with
      | none, none => return true
      | none, some _ => return false
      | some _, none => return false
      | some _, some _ => stuck "non-nil slices are not comparable"
  | .array left, .array right => do
      if left.size != right.size then
        stuck s!"array equality length mismatch: {left.size} vs {right.size}"
      let mut i := 0
      for leftValue in left do
        match right[i]? with
        | some rightValue =>
            if !(← valueEq leftValue rightValue) then
              return false
            i := i + 1
        | none => stuck s!"missing array equality operand at index {i}"
      return true
  | .struct leftType leftFields, .struct rightType rightFields => do
      if leftType != rightType then
        stuck s!"struct equality type mismatch: {leftType} vs {rightType}"
      if leftFields.size != rightFields.size then
        stuck s!"struct equality field count mismatch: {leftFields.size} vs {rightFields.size}"
      let mut i := 0
      for (leftName, leftValue) in leftFields do
        match rightFields[i]? with
        | some (rightName, rightValue) =>
            if leftName != rightName then
              stuck s!"struct equality field mismatch: {leftName} vs {rightName}"
            if !(← valueEq leftValue rightValue) then
              return false
            i := i + 1
        | none => stuck s!"missing struct equality operand at field {i}"
      return true
  | left, right => stuck s!"incomparable or mismatched equality operands: {repr left} and {repr right}"

partial def mapEntryIndex? (entries : Array (GoValue × GoValue)) (key : GoValue) :
    Except GoError (Option Nat) := do
  let mut i := 0
  for (entryKey, _) in entries do
    if ← valueEq entryKey key then
      return some i
    i := i + 1
  return none

def valueLess : GoValue → GoValue → Except GoError Bool
  | .int left, .int right => return left < right
  | .string left, .string right => return compare left right == .lt
  | left, right => stuck s!"mismatched < operands: {repr left} and {repr right}"

def valueAtMost : GoValue → GoValue → Except GoError Bool
  | .int left, .int right => return left <= right
  | .string left, .string right => return compare left right != .gt
  | left, right => stuck s!"mismatched <= operands: {repr left} and {repr right}"

def valueGreater : GoValue → GoValue → Except GoError Bool
  | .int left, .int right => return left > right
  | .string left, .string right => return compare left right == .gt
  | left, right => stuck s!"mismatched > operands: {repr left} and {repr right}"

def valueAtLeast : GoValue → GoValue → Except GoError Bool
  | .int left, .int right => return left >= right
  | .string left, .string right => return compare left right != .lt
  | left, right => stuck s!"mismatched >= operands: {repr left} and {repr right}"
