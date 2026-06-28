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

partial def coerceStoredValue : GoValue → GoValue → Except GoError GoValue
  | .int _ kind, .int value _ => return .int (kind.normalize value) kind
  | .array oldValues, .array newValues => do
      if oldValues.size != newValues.size then
        stuck s!"array store length mismatch: {oldValues.size} vs {newValues.size}"
      let mut out := #[]
      let mut i := 0
      for oldValue in oldValues do
        match newValues[i]? with
        | some newValue =>
            out := out.push (← coerceStoredValue oldValue newValue)
            i := i + 1
        | none => stuck s!"missing array store value at index {i}"
      return .array out
  | .struct oldType oldFields, .struct newType newFields => do
      if oldType != newType then
        stuck s!"struct store type mismatch: {oldType} vs {newType}"
      if oldFields.size != newFields.size then
        stuck s!"struct store field count mismatch: {oldFields.size} vs {newFields.size}"
      let mut out := #[]
      let mut i := 0
      for (oldName, oldValue) in oldFields do
        match newFields[i]? with
        | some (newName, newValue) =>
            if oldName != newName then
              stuck s!"struct store field mismatch: {oldName} vs {newName}"
            out := out.push (oldName, (← coerceStoredValue oldValue newValue))
            i := i + 1
        | none => stuck s!"missing struct store value at field {i}"
      return .struct oldType out
  | _, value => return value

def arraySet (values : Array GoValue) (index : Int) (value : GoValue) :
    Except GoError (Array GoValue) := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some old => return values.set! i (← coerceStoredValue old value)
  | none => panic "index out of range"

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
    | loc@(.base _), value => do
        let value ←
          match Heap.lookup state.heap loc with
          | some old => coerceStoredValue old value
          | none => pure value
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
  partial def normalizeValueForTy (state : ExecState) : Ty → GoValue → Except GoError GoValue
    | .int kind, .int value _ => return .int (kind.normalize value) kind
    | .int kind, value => stuck s!"expected {kind.name} value, got {repr value}"
    | .array length elem, .array values => do
        if values.size != length then
          stuck s!"array value length mismatch: expected {length}, got {values.size}"
        let mut out := #[]
        for value in values do
          out := out.push (← normalizeValueForTy state elem value)
        return .array out
    | .array length _, value => stuck s!"expected array({length}) value, got {repr value}"
    | .defined name, value => do
        match TypeEnv.lookup state.types name with
        | some (.alias target) => normalizeValueForTy state target value
        | some (.struct fields) => normalizeStructValueForFields state name fields value
        | some (.unsupported feature) => unsupported s!"normalizing {feature}"
        | none => unsupported s!"normalizing unknown defined type {name}"
    | .unsupported feature, _ => unsupported s!"normalizing {feature}"
    | _, value => return value

  partial def normalizeStructValueForFields (state : ExecState) (name : String)
      (fields : Array FieldDef) : GoValue → Except GoError GoValue
    | .struct actual fieldsValue => do
        if actual != name then
          stuck s!"struct value type mismatch: expected {name}, got {actual}"
        if fieldsValue.size != fields.size then
          stuck s!"struct value field count mismatch: expected {fields.size}, got {fieldsValue.size}"
        let mut out := #[]
        let mut i := 0
        for field in fields do
          match fieldsValue[i]? with
          | some (actualField, value) =>
              if actualField != field.name then
                stuck s!"struct value field mismatch: expected {field.name}, got {actualField}"
              out := out.push (field.name, (← normalizeValueForTy state field.typ value))
              i := i + 1
          | none => stuck s!"missing struct field value at index {i}"
        return .struct name out
    | value => stuck s!"expected struct {name} value, got {repr value}"
end

mutual
  partial def defaultValue (state : ExecState) : Ty → Except GoError GoValue
    | .bool => return .bool false
    | .int kind => return .int 0 kind
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
                  values := values.push (field.name, (← normalizeValueForTy state field.typ value))
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
      | some old => values := values.set! key.toNat (← coerceStoredValue old (← normalizeValueForTy state elem value))
      | none => stuck s!"GoCore array literal index out of range: {key}"
    return .array values
end

def buildDefaultArrayValue (state : ExecState) (length : Nat) (elem : Ty) :
    Except GoError GoValue :=
  buildArrayValue state length elem #[]

def valueAsInt : GoValue → Except GoError Int
  | .int value _ => return value
  | other => stuck s!"expected int value, got {repr other}"

def valueAsIntValue : GoValue → Except GoError (Int × IntKind)
  | .int value kind => return (value, kind)
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

partial def valueEq : ExecState → Ty → GoValue → GoValue → Except GoError Bool
  | _, .bool, .bool left, .bool right => return left == right
  | _, .bool, left, right => stuck s!"bool equality expected bool operands, got {repr left} and {repr right}"
  | _, .int _, .int left _, .int right _ => return left == right
  | _, .int kind, left, right => stuck s!"{kind.name} equality expected int operands, got {repr left} and {repr right}"
  | _, .string, .string left, .string right => return left == right
  | _, .string, left, right => stuck s!"string equality expected string operands, got {repr left} and {repr right}"
  | _, .pointer _, .addr left, .addr right => return left == right
  | _, .pointer _, .nil, .nil => return true
  | _, .pointer _, .addr _, .nil => return false
  | _, .pointer _, .nil, .addr _ => return false
  | _, .pointer _, left, right => stuck s!"pointer equality expected pointer/nil operands, got {repr left} and {repr right}"
  | state, .array length elem, .array left, .array right => do
      if left.size != length then
        stuck s!"left array equality length mismatch: expected {length}, got {left.size}"
      if right.size != length then
        stuck s!"right array equality length mismatch: expected {length}, got {right.size}"
      let mut i := 0
      for leftValue in left do
        match right[i]? with
        | some rightValue =>
            if !(← valueEq state elem leftValue rightValue) then
              return false
            i := i + 1
        | none => stuck s!"missing array equality operand at index {i}"
      return true
  | _, .array length _, left, right =>
      stuck s!"array equality expected array({length}) operands, got {repr left} and {repr right}"
  | _, .slice _, .slice left, .slice right => do
      validateSlice left
      validateSlice right
      match left.base, right.base with
      | none, none => return true
      | none, some _ => return false
      | some _, none => return false
      | some _, some _ => stuck "non-nil slices are not comparable"
  | _, .slice _, .slice left, .nil => do
      validateSlice left
      return left.base.isNone
  | _, .slice _, .nil, .slice right => do
      validateSlice right
      return right.base.isNone
  | _, .slice _, left, right => stuck s!"slice equality expected slice/nil operands, got {repr left} and {repr right}"
  | _, .map _ _, .map left, .map right =>
      match left.base, right.base with
      | none, none => return true
      | none, some _ => return false
      | some _, none => return false
      | some _, some _ => stuck "non-nil maps are not comparable"
  | _, .map _ _, .map left, .nil => return left.base.isNone
  | _, .map _ _, .nil, .map right => return right.base.isNone
  | _, .map _ _, left, right => stuck s!"map equality expected map/nil operands, got {repr left} and {repr right}"
  | state, .defined name, left, right => do
      match TypeEnv.lookup state.types name with
      | some (.alias target) => valueEq state target left right
      | some (.struct fields) =>
          match left, right with
          | .struct leftType leftFields, .struct rightType rightFields => do
              if leftType != name then
                stuck s!"left struct equality type mismatch: expected {name}, got {leftType}"
              if rightType != name then
                stuck s!"right struct equality type mismatch: expected {name}, got {rightType}"
              if leftFields.size != fields.size then
                stuck s!"left struct equality field count mismatch: expected {fields.size}, got {leftFields.size}"
              if rightFields.size != fields.size then
                stuck s!"right struct equality field count mismatch: expected {fields.size}, got {rightFields.size}"
              let mut i := 0
              for field in fields do
                match leftFields[i]?, rightFields[i]? with
                | some (leftName, leftValue), some (rightName, rightValue) =>
                    if leftName != field.name then
                      stuck s!"left struct equality field mismatch: expected {field.name}, got {leftName}"
                    if rightName != field.name then
                      stuck s!"right struct equality field mismatch: expected {field.name}, got {rightName}"
                    if !(← valueEq state field.typ leftValue rightValue) then
                      return false
                    i := i + 1
                | _, _ => stuck s!"missing struct equality operand at field {i}"
              return true
          | _, _ => stuck s!"struct equality expected struct {name} operands, got {repr left} and {repr right}"
      | some (.unsupported feature) => unsupported s!"equality for {feature}"
      | none => unsupported s!"equality for unknown defined type {name}"
  | _, .unsupported feature, _, _ => unsupported s!"equality for {feature}"

partial def mapEntryIndex? (state : ExecState) (keyTy : Ty) (entries : Array (GoValue × GoValue))
    (key : GoValue) : Except GoError (Option Nat) := do
  let mut i := 0
  for (entryKey, _) in entries do
    if ← valueEq state keyTy entryKey key then
      return some i
    i := i + 1
  return none

def valueLess : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left < right
  | .string left, .string right => return compare left right == .lt
  | left, right => stuck s!"mismatched < operands: {repr left} and {repr right}"

def valueAtMost : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left <= right
  | .string left, .string right => return compare left right != .gt
  | left, right => stuck s!"mismatched <= operands: {repr left} and {repr right}"

def valueGreater : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left > right
  | .string left, .string right => return compare left right == .gt
  | left, right => stuck s!"mismatched > operands: {repr left} and {repr right}"

def valueAtLeast : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left >= right
  | .string left, .string right => return compare left right != .lt
  | left, right => stuck s!"mismatched >= operands: {repr left} and {repr right}"
