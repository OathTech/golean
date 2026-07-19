import GoLean.GoCore.State

namespace GoLean.GoCore

open GoLean

/-- Depth bound for defined-type resolution in the type-directed operations
(`normalizeValueForTy`, `valueEq`, `defaultValue`). It is decremented *only*
when a `.defined` name is resolved through the type environment, so it bounds
type-nesting depth, not value size — array/struct child recursion is structural
and never consumes it, so no valid value can spuriously exhaust it. Go type
definitions cannot form value-containment cycles, so any well-formed program
stays far under this bound. Chosen over a type-environment-acyclicity
well-formedness proof for uniformity with `execStmt`'s fuel (design decision
2026-07-18; see docs/2026-07-18_totality-fuel-decision.md). -/
def typeResolutionFuel : Nat := 1024

def indexOutOfRangePanic (index : Int) (length : Nat) : Except GoError α :=
  if index < 0 then
    panic s!"runtime error: index out of range [{index}]"
  else
    panic s!"runtime error: index out of range [{index}] with length {length}"

def arrayIndexNat (values : Array GoValue) (index : Int) : Except GoError Nat := do
  if index < 0 then
    indexOutOfRangePanic index values.size
  let i := index.toNat
  if i < values.size then
    return i
  else
    indexOutOfRangePanic index values.size

def arrayGet (values : Array GoValue) (index : Int) : Except GoError GoValue := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some value => return value
  | none => indexOutOfRangePanic index values.size

-- Total: structurally recursive on the first `GoValue`. The array/struct
-- cases recurse into children through list helpers (`coerceArray`/
-- `coerceStruct`) rather than a `for`-loop, so Lean can see each recursive
-- call lands on a strict subterm and derives well-founded termination.
mutual
  def coerceStoredValue : GoValue → GoValue → Except GoError GoValue
    | .int _ kind, .int value _ => return .int (kind.normalize value) kind
    | .array oldValues, .array newValues =>
        if oldValues.size != newValues.size then
          stuck s!"array store length mismatch: {oldValues.size} vs {newValues.size}"
        else
          .array <$> coerceArray oldValues.toList newValues.toList
    | .struct oldType oldFields, .struct newType newFields =>
        if oldType != newType then
          stuck s!"struct store type mismatch: {oldType.key} vs {newType.key}"
        else if oldFields.size != newFields.size then
          stuck s!"struct store field count mismatch: {oldFields.size} vs {newFields.size}"
        else
          .struct oldType <$> coerceStruct oldFields.toList newFields.toList
    | _, value => return value

  /-- Coerce array elements pairwise; callers guarantee equal lengths. -/
  def coerceArray : List GoValue → List GoValue → Except GoError (Array GoValue)
    | oldValue :: oldRest, newValue :: newRest => do
        let head ← coerceStoredValue oldValue newValue
        let tail ← coerceArray oldRest newRest
        return #[head] ++ tail
    | _, _ => return #[]

  /-- Coerce struct fields pairwise, checking field-name alignment. -/
  def coerceStruct :
      List (String × GoValue) → List (String × GoValue) →
      Except GoError (Array (String × GoValue))
    | (oldName, oldValue) :: oldRest, (newName, newValue) :: newRest => do
        if oldName != newName then
          stuck s!"struct store field mismatch: {oldName} vs {newName}"
        let head ← coerceStoredValue oldValue newValue
        let tail ← coerceStruct oldRest newRest
        return #[(oldName, head)] ++ tail
    | _, _ => return #[]
end

def arraySet (values : Array GoValue) (index : Int) (value : GoValue) :
    Except GoError (Array GoValue) := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some old => return values.set! i (← coerceStoredValue old value)
  | none => indexOutOfRangePanic index values.size

def natFromNonnegativeInt (context : String) (value : Int) : Except GoError Nat := do
  if value < 0 then
    panic context
  return value.toNat

def fullSliceMaxBoundsPanic (max capacity : Nat) : Except GoError α :=
  panic s!"runtime error: slice bounds out of range [::{max}] with capacity {capacity}"

def stringByteGet (value : GoString) (index : Int) : Except GoError GoValue := do
  if index < 0 then
    indexOutOfRangePanic index value.length
  let i := index.toNat
  match value.byte? i with
  | some byte => return .int (Int.ofNat byte.toNat) .uint8
  | none => indexOutOfRangePanic index value.length

def stringSlice (value : GoString) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  if max.isSome then
    stuck "full slice expression over string"
  let low ← natFromNonnegativeInt "slice bounds out of range" low
  let high ← natFromNonnegativeInt "slice bounds out of range" high
  if low <= high && high <= value.length then
    return .string (value.slice low high)
  else
    panic "slice bounds out of range"

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
      if max > slice.cap then
        fullSliceMaxBoundsPanic max slice.cap
      else if low <= high && high <= max then
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
      if max > length then
        fullSliceMaxBoundsPanic max length
      else if low <= high && high <= max then
        return .slice {
          base := some base,
          offset := low,
          len := high - low,
          cap := max - low
        }
      else
        panic "slice bounds out of range"

-- Total via fuel: follows the `.defined → .alias` chain, decrementing fuel per
-- hop. On exhaustion it returns the type unresolved (a safe fixed point).
def resolveDefinedAliasesFuel : Nat → ExecState → Ty → Ty
  | fuel + 1, state, .defined name =>
      match TypeEnv.lookup state.types name with
      | some (.alias target) => resolveDefinedAliasesFuel fuel state target
      | _ => .defined name
  | _, _, other => other

def resolveDefinedAliases (state : ExecState) (typ : Ty) : Ty :=
  resolveDefinedAliasesFuel typeResolutionFuel state typ

def dynamicTypeName? (state : ExecState) (typ : Ty) : Option String :=
  match resolveDefinedAliases state typ with
  | .defined id => some id.key
  | .pointer (.defined id) => some s!"*{id.key}"
  | .bool => some "bool"
  | .int kind => some kind.name
  | .string => some "string"
  | _ => none

def methodInfoByFuncId? (state : ExecState) (id : FuncId) : Option MethodInfo :=
  state.methods.foldl
    (fun found method =>
      match found with
      | some method => some method
      | none => if method.funcId == id then some method else none)
    none

def methodRecvInterfaceName? (state : ExecState) (method : MethodInfo) : Option String :=
  match resolveDefinedAliases state method.recv with
  | .interface id => some id.key
  | _ => none

def methodRecvDynamicName? (state : ExecState) (method : MethodInfo) : Option String :=
  match resolveDefinedAliases state method.recv with
  | .defined id => some id.key
  | .pointer (.defined id) => some s!"*{id.key}"
  | _ => none

def interfaceMethodRequirements (state : ExecState) (interfaceName : String) : Array MethodInfo :=
  state.methods.foldl
    (fun out method =>
      match methodRecvInterfaceName? state method with
      | some name => if name == interfaceName then out.push method else out
      | none => out)
    #[]

def hasConcreteMethod (state : ExecState) (dynamicName methodName : String) : Bool :=
  state.methods.any
    (fun method =>
      method.name == methodName &&
        match methodRecvDynamicName? state method with
        | some name => name == dynamicName
        | none => false)

def dynamicImplementsInterface (state : ExecState) (dynamicName interfaceName : String) : Bool :=
  (interfaceMethodRequirements state interfaceName).all
    (fun requirement => hasConcreteMethod state dynamicName requirement.name)

def concreteMethodForDynamic? (state : ExecState) (dynamicName methodName : String) :
    Option MethodInfo :=
  state.methods.foldl
    (fun found method =>
      match found with
      | some method => some method
      | none =>
          if method.name == methodName then
            match methodRecvDynamicName? state method with
            | some name => if name == dynamicName then some method else none
            | none => none
          else
            none)
    none

-- Total via fuel: fuel is decremented only at `.defined` resolution; array and
-- struct child recursion is structural through list helpers. The public
-- `normalizeValueForTy` seeds `typeResolutionFuel` and keeps its signature.
mutual
  def normalizeValueForTyFuel : Nat → ExecState → Ty → GoValue → Except GoError GoValue
    | _, _, .int kind, .int value _ => return .int (kind.normalize value) kind
    | _, _, .int kind, value => stuck s!"expected {kind.name} value, got {repr value}"
    | fuel, state, .array length elem, .array values => do
        if values.size != length then
          stuck s!"array value length mismatch: expected {length}, got {values.size}"
        .array <$> normalizeArrayForTy fuel state elem values.toList
    | _, _, .array length _, value => stuck s!"expected array({length}) value, got {repr value}"
    | _, _, .interface _, value => return value
    | fuel + 1, state, .defined name, value => do
        match TypeEnv.lookup state.types name with
        | some (.alias target) => normalizeValueForTyFuel fuel state target value
        | some (.struct fields) => normalizeStructValueForFields fuel state name fields value
        | some (.unsupported feature) => unsupported s!"normalizing {feature}"
        | none => unsupported s!"normalizing unknown defined type {name.key}"
    | 0, _, .defined _, _ => unsupported "normalizing: type nesting too deep"
    | _, _, .unsupported feature, _ => unsupported s!"normalizing {feature}"
    | _, _, _, value => return value

  /-- Normalize array elements against the element type; equal length checked. -/
  def normalizeArrayForTy (fuel : Nat) (state : ExecState) (elem : Ty) :
      List GoValue → Except GoError (Array GoValue)
    | value :: rest => do
        let head ← normalizeValueForTyFuel fuel state elem value
        let tail ← normalizeArrayForTy fuel state elem rest
        return #[head] ++ tail
    | [] => return #[]

  def normalizeStructValueForFields (fuel : Nat) (state : ExecState) (name : TypeId)
      (fields : Array FieldDef) : GoValue → Except GoError GoValue
    | .struct actual fieldsValue => do
        if actual != name then
          stuck s!"struct value type mismatch: expected {name.key}, got {actual.key}"
        if fieldsValue.size != fields.size then
          stuck s!"struct value field count mismatch: expected {fields.size}, got {fieldsValue.size}"
        .struct name <$> normalizeStructFieldsForTy fuel state fields.toList fieldsValue.toList
    | value => stuck s!"expected struct {name.key} value, got {repr value}"

  /-- Normalize struct field values pairwise, checking field-name alignment. -/
  def normalizeStructFieldsForTy (fuel : Nat) (state : ExecState) :
      List FieldDef → List (String × GoValue) →
      Except GoError (Array (String × GoValue))
    | field :: fieldRest, (actualField, value) :: valueRest => do
        if actualField != field.name then
          stuck s!"struct value field mismatch: expected {field.name}, got {actualField}"
        let head ← normalizeValueForTyFuel fuel state field.typ value
        let tail ← normalizeStructFieldsForTy fuel state fieldRest valueRest
        return #[(field.name, head)] ++ tail
    | _, _ => return #[]
end

def normalizeValueForTy (state : ExecState) (ty : Ty) (value : GoValue) :
    Except GoError GoValue :=
  normalizeValueForTyFuel typeResolutionFuel state ty value

-- Total: structural recursion on the `Loc` argument (field/index bases are
-- strict subterms). loadLoc depends only on itself and total helpers, so it is
-- a genuine `def` — the premise of the eventual `wp_load` proof rule.
def loadLoc (state : ExecState) : Loc → Except GoError GoValue
  | loc@(.base _) =>
      match Heap.lookup state.heap loc with
      | some cell => return cell.value
      | none => stuck s!"unbound GoCore heap location: {repr loc}"
  | .field base typeId fieldName => do
      match ← loadLoc state base with
      | .struct actualType fields =>
          if actualType != typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return value
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct base for field load, got {repr other}"
  | .index base index => do
      match ← loadLoc state base with
      | .array values => arrayGet values index
      | other => stuck s!"expected array base for index load, got {repr other}"

-- Total: structural recursion on the `Loc` argument (field/index bases are
-- strict subterms); its non-structural callees (normalizeValueForTy,
-- coerceStoredValue) are now themselves total. The premise of `wp_store`.
def storeLoc (state : ExecState) : Loc → GoValue → Except GoError ExecState
    | loc@(.base _), value => do
        match Heap.lookup state.heap loc with
        | some cell => do
            let value ←
              match cell.declaredTy with
              | some ty => normalizeValueForTy state ty value
              | none => coerceStoredValue cell.value value
            return { state with heap := Heap.set state.heap loc { cell with value } }
        | none =>
            return { state with heap := Heap.set state.heap loc { value } }
    | .field base typeId fieldName, value => do
        match ← loadLoc state base with
        | .struct actualType fields =>
            if actualType != typeId then
              stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
            let updated ← StructFields.set fields fieldName value
            storeLoc state base (.struct actualType updated)
        | other => stuck s!"expected struct base for field store, got {repr other}"
    | .index base index, value => do
        match ← loadLoc state base with
        | .array values => storeLoc state base (.array (← arraySet values index value))
        | other => stuck s!"expected array base for index store, got {repr other}"

def lookup (state : ExecState) (name : String) : Except GoError GoValue := do
  loadLoc state (← lookupLoc state name)

-- Total via fuel: only the `.defined → .alias` chain recurses; fuel bounds it.
def convertValueToTyFuel : Nat → ExecState → Ty → GoValue → Except GoError GoValue
  | _, _, .int kind, .int value _ => return .int (kind.normalize value) kind
  | _, _, .int kind, other => stuck s!"expected integer operand for conversion to {kind.name}, got {repr other}"
  | fuel + 1, state, .defined name, value =>
      match TypeEnv.lookup state.types name with
      | some (.alias target) => convertValueToTyFuel fuel state target value
      | some (.struct _) => unsupported s!"conversion to struct type {name.key}"
      | some (.unsupported feature) => unsupported s!"conversion to {feature}"
      | none => unsupported s!"conversion to unknown defined type {name.key}"
  | 0, _, .defined _, _ => unsupported "conversion: type nesting too deep"
  | _, _, .unsupported feature, _ => unsupported s!"conversion to {feature}"
  | _, _, other, _ => unsupported s!"conversion to {repr other}"

def convertValueToTy (state : ExecState) (typ : Ty) (value : GoValue) :
    Except GoError GoValue :=
  convertValueToTyFuel typeResolutionFuel state typ value

-- Total via fuel: `defaultValueFuel` decrements fuel only at `.defined`
-- resolution. The array case computes the element default once and replicates
-- it (`defaultValue` is pure, so all elements are equal); the `length == 0`
-- guard preserves the original behavior of not evaluating the element type for
-- an empty array. Struct fields recurse through the `defaultStructFields`
-- list helper.
mutual
  def defaultValueFuel : Nat → ExecState → Ty → Except GoError GoValue
    | _, _, .bool => return .bool false
    | _, _, .int kind => return .int 0 kind
    | _, _, .string => return .string GoString.empty
    | fuel, state, .array length elem => do
        if length == 0 then
          return .array #[]
        let elemDefault ← defaultValueFuel fuel state elem
        return .array (Array.replicate length elemDefault)
    | _, _, .slice _ => return .slice { base := none, offset := 0, len := 0, cap := 0 }
    | _, _, .map _ _ => return .map { base := none }
    | _, _, .pointer _ => return .nil
    | _, _, .interface _ => return .nil
    | fuel + 1, state, .defined name => do
        match TypeEnv.lookup state.types name with
        | some (.struct fields) =>
            .struct name <$> defaultStructFields fuel state fields.toList
        | some (.alias target) => defaultValueFuel fuel state target
        | some (.unsupported feature) => unsupported s!"default value for {feature}"
        | none => unsupported s!"default value for unknown defined type {name.key}"
    | 0, _, .defined _ => unsupported "default value: type nesting too deep"
    | _, _, .unsupported feature => unsupported s!"default value for {feature}"

  /-- Default value for each struct field, in declaration order. -/
  def defaultStructFields (fuel : Nat) (state : ExecState) :
      List FieldDef → Except GoError (Array (String × GoValue))
    | field :: rest => do
        let head ← defaultValueFuel fuel state field.typ
        let tail ← defaultStructFields fuel state rest
        return #[(field.name, head)] ++ tail
    | [] => return #[]
end

def defaultValue (state : ExecState) (ty : Ty) : Except GoError GoValue :=
  defaultValueFuel typeResolutionFuel state ty

/-- Build a struct value field-by-field from positional literal args, normalizing
each against its field type. Not recursive with `buildStructValue` (it only calls
the total `normalizeValueForTy`); callers guarantee the checked length. -/
def buildStructFields (state : ExecState) :
    List FieldDef → List GoValue → Except GoError (Array (String × GoValue))
  | field :: fieldRest, value :: valueRest => do
      let head ← normalizeValueForTy state field.typ value
      let tail ← buildStructFields state fieldRest valueRest
      return #[(field.name, head)] ++ tail
  | _, _ => return #[]

-- Total via fuel: only the `.defined → .alias` chain recurses; fuel bounds it.
def buildStructValueFuel : Nat → ExecState → Ty → Array GoValue → Except GoError GoValue
  | fuel + 1, state, .defined name, args => do
      match TypeEnv.lookup state.types name with
      | some (.struct fields) =>
          if fields.size != args.size then
            stuck s!"struct {name.key} literal expected {fields.size} field value(s), got {args.size}"
          .struct name <$> buildStructFields state fields.toList args.toList
      | some (.alias target) => buildStructValueFuel fuel state target args
      | some (.unsupported feature) => unsupported s!"struct literal for {feature}"
      | none => unsupported s!"struct literal for unknown defined type {name.key}"
  | 0, _, .defined _, _ => unsupported "struct literal: type nesting too deep"
  | _, _, .unsupported feature, _ => unsupported s!"struct literal for {feature}"
  | _, _, other, _ => unsupported s!"struct literal for non-defined type {repr other}"

def buildStructValue (state : ExecState) (typ : Ty) (args : Array GoValue) :
    Except GoError GoValue :=
  buildStructValueFuel typeResolutionFuel state typ args

-- Not recursive: it calls only the now-total defaultValue / normalizeValueForTy
-- / coerceStoredValue, so the for-loops are fine in a plain def.
def buildArrayValue (state : ExecState) (length : Nat) (elem : Ty)
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

def buildDefaultArrayValue (state : ExecState) (length : Nat) (elem : Ty) :
    Except GoError GoValue :=
  buildArrayValue state length elem #[]

-- Not recursive; total now that defaultValue / resolveDefinedAliases are.
def typeAssertValue (state : ExecState) (value : GoValue) (targetTy : Ty) :
    Except GoError (GoValue × Bool) := do
  let failed ← defaultValue state targetTy
  match value with
  | .nil => return (failed, false)
  | .interface dynamicName inner =>
      match resolveDefinedAliases state targetTy with
      | .interface interfaceName =>
          if dynamicImplementsInterface state dynamicName interfaceName.key then
            return (.interface dynamicName inner, true)
          else
            return (failed, false)
      | _ =>
          match dynamicTypeName? state targetTy with
          | some targetName =>
              if dynamicName == targetName then
                return (inner, true)
              else
                return (failed, false)
          | none => unsupported s!"type assertion to {repr targetTy}"
  | other => unsupported s!"type assertion from non-interface value {repr other}"

-- Total via fuel: recurses through both alias resolution and type subterms
-- (pointer/slice/map/array elements), so fuel bounds combined depth. Only used
-- for error-message rendering; on exhaustion it returns a placeholder.
def goTypeNameForMessageFuel : Nat → ExecState → Ty → String
  | fuel + 1, state, typ =>
      match resolveDefinedAliases state typ with
      | .bool => "bool"
      | .int kind => kind.name
      | .string => "string"
      | .pointer elem => s!"*{goTypeNameForMessageFuel fuel state elem}"
      | .slice elem => s!"[]{goTypeNameForMessageFuel fuel state elem}"
      | .map key value => s!"map[{goTypeNameForMessageFuel fuel state key}]{goTypeNameForMessageFuel fuel state value}"
      | .interface ⟨"empty_interface"⟩ => "interface {}"
      | .interface name => name.key
      | .defined name => name.key
      | .array length elem => s!"[{length}]{goTypeNameForMessageFuel fuel state elem}"
      | .unsupported feature => feature
  | 0, _, _ => "<type nesting too deep>"

def goTypeNameForMessage (state : ExecState) (typ : Ty) : String :=
  goTypeNameForMessageFuel typeResolutionFuel state typ

def dynamicTypeNameForMessage : GoValue → String
  | .interface dynamicName _ => dynamicName
  | .nil => "nil"
  | other => s!"{repr other}"

def typeAssertPanicMessage (state : ExecState) (value : GoValue) (targetTy : Ty) : String :=
  "interface conversion: interface {} is " ++
    dynamicTypeNameForMessage value ++ ", not " ++ goTypeNameForMessage state targetTy

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
  | .nil => panic "runtime error: invalid memory address or nil pointer dereference"
  | other => stuck s!"expected address value, got {repr other}"

-- Total via fuel: `valueEqFuel` decrements fuel only when resolving a
-- `.defined` name through the type environment; array/struct element recursion
-- is structural (list helpers `valueEqArray`/`valueEqStruct`). The public
-- `valueEq` seeds `typeResolutionFuel`, keeping its original signature so call
-- sites are unchanged.
mutual
  def valueEqFuel : Nat → ExecState → Ty → GoValue → GoValue → Except GoError Bool
    | _, _, .bool, .bool left, .bool right => return left == right
    | _, _, .bool, left, right => stuck s!"bool equality expected bool operands, got {repr left} and {repr right}"
    | _, _, .int _, .int left _, .int right _ => return left == right
    | _, _, .int kind, left, right => stuck s!"{kind.name} equality expected int operands, got {repr left} and {repr right}"
    | _, _, .string, .string left, .string right => return left == right
    | _, _, .string, left, right => stuck s!"string equality expected string operands, got {repr left} and {repr right}"
    | _, _, .pointer _, .addr left, .addr right => return left == right
    | _, _, .pointer _, .nil, .nil => return true
    | _, _, .pointer _, .addr _, .nil => return false
    | _, _, .pointer _, .nil, .addr _ => return false
    | _, _, .pointer _, left, right => stuck s!"pointer equality expected pointer/nil operands, got {repr left} and {repr right}"
    | fuel, state, .array length elem, .array left, .array right => do
        if left.size != length then
          stuck s!"left array equality length mismatch: expected {length}, got {left.size}"
        if right.size != length then
          stuck s!"right array equality length mismatch: expected {length}, got {right.size}"
        valueEqArray fuel state elem left.toList right.toList
    | _, _, .array length _, left, right =>
        stuck s!"array equality expected array({length}) operands, got {repr left} and {repr right}"
    | _, _, .slice _, .slice left, .slice right => do
        validateSlice left
        validateSlice right
        match left.base, right.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil slices are not comparable"
    | _, _, .slice _, .slice left, .nil => do
        validateSlice left
        return left.base.isNone
    | _, _, .slice _, .nil, .slice right => do
        validateSlice right
        return right.base.isNone
    | _, _, .slice _, left, right => stuck s!"slice equality expected slice/nil operands, got {repr left} and {repr right}"
    | _, _, .map _ _, .map left, .map right =>
        match left.base, right.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil maps are not comparable"
    | _, _, .map _ _, .map left, .nil => return left.base.isNone
    | _, _, .map _ _, .nil, .map right => return right.base.isNone
    | _, _, .map _ _, left, right => stuck s!"map equality expected map/nil operands, got {repr left} and {repr right}"
    | _, _, .interface _, .nil, .nil => return true
    | _, _, .interface _, .nil, _ => return false
    | _, _, .interface _, _, .nil => return false
    | _, _, .interface _, left, right => unsupported s!"interface equality for {repr left} and {repr right}"
    | fuel + 1, state, .defined name, left, right => do
        match TypeEnv.lookup state.types name with
        | some (.alias target) => valueEqFuel fuel state target left right
        | some (.struct fields) =>
            match left, right with
            | .struct leftType leftFields, .struct rightType rightFields => do
                if leftType != name then
                  stuck s!"left struct equality type mismatch: expected {name.key}, got {leftType.key}"
                if rightType != name then
                  stuck s!"right struct equality type mismatch: expected {name.key}, got {rightType.key}"
                if leftFields.size != fields.size then
                  stuck s!"left struct equality field count mismatch: expected {fields.size}, got {leftFields.size}"
                if rightFields.size != fields.size then
                  stuck s!"right struct equality field count mismatch: expected {fields.size}, got {rightFields.size}"
                valueEqStruct fuel state fields.toList leftFields.toList rightFields.toList
            | _, _ => stuck s!"struct equality expected struct {name.key} operands, got {repr left} and {repr right}"
        | some (.unsupported feature) => unsupported s!"equality for {feature}"
        | none => unsupported s!"equality for unknown defined type {name.key}"
    | 0, _, .defined _, _, _ => unsupported "equality: type nesting too deep"
    | _, _, .unsupported feature, _, _ => unsupported s!"equality for {feature}"

  /-- Compare array elements pairwise; callers guarantee equal, checked lengths. -/
  def valueEqArray (fuel : Nat) (state : ExecState) (elem : Ty) :
      List GoValue → List GoValue → Except GoError Bool
    | leftValue :: leftRest, rightValue :: rightRest => do
        if ← valueEqFuel fuel state elem leftValue rightValue then
          valueEqArray fuel state elem leftRest rightRest
        else
          return false
    | _, _ => return true

  /-- Compare struct fields pairwise, checking field-name alignment on both sides. -/
  def valueEqStruct (fuel : Nat) (state : ExecState) :
      List FieldDef → List (String × GoValue) → List (String × GoValue) →
      Except GoError Bool
    | field :: fieldRest, (leftName, leftValue) :: leftRest, (rightName, rightValue) :: rightRest => do
        if leftName != field.name then
          stuck s!"left struct equality field mismatch: expected {field.name}, got {leftName}"
        if rightName != field.name then
          stuck s!"right struct equality field mismatch: expected {field.name}, got {rightName}"
        if ← valueEqFuel fuel state field.typ leftValue rightValue then
          valueEqStruct fuel state fieldRest leftRest rightRest
        else
          return false
    | _, _, _ => return true
end

def valueEq (state : ExecState) (ty : Ty) (left right : GoValue) : Except GoError Bool :=
  valueEqFuel typeResolutionFuel state ty left right

-- Not recursive; total now that valueEq is. The for-loop is fine in a plain def.
def mapEntryIndex? (state : ExecState) (keyTy : Ty) (entries : Array (GoValue × GoValue))
    (key : GoValue) : Except GoError (Option Nat) := do
  let mut i := 0
  for (entryKey, _) in entries do
    if ← valueEq state keyTy entryKey key then
      return some i
    i := i + 1
  return none

def valueLess : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left < right
  | .string left, .string right => return GoString.compare left right == .lt
  | left, right => stuck s!"mismatched < operands: {repr left} and {repr right}"

def valueAtMost : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left <= right
  | .string left, .string right => return GoString.compare left right != .gt
  | left, right => stuck s!"mismatched <= operands: {repr left} and {repr right}"

def valueGreater : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left > right
  | .string left, .string right => return GoString.compare left right == .gt
  | left, right => stuck s!"mismatched > operands: {repr left} and {repr right}"

def valueAtLeast : GoValue → GoValue → Except GoError Bool
  | .int left _, .int right _ => return left >= right
  | .string left, .string right => return GoString.compare left right != .lt
  | left, right => stuck s!"mismatched >= operands: {repr left} and {repr right}"
