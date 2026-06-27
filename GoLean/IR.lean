import GoLean.Runtime

namespace GoLean.GoCore

open GoLean

inductive Ty where
  | bool
  | int
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | pointer (elem : Ty)
  | defined (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Param where
  id : String
  typ : Ty
  deriving Repr, BEq

structure FieldDef where
  name : String
  typ : Ty
  deriving Repr, BEq

inductive TypeDef where
  | struct (fields : Array FieldDef)
  | alias (target : Ty)
  | unsupported (feature : String)
  deriving Repr, BEq

inductive Expr where
  | var (id : String)
  | intLit (value : Int)
  | boolLit (value : Bool)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | div (left right : Expr)
  | mod (left right : Expr)
  | eqCmp (left right : Expr)
  | neqCmp (left right : Expr)
  | atMostCmp (left right : Expr)
  | atLeastCmp (left right : Expr)
  | lessCmp (left right : Expr)
  | greaterCmp (left right : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  | not (operand : Expr)
  | ref (id : String)
  | deref (ptr : Expr) (typ : Ty)
  | structLit (typ : Ty) (args : Array Expr)
  | fieldGet (recv : Expr) (typeName fieldName : String)
  | fieldAddr (base : Expr) (typeName fieldName : String)
  | arrayLit (length : Nat) (elem : Ty) (args : Array (Int × Expr))
  | defaultValue (typ : Ty)
  | indexGet (base index : Expr)
  | indexAddr (base index : Expr)
  | slice (base low high : Expr) (max : Option Expr)
  | length (operand : Expr)
  | capacity (operand : Expr)
  | old (operand : Expr)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Assignee where
  | var (id : String)
  | addr (loc : Expr)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | seqn (stmts : Array Stmt)
  | block (decls : Array Param) (stmts : Array Stmt)
  | initialization (var : Param)
  | assign (left : Assignee) (right : Expr)
  | makeSlice (target : Assignee) (elem : Ty) (len : Expr) (cap : Option Expr)
  | appendSlice (target : Assignee) (slice elems : Expr)
  | copySlice (target : Assignee) (dst src : Expr)
  | call (targets : Array Assignee) (name : String) (args : Array Expr)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  | returnStmt
  | breakStmt
  | continueStmt
  | label (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Func where
  name : String
  args : Array Param
  results : Array Param
  body : Stmt
  deriving Repr, BEq

structure Program where
  typeDefs : Array (String × TypeDef) := #[]
  funcs : Array Func
  deriving Repr, BEq

private def findFunctionIn? (funcs : Array Func) (name : String) : Option Func :=
  funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.name == name then some func else none)
    none

abbrev LocalEnv := List (String × Loc)
abbrev Heap := List (Loc × GoValue)
abbrev TypeEnv := List (String × TypeDef)

structure ExecState where
  types : TypeEnv := []
  functions : Array Func := #[]
  locals : LocalEnv := []
  heap : Heap := []
  nextAddr : Nat := 0
  deriving Repr, BEq

structure Result where
  values : Array GoValue
  deriving Repr, BEq

inductive ExecOutcome where
  | normal (state : ExecState)
  | returned (state : ExecState)
  | broke (state : ExecState)
  | continued (state : ExecState)
  deriving Repr, BEq

private def ExecOutcome.state : ExecOutcome → ExecState
  | .normal state => state
  | .returned state => state
  | .broke state => state
  | .continued state => state

private def LocalEnv.lookup : LocalEnv → String → Option Loc
  | [], _ => none
  | (name, loc) :: rest, needle =>
      if name == needle then some loc else LocalEnv.lookup rest needle

private def LocalEnv.set : LocalEnv → String → Loc → LocalEnv
  | [], name, loc => [(name, loc)]
  | (name, old) :: rest, needle, loc =>
      if name == needle then
        (name, loc) :: rest
      else
        (name, old) :: LocalEnv.set rest needle loc

private def Heap.lookup : Heap → Loc → Option GoValue
  | [], _ => none
  | (loc, value) :: rest, needle =>
      if loc == needle then some value else Heap.lookup rest needle

private def Heap.set : Heap → Loc → GoValue → Heap
  | [], loc, value => [(loc, value)]
  | (loc, old) :: rest, needle, value =>
      if loc == needle then
        (loc, value) :: rest
      else
        (loc, old) :: Heap.set rest needle value

private def TypeEnv.lookup : TypeEnv → String → Option TypeDef
  | [], _ => none
  | (name, defn) :: rest, needle =>
      if name == needle then some defn else TypeEnv.lookup rest needle

private def StructFields.lookup : Array (String × GoValue) → String → Option GoValue
  | fields, needle =>
      fields.foldl
        (fun found (name, value) =>
          match found with
          | some value => some value
          | none => if name == needle then some value else none)
        none

private def StructFields.set (fields : Array (String × GoValue)) (needle : String)
    (value : GoValue) : Except GoError (Array (String × GoValue)) := do
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

private def ExecState.freshLoc (state : ExecState) : Loc × ExecState :=
  let loc := Loc.base { id := state.nextAddr }
  (loc, { state with nextAddr := state.nextAddr + 1 })

private def ExecState.bindLocal (state : ExecState) (name : String) (value : GoValue) :
    ExecState :=
  match LocalEnv.lookup state.locals name with
  | some loc =>
      { state with heap := Heap.set state.heap loc value }
  | none =>
      let (loc, state) := state.freshLoc
      { state with
        locals := LocalEnv.set state.locals name loc,
        heap := Heap.set state.heap loc value
      }

private def ExecState.alloc (state : ExecState) (value : GoValue) : Loc × ExecState :=
  let (loc, state) := state.freshLoc
  (loc, { state with heap := Heap.set state.heap loc value })

private def unsupported {α : Type} (feature : String) : Except GoError α :=
  throw (.unsupported feature)

private def panic {α : Type} (message : String) : Except GoError α :=
  throw (.panic message)

private def stuck {α : Type} (message : String) : Except GoError α :=
  throw (.stuck message)

private def lookupLoc (state : ExecState) (name : String) : Except GoError Loc :=
  match LocalEnv.lookup state.locals name with
  | some loc => return loc
  | none => stuck s!"unbound GoCore variable address: {name}"

private def arrayIndexNat (values : Array GoValue) (index : Int) : Except GoError Nat := do
  if index < 0 then
    panic "index out of range"
  let i := index.toNat
  if i < values.size then
    return i
  else
    panic "index out of range"

private def arrayGet (values : Array GoValue) (index : Int) : Except GoError GoValue := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some value => return value
  | none => panic "index out of range"

private def arraySet (values : Array GoValue) (index : Int) (value : GoValue) :
    Except GoError (Array GoValue) := do
  let i ← arrayIndexNat values index
  return values.set! i value

private def natFromNonnegativeInt (context : String) (value : Int) : Except GoError Nat := do
  if value < 0 then
    panic context
  return value.toNat

private def validateSlice (slice : SliceValue) : Except GoError Unit := do
  if slice.len > slice.cap then
    stuck s!"malformed GoCore slice: len {slice.len} > cap {slice.cap}"
  match slice.base with
  | some _ => return ()
  | none =>
      if slice.offset == 0 && slice.len == 0 && slice.cap == 0 then
        return ()
      else
        stuck s!"malformed GoCore nil slice: {repr slice}"

private def sliceIndexLoc (slice : SliceValue) (index : Int) : Except GoError Loc := do
  validateSlice slice
  let i ← natFromNonnegativeInt "slice index out of bounds" index
  if i < slice.len then
    match slice.base with
    | some base => return .index base (Int.ofNat (slice.offset + i))
    | none => stuck s!"malformed GoCore nil slice with length {slice.len}"
  else
    panic "slice index out of bounds"

private def sliceFromSlice (slice : SliceValue) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  validateSlice slice
  let low ← natFromNonnegativeInt "slice bounds out of range" low
  let high ← natFromNonnegativeInt "slice bounds out of range" high
  match max with
  | none =>
      if low <= high && high <= slice.len then
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

private def sliceFromArray (base : Loc) (length : Nat) (low high : Int) (max : Option Int) :
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

private def lookup (state : ExecState) (name : String) : Except GoError GoValue := do
  loadLoc state (← lookupLoc state name)

mutual
  partial def defaultValue (state : ExecState) : Ty → Except GoError GoValue
    | .bool => return .bool false
    | .int => return .int 0
    | .array length elem => do
        let mut values := #[]
        for _ in [:length] do
          values := values.push (← defaultValue state elem)
        return .array values
    | .slice _ => return .slice { base := none, offset := 0, len := 0, cap := 0 }
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

private def buildDefaultArrayValue (state : ExecState) (length : Nat) (elem : Ty) :
    Except GoError GoValue :=
  buildArrayValue state length elem #[]

private def valueAsInt : GoValue → Except GoError Int
  | .int value => return value
  | other => stuck s!"expected int value, got {repr other}"

private def valueAsBool : GoValue → Except GoError Bool
  | .bool value => return value
  | other => stuck s!"expected bool value, got {repr other}"

private def valueAsSlice : GoValue → Except GoError SliceValue
  | .slice value => return value
  | other => stuck s!"expected slice value, got {repr other}"

private def valueAsLoc : GoValue → Except GoError Loc
  | .addr loc => return loc
  | .nil => panic "nil pointer dereference"
  | other => stuck s!"expected address value, got {repr other}"

private partial def valueEq : GoValue → GoValue → Except GoError Bool
  | .bool left, .bool right => return left == right
  | .int left, .int right => return left == right
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

mutual
  partial def evalExpr (state : ExecState) : Expr → Except GoError GoValue
    | .var id => lookup state id
    | .intLit value => return .int value
    | .boolLit value => return .bool value
    | .add left right => do
        return .int ((← valueAsInt (← evalExpr state left)) + (← valueAsInt (← evalExpr state right)))
    | .sub left right => do
        return .int ((← valueAsInt (← evalExpr state left)) - (← valueAsInt (← evalExpr state right)))
    | .mul left right => do
        return .int ((← valueAsInt (← evalExpr state left)) * (← valueAsInt (← evalExpr state right)))
    | .div left right => do
        let dividend ← valueAsInt (← evalExpr state left)
        let divisor ← valueAsInt (← evalExpr state right)
        if divisor == 0 then
          panic "integer divide by zero"
        return .int (Int.tdiv dividend divisor)
    | .mod left right => do
        let dividend ← valueAsInt (← evalExpr state left)
        let divisor ← valueAsInt (← evalExpr state right)
        if divisor == 0 then
          panic "integer divide by zero"
        return .int (Int.tmod dividend divisor)
    | .eqCmp left right => do
        let leftValue ← evalExpr state left
        let rightValue ← evalExpr state right
        return .bool (← valueEq leftValue rightValue)
    | .neqCmp left right => do
        let leftValue ← evalExpr state left
        let rightValue ← evalExpr state right
        return .bool (!(← valueEq leftValue rightValue))
    | .atMostCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) <= (← valueAsInt (← evalExpr state right)))
    | .atLeastCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) >= (← valueAsInt (← evalExpr state right)))
    | .lessCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) < (← valueAsInt (← evalExpr state right)))
    | .greaterCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) > (← valueAsInt (← evalExpr state right)))
    | .and left right => do
        if ← valueAsBool (← evalExpr state left) then
          return .bool (← valueAsBool (← evalExpr state right))
        else
          return .bool false
    | .or left right => do
        if ← valueAsBool (← evalExpr state left) then
          return .bool true
        else
          return .bool (← valueAsBool (← evalExpr state right))
    | .not operand => do
        return .bool (!(← valueAsBool (← evalExpr state operand)))
    | .ref id => return .addr (← lookupLoc state id)
    | .deref ptr _typ => do
        loadLoc state (← valueAsLoc (← evalExpr state ptr))
    | .structLit typ args => do
        let mut values := #[]
        for arg in args do
          values := values.push (← evalExpr state arg)
        buildStructValue state typ values
    | .fieldGet recv typeName fieldName => do
        match ← evalExpr state recv with
        | .struct actualType fields =>
            if actualType != typeName then
              stuck s!"expected struct {typeName}, got struct {actualType}"
            match StructFields.lookup fields fieldName with
            | some value => return value
            | none => stuck s!"unknown GoCore struct field: {fieldName}"
        | other => stuck s!"expected struct value for field access, got {repr other}"
    | .fieldAddr base typeName fieldName => do
        return .addr (.field (← valueAsLoc (← evalExpr state base)) typeName fieldName)
    | .arrayLit length elem args => do
        let mut values := #[]
        for (key, arg) in args do
          values := values.push (key, (← evalExpr state arg))
        buildArrayValue state length elem values
    | .defaultValue typ => defaultValue state typ
    | .indexGet base index => do
        match ← evalExpr state base with
        | .array values => arrayGet values (← valueAsInt (← evalExpr state index))
        | .slice slice => do
            let loc ← sliceIndexLoc slice (← valueAsInt (← evalExpr state index))
            loadLoc state loc
        | other => stuck s!"expected array or slice value for index access, got {repr other}"
    | .indexAddr base index => do
        let indexValue ← valueAsInt (← evalExpr state index)
        match ← evalExpr state base with
        | .slice slice => return .addr (← sliceIndexLoc slice indexValue)
        | .addr baseLoc =>
            match ← loadLoc state baseLoc with
            | .array values =>
                let _ ← arrayIndexNat values indexValue
                return .addr (.index baseLoc indexValue)
            | .slice slice => return .addr (← sliceIndexLoc slice indexValue)
            | other => stuck s!"expected array or slice base for index address, got {repr other}"
        | other => stuck s!"expected array or slice base for index address, got {repr other}"
    | .slice base low high max => do
        let baseValue ← evalExpr state base
        let lowValue ← valueAsInt (← evalExpr state low)
        let highValue ← valueAsInt (← evalExpr state high)
        let maxValue ←
          match max with
          | none => pure none
          | some max => some <$> valueAsInt (← evalExpr state max)
        match baseValue with
        | .slice slice => sliceFromSlice slice lowValue highValue maxValue
        | .addr baseLoc =>
            match ← loadLoc state baseLoc with
            | .array values => sliceFromArray baseLoc values.size lowValue highValue maxValue
            | .slice slice => sliceFromSlice slice lowValue highValue maxValue
            | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
        | .array values =>
            unsupported s!"slice expression over non-addressable array value of length {values.size}"
        | other => stuck s!"expected array or slice value for slice expression, got {repr other}"
    | .length operand => do
        match ← evalExpr state operand with
        | .array values => return .int values.size
        | .slice slice => do
            validateSlice slice
            return .int slice.len
        | other => unsupported s!"len for non-array/slice value {repr other}"
    | .capacity operand => do
        match ← evalExpr state operand with
        | .array values => return .int values.size
        | .slice slice => do
            validateSlice slice
            return .int slice.cap
        | other => unsupported s!"cap for non-array/slice value {repr other}"
    | .old operand => evalExpr state operand
    | .unsupported feature => unsupported feature

  partial def evalAssigneeLoc (state : ExecState) : Assignee → Except GoError Loc
    | .var id => lookupLoc state id
    | .addr locExpr => do
        valueAsLoc (← evalExpr state locExpr)
    | .unsupported feature => unsupported feature

  partial def evalAssigneeLocs (state : ExecState) (targets : Array Assignee) :
      Except GoError (Array Loc) := do
    let mut locs := #[]
    for target in targets do
      locs := locs.push (← evalAssigneeLoc state target)
    return locs

  partial def assignLoc (state : ExecState) (loc : Loc) (value : GoValue) :
      Except GoError ExecState := do
    storeLoc state loc value

  partial def assignAssignee (state : ExecState) (assignee : Assignee) (value : GoValue) :
      Except GoError ExecState := do
    assignLoc state (← evalAssigneeLoc state assignee) value

  partial def assignLocs (state : ExecState) (targets : Array Loc)
      (values : Array GoValue) : Except GoError ExecState := do
    if targets.size != values.size then
      stuck s!"expected {targets.size} call result value(s), got {values.size}"
    let mut state := state
    let mut i := 0
    for target in targets do
      match values[i]? with
      | some value =>
          state ← assignLoc state target value
          i := i + 1
      | none => stuck s!"missing call result value {i}"
    return state

  partial def assignAssignees (state : ExecState) (targets : Array Assignee)
      (values : Array GoValue) : Except GoError ExecState := do
    assignLocs state (← evalAssigneeLocs state targets) values

  partial def sliceVisibleValues (state : ExecState) (slice : SliceValue) :
      Except GoError (Array GoValue) := do
    validateSlice slice
    let mut values := #[]
    for i in [:slice.len] do
      values := values.push (← loadLoc state (← sliceIndexLoc slice (Int.ofNat i)))
    return values

  partial def execCopySlice (state : ExecState) (target : Assignee) (dstExpr srcExpr : Expr) :
      Except GoError ExecState := do
    let targetLoc ← evalAssigneeLoc state target
    let dstSlice ← valueAsSlice (← evalExpr state dstExpr)
    let srcSlice ← valueAsSlice (← evalExpr state srcExpr)
    validateSlice dstSlice
    validateSlice srcSlice
    let count := Nat.min dstSlice.len srcSlice.len
    let mut values := #[]
    for i in [:count] do
      values := values.push (← loadLoc state (← sliceIndexLoc srcSlice (Int.ofNat i)))
    let mut state := state
    let mut i := 0
    for value in values do
      state ← storeLoc state (← sliceIndexLoc dstSlice (Int.ofNat i)) value
      i := i + 1
    assignLoc state targetLoc (.int (Int.ofNat count))

  partial def execAppendSlice (state : ExecState) (target : Assignee) (sliceExpr elemsExpr : Expr) :
      Except GoError ExecState := do
    let targetLoc ← evalAssigneeLoc state target
    let slice ← valueAsSlice (← evalExpr state sliceExpr)
    let elems ← valueAsSlice (← evalExpr state elemsExpr)
    validateSlice slice
    validateSlice elems
    let elemValues ← sliceVisibleValues state elems
    let newLen := slice.len + elemValues.size
    if newLen <= slice.cap then
      let mut state := state
      let mut i := 0
      for value in elemValues do
        match slice.base with
        | some base =>
            state ← storeLoc state (.index base (Int.ofNat (slice.offset + slice.len + i))) value
            i := i + 1
        | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place"
      assignLoc state targetLoc (.slice { slice with len := newLen })
    else
      let oldValues ← sliceVisibleValues state slice
      let backing := GoValue.array (oldValues ++ elemValues)
      let (base, state) := state.alloc backing
      assignLoc state targetLoc (.slice { base := some base, offset := 0, len := newLen, cap := newLen })

  partial def execMakeSlice (state : ExecState) (target : Assignee) (elem : Ty)
      (lenExpr : Expr) (capExpr : Option Expr) : Except GoError ExecState := do
    let target ← evalAssigneeLoc state target
    let lenValue ← valueAsInt (← evalExpr state lenExpr)
    let capValue ←
      match capExpr with
      | none => pure lenValue
      | some capExpr => valueAsInt (← evalExpr state capExpr)
    let len ← natFromNonnegativeInt "makeslice: len out of range" lenValue
    let cap ← natFromNonnegativeInt "makeslice: cap out of range" capValue
    if cap < len then
      panic "makeslice: cap out of range"
    let backing ← buildDefaultArrayValue state cap elem
    let (base, state) := state.alloc backing
    assignLoc state target (.slice { base := some base, offset := 0, len, cap })

  partial def execFunctionCallWithLocs (fuel : Nat) (state : ExecState) (targets : Array Loc)
      (name : String) (args : Array Expr) : Except GoError ExecState := do
    if fuel == 0 then
      stuck "GoCore execution fuel exhausted"
    let func ←
      match findFunctionIn? state.functions name with
      | some func => pure func
      | none => stuck s!"GoCore function not found: {name}"
    if func.args.size != args.size then
      stuck s!"function {name} expected {func.args.size} argument(s), got {args.size}"
    let mut argValues := #[]
    for arg in args do
      argValues := argValues.push (← evalExpr state arg)
    let callerLocals := state.locals
    let mut callState : ExecState := { state with locals := [] }
    let mut i := 0
    for param in func.args do
      match argValues[i]? with
      | some value =>
          callState := callState.bindLocal param.id value
          i := i + 1
      | none => stuck s!"missing argument {i}"
    for result in func.results do
      callState := callState.bindLocal result.id (← defaultValue callState result.typ)
    callState ←
      match ← execStmt (fuel - 1) callState func.body with
      | .normal nextState => pure nextState
      | .returned nextState => pure nextState
      | .broke _ => stuck s!"function {name} body escaped with break"
      | .continued _ => stuck s!"function {name} body escaped with continue"
    let mut resultValues := #[]
    for result in func.results do
      resultValues := resultValues.push (← lookup callState result.id)
    let state : ExecState := { callState with locals := callerLocals }
    assignLocs state targets resultValues

  partial def execFunctionCall (fuel : Nat) (state : ExecState) (targets : Array Assignee)
      (name : String) (args : Array Expr) : Except GoError ExecState := do
    execFunctionCallWithLocs fuel state (← evalAssigneeLocs state targets) name args

  partial def execDecl (state : ExecState) (param : Param) : Except GoError ExecState := do
    return state.bindLocal param.id (← defaultValue state param.typ)

  partial def execDecls (state : ExecState) (decls : Array Param) : Except GoError ExecState := do
    let mut state := state
    for decl in decls do
      state ← execDecl state decl
    return state

  partial def execStmts (fuel : Nat) (state : ExecState) (stmts : Array Stmt) :
      Except GoError ExecOutcome := do
    let mut state := state
    for stmt in stmts do
      match ← execStmt fuel state stmt with
      | .normal nextState => state := nextState
      | outcome => return outcome
    return .normal state

  partial def execStmt (fuel : Nat) (state : ExecState) : Stmt → Except GoError ExecOutcome
    | .seqn stmts => execStmts fuel state stmts
    | .block decls stmts => do
        execStmts fuel (← execDecls state decls) stmts
    | .initialization var => return .normal (← execDecl state var)
    | .assign left right => do
        let loc ← evalAssigneeLoc state left
        let value ← evalExpr state right
        return .normal (← assignLoc state loc value)
    | .makeSlice target elem len cap => return .normal (← execMakeSlice state target elem len cap)
    | .appendSlice target slice elems => return .normal (← execAppendSlice state target slice elems)
    | .copySlice target dst src => return .normal (← execCopySlice state target dst src)
    | .call targets name args => return .normal (← execFunctionCall fuel state targets name args)
    | .ifThenElse cond thenBranch elseBranch => do
        if ← valueAsBool (← evalExpr state cond) then
          execStmt fuel state thenBranch
        else
          execStmt fuel state elseBranch
    | .while cond body => do
        if fuel == 0 then
          stuck "GoCore execution fuel exhausted"
        if ← valueAsBool (← evalExpr state cond) then
          match ← execStmt fuel state body with
          | .normal bodyState => execStmt (fuel - 1) bodyState (.while cond body)
          | .continued bodyState => execStmt (fuel - 1) bodyState (.while cond body)
          | .broke bodyState => return .normal bodyState
          | .returned bodyState => return .returned bodyState
        else
          return .normal state
    | .returnStmt => return .returned state
    | .breakStmt => return .broke state
    | .continueStmt => return .continued state
    | .label _ => return .normal state
    | .unsupported feature => unsupported feature
end

private def bindParams (state : ExecState) (params : Array Param) (args : Array GoValue) :
    Except GoError ExecState := do
  if params.size != args.size then
    stuck s!"expected {params.size} argument(s), got {args.size}"
  let mut state := state
  let mut i := 0
  for param in params do
    match args[i]? with
    | some value =>
        state := state.bindLocal param.id value
        i := i + 1
    | none => stuck s!"missing argument {i}"
  return state

private def initResults (state : ExecState) (results : Array Param) : Except GoError ExecState := do
  let mut state := state
  for result in results do
    state := state.bindLocal result.id (← defaultValue state result.typ)
  return state

private def collectResults (state : ExecState) (results : Array Param) :
    Except GoError (Array GoValue) := do
  let mut values := #[]
  for result in results do
    values := values.push (← lookup state result.id)
  return values

def runFunctionWithContext (fuel : Nat) (types : TypeEnv) (functions : Array Func)
    (func : Func) (args : Array GoValue) : Except GoError Result := do
  let state ← bindParams { types := types, functions := functions } func.args args
  let state ← initResults state func.results
  let state ←
    match ← execStmt fuel state func.body with
    | .normal state => pure state
    | .returned state => pure state
    | .broke _ => stuck s!"function {func.name} body escaped with break"
    | .continued _ => stuck s!"function {func.name} body escaped with continue"
  return { values := (← collectResults state func.results) }

def runFunctionWithTypes (fuel : Nat) (types : TypeEnv) (func : Func) (args : Array GoValue) :
    Except GoError Result :=
  runFunctionWithContext fuel types #[func] func args

def runFunction (fuel : Nat) (func : Func) (args : Array GoValue) : Except GoError Result :=
  runFunctionWithTypes fuel [] func args

def findFunction? (program : Program) (name : String) : Option Func :=
  findFunctionIn? program.funcs name

def runNamedFunction (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) :
    Except GoError Result := do
  let func ←
    match findFunction? program name with
    | some func => pure func
    | none => stuck s!"GoCore function not found: {name}"
  runFunctionWithContext fuel program.typeDefs.toList program.funcs func args

def runNamedFunctionInts (fuel : Nat) (program : Program) (name : String) (args : Array Int) :
    Except GoError Result :=
  runNamedFunction fuel program name (args.map GoValue.int)

end GoLean.GoCore
