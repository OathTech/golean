import GoLean.GoCore.Ops

namespace GoLean.GoCore

open GoLean

mutual
  partial def evalExpr (state : ExecState) : Expr → Except GoError GoValue
    | .var id => lookup state id
    | .nil none => return .nil
    | .nil (some typ) =>
        match typ with
        | .slice _ => defaultValue state typ
        | .map _ _ => defaultValue state typ
        | .pointer _ => return .nil
        | .unsupported feature => unsupported s!"nil literal for {feature}"
        | other => stuck s!"nil literal for non-nilable type {repr other}"
    | .intLit value => return .int value
    | .stringLit value => return .string value
    | .boolLit value => return .bool value
    | .add left right => do
        match ← evalExpr state left, ← evalExpr state right with
        | .int leftValue, .int rightValue => return .int (leftValue + rightValue)
        | .string leftValue, .string rightValue => return .string (leftValue ++ rightValue)
        | leftValue, rightValue => stuck s!"mismatched + operands: {repr leftValue} and {repr rightValue}"
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
        return .bool (← valueAtMost (← evalExpr state left) (← evalExpr state right))
    | .atLeastCmp left right => do
        return .bool (← valueAtLeast (← evalExpr state left) (← evalExpr state right))
    | .lessCmp left right => do
        return .bool (← valueLess (← evalExpr state left) (← evalExpr state right))
    | .greaterCmp left right => do
        return .bool (← valueGreater (← evalExpr state left) (← evalExpr state right))
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
    | .mapGet base index valueTy => do
        let map ← valueAsMap (← evalExpr state base)
        let key ← evalExpr state index
        match map.base with
        | none => defaultValue state valueTy
        | some baseLoc =>
            match ← loadLoc state baseLoc with
            | .mapData entries =>
                match ← mapEntryIndex? entries key with
                | some i =>
                    match entries[i]? with
                    | some (_, value) => return value
                    | none => stuck s!"missing map entry at index {i}"
                | none => defaultValue state valueTy
            | other => stuck s!"expected map data, got {repr other}"
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
        | .string value => return .int value.utf8ByteSize
        | .slice slice => do
            validateSlice slice
            return .int slice.len
        | .map map => do
            match map.base with
            | none => return .int 0
            | some baseLoc =>
                match ← loadLoc state baseLoc with
                | .mapData entries => return .int entries.size
                | other => stuck s!"expected map data, got {repr other}"
        | other => unsupported s!"len for non-array/slice/map value {repr other}"
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

  partial def execAssignMany (state : ExecState) (left : Array Assignee) (right : Array Expr) :
      Except GoError ExecState := do
    if left.size != right.size then
      stuck s!"multi-assignment expected {left.size} value(s), got {right.size}"
    let locs ← evalAssigneeLocs state left
    let mut values := #[]
    for expr in right do
      values := values.push (← evalExpr state expr)
    assignLocs state locs values

  partial def execNewValue (state : ExecState) (target : Assignee) (valueExpr : Expr) :
      Except GoError ExecState := do
    let target ← evalAssigneeLoc state target
    let value ← evalExpr state valueExpr
    let (loc, state) := state.alloc value
    assignLoc state target (.addr loc)

  partial def execMakeMap (state : ExecState) (target : Assignee) (_key _value : Ty)
      (initialSpace : Option Expr) : Except GoError ExecState := do
    let target ← evalAssigneeLoc state target
    match initialSpace with
    | none => pure ()
    | some expr =>
        let size ← valueAsInt (← evalExpr state expr)
        let _ ← natFromNonnegativeInt "makemap: size out of range" size
    let (base, state) := state.alloc (.mapData #[])
    assignLoc state target (.map { base := some base })

  partial def mapEntries (state : ExecState) (map : MapValue) :
      Except GoError (Option (Loc × Array (GoValue × GoValue))) := do
    match map.base with
    | none => return none
    | some baseLoc =>
        match ← loadLoc state baseLoc with
        | .mapData entries => return some (baseLoc, entries)
        | other => stuck s!"expected map data, got {repr other}"

  partial def mapLookupValue (state : ExecState) (map : MapValue) (key : GoValue)
      (valueTy : Ty) : Except GoError (GoValue × Bool) := do
    match ← mapEntries state map with
    | none => return (← defaultValue state valueTy, false)
    | some (_, entries) =>
        match ← mapEntryIndex? entries key with
        | some i =>
            match entries[i]? with
            | some (_, value) => return (value, true)
            | none => stuck s!"missing map entry at index {i}"
        | none => return (← defaultValue state valueTy, false)

  partial def execMapAssign (state : ExecState) (baseExpr keyExpr valueExpr : Expr) :
      Except GoError ExecState := do
    let map ← valueAsMap (← evalExpr state baseExpr)
    let key ← evalExpr state keyExpr
    let value ← evalExpr state valueExpr
    match ← mapEntries state map with
    | none => panic "assignment to entry in nil map"
    | some (baseLoc, entries) =>
        let entries ←
          match ← mapEntryIndex? entries key with
          | some i => pure (entries.set! i (key, value))
          | none => pure (entries.push (key, value))
        storeLoc state baseLoc (.mapData entries)

  partial def execMapLookup (state : ExecState) (target okTarget : Assignee)
      (baseExpr keyExpr : Expr) (valueTy : Ty) : Except GoError ExecState := do
    let targetLoc ← evalAssigneeLoc state target
    let okLoc ← evalAssigneeLoc state okTarget
    let map ← valueAsMap (← evalExpr state baseExpr)
    let key ← evalExpr state keyExpr
    let pair ← mapLookupValue state map key valueTy
    let value := pair.1
    let ok := pair.2
    let state ← assignLoc state targetLoc value
    assignLoc state okLoc (.bool ok)

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
    | .assignMany left right => return .normal (← execAssignMany state left right)
    | .newValue target value => return .normal (← execNewValue state target value)
    | .makeSlice target elem len cap => return .normal (← execMakeSlice state target elem len cap)
    | .makeMap target key value initialSpace =>
        return .normal (← execMakeMap state target key value initialSpace)
    | .mapAssign base index value =>
        return .normal (← execMapAssign state base index value)
    | .mapLookup target okTarget base index valueTy =>
        return .normal (← execMapLookup state target okTarget base index valueTy)
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

def bindParams (state : ExecState) (params : Array Param) (args : Array GoValue) :
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

def initResults (state : ExecState) (results : Array Param) : Except GoError ExecState := do
  let mut state := state
  for result in results do
    state := state.bindLocal result.id (← defaultValue state result.typ)
  return state

def collectResults (state : ExecState) (results : Array Param) :
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
