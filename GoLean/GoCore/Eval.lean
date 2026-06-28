import GoLean.GoCore.Ops

namespace GoLean.GoCore

open GoLean

abbrev EvalResult := GoValue × ExecState
abbrev LocResult := Loc × ExecState
abbrev LocsResult := Array Loc × ExecState

mutual
  partial def evalExpr (state : ExecState) : Expr → Except GoError EvalResult
    | .var id => return (← lookup state id, state)
    | .nil none => return (.nil, state)
    | .nil (some typ) =>
        match typ with
        | .slice _ => return (← defaultValue state typ, state)
        | .map _ _ => return (← defaultValue state typ, state)
        | .pointer _ => return (.nil, state)
        | .unsupported feature => unsupported s!"nil literal for {feature}"
        | other => stuck s!"nil literal for non-nilable type {repr other}"
    | .intLit value => return (.int value, state)
    | .stringLit value => return (.string value, state)
    | .boolLit value => return (.bool value, state)
    | .add left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        match leftPair.1, rightPair.1 with
        | .int leftValue, .int rightValue => return (.int (leftValue + rightValue), rightPair.2)
        | .string leftValue, .string rightValue => return (.string (leftValue ++ rightValue), rightPair.2)
        | leftValue, rightValue => stuck s!"mismatched + operands: {repr leftValue} and {repr rightValue}"
    | .sub left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.int ((← valueAsInt leftPair.1) - (← valueAsInt rightPair.1)), rightPair.2)
    | .mul left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.int ((← valueAsInt leftPair.1) * (← valueAsInt rightPair.1)), rightPair.2)
    | .div left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        let dividend ← valueAsInt leftPair.1
        let divisor ← valueAsInt rightPair.1
        if divisor == 0 then
          panic "integer divide by zero"
        return (.int (Int.tdiv dividend divisor), rightPair.2)
    | .mod left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        let dividend ← valueAsInt leftPair.1
        let divisor ← valueAsInt rightPair.1
        if divisor == 0 then
          panic "integer divide by zero"
        return (.int (Int.tmod dividend divisor), rightPair.2)
    | .eqCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (← valueEq leftPair.1 rightPair.1), rightPair.2)
    | .neqCmp left right => do
        let leftPair ← evalExpr state left
        let rightPair ← evalExpr leftPair.2 right
        return (.bool (!(← valueEq leftPair.1 rightPair.1)), rightPair.2)
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
    | .deref ptr _typ => do
        let pair ← evalExpr state ptr
        return (← loadLoc pair.2 (← valueAsLoc pair.1), pair.2)
    | .structLit typ args => do
        let mut current := state
        let mut values := #[]
        for arg in args do
          let pair ← evalExpr current arg
          values := values.push pair.1
          current := pair.2
        return (← buildStructValue current typ values, current)
    | .fieldGet recv typeName fieldName => do
        let pair ← evalExpr state recv
        match pair.1 with
        | .struct actualType fields =>
            if actualType != typeName then
              stuck s!"expected struct {typeName}, got struct {actualType}"
            match StructFields.lookup fields fieldName with
            | some value => return (value, pair.2)
            | none => stuck s!"unknown GoCore struct field: {fieldName}"
        | other => stuck s!"expected struct value for field access, got {repr other}"
    | .fieldAddr base typeName fieldName => do
        let pair ← evalExpr state base
        return (.addr (.field (← valueAsLoc pair.1) typeName fieldName), pair.2)
    | .arrayLit length elem args => do
        let mut current := state
        let mut values := #[]
        for (key, arg) in args do
          let pair ← evalExpr current arg
          values := values.push (key, pair.1)
          current := pair.2
        return (← buildArrayValue current length elem values, current)
    | .defaultValue typ => return (← defaultValue state typ, state)
    | .indexGet base index => do
        let basePair ← evalExpr state base
        let indexPair ← evalExpr basePair.2 index
        let indexValue ← valueAsInt indexPair.1
        match basePair.1 with
        | .array values => return (← arrayGet values indexValue, indexPair.2)
        | .slice slice => do
            let loc ← sliceIndexLoc slice indexValue
            return (← loadLoc indexPair.2 loc, indexPair.2)
        | other => stuck s!"expected array or slice value for index access, got {repr other}"
    | .mapGet base index valueTy => do
        let basePair ← evalExpr state base
        let map ← valueAsMap basePair.1
        let keyPair ← evalExpr basePair.2 index
        match map.base with
        | none => return (← defaultValue keyPair.2 valueTy, keyPair.2)
        | some baseLoc =>
            match ← loadLoc keyPair.2 baseLoc with
            | .mapData entries =>
                match ← mapEntryIndex? entries keyPair.1 with
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
        | .slice slice => return (← sliceFromSlice slice lowValue highValue maxValue, current)
        | .addr baseLoc =>
            match ← loadLoc current baseLoc with
            | .array values => return (← sliceFromArray baseLoc values.size lowValue highValue maxValue, current)
            | .slice slice => return (← sliceFromSlice slice lowValue highValue maxValue, current)
            | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
        | .array values =>
            unsupported s!"slice expression over non-addressable array value of length {values.size}"
        | other => stuck s!"expected array or slice value for slice expression, got {repr other}"
    | .length operand => do
        let pair ← evalExpr state operand
        match pair.1 with
        | .array values => return (.int values.size, pair.2)
        | .string value => return (.int value.utf8ByteSize, pair.2)
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
    | .capacity operand => do
        let pair ← evalExpr state operand
        match pair.1 with
        | .array values => return (.int values.size, pair.2)
        | .slice slice => do
            validateSlice slice
            return (.int slice.cap, pair.2)
        | other => unsupported s!"cap for non-array/slice value {repr other}"
    | .old operand => evalExpr state operand
    | .unsupported feature => unsupported feature

  partial def evalAssigneeLoc (state : ExecState) : Assignee → Except GoError LocResult
    | .var id => return (← lookupLoc state id, state)
    | .addr locExpr => do
        let pair ← evalExpr state locExpr
        return (← valueAsLoc pair.1, pair.2)
    | .unsupported feature => unsupported feature

  partial def evalAssigneeLocs (state : ExecState) (targets : Array Assignee) :
      Except GoError LocsResult := do
    let mut current := state
    let mut locs := #[]
    for target in targets do
      let pair ← evalAssigneeLoc current target
      locs := locs.push pair.1
      current := pair.2
    return (locs, current)

  partial def assignLoc (state : ExecState) (loc : Loc) (value : GoValue) :
      Except GoError ExecState := do
    storeLoc state loc value

  partial def assignAssignee (state : ExecState) (assignee : Assignee) (value : GoValue) :
      Except GoError ExecState := do
    let pair ← evalAssigneeLoc state assignee
    assignLoc pair.2 pair.1 value

  partial def assignLocs (state : ExecState) (targets : Array Loc)
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

  partial def assignAssignees (state : ExecState) (targets : Array Assignee)
      (values : Array GoValue) : Except GoError ExecState := do
    let pair ← evalAssigneeLocs state targets
    assignLocs pair.2 pair.1 values

  partial def execAssignMany (state : ExecState) (left : Array Assignee) (right : Array Expr) :
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

  partial def execNewValue (state : ExecState) (target : Assignee) (valueExpr : Expr) :
      Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let valuePair ← evalExpr targetPair.2 valueExpr
    let (loc, current) := valuePair.2.alloc valuePair.1
    assignLoc current targetPair.1 (.addr loc)

  partial def execMakeMap (state : ExecState) (target : Assignee) (_key _value : Ty)
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
    let basePair ← evalExpr state baseExpr
    let map ← valueAsMap basePair.1
    let keyPair ← evalExpr basePair.2 keyExpr
    let valuePair ← evalExpr keyPair.2 valueExpr
    match ← mapEntries valuePair.2 map with
    | none => panic "assignment to entry in nil map"
    | some (baseLoc, entries) =>
        let entries ←
          match ← mapEntryIndex? entries keyPair.1 with
          | some i => pure (entries.set! i (keyPair.1, valuePair.1))
          | none => pure (entries.push (keyPair.1, valuePair.1))
        storeLoc valuePair.2 baseLoc (.mapData entries)

  partial def execMapLookup (state : ExecState) (target okTarget : Assignee)
      (baseExpr keyExpr : Expr) (valueTy : Ty) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLoc state target
    let okPair ← evalAssigneeLoc targetPair.2 okTarget
    let basePair ← evalExpr okPair.2 baseExpr
    let map ← valueAsMap basePair.1
    let keyPair ← evalExpr basePair.2 keyExpr
    let pair ← mapLookupValue keyPair.2 map keyPair.1 valueTy
    let value := pair.1
    let ok := pair.2
    let current ← assignLoc keyPair.2 targetPair.1 value
    assignLoc current okPair.1 (.bool ok)

  partial def sliceVisibleValues (state : ExecState) (slice : SliceValue) :
      Except GoError (Array GoValue) := do
    validateSlice slice
    let mut values := #[]
    for i in [:slice.len] do
      values := values.push (← loadLoc state (← sliceIndexLoc slice (Int.ofNat i)))
    return values

  partial def execCopySlice (state : ExecState) (target : Assignee) (dstExpr srcExpr : Expr) :
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

  partial def execAppendSlice (state : ExecState) (target : Assignee) (sliceExpr elemsExpr : Expr) :
      Except GoError ExecState := do
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
      assignLoc current targetPair.1 (.slice { slice with len := newLen })
    else
      let oldValues ← sliceVisibleValues elemsPair.2 slice
      let backing := GoValue.array (oldValues ++ elemValues)
      let (base, current) := elemsPair.2.alloc backing
      assignLoc current targetPair.1 (.slice { base := some base, offset := 0, len := newLen, cap := newLen })

  partial def execMakeSlice (state : ExecState) (target : Assignee) (elem : Ty)
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
    let len ← natFromNonnegativeInt "makeslice: len out of range" lenValue
    let cap ← natFromNonnegativeInt "makeslice: cap out of range" capValue
    if cap < len then
      panic "makeslice: cap out of range"
    let backing ← buildDefaultArrayValue current cap elem
    let allocated := current.alloc backing
    let base := allocated.1
    let afterAlloc := allocated.2
    assignLoc afterAlloc targetPair.1 (.slice { base := some base, offset := 0, len, cap })

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
    let mut current := state
    let mut argValues := #[]
    for arg in args do
      let pair ← evalExpr current arg
      argValues := argValues.push pair.1
      current := pair.2
    let callerLocals := current.locals
    let mut callState : ExecState := { current with locals := [] }
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
    let callerState : ExecState := { callState with locals := callerLocals }
    assignLocs callerState targets resultValues

  partial def execFunctionCall (fuel : Nat) (state : ExecState) (targets : Array Assignee)
      (name : String) (args : Array Expr) : Except GoError ExecState := do
    let targetPair ← evalAssigneeLocs state targets
    execFunctionCallWithLocs fuel targetPair.2 targetPair.1 name args

  partial def execDecl (state : ExecState) (param : Param) : Except GoError ExecState := do
    return state.bindLocal param.id (← defaultValue state param.typ)

  partial def execDecls (state : ExecState) (decls : Array Param) : Except GoError ExecState := do
    let mut current := state
    for decl in decls do
      current ← execDecl current decl
    return current

  partial def execStmts (fuel : Nat) (state : ExecState) (stmts : Array Stmt) :
      Except GoError ExecOutcome := do
    let mut current := state
    for stmt in stmts do
      match ← execStmt fuel current stmt with
      | .normal nextState => current := nextState
      | outcome => return outcome
    return .normal current

  partial def execStmt (fuel : Nat) (state : ExecState) : Stmt → Except GoError ExecOutcome
    | .seqn stmts => execStmts fuel state stmts
    | .block decls stmts => do
        execStmts fuel (← execDecls state decls) stmts
    | .initialization var => return .normal (← execDecl state var)
    | .assign left right => do
        let locPair ← evalAssigneeLoc state left
        let valuePair ← evalExpr locPair.2 right
        return .normal (← assignLoc valuePair.2 locPair.1 valuePair.1)
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
        let condPair ← evalExpr state cond
        if ← valueAsBool condPair.1 then
          execStmt fuel condPair.2 thenBranch
        else
          execStmt fuel condPair.2 elseBranch
    | .while cond body => do
        if fuel == 0 then
          stuck "GoCore execution fuel exhausted"
        let condPair ← evalExpr state cond
        if ← valueAsBool condPair.1 then
          match ← execStmt fuel condPair.2 body with
          | .normal bodyState => execStmt (fuel - 1) bodyState (.while cond body)
          | .continued bodyState => execStmt (fuel - 1) bodyState (.while cond body)
          | .broke bodyState => return .normal bodyState
          | .returned bodyState => return .returned bodyState
        else
          return .normal condPair.2
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
