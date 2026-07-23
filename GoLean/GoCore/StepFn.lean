import GoLean.GoCore.Machine

/-!
# The executable step function (reshape R2, S2c)

`stepFn` is the machine's instantiation: one arm per `Machine.Step` rule,
sharing the rule premises' functions verbatim (`strictPlan`,
`applyStrictOp`, `stmtPlan`, `applyStmtOp`, `enterFrame`, …), plus the
*why* on every configuration the relation is silent on — an explicit
`.stuck`/`.unsupported`/`.internal` error, never a silent approximation
(fail closed). Panics are in-model: a panic *step* produces the
`.panicked` configuration (`.ok`), which the driver reports as
`GoError.panic`; only out-of-model conditions are `Except` errors.

Nondeterminism: the two choice points (mapRange pick-next, appendSlice
spill capacity) consume from the external `Choices` stream, exactly as
the big-step interpreter did — the relation's corresponding rules
quantify over the choice.

Execution is fuel-bounded iteration (`runConfig`); fuel counts machine
steps (design note §5 — the CLI default retunes at S3). The whole-program
drivers (`runFunctionWithContextM`, `runNamedFunctionM`) mirror the
big-step entry points: bind arguments, allocate results, pin their
locations, run the body inside a targetless `frame`, and read the pinned
result locations at the terminal configuration. They use the machine's
env-in-config representation throughout — `ExecState.locals` is never
touched (it is deleted at S4).

Per-rule soundness/completeness lemmas against `Machine.Step` land at S5.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- One machine step. `.ok` is a step the relation permits (including
steps *to* `.panicked`); `.error` means the machine is stuck here, with
the reason. Never call on a terminal configuration (the driver guards). -/
def stepFn (s : ExecState) (c : Config) (choices : Choices) :
    Except GoError (Config × ExecState × Choices) := do
  match c with
  | .panicked _ => throw (.internal "step on terminal panicked configuration")
  | .exec stmt env k =>
      match stmt with
      | .seqn ss => return (.next (seqCont ss.toList env k), s, choices)
      | .block decls ss => do
          let (env', s') ← allocDecls env.pushScope s decls.toList
          return (.next (.seq ss.toList env' k), s', choices)
      | .initialization p =>
          match k with
          | .seq rest kenv k' =>
              if kenv == env then do
                let v ← defaultValue s p.typ
                let (loc, s') := s.alloc v (some p.typ)
                return (.next (.seq rest (env.declare p.id loc) k'), s', choices)
              else throw (.internal "initialization under foreign-scope sequence")
          | _ => throw (.stuck "GoCore initialization outside a statement sequence")
      | .assign lhs rhs =>
          match assigneeExpr lhs with
          | some te => return (.evalE te env (.assignTargetK rhs env k), s, choices)
          | none =>
              match lhs with
              | .unsupported feature => throw (.unsupported feature)
              | _ => throw (.internal "unclassified assignee")
      | .ifThenElse c t e => return (.evalE c env (.ifK t e env k), s, choices)
      | .while c b => return (.evalE c env (.whileK c b env k), s, choices)
      | .returnStmt => return (.returning k, s, choices)
      | .breakStmt => return (.breaking k, s, choices)
      | .continueStmt => return (.continuing k, s, choices)
      | .label _ => return (.next k, s, choices)
      | .call targets fid args =>
          match assigneesExprs targets.toList with
          | some (te :: rest) =>
              return (.evalE te env (.callTargetsK fid [] rest args.toList env k), s, choices)
          | some [] =>
              match args.toList with
              | a :: rest =>
                  return (.evalE a env (.callArgsK fid [] [] rest env k), s, choices)
              | [] => do
                  let (func, frameEnv, resultLocs, s') ← enterFrame s fid []
                  return (.exec func.body frameEnv (.frame [] resultLocs k), s', choices)
          | none => throw (.unsupported "unsupported call target assignee")
      | .mapRange keyVar valVar mapExpr keyTy valTy body =>
          return (.evalE mapExpr env
            (.mapRangeK keyVar valVar keyTy valTy body env k), s, choices)
      | .unsupported feature => throw (.unsupported feature)
      | wide =>
          -- assignMany / newValue / makeSlice / makeMap / mapAssign /
          -- mapLookup / typeAssert / appendSlice / copySlice
          match stmtPlan wide with
          | some (op, nt, e :: rest) =>
              return (.evalE e env (.stmtOpK op nt [] rest env k), s, choices)
          | some (op, nt, []) => do
              let (s', choices') ← applyStmtOp s choices op nt []
              return (.next k, s', choices')
          | none =>
              match wide with
              | .assignMany left right =>
                  if left.size != right.size then
                    throw (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}")
                  else throw (.unsupported "unsupported multi-assignment target assignee")
              | _ => throw (.unsupported "unsupported statement target assignee")
  | .evalE e env k =>
      match e with
      | .var id =>
          match LocalEnv.lookup env id with
          | some loc => do return (.retV (← loadLoc s loc) k, s, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .intLit value kind =>
          return (.retV (.int (kind.normalize value) kind) k, s, choices)
      | .boolLit value => return (.retV (.bool value) k, s, choices)
      | .stringLit value => return (.retV (.string value) k, s, choices)
      | .ref id =>
          match LocalEnv.lookup env id with
          | some loc => return (.retV (.addr loc) k, s, choices)
          | none => throw (.stuck s!"unbound GoCore variable address: {id}")
      | .locLit l => return (.retV (.addr l) k, s, choices)
      | .and l r => return (.evalE l env (.andK r env k), s, choices)
      | .or l r => return (.evalE l env (.orK r env k), s, choices)
      | .unsupported feature => throw (.unsupported feature)
      | e =>
          match strictPlan e with
          | some (op, e₁ :: rest) =>
              return (.evalE e₁ env (.strictK op [] rest env k), s, choices)
          | some (op, []) =>
              match applyStrictOp s op [] with
              | .ok (v, s') => return (.retV v k, s', choices)
              | .error (.panic msg) => return (.panicked msg, s, choices)
              | .error err => throw err
          | none => throw (.internal "unclassified expression")
  | .retV v k =>
      match k with
      | .strictK op done (e :: rest) env k' =>
          return (.evalE e env (.strictK op (v :: done) rest env k'), s, choices)
      | .strictK op done [] _ k' =>
          match applyStrictOp s op (v :: done).reverse with
          | .ok (out, s') => return (.retV out k', s', choices)
          | .error (.panic msg) => return (.panicked msg, s, choices)
          | .error err => throw err
      | .andK r env k' => do
          if ← valueAsBool v then
            return (.evalE r env (.boolK k'), s, choices)
          else
            return (.retV (.bool false) k', s, choices)
      | .orK r env k' => do
          if ← valueAsBool v then
            return (.retV (.bool true) k', s, choices)
          else
            return (.evalE r env (.boolK k'), s, choices)
      | .boolK k' => do return (.retV (.bool (← valueAsBool v)) k', s, choices)
      | .ifK t e env k' => do
          if ← valueAsBool v then
            return (.exec t env k', s, choices)
          else
            return (.exec e env k', s, choices)
      | .whileK c b env k' => do
          if ← valueAsBool v then
            return (.exec b env (.loop c b env k'), s, choices)
          else
            return (.next k', s, choices)
      | .assignTargetK rhs env k' =>
          match valueAsLoc v with
          | .ok loc => return (.evalE rhs env (.assignStoreK loc k'), s, choices)
          | .error (.panic msg) => return (.panicked msg, s, choices)
          | .error err => throw err
      | .assignStoreK loc k' =>
          match storeLoc s loc v with
          | .ok s' => return (.next k', s', choices)
          | .error (.panic msg) => return (.panicked msg, s, choices)
          | .error err => throw err
      | .callTargetsK fid locs pending args env k' =>
          match valueAsLoc v with
          | .error (.panic msg) => return (.panicked msg, s, choices)
          | .error err => throw err
          | .ok loc =>
              match pending with
              | te :: rest =>
                  return (.evalE te env
                    (.callTargetsK fid (locs ++ [loc]) rest args env k'), s, choices)
              | [] =>
                  match args with
                  | a :: rest =>
                      return (.evalE a env
                        (.callArgsK fid (locs ++ [loc]) [] rest env k'), s, choices)
                  | [] => do
                      let (func, frameEnv, resultLocs, s') ← enterFrame s fid []
                      return (.exec func.body frameEnv
                        (.frame (locs ++ [loc]) resultLocs k'), s', choices)
      | .callArgsK fid locs vals pending env k' =>
          match pending with
          | a :: rest =>
              return (.evalE a env
                (.callArgsK fid locs (vals ++ [v]) rest env k'), s, choices)
          | [] => do
              let (func, frameEnv, resultLocs, s') ← enterFrame s fid (vals ++ [v])
              return (.exec func.body frameEnv (.frame locs resultLocs k'), s', choices)
      | .stmtOpK op nt done pending env k' => do
          if done.length < nt then
            match valueAsLoc v with
            | .error (.panic msg) => return (.panicked msg, s, choices)
            | .error err => throw err
            | .ok _ => pure ()
          match pending with
          | e :: rest =>
              return (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, choices)
          | [] =>
              match applyStmtOp s choices op nt (v :: done).reverse with
              | .ok (s', choices') => return (.next k', s', choices')
              | .error (.panic msg) => return (.panicked msg, s, choices)
              | .error err => throw err
      | .mapRangeK keyVar valVar keyTy valTy body env k' => do
          let entries ← mapRangeEntries s v
          return (.next (.mapIterK keyVar valVar keyTy valTy body entries env k'), s, choices)
      | .stop => throw (.internal "value delivered to empty continuation")
      | _ => throw (.internal "value delivered to statement continuation")
  | .next k =>
      match k with
      | .stop => throw (.internal "step on terminal configuration")
      | .seq (t :: rest) env k' => return (.exec t env (.seq rest env k'), s, choices)
      | .seq [] _ k' => return (.next k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      | .frame targets results k' => do
          let vs ← loadMany s results
          let s' ← storeMany s targets vs
          return (.next k', s', choices)
      | .mapIterK keyVar valVar keyTy valTy body remaining env k' =>
          if remaining.isEmpty then
            return (.next k', s, choices)
          else do
            let (idx, choices') := choices.consume remaining.size
            match hidx : remaining[idx]? with
            | none => throw (.internal "mapRange choice index out of bounds")
            | some (key, value) => do
                have hlt : idx < remaining.size :=
                  (Array.getElem?_eq_some_iff.mp hidx).1
                let (env', s') ← bindIterVars env.pushScope s
                  keyVar valVar keyTy valTy key value
                return (.exec body env'
                  (.mapIterK keyVar valVar keyTy valTy body
                    (remaining.eraseIdx idx hlt) env k'), s', choices')
      | _ => throw (.internal "completion delivered to expression continuation")
  | .breaking k =>
      match k with
      | .seq _ _ k' => return (.breaking k', s, choices)
      | .loop _ _ _ k' => return (.next k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ k' => return (.next k', s, choices)
      | .frame _ _ _ => throw (.stuck "function body escaped with break")
      | .stop => throw (.stuck "break outside loop")
      | _ => throw (.internal "break delivered to expression continuation")
  | .continuing k =>
      match k with
      | .seq _ _ k' => return (.continuing k', s, choices)
      | .loop c b env k' => return (.exec (.while c b) env k', s, choices)
      | .mapIterK keyVar valVar keyTy valTy body remaining env k' =>
          return (.next (.mapIterK keyVar valVar keyTy valTy body remaining env k'), s, choices)
      | .frame _ _ _ => throw (.stuck "function body escaped with continue")
      | .stop => throw (.stuck "continue outside loop")
      | _ => throw (.internal "continue delivered to expression continuation")
  | .returning k =>
      match k with
      | .seq _ _ k' => return (.returning k', s, choices)
      | .loop _ _ _ k' => return (.returning k', s, choices)
      | .mapIterK _ _ _ _ _ _ _ k' => return (.returning k', s, choices)
      | .frame targets results k' => do
          let vs ← loadMany s results
          let s' ← storeMany s targets vs
          return (.next k', s', choices)
      | .stop => throw (.internal "return unwound past the entry frame")
      | _ => throw (.internal "return delivered to expression continuation")

/-- Fuel-bounded iteration of `stepFn` to a terminal configuration. Fuel
counts machine steps; the terminal check precedes the fuel check so a
finished program never reports exhaustion. `.panicked` reports as
`GoError.panic` — the same classification surface as the big-step
interpreter's. -/
def runConfig : Nat → ExecState → Config → Choices → Except GoError (ExecState × Choices)
  | fuel, s, c, choices =>
      match c with
      | .next .stop => return (s, choices)
      | .panicked msg => throw (.panic msg)
      | c =>
          match fuel with
          | 0 => throw (.stuck "GoCore execution fuel exhausted")
          | fuel + 1 => do
              let (c', s', choices') ← stepFn s c choices
              runConfig fuel s' c' choices'

/-- Whole-program entry, mirroring the big-step `runFunctionWithContext`:
bind arguments (normalized at declared type), allocate named results at
defaults, pin their locations, run the body inside a targetless `frame`
over `.stop`, and read the pinned result locations at the terminal
configuration. Env-in-config throughout — `ExecState.locals` unused. -/
def runFunctionWithContextM (fuel : Nat) (types : TypeEnv) (functions : Array Func)
    (func : Func) (args : Array GoValue) (methods : Array MethodInfo := #[])
    (choices : Choices := []) : Except GoError Result := do
  let state : ExecState := { types, functions, methods }
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let (env, s₁) ← bindParams [] state func.args.toList args.toList
  let (frameEnv, s₂) ← allocDecls env s₁ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  -- The entry frame is a pure barrier (`[] []`): the big-step entry never
  -- stored results anywhere — the driver reads the pinned locations from
  -- the terminal state below.
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] .stop)
  let (sF, _) ← runConfig fuel s₂ c₀ choices
  return { values := (← loadMany sF resultLocs).toArray }

def runFunctionWithTypesM (fuel : Nat) (types : TypeEnv) (func : Func)
    (args : Array GoValue) : Except GoError Result :=
  runFunctionWithContextM fuel types #[func] func args

def runFunctionM (fuel : Nat) (func : Func) (args : Array GoValue) :
    Except GoError Result :=
  runFunctionWithTypesM fuel [] func args

def runNamedFunctionM (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (choices : List Nat := []) : Except GoError Result := do
  let func ←
    match findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  runFunctionWithContextM fuel program.typeDefs.toList program.funcs func args
    program.methods choices

def runNamedFunctionIntsM (fuel : Nat) (program : Program) (name : String)
    (args : Array Int) (choices : List Nat := []) : Except GoError Result :=
  runNamedFunctionM fuel program name (args.map GoValue.int) choices

end GoLean.GoCore.Machine
