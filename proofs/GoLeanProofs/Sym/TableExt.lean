import GoLeanProofs.Sym.Refine
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure

/-!
# The handler-fragment extension, class 1: TYPE-TABLE INPUT
(campaign Arc 4, A4-U2 slice 1; design
`docs/2026-08-22_campaign-arc4-sym-extension-design.md` §2)

The Q4a lever, layered FULLY ADDITIVELY over the untouched Sym core:
store-time normalization at `.defined` types proceeds against an input
`TypeEnv` `T`, so struct-field stores — the raft handlers' bread and
butter, and the pilot's measured cost center — transport inside
windows instead of costing a conditioned kit step each.

Mechanism (design §0's additivity plan, realized even more strictly —
ZERO edits to the existing Sym modules):

- `normalizeValueForTyFuelT T` — the mirror normalizer with the
  machine's `.defined` arm (`Ops.lean:958-966` mirrored verbatim:
  alias/defined re-target, struct via `normalizeFieldsWith'` +
  `emptyStructAssignable'`; `interfaceDef`/`unsupported`/unknown stay
  quits). At `T = []` every defined lookup fails ⇒ behaviorally the
  shipped normalizer.
- `storeLocT`/`storeTargetT` — the store chain over it.
- `stepFnT T` — the extended step: ONE overridden arm
  (`.next (.storeK …)`, routed through `storeTargetT`), everything
  else DELEGATES to the shipped `stepFn'`. `symEvalWindowT` iterates
  it.
- Soundness/refinement: the same template as `Refine.lean` plus ONE
  premise, `SubTable T σ.types` — every successful lookup on the
  input table agrees with the run state's. `SubTable [] U` is
  trivial, so the shipped theorems are the degenerate instance and
  none of their statements move.

Outside the TCB by construction, like everything in `GoLean.Sym`
(the statement-TCB walker's third refusal class bans the prefix).
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

/-! ## The table-agreement premise -/

/-- Every successful lookup on the INPUT table agrees with the
carrier's table. Weaker than equality on purpose: a window emitted at
the pin's table transports into any state whose types extend it. -/
def SubTable (T U : TypeEnv) : Prop :=
  ∀ id d, TypeEnv.lookup T id = some d → TypeEnv.lookup U id = some d

/-- The empty input is a sub-table of anything — the degenerate
instance under which this module's theorems collapse to the shipped
ones. -/
theorem SubTable.nil (U : TypeEnv) : SubTable [] U := by
  intro id d h
  simp [TypeEnv.lookup] at h

/-- Table equality is the everyday discharge at a pinned program. -/
theorem SubTable.of_eq {T U : TypeEnv} (h : U = T) : SubTable T U := by
  intro id d hl
  rw [h]
  exact hl

/-! ## The mirror normalizer at an input table -/

/-- Mirror of `emptyStructAssignable` (payloads never read). -/
def emptyStructAssignable' (actual name : TypeId)
    (fields : Array FieldDef) (fieldsValue : Array (String × Value D)) : Bool :=
  (actual.key == "struct{}" || name.key == "struct{}") &&
    fields.isEmpty && fieldsValue.isEmpty

/-- Mirror of `normalizeFieldsWith` (field names concrete; payloads
through the parameterized element normalizer). -/
def normalizeFieldsWith' (f : Ty → Value D → M (Value D)) :
    List FieldDef → List (String × Value D) →
    M (Array (String × Value D))
  | field :: fieldRest, (actualField, value) :: valueRest => do
      if actualField != field.name then quit .q11Internal
      else do
        let head ← f field.typ value
        let tail ← normalizeFieldsWith' f fieldRest valueRest
        .ok (#[(field.name, head)] ++ tail)
  | _, _ => .ok #[]

/-- Mirror of `normalizeStructValueWith`. -/
def normalizeStructValueWith' (f : Ty → Value D → M (Value D))
    (name : TypeId) (fields : Array FieldDef) : Value D → M (Value D)
  | .struct actual fieldsValue => do
      if actual != name then
        if emptyStructAssignable' actual name fields fieldsValue then
          .ok (.struct name #[])
        else quit .q11Internal
      else if fieldsValue.size != fields.size then quit .q11Internal
      else do
        let out ← normalizeFieldsWith' f fields.toList fieldsValue.toList
        .ok (.struct name out)
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- The mirror normalizer WITH the defined-type arm, against the input
table `T`. Non-defined arms are the shipped
`normalizeValueForTyFuel'`'s, verbatim; the `.defined` arm mirrors the
machine's dispatch, quitting where the machine diagnoses
(`interfaceDef`/`unsupported`) or the input table has no answer. -/
def normalizeValueForTyFuelT (T : TypeEnv) : Nat → Ty → Value D → M (Value D)
  | 0, _, _ => quit .q11Internal
  | _ + 1, .int kind, .int value _ => .ok (.int (D.norm kind value) kind)
  | _ + 1, .int _, .atom _ => quit .q10Atom
  | _ + 1, .int _, _ => quit .q11Internal
  | _ + 1, .float kind, .float bits k =>
      if k == kind then .ok (.float (kind.normalizeBits bits) kind)
      else quit .q11Internal
  | _ + 1, .float _, .atom _ => quit .q10Atom
  | _ + 1, .float _, _ => quit .q11Internal
  | fuel + 1, .array length elem, .array values => do
      if values.size != length then quit .q11Internal
      else
        Value.array <$>
          normalizeListWith' (normalizeValueForTyFuelT T fuel elem) values.toList
  | _ + 1, .array _ _, .atom _ => quit .q10Atom
  | _ + 1, .array _ _, _ => quit .q11Internal
  | _ + 1, .interface _, value => .ok value
  | _ + 1, .funcType _ _ _, .funcVal fid captured => .ok (.funcVal fid captured)
  | _ + 1, .funcType _ _ _, .nil => .ok .nil
  | _ + 1, .funcType _ _ _, .atom _ => quit .q10Atom
  | _ + 1, .funcType _ _ _, _ => quit .q11Internal
  | _ + 1, .chan _ _, .chan cv => .ok (.chan cv)
  | _ + 1, .chan _ _, .nil => .ok (.chan { base := none })
  | _ + 1, .chan _ _, .atom _ => quit .q10Atom
  | _ + 1, .chan _ _, _ => quit .q11Internal
  | _ + 1, .sync kind, .syncData p =>
      if p.kind == kind then .ok (.syncData p) else quit .q11Internal
  | _ + 1, .sync _, .atom _ => quit .q10Atom
  | _ + 1, .sync _, _ => quit .q11Internal
  | fuel + 1, .defined name, value =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => normalizeValueForTyFuelT T fuel target value
       | some (.defined target) => normalizeValueForTyFuelT T fuel target value
       | some (.struct fields) =>
           normalizeStructValueWith' (normalizeValueForTyFuelT T fuel)
             name fields value
       | some (.unsupported _) => quit .q11Internal
       | some (.interfaceDef _) => quit .q11Internal
       | none => quit .q4Program)
  | _ + 1, .unsupported _, _ => quit .q11Internal
  | _ + 1, _, value => .ok value

def normalizeValueForTyT (T : TypeEnv) (ty : Ty) (value : Value D) :
    M (Value D) :=
  normalizeValueForTyFuelT T typeResolutionFuel ty value

/-! ### Struct literals at the input table (slice 4: the Q4-normalize
family's `buildStructValue` member — hit by `struct{}{}` in `Intn`'s
map build and the `Progress{...}` literal in `reset$lit0`). -/

def buildStructFieldsT (T : TypeEnv) :
    List FieldDef → List (Value D) → M (Array (String × Value D))
  | field :: fieldRest, value :: valueRest => do
      let head ← normalizeValueForTyT T field.typ value
      let tail ← buildStructFieldsT T fieldRest valueRest
      .ok (#[(field.name, head)] ++ tail)
  | _, _ => .ok #[]

def buildStructValueFuelT (T : TypeEnv) :
    Nat → Ty → Array (Value D) → M (Value D)
  | fuel + 1, .defined name, args =>
      (match TypeEnv.lookup T name with
       | some (.struct fields) =>
           if fields.size != args.size then quit .q11Internal
           else do
             let fs ← buildStructFieldsT T fields.toList args.toList
             .ok (.struct name fs)
       | some (.alias target) => buildStructValueFuelT T fuel target args
       | some _ => quit .q11Internal
       | none => quit .q4Program)
  | 0, .defined _, _ => quit .q11Internal
  | _, _, _ => quit .q11Internal

def buildStructValueT (T : TypeEnv) (ty : Ty) (args : Array (Value D)) :
    M (Value D) :=
  buildStructValueFuelT T typeResolutionFuel ty args

/-! ## The store chain over it -/

/-- `storeLoc'` with the table-aware normalizer (untyped cells still
coerce via the shipped `coerceStoredValue'`). -/
def storeLocT (T : TypeEnv) (s : State D) : Loc → Value D → M (State D)
  | loc@(.base _), value => do
      match Heap.lookup s.heap loc with
      | some (.mk declaredTy oldValue) => do
          let value ←
            match declaredTy with
            | some ty => normalizeValueForTyT T ty value
            | none => coerceStoredValue' oldValue value
          .ok { s with heap := Heap.set s.heap loc (.mk declaredTy value) }
      | some (.atom _) => quit .q10Atom
      | none =>
          .ok { s with heap := Heap.set s.heap loc (.mk none value) }
  | .field base typeId fieldName, value => do
      match ← loadLoc' s base with
      | .struct actualType fields =>
          if actualType != typeId then quit .q11Internal
          else do
            let updated ← StructFields.set' fields fieldName value
            storeLocT T s base (.struct actualType updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .index base index, value => do
      match ← loadLoc' s base with
      | .array values => do
          let updated ← arraySet' values index value
          storeLocT T s base (.array updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal

/-- `storeTarget'` with the table-aware store (the `mapElem` arm stays
the shipped one — map assigns at defined key/value types remain
quits, the recorded class-1 scope line). -/
def storeTargetT (T : TypeEnv) (s : State D) (r : TargetRef D)
    (v : Value D) : M (State D) := do
  match r with
  | .chain anchor idxs steps => do
      let resolved ← resolveChain' s anchor steps idxs
      let loc ← resolved.asLoc
      storeLocT T s loc v
  | .mapElem b k kt vt => mapAssignValue' s kt vt b k v

/-- `mapAssignValue'` at the input table (slice 4: map assigns whose
KEY/VALUE types are defined — `map[int]struct{}` in `Intn`). -/
def mapAssignValueT (T : TypeEnv) (s : State D) (keyTy valueTy : Ty)
    (baseV keyV valueV : Value D) : M (State D) := do
  let map ← baseV.asMap
  let key ← normalizeValueForTyT T keyTy keyV
  let value ← normalizeValueForTyT T valueTy valueV
  match ← mapEntries' s map with
  | none => quit .q6Panic
  | some (baseLoc, entries) =>
      let entries ←
        match ← mapEntryIndex?' keyTy entries key with
        | some i => pure (entries.set! i (key, value))
        | none => pure (entries.push (key, value))
      storeLocT T s baseLoc (.mapData entries)


/-! ### A4-U3 residuals (same lever, consumed on demand exactly as the
design's §"Residual Q4-family members" prescribes; both found by the
becomeFollower populated-fixture window probe):

- `Expr.defaultValue` at a DEFINED type — hit by `reset$lit0`'s
  Progress literal (`defaultValue tracker.StateType`).
- `eqCmp`/`neqCmp` at INTERFACE (nil arms) and at DEFINED types
  (alias/defined resolution) — hit by `raftLog.lastIndex`'s
  `err != nil`. Box-vs-box interface equality and struct equality at
  defined types stay quits (no census consumer; recorded scope line). -/

def defaultFieldsWithT (f : Ty → M (Value D)) :
    List FieldDef → M (Array (String × Value D))
  | field :: rest => do
      let head ← f field.typ
      let tail ← defaultFieldsWithT f rest
      .ok (#[(field.name, head)] ++ tail)
  | [] => .ok #[]

/-- The mirror default-value former WITH the defined-type arm at the
input table (struct defaults fieldwise, alias/defined re-target);
every non-defined type delegates to the shipped `defaultValueFuel'`. -/
def defaultValueFuelT (T : TypeEnv) : Nat → Ty → M (Value D)
  | 0, _ => quit .q11Internal
  | fuel + 1, .defined name =>
      (match TypeEnv.lookup T name with
       | some (.struct fields) =>
           Value.struct name <$>
             defaultFieldsWithT (defaultValueFuelT T fuel) fields.toList
       | some (.alias target) => defaultValueFuelT T fuel target
       | some (.defined target) => defaultValueFuelT T fuel target
       | some (.unsupported _) => quit .q11Internal
       | some (.interfaceDef _) => quit .q11Internal
       | none => quit .q4Program)
  | fuel + 1, ty => defaultValueFuel' (fuel + 1) ty

def defaultValueT (T : TypeEnv) (ty : Ty) : M (Value D) :=
  defaultValueFuelT T typeResolutionFuel ty

/-- The mirror decided equality WITH the interface NIL arms and the
defined-type resolution arm at the input table. Box-vs-box interface
equality (needs `tyUncomparable`) and struct equality at defined types
stay quits — no census consumer. Non-defined, non-interface types
delegate to the shipped `valueEqBFuel'`. -/
def valueEqBFuelT (T : TypeEnv) : Nat → Ty → Value D → Value D → M Bool
  | 0, _, _, _ => quit .q11Internal
  | _ + 1, .interface _, .nil, .nil => .ok true
  | _ + 1, .interface _, .nil, .interface _ _ => .ok false
  | _ + 1, .interface _, .interface _ _, .nil => .ok false
  | _ + 1, .interface _, _, _ => quit .q4Program
  | fuel + 1, .defined name, l, r =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => valueEqBFuelT T fuel target l r
       | some (.defined target) => valueEqBFuelT T fuel target l r
       | some _ => quit .q4Program
       | none => quit .q4Program)
  | fuel + 1, ty, l, r => valueEqBFuel' (fuel + 1) ty l r

/-- `valueEqR'` over the table-conditioned decided family. -/
def valueEqRT' (T : TypeEnv) (ty : Ty) (l r : Value D) : M D.BoolR :=
  match ty, l, r with
  | .int _, .int lv _, .int rv _ => .ok (D.eqI lv rv)
  | ty, l, r => do
      let b ← valueEqBFuelT T typeResolutionFuel ty l r
      .ok (D.litB b)

/-! ## Slice 2 — sequential sync-ops (design §3, class 3)

The pilot census (arc log): the handler fragment consumes exactly
`SyncStmtOp.lock`/`unlock` on plain `sync.Mutex` cells (lockedRand,
MemoryStorage) — no Once, no RWMutex on the path; the deferred-Unlock
DISCHARGE at frame exit additionally needs class 2 (a deferred call is
a frame entry). Only the consumed ops proceed; the rest of the family
stays Q7 (wider coverage is a later strengthening). The sync apply
consumes no choices (StepFn's arm), so the `ch`-unchanged theorem form
is untouched. Blocked acquisitions mirror the machine's
`.blockedSync` configuration faithfully (a dead end for a window, but
sound). -/

/-- Mirror of `syncCell`. -/
def syncCell' (s : State D) (loc : Loc) : M SyncPrim := do
  match ← loadLoc' s loc with
  | .syncData p => .ok p
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- Mirror of `applySyncOp`, the census subset: `lock`/`unlock` on a
mutex. Failure paths (unlock of unlocked = the machine's `.fatal`)
quit Q6; every other op quits Q7 as before. -/
def applySyncOp' (T : TypeEnv) (s : State D) (op : SyncOp) (vs : List (Value D))
    (env : LocalEnv) (k : Cont D) : M (Config D × State D) := do
  match op, vs with
  | .lock, [av] => do
      let loc ← av.asLoc
      match ← syncCell' s loc with
      | .mutex locked =>
          if locked then .ok (.blockedSync .lock loc env k, s)
          else do
            let s' ← storeLocT T s loc (.syncData (.mutex true))
            .ok (.opDone .postOp (.next k), s')
      | _ => quit .q11Internal
  | .unlock, [av] => do
      let loc ← av.asLoc
      match ← syncCell' s loc with
      | .mutex locked =>
          if locked then do
            let s' ← storeLocT T s loc (.syncData (.mutex false))
            .ok (.opDone .postOp (.next k), s')
          else quit .q6Panic
      | _ => quit .q11Internal
  | _, _ => quit .q7Concurrency

/-! ## The extended step and window driver -/

/-! ## U13: the comma-ok type assertion at the input table (the
becomeLeader census's `proto.Clone(es[i]).(*pb.Entry)` — the U3
consume-on-demand class: the `Stmt.typeAssert` spine entry + the
`rhsK` finish, mirrored over `typeAssertValueT`). Scoping (fail
closed, no census consumer): interface-TARGET asserts quit
(`dynamicImplementsInterface` needs method sets, unmirrored);
`map`/`chan`/`funcType` canonicalization arms quit. -/

/-- Mirror of `resolveDefinedAliasesFuel` at the input table: a failed
lookup QUITS (the machine's answer is unknowable from `T`); a
non-alias hit keeps the name (SubTable transfers the same def to the
run state). Fuel exhaustion mirrors the machine's safe fixed point. -/
def resolveDefinedAliasesFuelT (T : TypeEnv) : Nat → Ty → M Ty
  | fuel + 1, .defined name =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => resolveDefinedAliasesFuelT T fuel target
       | some _ => .ok (.defined name)
       | none => quit .q4Program)
  | _ + 1, other => .ok other
  | 0, ty => .ok ty

/-- Mirror of `canonicalTyFuel` at the input table (defined/pointer/
slice/array + the base identity arms; `map`/`chan`/`funcType` quit —
fail closed until a consumer arrives). Exhaustion mirrors the
machine's `.unsupported` markers verbatim. -/
def canonicalTyFuelT (T : TypeEnv) : Nat → Ty → M Ty
  | fuel + 1, .defined name =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => canonicalTyFuelT T fuel target
       | some _ => .ok (.defined name)
       | none => quit .q4Program)
  | fuel + 1, .pointer elem => do
      .ok (.pointer (← canonicalTyFuelT T fuel elem))
  | fuel + 1, .slice elem => do
      .ok (.slice (← canonicalTyFuelT T fuel elem))
  | fuel + 1, .array n elem => do
      .ok (.array n (← canonicalTyFuelT T fuel elem))
  | _ + 1, .map _ _ => quit .q4Program
  | _ + 1, .chan _ _ => quit .q4Program
  | _ + 1, .funcType _ _ _ => quit .q4Program
  | 0, .defined _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .pointer _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .slice _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .array _ _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .map _ _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .chan _ _ => .ok (.unsupported "canonical type: type nesting too deep")
  | 0, .funcType _ _ _ => .ok (.unsupported "canonical type: type nesting too deep")
  | _, other => .ok other

/-- Mirror of `typeAssertValue` (the comma-ok outcome: value + a
CONCRETE Bool — the assert decision is control-flow). Interface
targets and non-interface operands quit; atoms quit `q10Atom`. -/
def typeAssertValueT (T : TypeEnv) (value : Value D) (targetTy : Ty) :
    M (Value D × Bool) := do
  let failed ← defaultValueT T targetTy
  match value with
  | .nil => .ok (failed, false)
  | .interface dynTy inner => do
      match ← resolveDefinedAliasesFuelT T typeResolutionFuel targetTy with
      | .interface _ => quit .q4Program
      | _ =>
          if dynTy == (← canonicalTyFuelT T typeResolutionFuel targetTy) then
            .ok (inner, true)
          else
            .ok (failed, false)
  | .atom _ => quit .q10Atom
  | _ => quit .q4Program

/-- Mirror of `convertValueToTyFuel`'s `.defined` arm at the input
table (alias/defined re-target ONLY — struct value-conversion has no
census consumer and quits, fail closed); every other target type
delegates to the shipped `convertValueToTyFuel'`. Diagnosed
conversions quit where the machine diagnoses. -/
def convertValueToTyFuelT (T : TypeEnv) : Nat → Ty → Value D → M (Value D)
  | fuel + 1, .defined name, value =>
      (match TypeEnv.lookup T name with
       | some (.alias target) => convertValueToTyFuelT T fuel target value
       | some (.defined target) => convertValueToTyFuelT T fuel target value
       | some (.struct _) => quit .q4Program
       | some (.unsupported _) => quit .q4Program
       | some (.interfaceDef _) => quit .q4Program
       | none => quit .q4Program)
  | fuel, ty, value => convertValueToTyFuel' fuel ty value

/-- The extended mirror step: the store arm through the table-aware
chain, every other configuration DELEGATED verbatim to the shipped
`stepFn'`. At `T = []` this is behaviorally the shipped step. -/
def stepFnT (T : TypeEnv) (s : State D) (c : Config D) :
    M (Config D × State D) :=
  match c with
  | .next (.storeK refs vals body env k') =>
      (match refs, vals with
       | r :: rs, val :: vrest => do
          let s' ← storeTargetT T s r val
          .ok (.next (.storeK rs vrest body env k'), s')
       | [], [] => .ok (.exec body env k', s)
       | _, _ => quit .q11Internal)
  -- slice 2: sync-statement entry (the machine's operand-plan arm)
  | .exec (.syncStmt op args targets) env k =>
      (match syncPlan (.syncStmt op args targets) with
       | some (sop, e :: rest) =>
           .ok (.evalE e env (.syncStK sop [] rest env k), s)
       | some (_, []) => quit .q11Internal
       | none => quit .q11Internal)
  -- U10: `Stmt.initialization` at the input table (the machine's
  -- `defaultValue` call resolved through `defaultValueT` — the
  -- Q4-default family's STATEMENT member; first exercised instance:
  -- the `raftpb.Message` temp in `send` on the handleHeartbeat path.
  -- Non-defined types take the same route `defaultValueFuelT`
  -- delegates for, so this arm agrees with the shipped `stepFn'`
  -- wherever that one stepped).
  -- U13: the comma-ok type assertion, statement spine (the machine's
  -- `targetsPlan` arm mirrored verbatim; internal/unsupported plan
  -- outcomes quit where the machine diagnoses).
  | .exec (.typeAssert t okT expr targetTy) env k =>
      (match targetsPlan [t, okT] with
       | some ((sh, e :: ops) :: rest) =>
           .ok (.evalE e env
             (.tgtOpK sh [] ops [] rest (.typeAssert targetTy)
               [expr] [] (.seqn #[]) env k), s)
       | some _ => quit .q11Internal
       | none => quit .q4Program)
  -- U13: the comma-ok type assertion, rhsK finish (`done = []` always:
  -- the assert carries exactly one RHS expression).
  | .retV v (.rhsK (.typeAssert tty) refs [] [] body env k') => do
      let r ← typeAssertValueT T v tty
      .ok (.next (.storeK refs [r.1, .bool (D.litB r.2)] body env k'), s)
  -- U13: the single-value type-assert EXPRESSION (`x.(T)` — the
  -- machine's strict-op arm; a FAILED assert panics, which stays a
  -- quit: no census consumer asserts falsely).
  | .retV v (.strictK (.typeAssert tty sty) [] [] env k') => do
      let r ← typeAssertValueT T v tty
      if r.2 then .ok (.retV r.1 k', s)
      else quit .q6Panic
  -- U13: conversion to a DEFINED type (`raft.entryPayloadSize` on the
  -- becomeLeader path — the Q4-defined convert member).
  | .retV v (.strictK (.convert (.defined name)) [] [] env k') => do
      let out ← convertValueToTyFuelT T typeResolutionFuel (.defined name) v
      .ok (.retV out k', s)
  | .exec (.initialization p) env k =>
      (match k with
       | .seq rest kenv k' =>
          if kenv = env then do
            let v ← defaultValueT T p.typ
            let (loc, s') := s.alloc v (some p.typ)
            .ok (.next (.seq rest (env.declare p.id loc) k'), s')
          else quit .q11Internal
       | _ => quit .q11Internal)
  -- slice 2: sync operand collection + the apply
  | .retV v (.syncStK op done pending env k') =>
      (match pending with
       | e :: rest =>
           .ok (.evalE e env (.syncStK op (v :: done) rest env k'), s)
       | [] => applySyncOp' T s op (v :: done).reverse env k')
  -- slice 2: the sequential completion-marker strip
  | .opDone _ inner => .ok (inner, s)
  -- slice 4: struct literals at the input table (the Q4-normalize
  -- family's buildStructValue member; nullary entry + drained apply)
  | .evalE (.structLit ty elems) env k =>
      (match elems.toList with
       | e₁ :: rest =>
           .ok (.evalE e₁ env (.strictK (.structLit ty) [] rest env k), s)
       | [] => do
           let v ← buildStructValueT T ty #[]
           .ok (.retV v k, s))
  | .retV v (.strictK (.structLit ty) done [] env k') => do
      let out ← buildStructValueT T ty ((v :: done).reverse.toArray)
      .ok (.retV out k', s)
  -- slice 4: map assign at the input table (defined key/value types)
  | .retV v (.stmtOpK (.mapAssign kt vt) nt done [] env k') =>
      (match (v :: done).reverse with
       | [baseV, keyV, valueV] => do
          let s' ← mapAssignValueT T s kt vt baseV keyV valueV
          .ok (.next k', s')
       | _ => quit .q11Internal)
  -- U3-a: `Expr.defaultValue` at the input table (nullary strict op —
  -- the machine's `strictPlan` sends it straight to the apply)
  | .evalE (.defaultValue ty) env k => do
      let v ← defaultValueT T ty
      .ok (.retV v k, s)
  -- U3-a: eqCmp/neqCmp completions at the input table (interface-nil
  -- + defined-resolution compares)
  | .retV v (.strictK (.eqCmp ty) done [] env k') =>
      (match (v :: done).reverse with
       | [l, r] => do
          let b ← valueEqRT' T ty l r
          .ok (.retV (.bool b) k', s)
       | _ => quit .q11Internal)
  | .retV v (.strictK (.neqCmp ty) done [] env k') =>
      (match (v :: done).reverse with
       | [l, r] => do
          let b ← valueEqRT' T ty l r
          .ok (.retV (.bool (D.notB b)) k', s)
       | _ => quit .q11Internal)
  | c => stepFn' s c

/-- The extended step at the symbolic domain. -/
def stepFnST (T : TypeEnv) (S : SymState) (C : SymConfig) :
    M (SymConfig × SymState) :=
  stepFnT T S C

/-- The extended window driver (shape identical to `symEvalWindow`). -/
def symEvalWindowT (T : TypeEnv) :
    Nat → SymState → SymConfig → Nat × SymState × SymConfig
  | 0, S, C => (0, S, C)
  | budget + 1, S, C =>
      match stepFnST T S C with
      | .error _ => (0, S, C)
      | .ok (C', S') =>
          let (n, S'', C'') := symEvalWindowT T budget S' C'
          (n + 1, S'', C'')

/-! ## Soundness (the drift layer, table-conditioned) -/

/-- Field-walk commutation, parameterized like
`normalizeListWith_conc`. -/
theorem normalizeFieldsWith_conc {f : Ty → Value D → M (Value D)}
    {g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v out, f ty v = .ok out → g ty (concV I v) = .ok (concV I out)) :
    ∀ {fds : List FieldDef} {fvs : List (String × Value D)}
      {out : Array (String × Value D)},
      normalizeFieldsWith' f fds fvs = .ok out →
      normalizeFieldsWith g fds (fvs.map (fun p => (p.1, concV I p.2)))
        = .ok (out.map (fun p => (p.1, concV I p.2))) := by
  intro fds
  induction fds with
  | nil =>
      intro fvs out h
      cases fvs with
      | nil =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
      | cons a rest =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
  | cons fd fdRest ih =>
      intro fvs out h
      cases fvs with
      | nil =>
          simp only [normalizeFieldsWith'] at h
          cases h
          simp [normalizeFieldsWith]
      | cons fv rest =>
          obtain ⟨actualField, value⟩ := fv
          simp only [normalizeFieldsWith', quit] at h
          by_cases hname : (actualField != fd.name) = true
          · rw [if_pos hname] at h
            cases h
          · rw [if_neg hname] at h
            obtain ⟨head, hhead, h2⟩ := bind_eq_ok.mp h
            obtain ⟨tail, htail, h3⟩ := bind_eq_ok.mp h2
            cases h3
            simp only [List.map_cons, normalizeFieldsWith]
            rw [if_neg hname]
            simp only [Bind.bind, Except.bind, pure, Except.pure]
            rw [hfg _ _ _ hhead, ih htail]
            simp [Array.map_append]

/-- The `.defined`-arm transport, factored out so the master induction
can close all value shapes uniformly. -/
private theorem normalizeFuelT_defined_conc (_hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) (fuel : Nat)
    (ih : ∀ (ty : Ty) (v out : Value D),
      normalizeValueForTyFuelT T fuel ty v = .ok out →
      normalizeValueForTyFuel fuel σ ty (concV I v) = .ok (concV I out))
    {name : TypeId} {v out : Value D}
    (h : (match TypeEnv.lookup T name with
          | some (.alias target) => normalizeValueForTyFuelT T fuel target v
          | some (.defined target) => normalizeValueForTyFuelT T fuel target v
          | some (.struct fields) =>
              normalizeStructValueWith' (normalizeValueForTyFuelT T fuel)
                name fields v
          | some (.unsupported _) => quit .q11Internal
          | some (.interfaceDef _) => quit .q11Internal
          | none => quit .q4Program) = .ok out) :
    normalizeValueForTyFuel (fuel + 1) σ (.defined name) (concV I v)
      = .ok (concV I out) := by
  revert h
  rcases hlk : TypeEnv.lookup T name with _ | td
  · intro h
    simp only [quit] at h
    cases h
  · intro h
    have hσlk := hsub name td hlk
    cases td with
    | alias target =>
        simp only [normalizeValueForTyFuel, hσlk]
        exact ih _ _ _ h
    | defined target =>
        simp only [normalizeValueForTyFuel, hσlk]
        exact ih _ _ _ h
    | struct fields =>
        simp only [normalizeValueForTyFuel, hσlk]
        revert h
        cases v
        case struct actual fieldsValue =>
            intro h
            simp only [normalizeStructValueWith', quit] at h
            by_cases hne : (actual != name) = true
            · rw [if_pos hne] at h
              by_cases hemp : emptyStructAssignable' actual name fields
                  fieldsValue = true
              · rw [if_pos hemp] at h
                cases h
                simp only [concV_struct, normalizeStructValueWith]
                rw [if_pos hne]
                have hemp2 : emptyStructAssignable actual name fields
                    (fieldsValue.map (fun p => (p.1, concV I p.2))) = true := by
                  simp only [emptyStructAssignable',
                    Bool.and_eq_true] at hemp
                  have hfv : fieldsValue = #[] := by
                    simpa using hemp.2
                  subst hfv
                  simp [emptyStructAssignable, hemp.1.1, hemp.1.2]
                rw [if_pos hemp2]
                simp
              · rw [if_neg hemp] at h
                cases h
            · rw [if_neg hne] at h
              by_cases hsz : (fieldsValue.size != fields.size) = true
              · rw [if_pos hsz] at h
                cases h
              · rw [if_neg hsz] at h
                obtain ⟨out2, hout, h2⟩ := bind_eq_ok.mp h
                cases h2
                simp only [concV_struct, normalizeStructValueWith]
                rw [if_neg hne]
                rw [if_neg (by simpa using hsz)]
                have hf := normalizeFieldsWith_conc (I := I)
                  (g := normalizeValueForTyFuel fuel σ)
                  (fun ty v out hv => ih ty v out hv) hout
                simp only [Array.toList_map] at hf ⊢
                rw [hf]
                simp [Functor.map, Except.map]
        case atom a =>
            intro h
            simp only [normalizeStructValueWith', quit] at h
            cases h
        all_goals
          intro h
          simp only [normalizeStructValueWith', quit] at h
          cases h
    | unsupported f =>
        simp only [quit] at h
        cases h
    | interfaceDef sigs =>
        simp only [quit] at h
        cases h

/-- THE TABLE-CONDITIONED NORMALIZER COMMUTATION: a successful mirror
normalization at input table `T` transports to the machine at any
state whose types extend `T`. Non-defined arms replay the shipped
`normalizeFuel_conc`'s cases; the `.defined` arm rides `hsub`. -/
theorem normalizeFuelT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) (v out : Value D),
      normalizeValueForTyFuelT T fuel ty v = .ok out →
      normalizeValueForTyFuel fuel σ ty (concV I v) = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v out h
      simp only [normalizeValueForTyFuelT, quit] at h
      cases h
  | succ fuel ih =>
      intro ty v out h
      cases ty <;> cases v <;>
        simp only [normalizeValueForTyFuelT, quit] at h <;>
        first
          | (cases h; done)
          | (cases h; simp [normalizeValueForTyFuel]; done)
          | skip
      all_goals try (cases h; done)
      case succ.int.int =>
        rename_i kind payload kind1
        cases h
        simp [normalizeValueForTyFuel, hI.norm]
      case succ.float.float =>
        rename_i kind bits k
        by_cases hk : (k == kind) = true
        · rw [if_pos hk] at h
          cases h
          simp only [concV_float, normalizeValueForTyFuel]
          rw [if_pos hk]
          rfl
        · rw [if_neg hk] at h
          cases h
      case succ.array.array =>
        rename_i length elem values
        by_cases hsz : (values.size != length) = true
        · rw [if_pos hsz] at h
          cases h
        · rw [if_neg hsz] at h
          rcases hok : normalizeListWith' (normalizeValueForTyFuelT T fuel elem)
              values.toList with _ | arr
          · rw [hok] at h
            exact absurd h (by simp [Functor.map, Except.map])
          · rw [hok] at h
            simp only [Functor.map, Except.map] at h
            cases h
            have := normalizeListWith_conc (fun v out hv => ih elem v out hv)
              values.toList arr hok
            simp only [concV_array, normalizeValueForTyFuel]
            rw [if_neg (by simp_all)]
            simp only [Array.toList_map] at this ⊢
            rw [this]
            simp [Functor.map, Except.map]
      case succ.sync.syncData =>
        rename_i kind p
        by_cases hp : (p.kind == kind) = true
        · rw [if_pos hp] at h
          cases h
          simp only [concV_syncData, normalizeValueForTyFuel]
          rw [if_pos hp]
          rfl
        · rw [if_neg hp] at h
          cases h
      all_goals exact normalizeFuelT_defined_conc hI σ hsub fuel ih h

theorem normalizeT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {ty : Ty} {v out : Value D}
    (h : normalizeValueForTyT T ty v = .ok out) :
    normalizeValueForTy σ ty (concV I v) = .ok (concV I out) := by
  simp only [normalizeValueForTy]
  exact normalizeFuelT_conc hI σ hsub _ ty v out h

theorem buildStructFieldsT_conc (hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) :
    ∀ {fds : List FieldDef} {vs : List (Value D)}
      {out : Array (String × Value D)},
      buildStructFieldsT T fds vs = .ok out →
      buildStructFields σ fds (vs.map (concV I))
        = .ok (out.map (fun p => (p.1, concV I p.2))) := by
  intro fds
  induction fds with
  | nil =>
      intro vs out h
      cases vs with
      | nil =>
          simp only [buildStructFieldsT] at h
          cases h
          simp [buildStructFields]
      | cons a rest =>
          simp only [buildStructFieldsT] at h
          cases h
          simp [buildStructFields]
  | cons fd fdRest ih =>
      intro vs out h
      cases vs with
      | nil =>
          simp only [buildStructFieldsT] at h
          cases h
          simp [buildStructFields]
      | cons v rest =>
          simp only [buildStructFieldsT] at h
          obtain ⟨head, hhead, h2⟩ := bind_eq_ok.mp h
          obtain ⟨tail, htail, h3⟩ := bind_eq_ok.mp h2
          cases h3
          simp only [List.map_cons, buildStructFields, Bind.bind,
            Except.bind]
          rw [normalizeT_conc hI σ hsub hhead, ih htail]
          simp [pure, Except.pure, Array.map_append]

theorem buildStructValueFuelT_conc (hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) (args : Array (Value D)) {out : Value D},
      buildStructValueFuelT T fuel ty args = .ok out →
      buildStructValueFuel fuel σ ty (args.map (concV I))
        = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty args out h
      cases ty <;> simp only [buildStructValueFuelT, quit] at h <;> cases h
  | succ fuel ih =>
      intro ty args out h
      cases ty <;> simp only [buildStructValueFuelT, quit] at h <;>
        try (cases h; done)
      case defined name =>
        revert h
        rcases hlk : TypeEnv.lookup T name with _ | td
        · intro h
          simp only [quit] at h
          cases h
        · intro h
          have hσlk := hsub name td hlk
          cases td <;> simp only [quit] at h <;> try (cases h; done)
          case struct fields =>
            by_cases hsz : (fields.size != args.size) = true
            · rw [if_pos hsz] at h
              simp [quit] at h
            · rw [if_neg hsz] at h
              obtain ⟨fs, hfs, h2⟩ := bind_eq_ok.mp h
              cases h2
              simp only [buildStructValueFuel, hσlk]
              rw [if_neg (by simpa [Array.size_map] using hsz)]
              have hf := buildStructFieldsT_conc (I := I) hI σ hsub hfs
              simp only [Array.toList_map] at hf ⊢
              rw [hf]
              simp [Functor.map, Except.map, concV_struct]
          case alias target =>
            simp only [buildStructValueFuel, hσlk]
            exact ih _ _ h

theorem buildStructValueT_conc (hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) {ty : Ty}
    {args : Array (Value D)} {out : Value D}
    (h : buildStructValueT T ty args = .ok out) :
    buildStructValue σ ty (args.map (concV I)) = .ok (concV I out) := by
  simp only [buildStructValue]
  exact buildStructValueFuelT_conc hI σ hsub _ ty args h

set_option linter.unusedSimpArgs false in
/-- `storeLoc_conc`, table-conditioned (proof = the shipped one with
`normalizeT_conc` at the typed-cell arm). -/
theorem storeLocT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D} :
    ∀ {loc : Loc} {v : Value D} {s' : State D}, storeLocT T s loc v = .ok s' →
      storeLoc (concS I σ s) loc (concV I v) = .ok (concS I σ s') := by
  intro loc
  induction loc with
  | base a =>
      intro v s' h
      simp only [storeLocT, quit] at h
      rcases hq : Heap.lookup s.heap (.base a) with _ | cell
      · rw [hq] at h
        cases h
        simp only [storeLoc, concS]
        rw [lookup_conc, hq]
        simp only [Option.map]
        rw [show ({ value := concV I v } : GoCore.HeapCell)
              = concCell I (.mk none v) from rfl, set_conc]
        rfl
      · rw [hq] at h
        rcases cell with ⟨dty, oldv⟩ | ca
        case atom => cases h
        cases dty with
        | none =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            refine ⟨concV I nv, coerce_conc hI hnv, ?_⟩
            rw [show ({ declaredTy := none, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk none nv) from rfl,
              set_conc]
            rfl
        | some ty =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            have hsub' : SubTable T (concS I σ s).types := hsub
            refine ⟨concV I nv, normalizeT_conc hI (concS I σ s) hsub' hnv, ?_⟩
            rw [show ({ declaredTy := some ty, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk (some ty) nv) from rfl,
              set_conc]
            rfl
  | field base tid fname ih =>
      intro v s' h
      simp only [storeLocT, bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next actual fields =>
        simp only [concV_struct]
        by_cases hty : (actual != tid) = true
        · rw [if_pos hty] at h2
          cases h2
        · rw [if_neg hty] at h2
          have hty2 : ¬(actual != tid
              && !structTagCompatible (concS I σ s) actual tid) = true := by
            simp only [Bool.not_eq_true] at hty
            simp [hty]
          rw [if_neg hty2]
          simp only [bind_eq_ok] at h2
          obtain ⟨updated, hupd, h3⟩ := h2
          simp only [pure_bind, bind_eq_ok]
          refine ⟨_, structSet_conc hupd, ?_⟩
          have := ih h3
          simpa [concV_struct] using this
  | index base i ih =>
      intro v s' h
      simp only [storeLocT, bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next values =>
        simp only [concV_array]
        simp only [bind_eq_ok] at h2
        obtain ⟨updated, hupd, h3⟩ := h2
        simp only [bind_eq_ok]
        refine ⟨_, arraySet_conc hI hupd, ?_⟩
        have := ih h3
        simpa using this

/-- `storeTarget_conc`, table-conditioned. -/
theorem storeTargetT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D}
    {r : TargetRef D} {v : Value D} {s' : State D}
    (h : storeTargetT T s r v = .ok s') :
    storeTarget (concS I σ s) (concRef I r) (concV I v)
      = .ok (concS I σ s') := by
  cases r with
  | chain anchor idxs steps =>
      simp only [storeTargetT] at h
      obtain ⟨resolved, hres, h⟩ := bind_eq_ok.mp h
      obtain ⟨loc, hloc, h⟩ := bind_eq_ok.mp h
      simp only [storeTarget, concRef]
      refine bind_eq_ok.mpr ⟨concV I resolved,
        resolveChain_conc hI σ steps anchor idxs hres, ?_⟩
      refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
      exact storeLocT_conc hI σ hsub h
  | mapElem b k kt vt =>
      simp only [storeTargetT] at h
      simpa [storeTarget, concRef] using mapAssignValue_conc hI σ h

theorem mapAssignValueT_conc (hI : I.Sound) (σ : ExecState)
    {T : TypeEnv} (hsub : SubTable T σ.types) {s : State D}
    {keyTy valueTy : Ty} {baseV keyV valueV : Value D} {s' : State D}
    (h : mapAssignValueT T s keyTy valueTy baseV keyV valueV = .ok s') :
    mapAssignValue (concS I σ s) keyTy valueTy (concV I baseV)
      (concV I keyV) (concV I valueV) = .ok (concS I σ s') := by
  unfold mapAssignValueT at h
  unfold mapAssignValue
  obtain ⟨map, hmap, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨map, asMap_conc hmap, ?_⟩
  obtain ⟨key, hkey, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨concV I key,
    normalizeT_conc hI (concS I σ s) hsub hkey, ?_⟩
  obtain ⟨value, hvalue, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨concV I value,
    normalizeT_conc hI (concS I σ s) hsub hvalue, ?_⟩
  obtain ⟨me, hme, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr
    ⟨me.map (fun p => (p.1, concEntries I p.2)), mapEntries_conc σ hme, ?_⟩
  rcases me with _ | ⟨baseLoc, entries⟩
  · cases h
  simp only [Option.map_some] at *
  obtain ⟨idx, hidx, h⟩ := bind_eq_ok.mp h
  refine bind_eq_ok.mpr ⟨idx, mapEntryIndex_conc hI (concS I σ s) hidx _, ?_⟩
  rcases idx with _ | i <;> simp only [] at h ⊢
  · obtain ⟨es, hes, h⟩ := bind_eq_ok.mp h
    have hesv : es = entries.push (key, value) := by
      simpa [pure, Except.pure, eq_comm] using hes
    subst hesv
    refine bind_eq_ok.mpr
      ⟨(concEntries I entries).push (concV I key, concV I value), rfl, ?_⟩
    have := storeLocT_conc hI σ hsub (loc := baseLoc)
      (v := .mapData (entries.push (key, value))) (s' := s') h
    simpa [concV_mapData, concEntries, Array.map_push] using this
  · obtain ⟨es, hes, h⟩ := bind_eq_ok.mp h
    have hesv : es = entries.set! i (key, value) := by
      simpa [pure, Except.pure, eq_comm] using hes
    subst hesv
    refine bind_eq_ok.mpr
      ⟨(concEntries I entries).set! i (concV I key, concV I value), rfl, ?_⟩
    have := storeLocT_conc hI σ hsub (loc := baseLoc)
      (v := .mapData (entries.set! i (key, value))) (s' := s') h
    simpa [concV_mapData, concEntries, Array.set!, map_setIfInBounds]
      using this


/-! ### U3-a transports -/

theorem defaultFieldsWithT_conc {f : Ty → M (Value D)}
    {g : Ty → Except GoError GoValue}
    (hfg : ∀ ty out, f ty = .ok out → g ty = .ok (concV I out)) :
    ∀ {fds : List FieldDef} {out : Array (String × Value D)},
      defaultFieldsWithT f fds = .ok out →
      defaultFieldsWith g fds = .ok (out.map (fun p => (p.1, concV I p.2))) := by
  intro fds
  induction fds with
  | nil =>
      intro out h
      simp only [defaultFieldsWithT] at h
      cases h
      simp [defaultFieldsWith]
  | cons fd rest ih =>
      intro out h
      simp only [defaultFieldsWithT] at h
      obtain ⟨head, hhead, h2⟩ := bind_eq_ok.mp h
      obtain ⟨tail, htail, h3⟩ := bind_eq_ok.mp h2
      cases h3
      simp only [defaultFieldsWith, Bind.bind, Except.bind]
      rw [hfg _ _ hhead, ih htail]
      simp [pure, Except.pure, Array.map_append]

/-- Default-value commutation at the input table. -/
theorem defaultValueFuelT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) {v : Value D},
      defaultValueFuelT T fuel ty = .ok v →
      defaultValueFuel fuel σ ty = .ok (concV I v) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v h
      simp only [defaultValueFuelT, quit] at h
      cases h
  | succ fuel ih =>
      intro ty v h
      cases ty <;>
        simp only [defaultValueFuelT] at h <;>
        try (exact defaultFuel_conc hI σ _ _ _ h)
      case defined name =>
        revert h
        rcases hlk : TypeEnv.lookup T name with _ | td
        · intro h
          simp [quit] at h
        · intro h
          have hσlk := hsub name td hlk
          cases td <;> simp only [quit] at h <;> try (cases h; done)
          case struct fields =>
            rcases hf : defaultFieldsWithT (defaultValueFuelT T fuel)
                fields.toList with e | out2
            · rw [hf] at h
              exact absurd h (by simp [Functor.map, Except.map])
            · rw [hf] at h
              simp only [Functor.map, Except.map] at h
              cases h
              have hg := defaultFieldsWithT_conc (I := I)
                (g := defaultValueFuel fuel σ) (fun ty out hv => ih ty hv) hf
              simp only [defaultValueFuel, hσlk, hg, Functor.map,
                Except.map, concV_struct]
          case alias target =>
            simp only [defaultValueFuel, hσlk]
            exact ih _ h
          case defined target =>
            simp only [defaultValueFuel, hσlk]
            exact ih _ h

/-- Decided-equality commutation at the input table (interface nil
arms + defined-type resolution; delegated arms via the shipped
`valueEqBFuel_conc`). -/
theorem valueEqBFuelT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) (l r : Value D) {b : Bool},
      valueEqBFuelT T fuel ty l r = .ok b →
      valueEqFuel fuel σ ty (concV I l) (concV I r) = .ok b := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty l r b h
      simp [valueEqBFuelT, quit] at h
  | succ fuel ih =>
      intro ty l r b h
      cases ty
      case interface iname =>
        cases l <;> cases r <;>
          simp only [valueEqBFuelT] at h <;>
          first
            | (simp [quit] at h; done)
            | (cases h; rfl)
            | (cases h; simp [valueEqFuel])
      case defined name =>
        simp only [valueEqBFuelT] at h
        revert h
        rcases hlk : TypeEnv.lookup T name with _ | td
        · intro h
          simp [quit] at h
        · intro h
          have hσlk := hsub name td hlk
          cases td <;> try (simp only [quit] at h; cases h; done)
          case alias target =>
            simp only [valueEqFuel, hσlk]
            exact ih _ _ _ h
          case defined target =>
            simp only [valueEqFuel, hσlk]
            exact ih _ _ _ h
      all_goals
        simp only [valueEqBFuelT] at h
        exact valueEqBFuel_conc hI σ _ _ _ _ h

/-- The value-producing equality at the input table. -/
theorem valueEqRT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {ty : Ty}
    {l r : Value D} {b : D.BoolR} (h : valueEqRT' T ty l r = .ok b) :
    valueEq σ ty (concV I l) (concV I r) = .ok (I.boolV b) := by
  unfold valueEqRT' at h
  split at h
  · cases h
    simp only [concV_int, valueEq]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [valueEqFuel, hI.eqI, pure, Except.pure]
  · simp only [bind_eq_ok] at h
    obtain ⟨b0, hb0, h2⟩ := h
    cases h2
    simp only [valueEq]
    rw [valueEqBFuelT_conc hI σ hsub _ _ _ _ hb0, hI.litB]

/-- Alias-resolution commutation at the input table. -/
theorem resolveDefinedAliasesFuelT_conc (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) {t' : Ty},
      resolveDefinedAliasesFuelT T fuel ty = .ok t' →
      resolveDefinedAliasesFuel fuel σ ty = t' := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty t' h
      cases ty <;> (cases h; rfl)
  | succ fuel ih =>
      intro ty t' h
      cases ty <;> try (cases h; rfl)
      case defined name =>
        revert h
        simp only [resolveDefinedAliasesFuelT]
        rcases hl : TypeEnv.lookup T name with _ | d
        · intro h
          simp [quit] at h
        · have hσ := hsub _ _ hl
          cases d <;> intro h <;>
            simp only [resolveDefinedAliasesFuel, hσ] <;>
            first
            | (cases h; rfl)
            | exact ih _ h

/-- Canonicalization commutation at the input table (the mirrored
arms; quits assert nothing). -/
theorem canonicalTyFuelT_conc (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) {t' : Ty},
      canonicalTyFuelT T fuel ty = .ok t' →
      canonicalTyFuel fuel σ ty = t' := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty t' h
      cases ty <;> (cases h; rfl)
  | succ fuel ih =>
      intro ty t' h
      cases ty <;> try (cases h; rfl)
      case defined name =>
        revert h
        simp only [canonicalTyFuelT]
        rcases hl : TypeEnv.lookup T name with _ | d
        · intro h
          simp [quit] at h
        · have hσ := hsub _ _ hl
          cases d <;> intro h <;>
            simp only [canonicalTyFuel, hσ] <;>
            first
            | (cases h; rfl)
            | exact ih _ h
      case pointer elem =>
        simp only [canonicalTyFuelT, bind_eq_ok] at h
        obtain ⟨t2, ht2, h2⟩ := h
        cases h2
        simp only [canonicalTyFuel, ih _ ht2]
      case slice elem =>
        simp only [canonicalTyFuelT, bind_eq_ok] at h
        obtain ⟨t2, ht2, h2⟩ := h
        cases h2
        simp only [canonicalTyFuel, ih _ ht2]
      case array n elem =>
        simp only [canonicalTyFuelT, bind_eq_ok] at h
        obtain ⟨t2, ht2, h2⟩ := h
        cases h2
        simp only [canonicalTyFuel, ih _ ht2]
      all_goals simp [canonicalTyFuelT, quit] at h

/-- Type-assert commutation at the input table (comma-ok outcome; the
assert decision is a concrete Bool on both sides). -/
theorem typeAssertValueT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {v : Value D} {ty : Ty}
    {r : Value D} {b : Bool}
    (h : typeAssertValueT T v ty = .ok (r, b)) :
    typeAssertValue σ (concV I v) ty = .ok (concV I r, b) := by
  unfold typeAssertValueT at h
  obtain ⟨failed, hfd, h2⟩ := bind_eq_ok.mp h
  have hfail : defaultValue σ ty = .ok (concV I failed) := by
    unfold defaultValue
    exact defaultValueFuelT_conc hI σ hsub _ _
      (by simpa [defaultValueT] using hfd)
  unfold typeAssertValue
  simp only [hfail, Bind.bind, Except.bind]
  cases v with
  | nil =>
      simp only [pure, Except.pure] at h2
      cases h2
      simp [concV, pure, Except.pure]
  | interface dynTy inner =>
      obtain ⟨rt, hrt, h3⟩ := bind_eq_ok.mp h2
      have hrtm : resolveDefinedAliases σ ty = rt := by
        unfold resolveDefinedAliases
        exact resolveDefinedAliasesFuelT_conc σ hsub _ _ hrt
      simp only [concV_interface, hrtm]
      cases rt <;> simp only [quit] at h3 <;>
        try (cases h3; done)
      all_goals
        obtain ⟨ct, hct, h4⟩ := bind_eq_ok.mp h3
        have hctm : canonicalTy σ ty = ct := by
          unfold canonicalTy
          exact canonicalTyFuelT_conc σ hsub _ _ hct
        rw [hctm] at *
        by_cases hde : dynTy == ct
        · rw [if_pos hde] at h4
          cases h4
          simp [hde]
        · rw [if_neg hde] at h4
          cases h4
          simp [hde]
  | atom a =>
      simp [quit] at h2
  | _ =>
      simp [quit] at h2

/-- Conversion commutation at the input table (the `.defined` arm;
delegated targets via the shipped `convertFuel_conc`). -/
theorem convertValueToTyFuelT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (fuel : Nat) (ty : Ty) (v : Value D) {out : Value D},
      convertValueToTyFuelT T fuel ty v = .ok out →
      convertValueToTyFuel fuel σ ty (concV I v) = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v out h
      exact convertFuel_conc hI σ _ _ _ _ h
  | succ fuel ih =>
      intro ty v out h
      cases ty <;> try exact convertFuel_conc hI σ _ _ _ _ h
      case defined name =>
        revert h
        simp only [convertValueToTyFuelT]
        rcases hl : TypeEnv.lookup T name with _ | d
        · intro h
          simp [quit] at h
        · have hσ := hsub _ _ hl
          cases d <;> intro h <;>
            simp only [convertValueToTyFuel, hσ]
          case alias target => exact ih _ _ h
          case defined target => exact ih _ _ h
          case unsupported f => simp [quit] at h
          case interfaceDef ms => simp [quit] at h
          case struct targetFields => simp [quit] at h

set_option linter.unusedSimpArgs false in
/-- `applySyncOp'` transports (census subset; `storeLoc_conc` carries
the flag store — sync cells normalize at the concrete `.sync` arm, no
table needed). -/
theorem applySyncOp_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) {s : State D}
    {op : SyncOp} {vs : List (Value D)} {env : LocalEnv} {k : Cont D}
    {c' : Config D} {s' : State D}
    (h : applySyncOp' T s op vs env k = .ok (c', s')) :
    applySyncOp (concS I σ s) op (vs.map (concV I)) env (concK I k)
      = .ok (concC I c', concS I σ s') := by
  cases op <;> simp only [applySyncOp', quit] at h <;> try (cases h; done)
  case lock =>
      match vs, h with
      | [av], h =>
        obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
        obtain ⟨p, hp, h3⟩ := bind_eq_ok.mp h2
        simp only [List.map_cons, List.map_nil, applySyncOp]
        refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
        simp only [syncCell'] at hp
        obtain ⟨pv, hpv, hp2⟩ := bind_eq_ok.mp hp
        have hload := loadLoc_conc (I := I) σ hpv
        cases pv <;> simp only [quit] at hp2 <;> try (cases hp2; done)
        case syncData prim =>
          cases hp2
          refine bind_eq_ok.mpr ⟨p, ?_, ?_⟩
          · simp only [syncCell, hload, concV_syncData, Bind.bind,
              Except.bind, pure, Except.pure]
          · cases p <;> simp only [quit] at h3 <;> try (cases h3; done)
            case mutex locked =>
              by_cases hl : locked = true
              · subst hl
                rw [if_pos rfl] at h3
                cases h3
                simp [concC, concK]
              · rw [if_neg hl] at h3
                obtain ⟨s2, hst, h4⟩ := bind_eq_ok.mp h3
                cases h4
                simp only [Bool.not_eq_true] at hl
                subst hl
                have hstc := storeLocT_conc hI σ hsub hst
                simp only [concV_syncData] at hstc
                simp [hstc, concC, concK, Bind.bind, Except.bind, pure,
                  Except.pure]
  case unlock =>
      match vs, h with
      | [av], h =>
        obtain ⟨loc, hloc, h2⟩ := bind_eq_ok.mp h
        obtain ⟨p, hp, h3⟩ := bind_eq_ok.mp h2
        simp only [List.map_cons, List.map_nil, applySyncOp]
        refine bind_eq_ok.mpr ⟨loc, asLoc_conc hloc, ?_⟩
        simp only [syncCell'] at hp
        obtain ⟨pv, hpv, hp2⟩ := bind_eq_ok.mp hp
        have hload := loadLoc_conc (I := I) σ hpv
        cases pv <;> simp only [quit] at hp2 <;> try (cases hp2; done)
        case syncData prim =>
          cases hp2
          refine bind_eq_ok.mpr ⟨p, ?_, ?_⟩
          · simp only [syncCell, hload, concV_syncData, Bind.bind,
              Except.bind, pure, Except.pure]
          · cases p <;> simp only [quit] at h3 <;> try (cases h3; done)
            case mutex locked =>
              by_cases hl : locked = true
              · subst hl
                rw [if_pos rfl] at h3
                obtain ⟨s2, hst, h4⟩ := bind_eq_ok.mp h3
                cases h4
                have hstc := storeLocT_conc hI σ hsub hst
                simp only [concV_syncData] at hstc
                simp [hstc, concC, concK, Bind.bind, Except.bind, pure,
                  Except.pure]
              · rw [if_neg hl] at h3
                cases h3


/-! ## The extended master step + window, sound -/

/-- The extended step transports: the overridden arm via
`storeTargetT_conc`, every delegated arm via the SHIPPED master walk
`stepFn'_conc` — which is what makes this module additive. -/
theorem stepFnT_conc (hI : I.Sound) (σ : ExecState) (ch : Choices)
    {T : TypeEnv} (hsub : SubTable T σ.types)
    {s : State D} {c : Config D} {c₁ : Config D} {s₁ : State D}
    (h : stepFnT T s c = .ok (c₁, s₁)) :
    stepFn (concS I σ s) (concC I c) ch
      = .ok (concC I c₁, concS I σ s₁, ch) := by
  cases c with
  | next k =>
      cases k with
      | storeK refs vals body env k' =>
          simp only [stepFnT] at h
          cases refs with
          | nil =>
              cases vals with
              | nil =>
                  cases h
                  rfl
              | cons a b => simp [quit] at h
          | cons r rs =>
              cases vals with
              | nil => simp [quit] at h
              | cons val vrest =>
                  obtain ⟨s2, hstore, h2⟩ := bind_eq_ok.mp h
                  have hout : c₁ = .next (.storeK rs vrest body env k')
                      ∧ s₁ = s2 := by
                    simpa [pure, Except.pure, eq_comm, and_comm] using h2
                  rw [hout.1, hout.2]
                  simp only [concC, concK, stepFn, List.map_cons]
                  rw [storeTargetT_conc hI σ hsub hstore]
                  rfl
      | _ => exact stepFn'_conc hI σ ch h
  | exec stmt env k =>
      cases stmt with
      | syncStmt op args targets =>
          simp only [stepFnT] at h
          revert h
          rcases hplan : syncPlan (.syncStmt op args targets) with _ | ⟨sop, es⟩
          · intro h
            simp [quit] at h
          · cases es with
            | nil =>
                intro h
                simp [quit] at h
            | cons e rest =>
                intro h
                cases h
                simp only [concC, concK, stepFn]
                split
                all_goals simp_all
      | typeAssert t okT expr targetTy =>
          simp only [stepFnT] at h
          revert h
          rcases hplan : targetsPlan [t, okT] with _ | plan
          · intro h
            simp [quit] at h
          · rcases plan with _ | ⟨⟨sh, es⟩, rest⟩
            · intro h
              simp [quit] at h
            · rcases es with _ | ⟨e, ops⟩
              · intro h
                simp [quit] at h
              · intro h
                cases h
                simp only [concC, concK, stepFn, List.map_nil]
                rw [hplan]
                rfl
      | initialization p =>
          simp only [stepFnT] at h
          revert h
          cases k
          case seq rest kenv k' =>
            intro h
            dsimp only at h
            by_cases hkenv : kenv = env
            · rw [if_pos hkenv] at h
              obtain ⟨v2, hdv, h2⟩ := bind_eq_ok.mp h
              have hd : defaultValue (concS I σ s) p.typ
                  = .ok (concV I v2) := by
                simp only [defaultValue]
                exact defaultValueFuelT_conc hI (concS I σ s) hsub _ _ hdv
              have hout : c₁ = .next (.seq rest
                    (env.declare p.id (s.alloc v2 (some p.typ)).1) k')
                  ∧ s₁ = (s.alloc v2 (some p.typ)).2 := by
                simpa [pure, Except.pure, eq_comm, and_comm] using h2
              rw [hout.1, hout.2]
              simp only [concC, concK, stepFn]
              rw [if_pos hkenv]
              simp [hd, Bind.bind, Except.bind, alloc_conc (I := I),
                pure, Except.pure, concC, concK]
            · rw [if_neg hkenv] at h
              simp [quit] at h
          all_goals (intro h; simp [quit] at h)
      | _ => exact stepFn'_conc hI σ ch h
  | retV v k =>
      cases k with
      | syncStK op done pending env k' =>
          simp only [stepFnT] at h
          cases pending with
          | cons e rest =>
              cases h
              rfl
          | nil =>
              have happ := applySyncOp_conc (I := I) hI σ hsub h
              rw [List.map_reverse] at happ
              simp only [concC, concK, stepFn]
              rw [show (concV I v :: List.map (concV I) done)
                    = List.map (concV I) (v :: done) from rfl, happ]
              rfl
      | stmtOpK op nt done pending env k' =>
          cases op <;> try exact stepFn'_conc hI σ ch h
          case mapAssign kt vt =>
            cases pending with
            | cons e rest => exact stepFn'_conc hI σ ch h
            | nil =>
                simp only [stepFnT] at h
                revert h
                rcases hrev : (v :: done).reverse with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, brest⟩⟩⟩ <;>
                  intro h <;> try (simp [quit] at h; done)
                rcases brest with _ | ⟨b4, brest2⟩
                · obtain ⟨s2, hma, h2⟩ := bind_eq_ok.mp h
                  cases h2
                  have hmc := mapAssignValueT_conc (I := I) hI σ hsub hma
                  simp only [concC, concK, stepFn, applyStmtOp,
                    applyStmtOpCore]
                  rw [show ((concV I v :: List.map (concV I) done)).reverse
                        = List.map (concV I) ((v :: done).reverse) from by
                    simp [List.map_reverse]]
                  rw [hrev]
                  simp only [List.map_cons, List.map_nil]
                  rw [hmc]
                  rfl
                · simp [quit] at h
      | strictK op done pending env k' =>
          cases op <;> try exact stepFn'_conc hI σ ch h
          case convert cty =>
            cases cty <;> try exact stepFn'_conc hI σ ch h
            case defined name =>
              cases done with
              | cons a b => exact stepFn'_conc hI σ ch h
              | nil =>
                cases pending with
                | cons e rest => exact stepFn'_conc hI σ ch h
                | nil =>
                    simp only [stepFnT] at h
                    obtain ⟨out, hcv, h2⟩ := bind_eq_ok.mp h
                    cases h2
                    have hcvm := convertValueToTyFuelT_conc (I := I) hI
                      (concS I σ s) hsub _ _ _ hcv
                    simp only [concC, concK, stepFn, List.map_nil,
                      List.reverse_cons, List.reverse_nil, List.nil_append]
                    simp [applyStrictOp, convertValueToTy, hcvm, Bind.bind,
                      Except.bind, pure, Except.pure]
          case typeAssert tty sty =>
            cases done with
            | cons a b => exact stepFn'_conc hI σ ch h
            | nil =>
              cases pending with
              | cons e rest => exact stepFn'_conc hI σ ch h
              | nil =>
                  simp only [stepFnT] at h
                  obtain ⟨⟨rv, rb⟩, hta, h2⟩ := bind_eq_ok.mp h
                  have htam := typeAssertValueT_conc (I := I) hI
                    (concS I σ s) hsub hta
                  revert h2
                  by_cases hrb : rb = true
                  · subst hrb
                    rw [if_pos rfl]
                    intro h2
                    cases h2
                    simp only [concC, concK, stepFn, List.map_nil,
                      List.reverse_cons, List.reverse_nil, List.nil_append]
                    simp [applyStrictOp, htam, Bind.bind, Except.bind,
                      pure, Except.pure]
                  · rw [if_neg hrb]
                    intro h2
                    simp [quit] at h2
          case eqCmp ty =>
            cases pending with
            | cons e rest => exact stepFn'_conc hI σ ch h
            | nil =>
                simp only [stepFnT] at h
                revert h
                rcases hrev : (v :: done).reverse with _ | ⟨l, _ | ⟨r, rest2⟩⟩ <;>
                  intro h <;> try (simp [quit] at h; done)
                rcases rest2 with _ | ⟨x, rest3⟩
                · obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
                  cases h2
                  have hsub' : SubTable T (concS I σ s).types := hsub
                  have hv := valueEqRT_conc (I := I) hI (concS I σ s) hsub' hb
                  simp only [concC, concK, stepFn]
                  rw [show ((concV I v :: List.map (concV I) done)).reverse
                        = List.map (concV I) ((v :: done).reverse) from by
                    simp [List.map_reverse]]
                  rw [hrev]
                  simp [applyStrictOp, hv, Bind.bind, Except.bind, pure,
                    Except.pure, concV_bool]
                · simp [quit] at h
          case neqCmp ty =>
            cases pending with
            | cons e rest => exact stepFn'_conc hI σ ch h
            | nil =>
                simp only [stepFnT] at h
                revert h
                rcases hrev : (v :: done).reverse with _ | ⟨l, _ | ⟨r, rest2⟩⟩ <;>
                  intro h <;> try (simp [quit] at h; done)
                rcases rest2 with _ | ⟨x, rest3⟩
                · obtain ⟨b, hb, h2⟩ := bind_eq_ok.mp h
                  cases h2
                  have hsub' : SubTable T (concS I σ s).types := hsub
                  have hv := valueEqRT_conc (I := I) hI (concS I σ s) hsub' hb
                  simp only [concC, concK, stepFn]
                  rw [show ((concV I v :: List.map (concV I) done)).reverse
                        = List.map (concV I) ((v :: done).reverse) from by
                    simp [List.map_reverse]]
                  rw [hrev]
                  simp [applyStrictOp, hv, hI.notB, Bind.bind, Except.bind,
                    pure, Except.pure, concV_bool]
                · simp [quit] at h
          case structLit ty =>
            cases pending with
            | cons e rest => exact stepFn'_conc hI σ ch h
            | nil =>
                simp only [stepFnT] at h
                obtain ⟨out, hbuild, h2⟩ := bind_eq_ok.mp h
                cases h2
                have hb := buildStructValueT_conc (I := I) hI
                  (concS I σ s) hsub hbuild
                have hb2 : buildStructValue (concS I σ s) ty
                    (((List.map (concV I) done).reverse
                      ++ [concV I v]).toArray) = .ok (concV I out) := by
                  simpa [List.map_toArray, List.map_reverse,
                    List.reverse_cons] using hb
                simp [concC, concK, stepFn, applyStrictOp,
                  List.reverse_cons, List.map_append, List.map_reverse,
                  List.map_cons, List.map_nil, hb2, Bind.bind,
                  Except.bind, pure, Except.pure]
      | rhsK rop refs done pending body env k' =>
          cases rop <;> try exact stepFn'_conc hI σ ch h
          case typeAssert tty =>
            cases done with
            | cons a b => exact stepFn'_conc hI σ ch h
            | nil =>
              cases pending with
              | cons e rest => exact stepFn'_conc hI σ ch h
              | nil =>
                  simp only [stepFnT] at h
                  obtain ⟨⟨rv, rb⟩, hta, h2⟩ := bind_eq_ok.mp h
                  cases h2
                  have htam := typeAssertValueT_conc (I := I) hI
                    (concS I σ s) hsub hta
                  simp only [concC, concK, stepFn, List.map_nil,
                    List.reverse_cons, List.reverse_nil, List.nil_append]
                  simp [applyRhsOp, htam, Bind.bind, Except.bind, pure,
                    Except.pure, hI.litB, concC, concK]
      | _ => exact stepFn'_conc hI σ ch h
  | evalE e env k =>
      cases e with
      | structLit ty elems =>
          simp only [stepFnT] at h
          revert h
          rcases helems : elems.toList with _ | ⟨e₁, rest⟩
          · intro h
            obtain ⟨out, hbuild, h2⟩ := bind_eq_ok.mp h
            cases h2
            have hb := buildStructValueT_conc (I := I) hI
              (concS I σ s) hsub hbuild
            have hb2 : buildStructValue (concS I σ s) ty
                (#[] : Array GoValue) = .ok (concV I out) := by
              simpa using hb
            simp [concC, concK, stepFn, strictPlan, helems,
              applyStrictOp, hb2, Bind.bind, Except.bind, pure,
              Except.pure]
          · intro h
            cases h
            simp [concC, concK, stepFn, strictPlan, helems]
      | defaultValue ty =>
          simp only [stepFnT] at h
          obtain ⟨v2, hdv, h2⟩ := bind_eq_ok.mp h
          cases h2
          have hsub' : SubTable T (concS I σ s).types := hsub
          have hd : defaultValue (concS I σ s) ty = .ok (concV I v2) := by
            simp only [defaultValue]
            exact defaultValueFuelT_conc hI (concS I σ s) hsub' _ _ hdv
          simp [concC, concK, stepFn, strictPlan, applyStrictOp, hd,
            Bind.bind, Except.bind, pure, Except.pure]
      | _ => exact stepFn'_conc hI σ ch h
  | opDone sched inner =>
      cases h
      rfl
  | _ => exact stepFn'_conc hI σ ch h

/-- The symbolic instance of the extended step (the refinement
theorem's per-step half; mirrors `stepFnS_sound`). -/
theorem stepFnST_sound (ρ : Valuation) (σ : ExecState) (ch : Choices)
    {T : TypeEnv} (hsub : SubTable T σ.types)
    {S : SymState} {C C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnST T S C = .ok (C₁, S₁)) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) :=
  stepFnT_conc (symInterp_sound ρ) σ ch hsub h

/-- **THE TABLE-CONDITIONED REFINEMENT THEOREM** — the shipped
template (`symEvalWindow_refines`) plus exactly one premise:
`SubTable T σ.types`. At `T = []` this IS the shipped theorem (via
`SubTable.nil`). -/
theorem symEvalWindowT_refines :
    ∀ {T : TypeEnv} {budget : Nat} {S : SymState} {C : SymConfig} {n : Nat}
      {S' : SymState} {C' : SymConfig},
      symEvalWindowT T budget S C = (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        SubTable T σ.types →
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S' , ch) := by
  intro T budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch hsub
      simp only [symEvalWindowT, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch hsub
      simp only [symEvalWindowT] at h
      rcases hstep : stepFnST T S C with q | ⟨C₁, S₁⟩ <;> rw [hstep] at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · simp only [] at h
        rcases hrec : symEvalWindowT T budget S₁ C₁ with ⟨m, S₂, C₂⟩
        rw [hrec] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := stepFnST_sound ρ σ ch hsub hstep
        simp only [stepFnIter, h1, Bind.bind, Except.bind]
        exact ih hrec ρ σ ch hsub

/-- The projection-form corollary (the emission seam; mirrors
`symEvalWindow_refines'`). -/
theorem symEvalWindowT_refines' {T : TypeEnv} {budget n : Nat}
    {S : SymState} {C : SymConfig}
    (hn : (symEvalWindowT T budget S C).1 = n)
    (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hsub : SubTable T σ.types) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (symEvalWindowT T budget S C).2.2,
          γS ρ σ (symEvalWindowT T budget S C).2.1, ch) :=
  symEvalWindowT_refines (by rw [← hn]) ρ σ ch hsub

/-! ## Slice-2 discharge witness (constitution §3.3): a lock/unlock
pair crossed IN-window — the sync arms exercised end to end on a
concrete mutex cell (the `#eval` check ran first: 12 steps, final
state unlocked — the standing rule). No table needed (`SubTable.nil`),
so this also witnesses the degenerate-instance claim. -/

def syncWitS : SymState :=
  { heap := [(.base ⟨0⟩, .mk (some (.sync .mutex)) (.syncData (.mutex false)))],
    nextAddr := 1 }

def syncWitC : SymConfig :=
  .exec (.seqn #[.syncStmt .lock #[.locLit (.base ⟨0⟩)] #[],
                 .syncStmt .unlock #[.locLit (.base ⟨0⟩)] #[]])
    [] (.seq [] [] .stop)

theorem syncWit_window_n : (symEvalWindowT [] 12 syncWitS syncWitC).1 = 12 := by
  rfl

/-- The transported lock/unlock window, ∀ρ ∀σ ∀ch — and the witness
that the sync arms' claims are not vacuous. -/
theorem syncWit_refines (ρ : Valuation) (σ : ExecState) (ch : Choices) :
    stepFnIter 12 (γS ρ σ syncWitS) (γC ρ syncWitC) ch
      = .ok (γC ρ (symEvalWindowT [] 12 syncWitS syncWitC).2.2,
          γS ρ σ (symEvalWindowT [] 12 syncWitS syncWitC).2.1, ch) :=
  symEvalWindowT_refines' syncWit_window_n ρ σ ch (SubTable.nil _)

/-- The window's post-heap: the mutex ends UNLOCKED (both ops ran). -/
theorem syncWit_final :
    (symEvalWindowT [] 12 syncWitS syncWitC).2.1.heap
      = [(.base ⟨0⟩, .mk (some (.sync .mutex)) (.syncData (.mutex false)))] := by
  rfl


/-! ## Slice 3 — call entry (design §3, class 2): ONE lever for fid
calls, closure call-values, deferred-call drains, and interface
dispatch, all through a mirrored `enterFrame` at an input TABLE PACK.

The delegation-vs-refactor decision (deferred at slice 1, decided
here from contact): DELEGATION AGAIN, LAYERED — `stepFnTB` overrides
the four call/drain configuration shapes and delegates everything
else to `stepFnT` (which delegates to the shipped `stepFn'`). The
override sets are disjoint config shapes, so the layers never
interleave; slice-1's theorems (and their weaker `SubTable`-only
premise, which store-only windows keep) survive verbatim. A refactor
into one step function is re-posed only if a future class needs to
interleave with an existing override.

The premise strengthens for THIS layer: `SymTables.Agrees` demands
table EQUALITY, not sub-table — alias-resolution walks
(`canonicalTy`, `resolveDefinedAliases`) return partial answers on a
MISS rather than failing, so a sub-table's miss is indistinguishable
from a genuine absence and equality is the honest condition
(recorded; the store layer keeps sub-table). -/

/-- The call-entry input pack. -/
structure SymTables where
  types : TypeEnv := []
  functions : Array Func := #[]
  methods : Array MethodInfo := #[]
  methodSets : Array MethodSetRecord := #[]

/-- The pack as a heapless machine state — the carrier the MACHINE'S
OWN table helpers run against inside the mirror (zero
re-implementation of the dispatch walks). -/
def SymTables.toState (TB : SymTables) : ExecState :=
  { types := TB.types, functions := TB.functions,
    methods := TB.methods, methodSets := TB.methodSets }

/-- Table agreement (equality on all four components — see the module
docstring for why not sub-table here). -/
def SymTables.Agrees (TB : SymTables) (σ : ExecState) : Prop :=
  σ.types = TB.types ∧ σ.functions = TB.functions
    ∧ σ.methods = TB.methods ∧ σ.methodSets = TB.methodSets

/-- **The table pin at concretization** (A4-U24, promoted from
`RoundVoteEqA.γS_pin` at its second consumer per the U23 ledger row):
under `Agrees`, concretization over ANY table carrier equals
concretization over the pack's own heapless state — `concS` overrides
`heap`/`nextAddr`, and `Agrees` pins the remaining four `ExecState`
fields, which is the whole record. The consumer family: ∀σ crossing
statements whose single step has a nonempty TABLE footprint (mapIter
over a defined-value-type map consults `s.types` via
`snapshotEntriesSelfNormalized` — the U23 bisect finding), which
rewrite through this and close by kernel_rfl at the pinned carrier
(`RoundVoteEqA`'s four Visit resets; `RoundMarEqA`'s six). -/
theorem SymTables.Agrees.concS_eq {D : ScalarDom} {I : Interp D}
    {TB : SymTables} {σ : ExecState} (hag : TB.Agrees σ)
    (s : State D) : concS I σ s = concS I TB.toState s := by
  obtain ⟨h1, h2, h3, h4⟩ := hag
  cases σ
  simp only [concS, SymTables.toState] at *
  subst h1 h2 h3 h4
  rfl

/-! ### Table-only congruence for the machine's dispatch helpers -/

theorem resolveDefinedAliasesFuel_types {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) :
    ∀ (fuel : Nat) (ty : Ty),
      resolveDefinedAliasesFuel fuel σ₁ ty
        = resolveDefinedAliasesFuel fuel σ₂ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; rfl
  | succ fuel ih =>
      intro ty
      cases ty <;> simp only [resolveDefinedAliasesFuel]
      next name =>
        rw [h]
        cases TypeEnv.lookup σ₂.types name with
        | none => rfl
        | some td => cases td <;> simp [ih]

theorem canonicalTyFuel_types {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) :
    ∀ (fuel : Nat) (ty : Ty),
      canonicalTyFuel fuel σ₁ ty = canonicalTyFuel fuel σ₂ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; cases ty <;> rfl
  | succ fuel ih =>
      intro ty
      have hfun : canonicalTyFuel fuel σ₁ = canonicalTyFuel fuel σ₂ :=
        funext ih
      cases ty <;> simp only [canonicalTyFuel, ih, hfun] <;> (try rw [h])

theorem methodInfoByFuncId_tables {σ₁ σ₂ : ExecState}
    (h : σ₁.methods = σ₂.methods) (fid : FuncId) :
    methodInfoByFuncId? σ₁ fid = methodInfoByFuncId? σ₂ fid := by
  simp only [methodInfoByFuncId?, h]

theorem methodRecvInterfaceName_tables {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) (m : MethodInfo) :
    methodRecvInterfaceName? σ₁ m = methodRecvInterfaceName? σ₂ m := by
  simp only [methodRecvInterfaceName?, resolveDefinedAliases,
    resolveDefinedAliasesFuel_types h]

/-! ### The mirrored frame entry -/

/-- Mirror of `bindParams` at the pack's type table. -/
def bindParamsT (T : TypeEnv) :
    LocalEnv → State D → List Param → List (Value D) → M (LocalEnv × State D)
  | env, s, [], [] => .ok (env, s)
  | env, s, p :: ps, v :: vs => do
      let v' ← normalizeValueForTyT T p.typ v
      match s.alloc v' (some p.typ) with
      | (loc, s₁) => bindParamsT T (env.declare p.id loc) s₁ ps vs
  | _, _, [], _ :: _ => quit .q11Internal
  | _, _, _ :: _, [] => quit .q11Internal

/-- `allocDecls'` WITH the defined-type default former at the input
table (U10: result cells of a DEFINED result type — `raftpb.MessageType`
on the `GetType` entry is the first exercised instance; the shipped
`allocDecls'` quits exactly there, so this agrees with it wherever it
stepped). -/
def allocDeclsT (T : TypeEnv) :
    LocalEnv → State D → List Param → M (LocalEnv × State D)
  | env, s, [] => .ok (env, s)
  | env, s, p :: rest => do
      let v ← defaultValueT T p.typ
      let (loc, s₁) := s.alloc v (some p.typ)
      allocDeclsT T (env.declare p.id loc) s₁ rest

theorem allocDeclsT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (ps : List Param) (env : LocalEnv) {s : State D}
      {env' : LocalEnv} {s' : State D},
      allocDeclsT T env s ps = .ok (env', s') →
      allocDecls env (concS I σ s) ps = .ok (env', concS I σ s') := by
  intro ps
  induction ps with
  | nil =>
      intro env s env' s' h
      cases h
      simp [allocDecls, pure, Except.pure]
  | cons p rest ih =>
      intro env s env' s' h
      simp only [allocDeclsT] at h
      obtain ⟨v, hv, h2⟩ := bind_eq_ok.mp h
      rcases halloc : s.alloc v (some p.typ) with ⟨loc, s₁⟩
      rw [halloc] at h2
      have hd : defaultValue (concS I σ s) p.typ = .ok (concV I v) := by
        simp only [defaultValue]
        exact defaultValueFuelT_conc hI (concS I σ s) hsub _ _ hv
      simp only [allocDecls, hd, Bind.bind, Except.bind]
      rw [alloc_conc, halloc]
      exact ih _ h2

/-- `pinResultLocs` is env-only; the machine's own function serves,
error-converted. -/
def pinResultLocs' (env : LocalEnv) (ps : List Param) : M (List Loc) :=
  match pinResultLocs env ps with
  | .ok locs => .ok locs
  | .error _ => quit .q11Internal

/-- Mirror of `dynamicDispatch?` at the pack (A4-U3 completes the
design §3 "ONE lever, not three" scope — class 2b): plain functions
and concrete-receiver methods dispatch to `none`; INTERFACE-receiver
methods resolve through the machine's OWN walks at `TB.toState`
(`concreteMethodForDynamic?` — the method-set fold over
`canonicalTy`), on the NO-DEREF path only (a pointer box dispatching
to a value-receiver method reads the heap — `needsDeref` stays a
quit; so do a nil receiver — the machine's nil-deref panic — and an
unrecorded method set). -/
def dynamicDispatchT (TB : SymTables) (func : Func) (args : List (Value D)) :
    M (Option (Func × List (Value D))) :=
  match methodInfoByFuncId? TB.toState func.id with
  | none => .ok none
  | some method =>
      match methodRecvInterfaceName? TB.toState method with
      | none => .ok none
      | some _ =>
          match args with
          | .interface dynTy inner :: rest =>
              (match concreteMethodForDynamic? TB.toState dynTy method.name with
               | some (concrete, needsDeref) =>
                   if needsDeref then quit .q4Program
                   else
                     match findFunctionIn? TB.functions concrete.funcId with
                     | some targetFunc => .ok (some (targetFunc, inner :: rest))
                     | none => quit .q4Program
               | none => quit .q4Program)
          | .nil :: _ => quit .q6Panic
          | .atom _ :: _ => quit .q10Atom
          | _ => quit .q11Internal

/-- Mirror of `enterFrame` at the pack (the machine's structure
verbatim, including the post-dispatch arity re-check). -/
def enterFrameT (TB : SymTables) (s : State D) (fid : FuncId)
    (args : List (Value D)) : M (Func × LocalEnv × List Loc × State D) := do
  let func ←
    match findFunctionIn? TB.functions fid with
    | some f => .ok f
    | none => quit .q4Program
  if func.args.size != args.length then quit .q11Internal
  else do
    let (func, args) ←
      match ← dynamicDispatchT TB func args with
      | some (targetFunc, targetArgs) => .ok (targetFunc, targetArgs)
      | none => .ok (func, args)
    if func.args.size != args.length then quit .q11Internal
    else do
      let (argsEnv, s₁) ← bindParamsT TB.types [] s func.args.toList args
      let (frameEnv, s₂) ← allocDeclsT TB.types argsEnv s₁ func.results.toList
      let resultLocs ← pinResultLocs' frameEnv func.results.toList
      .ok (func, frameEnv, resultLocs, s₂)

/-! ### Call-entry soundness -/

theorem bindParamsT_conc (hI : I.Sound) (σ : ExecState) {T : TypeEnv}
    (hsub : SubTable T σ.types) :
    ∀ (ps : List Param) (vs : List (Value D)) (env : LocalEnv) {s : State D}
      {env' : LocalEnv} {s' : State D},
      bindParamsT T env s ps vs = .ok (env', s') →
      bindParams env (concS I σ s) ps (vs.map (concV I))
        = .ok (env', concS I σ s') := by
  intro ps
  induction ps with
  | nil =>
      intro vs env s env' s' h
      cases vs with
      | nil =>
          simp only [bindParamsT] at h
          cases h
          simp [bindParams, pure, Except.pure]
      | cons a rest =>
          simp only [bindParamsT, quit] at h
          cases h
  | cons p ps ih =>
      intro vs env s env' s' h
      cases vs with
      | nil =>
          simp only [bindParamsT, quit] at h
          cases h
      | cons v vrest =>
          simp only [bindParamsT] at h
          obtain ⟨nv, hnv, h2⟩ := bind_eq_ok.mp h
          rcases halloc : s.alloc nv (some p.typ) with ⟨loc, s₁⟩
          rw [halloc] at h2
          simp only [List.map_cons, bindParams, bind_eq_ok]
          refine ⟨concV I nv, normalizeT_conc hI (concS I σ s) hsub hnv, ?_⟩
          rw [alloc_conc, halloc]
          exact ih _ _ h2

theorem methodRecvDynamicTy_tables {σ₁ σ₂ : ExecState}
    (h : σ₁.types = σ₂.types) (m : MethodInfo) :
    methodRecvDynamicTy? σ₁ m = methodRecvDynamicTy? σ₂ m := by
  simp only [methodRecvDynamicTy?, canonicalTy, canonicalTyFuel_types h]

theorem concreteMethodForDynamic_tables {σ₁ σ₂ : ExecState}
    (ht : σ₁.types = σ₂.types) (hm : σ₁.methods = σ₂.methods)
    (dynTy : Ty) (name : String) :
    concreteMethodForDynamic? σ₁ dynTy name
      = concreteMethodForDynamic? σ₂ dynTy name := by
  have hr : ∀ m, methodRecvDynamicTy? σ₁ m = methodRecvDynamicTy? σ₂ m :=
    methodRecvDynamicTy_tables ht
  simp only [concreteMethodForDynamic?, hm, hr]

theorem dynamicDispatchT_conc (σ : ExecState)
    {TB : SymTables} (hag : TB.Agrees σ) {s : State D}
    {func : Func} {args : List (Value D)}
    {result : Option (Func × List (Value D))}
    (h : dynamicDispatchT TB func args = .ok result) :
    dynamicDispatch? (concS I σ s) func ((args.map (concV I)).toArray)
      = .ok (result.map (fun p => (p.1, (p.2.map (concV I)).toArray))) := by
  obtain ⟨ht, hf, hm, hms⟩ := hag
  have htc : (concS I σ s).types = TB.toState.types := by
    simp [concS, ht, SymTables.toState]
  have hmc : (concS I σ s).methods = TB.toState.methods := by
    simp [concS, hm, SymTables.toState]
  have hfc : (concS I σ s).functions = TB.functions := by
    simp [concS, hf]
  have hmi := methodInfoByFuncId_tables (σ₁ := concS I σ s)
    (σ₂ := TB.toState) hmc func.id
  have hric : ∀ m, methodRecvInterfaceName? (concS I σ s) m
      = methodRecvInterfaceName? TB.toState m :=
    fun m => methodRecvInterfaceName_tables htc m
  have hcmc : ∀ d n, concreteMethodForDynamic? (concS I σ s) d n
      = concreteMethodForDynamic? TB.toState d n :=
    fun d n => concreteMethodForDynamic_tables htc hmc d n
  simp only [dynamicDispatchT] at h
  split at h
  next hinfo =>
    cases h
    simp [dynamicDispatch?, hmi, hinfo]
  next method hinfo =>
    split at h
    next hrecv =>
      cases h
      simp [dynamicDispatch?, hmi, hinfo, hric, hrecv]
    next iname hrecv =>
      split at h
      next dynTy inner rest =>
        split at h
        next concrete needsDeref hcm =>
          split at h
          next hnd =>
            simp [quit] at h
          next hnd =>
            split at h
            next targetFunc hfind =>
              cases h
              simp only [Bool.not_eq_true] at hnd
              subst hnd
              simp only [dynamicDispatch?, hmi, hinfo, hric, hrecv,
                List.map_cons, concV_interface]
              simp [hcmc, hcm, hfc, hfind, Bind.bind, Except.bind, pure,
                Except.pure, Array.set!, List.getElem?_toArray]
            next hfind =>
              simp [quit] at h
        next hcm =>
          simp [quit] at h
      next => simp [quit] at h
      next => simp [quit] at h
      next => simp [quit] at h

/-- Frame entry transports (census subset), composing the table
congruences with the mirrored binding chain. -/
theorem enterFrameT_conc (hI : I.Sound) (σ : ExecState) {TB : SymTables}
    (hag : TB.Agrees σ) {s : State D} {fid : FuncId} {args : List (Value D)}
    {func : Func} {env : LocalEnv} {locs : List Loc} {s' : State D}
    (h : enterFrameT TB s fid args = .ok (func, env, locs, s')) :
    enterFrame (concS I σ s) fid (args.map (concV I))
      = .ok (func, env, locs, concS I σ s') := by
  have hf : (concS I σ s).functions = TB.functions := by
    simp [concS, hag.2.1]
  simp only [enterFrameT] at h
  revert h
  rcases hfind : findFunctionIn? TB.functions fid with _ | f0
  · intro h
    simp [quit, Bind.bind, Except.bind] at h
  · intro h
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    by_cases harity : (f0.args.size != args.length) = true
    · rw [if_pos harity] at h
      simp [quit] at h
    · rw [if_neg harity] at h
      obtain ⟨disp, hdisp, h2⟩ := bind_eq_ok.mp h
      have hdc := dynamicDispatchT_conc (I := I) σ hag (s := s) hdisp
      have hpinM : ∀ (fe : LocalEnv) (f' : Func) (ls : List Loc),
          pinResultLocs' fe f'.results.toList = (.ok ls : M (List Loc)) →
          pinResultLocs fe f'.results.toList = .ok ls := by
        intro fe f' ls hp
        revert hp
        simp only [pinResultLocs']
        rcases pinResultLocs fe f'.results.toList with e | ls2
        · intro hp
          simp [quit] at hp
        · intro hp
          cases hp
          rfl
      rcases disp with _ | ⟨tf, ta⟩
      · -- no dispatch: the tail runs at (f0, args)
        simp only [] at h2
        rw [if_neg harity] at h2
        rcases hbind : bindParamsT TB.types [] s f0.args.toList args
          with e | ⟨argsEnv, s₁⟩ <;> simp only [hbind] at h2
        · cases h2
        rcases halloc : allocDeclsT TB.types argsEnv s₁ f0.results.toList
          with e | ⟨frameEnv, s₂⟩ <;> simp only [halloc] at h2
        · cases h2
        rcases hpin : pinResultLocs' frameEnv f0.results.toList
          with e | rlocs <;> simp only [hpin] at h2
        · cases h2
        cases h2
        have harityF : (func.args.size != args.length) = false := by
          simpa using harity
        have hb := bindParamsT_conc (I := I) hI σ (SubTable.of_eq hag.1)
          func.args.toList args [] hbind
        have hal := allocDeclsT_conc (I := I) hI σ (SubTable.of_eq hag.1)
          _ _ halloc
        simp only [enterFrame, hf, hfind, Bind.bind, Except.bind, pure,
          Except.pure, List.length_map, harityF, hdc, Option.map_none,
          Bool.false_eq_true, if_false, hb, hal, hpinM _ _ _ hpin]
      · -- dispatch redirect: the tail runs at (tf, ta)
        simp only [] at h2
        by_cases harity2 : (tf.args.size != ta.length) = true
        · rw [if_pos harity2] at h2
          simp [quit] at h2
        · rw [if_neg harity2] at h2
          rcases hbind : bindParamsT TB.types [] s tf.args.toList ta
            with e | ⟨argsEnv, s₁⟩ <;> simp only [hbind] at h2
          · cases h2
          rcases halloc : allocDeclsT TB.types argsEnv s₁ tf.results.toList
            with e | ⟨frameEnv, s₂⟩ <;> simp only [halloc] at h2
          · cases h2
          rcases hpin : pinResultLocs' frameEnv tf.results.toList
            with e | rlocs <;> simp only [hpin] at h2
          · cases h2
          cases h2
          have harityF : (f0.args.size != args.length) = false := by
            simpa using harity
          have harity2F : (func.args.size != (ta.map (concV I)).length)
              = false := by
            simpa using harity2
          have hb := bindParamsT_conc (I := I) hI σ (SubTable.of_eq hag.1)
            func.args.toList ta [] hbind
          have hal := allocDeclsT_conc (I := I) hI σ (SubTable.of_eq hag.1)
            _ _ halloc
          simp only [enterFrame, hf, hfind, Bind.bind, Except.bind, pure,
            Except.pure, List.length_map, harityF, hdc, Option.map_some,
            Bool.false_eq_true, if_false, List.toList_toArray,
            harity2F, hb, hal, hpinM _ _ _ hpin]
          rw [if_neg harity2]

/-- The class-2 layered step: the four call/drain configuration
shapes through `enterFrameT`; EVERYTHING else delegates to the
slice-1/2 `stepFnT` (which delegates to the shipped `stepFn'`). The
layers never interleave — the override sets are disjoint config
shapes (the deferred delegation-vs-refactor decision, resolved:
delegation again; see the slice-3 docstring above). -/
def stepFnTB (TB : SymTables) (s : State D) (c : Config D) :
    M (Config D × State D) :=
  match c with
  | .retV v (.callArgsK fid plans vals pending env k') =>
      (match pending with
       | a :: rest =>
           .ok (.evalE a env
             (.callArgsK fid plans (vals ++ [v]) rest env k'), s)
       | [] => do
           let (func, frameEnv, resultLocs, s') ←
             enterFrameT TB s fid (vals ++ [v])
           .ok (.exec func.body frameEnv
             (.frame plans env resultLocs [] k' func.wrapper), s'))
  | .retV v (.callValArgsK cv plans vals pending env k') =>
      (match pending with
       | a :: rest =>
           .ok (.evalE a env
             (.callValArgsK cv plans (vals ++ [v]) rest env k'), s)
       | [] =>
           match cv with
           | .funcVal fid captured => do
               let (func, frameEnv, resultLocs, s') ←
                 enterFrameT TB s fid (captured ++ vals ++ [v])
               .ok (.exec func.body frameEnv
                 (.frame plans env resultLocs [] k' func.wrapper), s')
           | .nil => quit .q6Panic
           | .atom _ => quit .q10Atom
           | _ => quit .q11Internal)
  | .next (.frame targets tenv results ((cv, dargs) :: ds) k' w) =>
      (match cv with
       | .funcVal fid captured => do
           let (func, frameEnv, _, s') ←
             enterFrameT TB s fid (captured ++ dargs)
           .ok (.exec func.body frameEnv
             (.frame [] [] [] []
               (.frame targets tenv results ds k' w) func.wrapper), s')
       | .nil => quit .q6Panic
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .returning (.frame targets tenv results ((cv, dargs) :: ds) k' w) =>
      (match cv with
       | .funcVal fid captured => do
           let (func, frameEnv, _, s') ←
             enterFrameT TB s fid (captured ++ dargs)
           .ok (.exec func.body frameEnv
             (.frame [] [] [] []
               (.frame targets tenv results ds k' w) func.wrapper), s')
       | .nil => quit .q6Panic
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  -- U3-a: `toInterface` boxing. Lives in THIS layer (not stepFnT)
  -- because `canonicalTy` returns partial answers on a lookup miss —
  -- only table EQUALITY (the Agrees premise) makes it transportable
  -- (the same reason the pack demands equality; slice-3 docstring).
  | .retV v (.strictK (.toInterface target dynamic) done [] env k') =>
      (match (v :: done).reverse with
       | [x] => do
           let dynTy ←
             match canonicalDynamicTy TB.toState dynamic with
             | .ok t => .ok t
             | .error _ => quit .q4Program
           match dynTy with
           | .interface _ => .ok (.retV x k', s)
           | _ => .ok (.retV (.interface dynTy x) k', s)
       | _ => quit .q11Internal)
  | c => stepFnT TB.types s c

/-- The layered step transports (the class-2 arms via
`enterFrameT_conc`; the pending-cons operand steps structurally;
everything else via the slice-1/2 `stepFnT_conc`). -/
theorem stepFnTB_conc (hI : I.Sound) (σ : ExecState) (ch : Choices)
    {TB : SymTables} (hag : TB.Agrees σ)
    {s : State D} {c : Config D} {c₁ : Config D} {s₁ : State D}
    (h : stepFnTB TB s c = .ok (c₁, s₁)) :
    stepFn (concS I σ s) (concC I c) ch
      = .ok (concC I c₁, concS I σ s₁, ch) := by
  have hsub : SubTable TB.types σ.types := SubTable.of_eq hag.1
  cases c with
  | retV v k =>
      cases k with
      | callArgsK fid plans vals pending env k' =>
          simp only [stepFnTB] at h
          cases pending with
          | cons a rest =>
              cases h
              simp [concC, concK, stepFn, List.map_append]
          | nil =>
              obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                bind_eq_ok.mp h
              cases h2
              have hef := enterFrameT_conc (I := I) hI σ hag hent
              simp only [concC, concK, stepFn, enterFrameStep,
                List.map_append, List.map_cons, List.map_nil] at hef ⊢
              rw [hef]
      | callValArgsK cv plans vals pending env k' =>
          simp only [stepFnTB] at h
          cases pending with
          | cons a rest =>
              cases h
              simp [concC, concK, stepFn, List.map_append]
          | nil =>
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | strictK op done pending env k' =>
          cases op <;> try (exact stepFnT_conc hI σ ch hsub h)
          case toInterface target dynamic =>
            cases pending with
            | cons e rest => exact stepFnT_conc hI σ ch hsub h
            | nil =>
                simp only [stepFnTB] at h
                have hcanon : canonicalDynamicTy (concS I σ s) dynamic
                    = canonicalDynamicTy TB.toState dynamic := by
                  simp only [canonicalDynamicTy, canonicalTy]
                  rw [canonicalTyFuel_types
                    (show (concS I σ s).types = TB.toState.types by
                      simp [concS, SymTables.toState, hag.1])]
                revert h
                rcases hrev : (v :: done).reverse with _ | ⟨x, _ | ⟨y, rest2⟩⟩ <;>
                  intro h <;> try (simp [quit] at h; done)
                revert h
                rcases hcd : canonicalDynamicTy TB.toState dynamic with e | t
                · intro h
                  simp [quit, Bind.bind, Except.bind] at h
                · intro h
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
                  cases t <;> cases h <;>
                    · simp only [concC, concK, stepFn]
                      rw [show ((concV I v :: List.map (concV I) done)).reverse
                            = List.map (concV I) ((v :: done).reverse) from by
                        simp [List.map_reverse]]
                      rw [hrev]
                      simp [applyStrictOp, hcanon, hcd, Bind.bind,
                        Except.bind, pure, Except.pure]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | next k =>
      cases k with
      | frame targets tenv results defers k' w =>
          cases defers with
          | nil => exact stepFnT_conc hI σ ch hsub h
          | cons d ds =>
              obtain ⟨cv, dargs⟩ := d
              simp only [stepFnTB] at h
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | returning k =>
      cases k with
      | frame targets tenv results defers k' w =>
          cases defers with
          | nil => exact stepFnT_conc hI σ ch hsub h
          | cons d ds =>
              obtain ⟨cv, dargs⟩ := d
              simp only [stepFnTB] at h
              cases cv <;> simp only [quit] at h <;> try (cases h; done)
              case funcVal fid captured =>
                obtain ⟨⟨func, frameEnv, resultLocs, s'⟩, hent, h2⟩ :=
                  bind_eq_ok.mp h
                cases h2
                have hef := enterFrameT_conc (I := I) hI σ hag hent
                simp only [concC, concK, concV_funcVal, stepFn,
                  enterFrameStep, List.map_append, List.map_cons,
                  List.map_nil] at hef ⊢
                rw [hef]
      | _ => exact stepFnT_conc hI σ ch hsub h
  | _ => exact stepFnT_conc hI σ ch hsub h

/-- The layered step at the symbolic domain. -/
def stepFnSTB (TB : SymTables) (S : SymState) (C : SymConfig) :
    M (SymConfig × SymState) :=
  stepFnTB TB S C

theorem stepFnSTB_sound (ρ : Valuation) (σ : ExecState) (ch : Choices)
    {TB : SymTables} (hag : TB.Agrees σ)
    {S : SymState} {C C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnSTB TB S C = .ok (C₁, S₁)) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) :=
  stepFnTB_conc (symInterp_sound ρ) σ ch hag h

/-- The class-2 window driver. -/
def symEvalWindowTB (TB : SymTables) :
    Nat → SymState → SymConfig → Nat × SymState × SymConfig
  | 0, S, C => (0, S, C)
  | budget + 1, S, C =>
      match stepFnSTB TB S C with
      | .error _ => (0, S, C)
      | .ok (C', S') =>
          let (n, S'', C'') := symEvalWindowTB TB budget S' C'
          (n + 1, S'', C'')

/-- **THE PACK-CONDITIONED REFINEMENT THEOREM** — the shipped
template + the `SymTables.Agrees` premise (equality on the four
tables; see the slice-3 docstring for why not sub-table). -/
theorem symEvalWindowTB_refines :
    ∀ {TB : SymTables} {budget : Nat} {S : SymState} {C : SymConfig}
      {n : Nat} {S' : SymState} {C' : SymConfig},
      symEvalWindowTB TB budget S C = (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        TB.Agrees σ →
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S', ch) := by
  intro TB budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch hag
      simp only [symEvalWindowTB, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch hag
      simp only [symEvalWindowTB] at h
      rcases hstep : stepFnSTB TB S C with q | ⟨C₁, S₁⟩ <;> rw [hstep] at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · simp only [] at h
        rcases hrec : symEvalWindowTB TB budget S₁ C₁ with ⟨m, S₂, C₂⟩
        rw [hrec] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := stepFnSTB_sound ρ σ ch hag hstep
        simp only [stepFnIter, h1, Bind.bind, Except.bind]
        exact ih hrec ρ σ ch hag

/-- The projection-form corollary at the pack. -/
theorem symEvalWindowTB_refines' {TB : SymTables} {budget n : Nat}
    {S : SymState} {C : SymConfig}
    (hn : (symEvalWindowTB TB budget S C).1 = n)
    (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : TB.Agrees σ) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (symEvalWindowTB TB budget S C).2.2,
          γS ρ σ (symEvalWindowTB TB budget S C).2.1, ch) :=
  symEvalWindowTB_refines (by rw [← hn]) ρ σ ch hag

/-! ## Slice 4 — the choice-crossing composition (design §4(ii))

Q3 stays a WINDOW BOUNDARY: windows transport the segments between
consumption points; each pick is crossed by ONE machine step
(`stepFn_pick_generic` below — the class-5 kit half, type-generic
where `MapMem.stepFn_pick_bind` is uint64-shaped), and the spine
`stepFnIter_window_pick_window` chains window–pick–window over a
stream with the consumed prefix quantified. Latitude-bearing fields
stay unprojected (the pick's landing spots — `randomizedElectionTimeout`,
the iteration key cell — are never read by `absRaftNode`), so
handler-level spans stay choice-prefix-quantified with
choice-independent projections. -/

/-- The TYPE-GENERIC map-range pick step (any key/value types, any
binder shape), conditioned on the candidate set, the mandatory check,
the consume, the indexed candidate, and the binder allocation. -/
theorem stepFn_pick_generic {σ σ' : ExecState} {base : Option Loc}
    {produced start : Array GoValue} {cands : Array (GoValue × GoValue)}
    {mand : Bool} {idx : Nat} {ch ch' : Choices} {ko vo : Option String}
    {kt vt : Ty} {body : Stmt} {env env' : LocalEnv}
    {k : Machine.Cont} {kv vv : GoValue}
    (hcands : mapIterCandidates σ kt vt base produced = .ok cands)
    (hne : cands.isEmpty = false)
    (hmand : mapIterMandatoryRemains σ kt cands start = .ok mand)
    (hconsume : Choices.consume ch
      (cands.size + (if mand then 0 else 1)) = (idx, ch'))
    (hget : cands[idx]? = some (kv, vv))
    (hbind : bindIterVars env.pushScope σ ko vo kt vt kv vv
      = .ok (env', σ')) :
    stepFn σ
      (.next (.mapIterK ko vo kt vt body base produced start env k)) ch
      = .ok (.exec body env'
          (.mapIterK ko vo kt vt body base (produced.push kv) start env k),
        σ', ch') := by
  simp only [stepFn, Choices.consumeAt_mapIter, hcands, Bind.bind,
    Except.bind, hne, Bool.false_eq_true, if_false, hmand, hconsume,
    hget, hbind, pure, Except.pure]

/-- **THE HANDLER SPINE**: pre-window (stream-invariant), one pick
step (consumes the prefix head), post-window (stream-invariant) —
composed over the quantified prefix. Every handler-level span is an
iteration of this shape (one application per consumption point). -/
theorem stepFnIter_window_pick_window {n₁ n₂ : Nat}
    {σ₀ σ₁ σ₂ σ₃ : ExecState} {c₀ c₁ c₂ c₃ : Machine.Config}
    {ch ch' : Choices}
    (hw1 : ∀ ch, stepFnIter n₁ σ₀ c₀ ch = .ok (c₁, σ₁, ch))
    (hpick : stepFn σ₁ c₁ ch = .ok (c₂, σ₂, ch'))
    (hw2 : ∀ ch, stepFnIter n₂ σ₂ c₂ ch = .ok (c₃, σ₃, ch)) :
    stepFnIter (n₁ + 1 + n₂) σ₀ c₀ ch = .ok (c₃, σ₃, ch') :=
  GoLean.Surface.stepFnIter_chain
    (GoLean.Surface.stepFnIter_chain (hw1 ch)
      (GoLean.Surface.stepFnIter_one hpick))
    (hw2 ch')

end GoLean.Sym
