import GoLean.GoCore.State

namespace GoLean.GoCore

open GoLean

/-- Depth bound for the type-directed operations (`normalizeValueForTy`,
`valueEq`, `defaultValue`, `Ty.mentionsUnsupported`, and — since the
snapshot-validation slice — `isNormalForTy`, whose depth accounting must
stay in lockstep with `normalizeValueForTyFuel`'s arm-for-arm; arc-final
audit addition 2026-08-04). Since the de-WF
restructure (2026-08-03, sub-branch audit wording) it is decremented once
per NESTING LEVEL — a `.defined` resolution, an `.array` descent, or the
leaf itself — never per element or field (siblings share the decremented
budget through the parameterized list helpers), so it still bounds nesting
DEPTH, not value size. Measured budget shifts vs the pre-restructure
accounting, all fail-closed and unreachable from Go source: a pure
`.defined` chain now supports 1023 links (was 1024); `[1]…[1]int` array
nesting now bounded at depth 1023 (was unbounded); flat leaves at literal
fuel 0 now fail (previously succeeded — the wrappers always seed 1024, so
only direct fuel-0 calls see this). `Ty.mentionsUnsupported`, previously
budget-free total recursion, now shares this budget and fails CLOSED
(`true`) at depth 1024+ types. Go type definitions cannot form
value-containment cycles, so any well-formed program stays far under the
bound. Chosen over a type-environment-acyclicity well-formedness proof for
uniformity with `execStmt`'s fuel (design decision 2026-07-18; see
docs/2026-07-18_totality-fuel-decision.md). -/
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

/-- Go's TWO-index slice-expression bounds check, with the runtime's exact
messages and check ORDER (oracle-pinned 2026-07-25, arc
`wrong-answers-builtins`): the HIGH bound first — negative renders `[:h]`
with no suffix, over the limit renders `[:h] with <limitName> <limit>` —
then the LOW: negative renders `[l:]` (Go omits the high there), else
`[l:h]`. `limitName` is `length` for strings/arrays, `capacity` for
slices. Returns the checked bounds. -/
def checkSliceBounds (limitName : String) (limit : Nat) (low high : Int) :
    Except GoError (Nat × Nat) := do
  if high < 0 then
    panic s!"runtime error: slice bounds out of range [:{high}]"
  if high > limit then
    panic s!"runtime error: slice bounds out of range [:{high}] with {limitName} {limit}"
  if low < 0 then
    panic s!"runtime error: slice bounds out of range [{low}:]"
  if low > high then
    panic s!"runtime error: slice bounds out of range [{low}:{high}]"
  return (low.toNat, high.toNat)

/-- Go's THREE-index (full) slice-expression bounds check after the
max-vs-capacity check: HIGH against max (negative `[:h:]`, over `[:h:m]`),
then LOW (negative `[l::]`, over `[l:h:]`) — the runtime's exact messages,
oracle-pinned 2026-07-25. -/
def checkSliceBounds3 (max : Nat) (low high : Int) :
    Except GoError (Nat × Nat) := do
  if high < 0 then
    panic s!"runtime error: slice bounds out of range [:{high}:]"
  if high > max then
    panic s!"runtime error: slice bounds out of range [:{high}:{max}]"
  if low < 0 then
    panic s!"runtime error: slice bounds out of range [{low}::]"
  if low > high then
    panic s!"runtime error: slice bounds out of range [{low}:{high}:]"
  return (low.toNat, high.toNat)

/-- The full-slice MAX bound against its limit: negative renders `[::m]`
with no suffix, over renders `[::m] with <limitName> <limit>` — `capacity`
for slices, `length` for arrays (pre-merge audit 2026-07-26 caught the
hardcoded "capacity" diverging on array bases; oracle-pinned). -/
def checkSliceMax (limitName : String) (limit : Nat) (max : Int) :
    Except GoError Nat := do
  if max < 0 then
    panic s!"runtime error: slice bounds out of range [::{max}]"
  if max > limit then
    panic s!"runtime error: slice bounds out of range [::{max}] with {limitName} {limit}"
  return max.toNat

/-- Go's `utf8.DecodeRuneInString` at a byte offset, with range-over-string
semantics: an invalid, surrogate, overlong, or truncated encoding yields
U+FFFD with width 1 (the accept-range table of `unicode/utf8`;
oracle-pinned by `strings/range-invalid-utf8`). Returns (rune, width). -/
def decodeRuneAt (s : GoString) (off : Nat) : Int × Nat :=
  -- Out-of-range reads yield a sentinel that fails every range check.
  let b (i : Nat) : Nat := ((s.bytes[off + i]?).map (·.toNat)).getD 0x100
  let cont (x lo hi : Nat) : Bool := lo ≤ x && x ≤ hi
  let bad : Int × Nat := (0xFFFD, 1)
  let b0 := b 0
  if b0 < 0x80 then (Int.ofNat b0, 1)
  else if b0 < 0xC2 then bad
  else if b0 ≤ 0xDF then
    let b1 := b 1
    if cont b1 0x80 0xBF then
      (Int.ofNat (((b0 - 0xC0) <<< 6) + (b1 - 0x80)), 2)
    else bad
  else if b0 ≤ 0xEF then
    let b1 := b 1
    let lo1 := if b0 == 0xE0 then 0xA0 else 0x80
    let hi1 := if b0 == 0xED then 0x9F else 0xBF
    let b2 := b 2
    if cont b1 lo1 hi1 && cont b2 0x80 0xBF then
      (Int.ofNat (((b0 - 0xE0) <<< 12) + ((b1 - 0x80) <<< 6) + (b2 - 0x80)), 3)
    else bad
  else if b0 ≤ 0xF4 then
    let b1 := b 1
    let lo1 := if b0 == 0xF0 then 0x90 else 0x80
    let hi1 := if b0 == 0xF4 then 0x8F else 0xBF
    let b2 := b 2
    let b3 := b 3
    if cont b1 lo1 hi1 && cont b2 0x80 0xBF && cont b3 0x80 0xBF then
      (Int.ofNat (((b0 - 0xF0) <<< 18) + ((b1 - 0x80) <<< 12)
        + ((b2 - 0x80) <<< 6) + (b3 - 0x80)), 4)
    else bad
  else bad

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
  let (low, high) ← checkSliceBounds "length" value.length low high
  return .string (value.slice low high)

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
  -- Go's exact index message (same renderer as arrays; the old plain
  -- "slice index out of bounds" was a latent divergence found by the
  -- unwinding-arc audit's probes, fixed in arc `wrong-answers-builtins`).
  let i ← (do
    if index < 0 then indexOutOfRangePanic index slice.len
    else pure index.toNat)
  if i < slice.len then
    match slice.base with
    | some base => return .index base (Int.ofNat (slice.offset + i))
    | none => stuck s!"malformed GoCore nil slice with length {slice.len}"
  else
    indexOutOfRangePanic index slice.len

def sliceFromSlice (slice : SliceValue) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  validateSlice slice
  match max with
  | none =>
      let (low, high) ← checkSliceBounds "capacity" slice.cap low high
      return .slice {
        base := slice.base,
        offset := slice.offset + low,
        len := high - low,
        cap := slice.cap - low
      }
  | some max =>
      let max ← checkSliceMax "capacity" slice.cap max
      let (low, high) ← checkSliceBounds3 max low high
      return .slice {
        base := slice.base,
        offset := slice.offset + low,
        len := high - low,
        cap := max - low
      }

def sliceFromArray (base : Loc) (length : Nat) (low high : Int) (max : Option Int) :
    Except GoError GoValue := do
  match max with
  | none =>
      let (low, high) ← checkSliceBounds "length" length low high
      return .slice {
        base := some base,
        offset := low,
        len := high - low,
        cap := length - low
      }
  | some max =>
      let max ← checkSliceMax "length" length max
      let (low, high) ← checkSliceBounds3 max low high
      return .slice {
        base := some base,
        offset := low,
        len := high - low,
        cap := max - low
      }

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

/-- Deep canonicalization for DYNAMIC-TYPE identity (interfaces campaign
S3): resolve alias chains everywhere in the type structure, stopping at
identity-bearing `.defined` names. Two types denote the same Go dynamic
type iff their canonical forms are `BEq` — box tags, assert targets, and
method-set receivers all compare in canonical form. EVERY arm consumes
fuel, so the budget bounds COMBINED alias-and-structure depth, not alias
chains alone (the docstring claimed otherwise until the pre-merge audit
2026-07-31, finding 10, measured the real horizon at ~512 interleaved
levels). Exhaustion yields `.unsupported`, which `canonicalDynamicTy`
rejects at boxing time: identity must never be decided on a partly
resolved type. -/
def canonicalTyFuel : Nat → ExecState → Ty → Ty
  | fuel + 1, state, .defined name =>
      (match TypeEnv.lookup state.types name with
       | some (.alias target) => canonicalTyFuel fuel state target
       | _ => .defined name)
  | fuel + 1, state, .pointer elem => .pointer (canonicalTyFuel fuel state elem)
  | fuel + 1, state, .slice elem => .slice (canonicalTyFuel fuel state elem)
  | fuel + 1, state, .array n elem => .array n (canonicalTyFuel fuel state elem)
  | fuel + 1, state, .map k v =>
      .map (canonicalTyFuel fuel state k) (canonicalTyFuel fuel state v)
  | fuel + 1, state, .funcType ps rs =>
      .funcType (ps.map (canonicalTyFuel fuel state))
        (rs.map (canonicalTyFuel fuel state))
  -- Fuel exhausted on a type that still needs resolving: fail closed.
  | 0, _, .defined _ => .unsupported "canonical type: type nesting too deep"
  | 0, _, .pointer _ => .unsupported "canonical type: type nesting too deep"
  | 0, _, .slice _ => .unsupported "canonical type: type nesting too deep"
  | 0, _, .array _ _ => .unsupported "canonical type: type nesting too deep"
  | 0, _, .map _ _ => .unsupported "canonical type: type nesting too deep"
  | 0, _, .funcType _ _ => .unsupported "canonical type: type nesting too deep"
  | _, _, other => other

def canonicalTy (state : ExecState) (typ : Ty) : Ty :=
  canonicalTyFuel typeResolutionFuel state typ

/-- Fuel-structural worker for `Ty.mentionsUnsupported` (de-WF restructure,
2026-08-03: the `attach`-based nested recursion compiled well-founded, which
the kernel cannot reduce). Recursion is structural on the fuel; exhaustion
answers `true` — FAIL CLOSED, an unresolvable type must never become a
boxing tag. -/
def Ty.mentionsUnsupportedFuel : Nat → Ty → Bool
  | 0, _ => true
  | fuel + 1, ty =>
    match ty with
    | .unsupported _ => true
    | .pointer e => Ty.mentionsUnsupportedFuel fuel e
    | .slice e => Ty.mentionsUnsupportedFuel fuel e
    | .array _ e => Ty.mentionsUnsupportedFuel fuel e
    | .map k v => Ty.mentionsUnsupportedFuel fuel k || Ty.mentionsUnsupportedFuel fuel v
    | .funcType ps rs =>
        ps.any (fun t => Ty.mentionsUnsupportedFuel fuel t)
          || rs.any (fun t => Ty.mentionsUnsupportedFuel fuel t)
    | _ => false

-- Downstream-unfolding pin: the wrapper+worker+budget simp pattern every
-- proof site uses must keep working (literal offset-matching included).
example : Ty.mentionsUnsupportedFuel 3 (.pointer .bool) = false := by
  simp [Ty.mentionsUnsupportedFuel]

/-- Does the type mention an `.unsupported` leaf? Used to fail closed at
boxing time (an unrenderable dynamic type must never become a tag).
Type syntax is small, so the `typeResolutionFuel` DEPTH budget is ample
(one unit per nesting level, siblings share); the worker fails CLOSED
(`true`) on exhaustion. -/
def Ty.mentionsUnsupported (ty : Ty) : Bool :=
  Ty.mentionsUnsupportedFuel typeResolutionFuel ty

/-- The canonical dynamic-type tag for boxing, fail-closed. -/
def canonicalDynamicTy (state : ExecState) (typ : Ty) : Except GoError Ty := do
  let c := canonicalTy state typ
  if c.mentionsUnsupported then
    unsupported s!"interface conversion for dynamic type {repr typ}"
  else
    return c

/-- Is the type uncomparable in Go's runtime sense (a slice, map, or func
anywhere in its resolved structure)? Drives the `comparing uncomparable
type` panic on interface equality and the map hash panic. Struct fields
and array elements recurse; interfaces themselves are comparable (their
comparison may panic deeper, at their own dynamic types).

Three-valued on purpose: `none` is UNKNOWN — a `.defined` name with no
`TypeDef` (today: any imported/stdlib named type, since the frontend emits
declarations only for the analyzed package) or fuel exhaustion. Callers
must fail CLOSED on `none`; the old `Bool` version answered "comparable",
which silently accepted `m[sort.IntSlice{1,2}] = 1` where Go panics
(pre-merge audit 2026-07-31, finding 11). -/
def tyUncomparableFuel : Nat → ExecState → Ty → Option Bool
  | _, _, .slice _ => some true
  | _, _, .map _ _ => some true
  | _, _, .funcType _ _ => some true
  | fuel + 1, state, .defined name =>
      (match TypeEnv.lookup state.types name with
       | some (.alias t) => tyUncomparableFuel fuel state t
       | some (.defined t) => tyUncomparableFuel fuel state t
       | some (.struct fields) =>
           -- Any DEFINITELY-uncomparable field decides it; otherwise an
           -- unknown field leaves the whole struct unknown.
           fields.foldl
             (fun acc f =>
               match acc, tyUncomparableFuel fuel state f.typ with
               | some true, _ => some true
               | _, some true => some true
               | none, _ => none
               | _, none => none
               | some false, some false => some false)
             (some false)
       -- An interface-typed field is itself comparable (its own dynamic
       -- type decides at comparison time), as is `.unsupported`-free
       -- structure; an ABSENT declaration is unknown.
       | some (.interfaceDef _) => some false
       | some (.unsupported _) => none
       | none => none)
  | fuel + 1, state, .array _ e => tyUncomparableFuel fuel state e
  | 0, _, .defined _ => none
  | 0, _, .array _ _ => none
  | _, _, _ => some false

def tyUncomparable (state : ExecState) (typ : Ty) : Option Bool :=
  tyUncomparableFuel typeResolutionFuel state typ

/-- The canonical EMPTY interface: satisfied by every type BY DESIGN (Go's
`any`), so it needs no wire declaration and renders as `interface {}`.
`"any"` is what the native frontend emits; `"empty_interface"` is the legacy
key still used by hand-written GoCore terms in `Tests/` and the proof
layer. -/
def isEmptyInterfaceName (id : TypeId) : Bool :=
  id.key == "any" || id.key == "empty_interface"

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
      | .interface name => if isEmptyInterfaceName name then "interface {}" else name.key
      | .defined name => name.key
      | .array length elem => s!"[{length}]{goTypeNameForMessageFuel fuel state elem}"
      | .funcType params results =>
          -- Go renders the signature: `func()`, `func(int) bool`,
          -- `func() (int, error)` (message-fidelity, 2026-07-30).
          let ps := ", ".intercalate (params.map (goTypeNameForMessageFuel fuel state))
          let base := s!"func({ps})"
          match results with
          | [] => base
          | [r] => s!"{base} {goTypeNameForMessageFuel fuel state r}"
          | rs => s!"{base} ({", ".intercalate (rs.map (goTypeNameForMessageFuel fuel state))})"
      | .unsupported feature => feature
  | 0, _, _ => "<type nesting too deep>"

def goTypeNameForMessage (state : ExecState) (typ : Ty) : String :=
  goTypeNameForMessageFuel typeResolutionFuel state typ

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

/-- An interface-RECEIVER method's interface name — the marker that a
`MethodInfo` is a dispatch anchor (a requirement) rather than a concrete
implementation. Used by `dynamicDispatch?`; satisfaction requirements come
from the interface DECLARATION, not from this table. -/
def methodRecvInterfaceName? (state : ExecState) (method : MethodInfo) : Option String :=
  match resolveDefinedAliases state method.recv with
  | .interface id => some id.key
  | _ => none

/-- A concrete method's receiver in canonical form (Ty-keyed identity,
interfaces campaign S3 — was a rendered name string). `none` for
interface receivers (those are requirements, not implementations). -/
def methodRecvDynamicTy? (state : ExecState) (method : MethodInfo) : Option Ty :=
  match canonicalTy state method.recv with
  | .interface _ => none
  | recv => some recv

/-- The DECLARED method set of an interface name, or `none` when the program
records no declaration for it — the distinction a `Bool`-shaped requirement
list structurally could not make (pre-merge audit 2026-07-31, finding 0). -/
def interfaceDeclaredMethods? (state : ExecState) (id : TypeId) : Option (Array MethodSig) :=
  match TypeEnv.lookup state.types id with
  | some (.interfaceDef methods) => some methods
  | _ => none

/-- Go's method-set rule: the method set of `*T` includes `T`'s value-
receiver methods (the reverse is FALSE — a value box never satisfies a
pointer-receiver method; probed 2026-07-30, design note Q3). The method set
of `*T` exists only when `T` is a defined non-pointer, non-interface type —
`**T` has an EMPTY method set, so the fallback declines a pointer pointee
(pre-merge audit 2026-07-31, finding 4). The lookup result records whether
the receiver must be auto-dereferenced (a pointer box dispatching to a
value-receiver method). -/
def concreteMethodForDynamic? (state : ExecState) (dynTy : Ty) (methodName : String) :
    Option (MethodInfo × Bool) :=
  let direct := state.methods.foldl
    (fun found method =>
      match found with
      | some _ => found
      | none =>
          if method.name == methodName &&
              methodRecvDynamicTy? state method == some dynTy then
            some (method, false)
          else none)
    none
  match direct, dynTy with
  | some hit, _ => some hit
  -- `*T` inherits `T`'s value-receiver methods — but ONLY when `T` is a
  -- defined non-pointer, non-interface type. `**T`'s method set is empty.
  | none, .pointer (.pointer _) => none
  | none, .pointer (.interface _) => none
  | none, .pointer elem =>
      state.methods.foldl
        (fun found method =>
          match found with
          | some _ => found
          | none =>
              if method.name == methodName &&
                  methodRecvDynamicTy? state method == some elem then
                some (method, true)
              else none)
        none
  | none, _ => none

def hasConcreteMethod (state : ExecState) (dynTy : Ty) (methodName : String) : Bool :=
  (concreteMethodForDynamic? state dynTy methodName).isSome

/-- A concrete method's declared signature: its executable `Func`'s
parameters MINUS the receiver, its results (both canonicalized), and its
VARIADIC marker. `none` when no body is recorded (a dispatch anchor or a
quarantined declaration) — which is a failure to match, never a silent
pass. -/
def concreteMethodSignature? (state : ExecState) (info : MethodInfo) :
    Option (Array Ty × Array Ty × Bool) :=
  match findFunctionIn? state.functions info.funcId with
  | some f =>
      some ((f.args.extract 1 f.args.size).map (fun p => canonicalTy state p.typ),
            f.results.map (fun p => canonicalTy state p.typ),
            f.variadic)
  | none => none

/-- Does `dynTy` carry a method matching this REQUIREMENT — name AND full
signature? Comparing names alone accepted a differently typed method
(pre-merge audit 2026-07-31, finding 2); comparing only the param/result
TYPES accepted `M(xs []int)` for a required `M(xs ...int)` and vice versa,
since both render the param as `[]int` — Go treats them as different
methods, so the machine ran a dispatch on a program Go aborts (pre-merge
audit 2026-07-31, finding 0). -/
def satisfiesMethodSig (state : ExecState) (dynTy : Ty) (req : MethodSig) : Bool :=
  match concreteMethodForDynamic? state dynTy req.name with
  | some (info, _) =>
      match concreteMethodSignature? state info with
      | some (params, results, variadic) =>
          params == req.params.map (canonicalTy state) &&
            results == req.results.map (canonicalTy state) &&
            variadic == req.variadic
      | none => false
  | none => false

/-- Is `dynTy`'s METHOD SET fully recorded on the wire?

Methods can only be declared in their type's OWN package, and the frontend
emits a `TypeDef` for every named type the analyzed package declares — so
for a `.defined` name the type environment KNOWS, the method table holds
that type's complete method set and a "no such method" answer is real
information. For a `.defined` name it does NOT know (today: every
imported/stdlib named type, which reaches GoCore as a bare `.defined` with
no declaration — BUG-008's premise), the empty method table means UNKNOWN,
not empty: `*strings.Builder` really does have `String() string`.
Answering `false` from it was a definite answer derived from nothing —
the wrong comma-ok boolean, and a FABRICATED `missing method` panic on a
program Go runs to completion (pre-merge audit 2026-07-31, finding 8).

Types that are not `.defined` (basics, slices, maps, pointers to those,
`**T`) can carry no methods in Go at all, so an empty method set is
correct — and a pointer inherits its POINTEE's declarations, so `*T` is
known exactly when `T` is. -/
def dynamicMethodSetRecorded (state : ExecState) (dynTy : Ty) : Bool :=
  let base := match dynTy with
    | .pointer elem => elem
    | other => other
  match base with
  | .defined name => (TypeEnv.lookup state.types name).isSome
  | _ => true

/-- Could a method be PROMOTED into `dynTy`'s method set from an embedded
field? Promotion is unmodeled (BUG-007), so a satisfaction check that would
answer `false` on such a type must fail CLOSED rather than answer — the
comma-ok assert turned that `false` into a silent wrong answer (pre-merge
audit 2026-07-31, finding 5). Value and pointer forms both, since `*Outer`
promotes too. -/
def dynamicHasEmbeddedFields (state : ExecState) (dynTy : Ty) : Bool :=
  let base := match dynTy with
    | .pointer elem => elem
    | other => other
  match base with
  | .defined name =>
      match TypeEnv.lookup state.types name with
      | some (.struct fields) => fields.any (fun f => f.embedded)
      | _ => false
  | _ => false

/-- The FIRST requirement of `interfaceName` that `dynTy` does not meet, in
the interface's own (name-sorted) method order — `none` means it satisfies
the interface. Go names exactly this method in its assert-panic message.

Fails CLOSED, never vacuously true, in three situations:
  * no declaration is recorded for a non-empty interface name (the wire
    carries one for every interface it mentions; an absent one means the
    program used an interface the frontend did not export);
  * the answer would be "unsatisfied" on a type whose method set is not
    RECORDED at all (an imported/stdlib named type — BUG-008/BUG-009);
  * the answer would be "unsatisfied" on a type whose method set may be
    extended by unmodeled PROMOTION (BUG-007).

The last two guard the `some name` (definite-FALSE) answer specifically:
satisfaction found is still sound, since a recorded matching method really
is in the method set. -/
def firstUnsatisfiedMethod? (state : ExecState) (dynTy : Ty) (interfaceName : TypeId) :
    Except GoError (Option String) := do
  if isEmptyInterfaceName interfaceName then
    return none
  match interfaceDeclaredMethods? state interfaceName with
  | none =>
      unsupported s!"interface {interfaceName.key} has no recorded declaration"
  | some reqs =>
      let missing := reqs.foldl
        (fun found req =>
          match found with
          | some _ => found
          | none => if satisfiesMethodSig state dynTy req then none else some req.name)
        none
      match missing with
      | none => return none
      | some name =>
          if !dynamicMethodSetRecorded state dynTy then
            unsupported s!"interface satisfaction for {goTypeNameForMessage state dynTy}: \
its method set is NOT on the wire (an imported named type carries no \
declaration), so `missing method {name}' would be an answer derived from \
no information (BUG-009)"
          else if dynamicHasEmbeddedFields state dynTy then
            unsupported s!"interface satisfaction for {goTypeNameForMessage state dynTy}: \
method {name} may be PROMOTED from an embedded field (BUG-007, unmodeled)"
          else
            return (some name)

def dynamicImplementsInterface (state : ExecState) (dynTy : Ty) (interfaceName : TypeId) :
    Except GoError Bool := do
  return (← firstUnsatisfiedMethod? state dynTy interfaceName).isNone

/-- Apply the (already fuel-decremented) element normalizer to each list
element in order; fail-closed on the first error. Structural on the LIST and
parameterized over `f` rather than mutually recursive — the de-WF recipe
(2026-08-03): the old mutual block (list helpers recursing at unchanged
fuel) had no common structural argument, so Lean compiled it well-founded,
and `Acc.rec` reduces nowhere — which blocked kernel evaluation of the
interpreter (`docs/2026-08-03_sem-adequacy-arc.md`, slice-1 spike).
Crucially the fuel still bounds only NESTING DEPTH, not node count: a first
de-WF attempt charged fuel per element and was caught making `Progress` —
and with it the ∀-config theorem — false at configs past the budget. -/
def normalizeListWith (f : GoValue → Except GoError GoValue) :
    List GoValue → Except GoError (Array GoValue)
  | value :: rest => do
      let head ← f value
      let tail ← normalizeListWith f rest
      return #[head] ++ tail
  | [] => return #[]

/-- Normalize struct field values pairwise with the (already
fuel-decremented) normalizer, checking field-name alignment. -/
def normalizeFieldsWith (f : Ty → GoValue → Except GoError GoValue) :
    List FieldDef → List (String × GoValue) →
    Except GoError (Array (String × GoValue))
  | field :: fieldRest, (actualField, value) :: valueRest => do
      if actualField != field.name then
        stuck s!"struct value field mismatch: expected {field.name}, got {actualField}"
      let head ← f field.typ value
      let tail ← normalizeFieldsWith f fieldRest valueRest
      return #[(field.name, head)] ++ tail
  | _, _ => return #[]

/-- Struct-shape checks for normalization at a defined struct type, with the
(already fuel-decremented) field normalizer. -/
def normalizeStructValueWith (f : Ty → GoValue → Except GoError GoValue)
    (name : TypeId) (fields : Array FieldDef) : GoValue → Except GoError GoValue
  | .struct actual fieldsValue => do
      if actual != name then
        stuck s!"struct value type mismatch: expected {name.key}, got {actual.key}"
      if fieldsValue.size != fields.size then
        stuck s!"struct value field count mismatch: expected {fields.size}, got {fieldsValue.size}"
      .struct name <$> normalizeFieldsWith f fields.toList fieldsValue.toList
  | value => stuck s!"expected struct {name.key} value, got {repr value}"

-- Total via fuel, STRUCTURALLY on the fuel: recursion into child values goes
-- through the parameterized list/field helpers above at DECREMENTED fuel, so
-- the definition is plain structural recursion (kernel-reducible) while the
-- fuel still bounds nesting DEPTH only — one unit per array/struct level or
-- defined-type resolution, never per element. The public
-- `normalizeValueForTy` seeds `typeResolutionFuel` and keeps its signature.
def normalizeValueForTyFuel : Nat → ExecState → Ty → GoValue → Except GoError GoValue
  | 0, _, _, _ => unsupported "normalizing: type nesting too deep"
  | _ + 1, _, .int kind, .int value _ => return .int (kind.normalize value) kind
  | _ + 1, _, .int kind, value => stuck s!"expected {kind.name} value, got {repr value}"
  | fuel + 1, state, .array length elem, .array values => do
      if values.size != length then
        stuck s!"array value length mismatch: expected {length}, got {values.size}"
      .array <$> normalizeListWith (normalizeValueForTyFuel fuel state elem) values.toList
  | _ + 1, _, .array length _, value => stuck s!"expected array({length}) value, got {repr value}"
  | _ + 1, _, .interface _, value => return value
  -- Func values carry their own identity; nil is the zero value.
  | _ + 1, _, .funcType _ _, .funcVal fid captured => return .funcVal fid captured
  | _ + 1, _, .funcType _ _, .nil => return .nil
  | _ + 1, _, .funcType _ _, value => stuck s!"expected func value, got {repr value}"
  | fuel + 1, state, .defined name, value => do
      match TypeEnv.lookup state.types name with
      | some (.alias target) => normalizeValueForTyFuel fuel state target value
      | some (.defined target) => normalizeValueForTyFuel fuel state target value
      | some (.struct fields) =>
          normalizeStructValueWith (normalizeValueForTyFuel fuel state) name fields value
      | some (.unsupported feature) => unsupported s!"normalizing {feature}"
      | some (.interfaceDef _) => unsupported s!"normalizing at interface type {name.key}"
      | none => unsupported s!"normalizing unknown defined type {name.key}"
  | _ + 1, _, .unsupported feature, _ => unsupported s!"normalizing {feature}"
  | _ + 1, _, _, value => return value



example (σ : ExecState) (kind : IntKind) :
    normalizeValueForTyFuel 5 σ (.int kind) (.int 3 kind)
      = .ok (.int (kind.normalize 3) kind) := by
  simp [normalizeValueForTyFuel]; rfl

def normalizeValueForTy (state : ExecState) (ty : Ty) (value : GoValue) :
    Except GoError GoValue :=
  normalizeValueForTyFuel typeResolutionFuel state ty value

/-! ### Self-normalization check (sem-adequacy arc slice 3, 2026-08-04)

`isNormalForTyFuel types ty v` decides `normalizeValueForTyFuel fuel σ ty v
= .ok v` (for any `σ` with `σ.types = types`) WITHOUT a generic `GoValue`
equality: it mirrors the normalizer arm-for-arm and compares only at the
leaves (`Int`/`IntKind`/`TypeId`/`String` — all `DecidableEq`, so the
whole family is kernel-reducible; the derived `BEq GoValue` is
WF-compiled/opaque and must never sit on a kernel-evaluation path). It is
deliberately parameterized by the TYPE ENVIRONMENT, not the state: the
normalizer provably reads nothing else, and taking `TypeEnv` makes the
well-formedness component built on this check invariant along
types-preserving steps BY REWRITING rather than by a congruence lemma.

The proved direction is soundness (`isNormalForTyFuel_sound`,
`StateWf.lean`): check true ⇒ the normalizer returns the value UNCHANGED.
The converse (the check never rejects a value the normalizer would fix)
is not needed by any theorem; the machine's snapshot validation built on
this check is differential-validated instead (arc doc, slice-3 entry). -/

/-- Element-wise check, parameterized over the (already fuel-decremented)
element checker — the de-WF recipe's shape, mirroring `normalizeListWith`. -/
def isNormalListWith (f : GoValue → Bool) : List GoValue → Bool
  | [] => true
  | v :: rest => f v && isNormalListWith f rest

/-- Field-wise check mirroring `normalizeFieldsWith`: field-name alignment
plus the per-field value check. Length mismatch fails closed (the struct
wrapper checks sizes first, exactly like the normalizer). -/
def isNormalFieldsWith (f : Ty → GoValue → Bool) :
    List FieldDef → List (String × GoValue) → Bool
  | [], [] => true
  | field :: fieldRest, (actualField, v) :: valueRest =>
      decide (actualField = field.name) && f field.typ v
        && isNormalFieldsWith f fieldRest valueRest
  | _, _ => false

/-- Does `normalizeValueForTyFuel fuel σ ty v` (for `σ.types = types`)
return `.ok v` — i.e. is `v` self-normalized at `ty`? Structural on the
fuel, mirroring the normalizer arm-for-arm. -/
def isNormalForTyFuel : Nat → TypeEnv → Ty → GoValue → Bool
  | 0, _, _, _ => false
  | _ + 1, _, .int kind, .int value k =>
      decide (kind.normalize value = value) && decide (kind = k)
  | _ + 1, _, .int _, _ => false
  | fuel + 1, types, .array length elem, .array values =>
      decide (values.size = length)
        && isNormalListWith (isNormalForTyFuel fuel types elem) values.toList
  | _ + 1, _, .array _ _, _ => false
  | _ + 1, _, .interface _, _ => true
  | _ + 1, _, .funcType _ _, .funcVal _ _ => true
  | _ + 1, _, .funcType _ _, .nil => true
  | _ + 1, _, .funcType _ _, _ => false
  | fuel + 1, types, .defined name, value =>
      match TypeEnv.lookup types name with
      | some (.alias target) => isNormalForTyFuel fuel types target value
      | some (.defined target) => isNormalForTyFuel fuel types target value
      | some (.struct fields) =>
          match value with
          | .struct actual fieldsValue =>
              decide (actual = name) && decide (fieldsValue.size = fields.size)
                && isNormalFieldsWith (isNormalForTyFuel fuel types)
                    fields.toList fieldsValue.toList
          | _ => false
      | some (.unsupported _) => false
      | some (.interfaceDef _) => false
      | none => false
  | _ + 1, _, .unsupported _, _ => false
  | _ + 1, _, _, _ => true

@[inherit_doc isNormalForTyFuel]
def isNormalForTy (types : TypeEnv) (ty : Ty) (value : GoValue) : Bool :=
  isNormalForTyFuel typeResolutionFuel types ty value

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

-- `lookup` deleted (reshape S4): variable reads are `Machine.Step.evalVar`
-- (control-side env lookup + `loadLoc`), never a state-side name lookup.

-- Total via fuel: only the `.defined → .alias` chain recurses; fuel bounds it.
def convertValueToTyFuel : Nat → ExecState → Ty → GoValue → Except GoError GoValue
  | _, _, .int kind, .int value _ => return .int (kind.normalize value) kind
  | _, _, .int kind, other => stuck s!"expected integer operand for conversion to {kind.name}, got {repr other}"
  | fuel + 1, state, .defined name, value =>
      match TypeEnv.lookup state.types name with
      | some (.alias target) => convertValueToTyFuel fuel state target value
      | some (.defined target) => convertValueToTyFuel fuel state target value
      | some (.struct _) => unsupported s!"conversion to struct type {name.key}"
      | some (.unsupported feature) => unsupported s!"conversion to {feature}"
      | some (.interfaceDef _) => unsupported s!"conversion to interface type {name.key}"
      | none => unsupported s!"conversion to unknown defined type {name.key}"
  -- Identity conversions Go permits at runtime with no representation
  -- change (`string(s)` — surfaced by interfaces/error-interface's
  -- `string(e.Error())` shape, 2026-07-30).
  | _, _, .string, .string s => return .string s
  -- Conversion INTO an interface type at a machine site (map key slots,
  -- assert results): a box or nil interface passes as-is (the frontend's
  -- to-interface wrap already built the box); a raw value here is a
  -- lowering bug — fail closed, never silently box without a dynamic
  -- type (interfaces campaign, 2026-07-30).
  | _, _, .interface _, value@(.interface _ _) => return value
  | _, _, .interface _, .nil => return .nil
  | _, _, .interface id, value =>
      stuck s!"raw value reached interface conversion to {id.key}: {repr value}"
  | 0, _, .defined _, _ => unsupported "conversion: type nesting too deep"
  | _, _, .unsupported feature, _ => unsupported s!"conversion to {feature}"
  | _, _, other, _ => unsupported s!"conversion to {repr other}"

def convertValueToTy (state : ExecState) (typ : Ty) (value : GoValue) :
    Except GoError GoValue :=
  convertValueToTyFuel typeResolutionFuel state typ value

/-- Default value for each struct field with the (already fuel-decremented)
default builder, in declaration order. Structural on the list; part of the
de-WF recipe (see `normalizeListWith`). -/
def defaultFieldsWith (f : Ty → Except GoError GoValue) :
    List FieldDef → Except GoError (Array (String × GoValue))
  | field :: rest => do
      let head ← f field.typ
      let tail ← defaultFieldsWith f rest
      return #[(field.name, head)] ++ tail
  | [] => return #[]

-- Total via fuel, STRUCTURALLY on the fuel (de-WF recipe — see the
-- normalize block; fuel bounds nesting DEPTH only). The array case computes
-- the element default once and replicates it (`defaultValue` is pure, so all
-- elements are equal); the `length == 0` guard preserves the original
-- behavior of not evaluating the element type for an empty array.
def defaultValueFuel : Nat → ExecState → Ty → Except GoError GoValue
  | 0, _, _ => unsupported "default value: type nesting too deep"
  | _ + 1, _, .bool => return .bool false
  | _ + 1, _, .int kind => return .int 0 kind
  | _ + 1, _, .string => return .string GoString.empty
  | fuel + 1, state, .array length elem => do
      if length == 0 then
        return .array #[]
      let elemDefault ← defaultValueFuel fuel state elem
      return .array (Array.replicate length elemDefault)
  | _ + 1, _, .slice _ => return .slice { base := none, offset := 0, len := 0, cap := 0 }
  | _ + 1, _, .map _ _ => return .map { base := none }
  | _ + 1, _, .pointer _ => return .nil
  | _ + 1, _, .funcType _ _ => return .nil
  | _ + 1, _, .interface _ => return .nil
  | fuel + 1, state, .defined name => do
      match TypeEnv.lookup state.types name with
      | some (.struct fields) =>
          .struct name <$> defaultFieldsWith (defaultValueFuel fuel state) fields.toList
      | some (.alias target) => defaultValueFuel fuel state target
      | some (.defined target) => defaultValueFuel fuel state target
      | some (.unsupported feature) => unsupported s!"default value for {feature}"
      | some (.interfaceDef _) => unsupported s!"default value at interface type {name.key}"
      | none => unsupported s!"default value for unknown defined type {name.key}"
  | _ + 1, _, .unsupported feature => unsupported s!"default value for {feature}"



example (σ : ExecState) (kind : IntKind) :
    defaultValueFuel 5 σ (.int kind) = .ok (.int 0 kind) := by
  simp [defaultValueFuel]; rfl

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
      -- Defined-over-struct stays `.struct`; a `.defined` here would be a
      -- struct literal at a NON-struct named type — fail closed (identity
      -- tagging for defined-over-defined-struct is unresolved; see the
      -- TypeDef.defined docstring).
      | some (.defined _) => unsupported s!"struct literal for defined type {name.key} over non-struct underlying"
      | some (.interfaceDef _) => unsupported s!"struct literal for interface type {name.key}"
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
  | .interface dynTy inner =>
      match resolveDefinedAliases state targetTy with
      | .interface interfaceName =>
          if ← dynamicImplementsInterface state dynTy interfaceName then
            return (.interface dynTy inner, true)
          else
            return (failed, false)
      | _ =>
          -- Concrete target: canonical dynamic-type identity (S3 —
          -- structural BEq, no name rendering, so slice/map/array
          -- dynamic types assert correctly too).
          if dynTy == canonicalTy state targetTy then
            return (inner, true)
          else
            return (failed, false)
  | other => unsupported s!"type assertion from non-interface value {repr other}"

def dynamicTypeNameForMessage (state : ExecState) : GoValue → String
  | .interface dynTy _ => goTypeNameForMessage state dynTy
  | .nil => "nil"
  | other => s!"{repr other}"

/-- Go's failed-type-assert panic message, in all FOUR of its real shapes
(probed 2026-07-31, `.tmp/fix/probe/assert`; the machine had one shape, with
a hardcoded `interface {}` source and no missing-method form at all —
pre-merge audit 2026-07-31, findings 7 and 8):

  * interface target, non-nil operand:
    `interface conversion: main.T is not main.J: missing method N`
    (the source's static type is NOT printed; `missing` names the first
    unmet requirement in the interface's method order)
  * interface target, nil operand:
    `interface conversion: interface is nil, not main.J`
  * concrete target: `interface conversion: <source> is <dyn>, not <target>`,
    where `<source>` is the operand's STATIC interface type — `interface {}`
    only when that really is the empty interface.

`sourceTy` is `none` when the lowering did not carry the operand's static
type; the message then falls back to the empty-interface spelling, which is
what every pre-existing GoCore term meant. -/
def typeAssertPanicMessage (state : ExecState) (value : GoValue) (targetTy : Ty)
    (sourceTy : Option Ty) (missingMethod : Option String) : String :=
  let sourceName :=
    match sourceTy with
    | some t => goTypeNameForMessage state t
    | none => "interface {}"
  match resolveDefinedAliases state targetTy, value with
  | .interface _, .nil =>
      "interface conversion: interface is nil, not " ++ goTypeNameForMessage state targetTy
  | .interface _, _ =>
      let missing :=
        match missingMethod with
        | some m => s!": missing method {m}"
        | none => ""
      "interface conversion: " ++ dynamicTypeNameForMessage state value ++
        " is not " ++ goTypeNameForMessage state targetTy ++ missing
  | _, _ =>
      "interface conversion: " ++ sourceName ++ " is " ++
        dynamicTypeNameForMessage state value ++ ", not " ++
        goTypeNameForMessage state targetTy

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

/-- Compare list elements pairwise with the (already fuel-decremented)
comparator; callers guarantee equal, checked lengths. Structural on the
list; part of the de-WF recipe (see `normalizeListWith`). -/
def valueEqListWith (f : GoValue → GoValue → Except GoError Bool) :
    List GoValue → List GoValue → Except GoError Bool
  | leftValue :: leftRest, rightValue :: rightRest => do
      if ← f leftValue rightValue then
        valueEqListWith f leftRest rightRest
      else
        return false
  | _, _ => return true

/-- Compare struct fields pairwise with the (already fuel-decremented)
comparator, checking field-name alignment on both sides. -/
def valueEqFieldsWith (f : Ty → GoValue → GoValue → Except GoError Bool) :
    List FieldDef → List (String × GoValue) → List (String × GoValue) →
    Except GoError Bool
  | field :: fieldRest, (leftName, leftValue) :: leftRest, (rightName, rightValue) :: rightRest => do
      if leftName != field.name then
        stuck s!"left struct equality field mismatch: expected {field.name}, got {leftName}"
      if rightName != field.name then
        stuck s!"right struct equality field mismatch: expected {field.name}, got {rightName}"
      if ← f field.typ leftValue rightValue then
        valueEqFieldsWith f fieldRest leftRest rightRest
      else
        return false
  | _, _, _ => return true

-- Total via fuel, STRUCTURALLY on the fuel (de-WF recipe — see the
-- normalize block; fuel bounds nesting DEPTH only). The public `valueEq`
-- seeds `typeResolutionFuel`, keeping its original signature so call sites
-- are unchanged.
def valueEqFuel : Nat → ExecState → Ty → GoValue → GoValue → Except GoError Bool
    | 0, _, _, _, _ => unsupported "equality: type nesting too deep"
    | _ + 1, _, .bool, .bool left, .bool right => return left == right
    | _ + 1, _, .bool, left, right => stuck s!"bool equality expected bool operands, got {repr left} and {repr right}"
    | _ + 1, _, .int _, .int left _, .int right _ => return left == right
    | _ + 1, _, .int kind, left, right => stuck s!"{kind.name} equality expected int operands, got {repr left} and {repr right}"
    | _ + 1, _, .string, .string left, .string right => return left == right
    | _ + 1, _, .string, left, right => stuck s!"string equality expected string operands, got {repr left} and {repr right}"
    -- Go: func values are comparable only against nil.
    | _ + 1, _, .funcType _ _, .nil, .nil => return true
    | _ + 1, _, .funcType _ _, .funcVal _ _, .nil => return false
    | _ + 1, _, .funcType _ _, .nil, .funcVal _ _ => return false
    | _ + 1, _, .funcType _ _, left, right =>
        stuck s!"func values are not comparable: {repr left} and {repr right}"
    | _ + 1, _, .pointer _, .addr left, .addr right => return left == right
    | _ + 1, _, .pointer _, .nil, .nil => return true
    | _ + 1, _, .pointer _, .addr _, .nil => return false
    | _ + 1, _, .pointer _, .nil, .addr _ => return false
    | _ + 1, _, .pointer _, left, right => stuck s!"pointer equality expected pointer/nil operands, got {repr left} and {repr right}"
    | fuel + 1, state, .array length elem, .array left, .array right => do
        if left.size != length then
          stuck s!"left array equality length mismatch: expected {length}, got {left.size}"
        if right.size != length then
          stuck s!"right array equality length mismatch: expected {length}, got {right.size}"
        valueEqListWith (valueEqFuel fuel state elem) left.toList right.toList
    | _ + 1, _, .array length _, left, right =>
        stuck s!"array equality expected array({length}) operands, got {repr left} and {repr right}"
    | _ + 1, _, .slice _, .slice left, .slice right => do
        validateSlice left
        validateSlice right
        match left.base, right.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil slices are not comparable"
    | _ + 1, _, .slice _, .slice left, .nil => do
        validateSlice left
        return left.base.isNone
    | _ + 1, _, .slice _, .nil, .slice right => do
        validateSlice right
        return right.base.isNone
    | _ + 1, _, .slice _, left, right => stuck s!"slice equality expected slice/nil operands, got {repr left} and {repr right}"
    | _ + 1, _, .map _ _, .map left, .map right =>
        match left.base, right.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil maps are not comparable"
    | _ + 1, _, .map _ _, .map left, .nil => return left.base.isNone
    | _ + 1, _, .map _ _, .nil, .map right => return right.base.isNone
    | _ + 1, _, .map _ _, left, right => stuck s!"map equality expected map/nil operands, got {repr left} and {repr right}"
    | _ + 1, _, .interface _, .nil, .nil => return true
    | _ + 1, _, .interface _, .nil, _ => return false
    | _ + 1, _, .interface _, _, .nil => return false
    -- Box-vs-box (S3, Perennial `go_eq_interface` shape): different
    -- canonical dynamic types → false, no value comparison. Same dynamic
    -- type → Go first checks the DYNAMIC type's comparability (resolved
    -- through defined types: slices/maps/funcs anywhere inside panic at
    -- runtime under the DYNAMIC name — `comparing uncomparable type
    -- main.T`), then compares the payloads AT the dynamic type.
    | fuel + 1, state, .interface _,
        .interface dynL innerL, .interface dynR innerR =>
      if dynL != dynR then
        return false
      else
        match tyUncomparable state dynL with
        | some true =>
            throw (.panic s!"runtime error: comparing uncomparable type {goTypeNameForMessage state dynL}")
        -- UNKNOWN comparability (an undeclared defined type) falls through
        -- to `valueEqFuel`, whose `.defined` arm already fails closed with
        -- the precise "unknown defined type" reason.
        | _ => valueEqFuel fuel state dynL innerL innerR
    | _ + 1, _, .interface _, left, right => unsupported s!"interface equality for {repr left} and {repr right}"
    | fuel + 1, state, .defined name, left, right => do
        match TypeEnv.lookup state.types name with
        | some (.alias target) => valueEqFuel fuel state target left right
        -- Runtime values of a defined type share the underlying
        -- representation; static typing guarantees both sides have the
        -- same defined type, so equality is equality at the underlying.
        | some (.defined target) => valueEqFuel fuel state target left right
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
                valueEqFieldsWith (valueEqFuel fuel state) fields.toList leftFields.toList rightFields.toList
            | _, _ => stuck s!"struct equality expected struct {name.key} operands, got {repr left} and {repr right}"
        | some (.unsupported feature) => unsupported s!"equality for {feature}"
        | some (.interfaceDef _) => unsupported s!"equality at interface type {name.key}"
        | none => unsupported s!"equality for unknown defined type {name.key}"
    | _ + 1, _, .unsupported feature, _, _ => unsupported s!"equality for {feature}"



example (σ : ExecState) (a b : Bool) :
    valueEqFuel 5 σ .bool (.bool a) (.bool b) = .ok (a == b) := by
  simp [valueEqFuel]; rfl

def valueEq (state : ExecState) (ty : Ty) (left right : GoValue) : Except GoError Bool :=
  valueEqFuel typeResolutionFuel state ty left right

/-- Go's `typehash` is VALUE-directed, not type-directed: it recurses into
struct fields and array elements, so a statically COMPARABLE aggregate key
panics when a box nested anywhere inside it has an uncomparable dynamic
type — and the panic names that INNER type (probed 2026-07-31,
`.tmp/fix/probe/hash`; the precheck used to match only a key that was itself
a box — pre-merge audit 2026-07-31, finding 1).

The walk is structural over the VALUE (fuel bounds only the type-level
comparability check inside `tyUncomparable`), and stops at the first
offending component in Go's own hashing order: struct fields in declaration
order, array elements in index order. -/
inductive KeyHashability where
  /-- No unhashable component anywhere in the key. -/
  | hashable
  /-- Definitely unhashable; the name is what Go's panic prints. -/
  | unhashable (typeName : String)
  /-- Comparability of some component could not be decided (a defined type
  with no declaration): the caller must fail CLOSED. -/
  | unknown (typeName : String)
  deriving Repr, BEq

mutual
  def valueHashability (state : ExecState) : GoValue → KeyHashability
    | .interface dynTy inner =>
        match tyUncomparable state dynTy with
        | some true => .unhashable (goTypeNameForMessage state dynTy)
        | some false => valueHashability state inner
        | none => .unknown (goTypeNameForMessage state dynTy)
    | .struct _ fields => valueHashabilityFields state fields.toList
    | .array values => valueHashabilityList state values.toList
    | _ => .hashable

  /-- Struct fields in declaration order — Go hashes them in that order. -/
  def valueHashabilityFields (state : ExecState) :
      List (String × GoValue) → KeyHashability
    | [] => .hashable
    | (_, v) :: rest =>
        match valueHashability state v with
        | .hashable => valueHashabilityFields state rest
        | other => other

  def valueHashabilityList (state : ExecState) : List GoValue → KeyHashability
    | [] => .hashable
    | v :: rest =>
        match valueHashability state v with
        | .hashable => valueHashabilityList state rest
        | other => other
end

/-- Go's TWO hash-panic phrasings, keyed on the map's CURRENT entry count —
NOT on insert-vs-access (probed 2026-07-31; the previous rule was
generalized from empty maps only — pre-merge audit 2026-07-31, finding 6).
`mapassign` never short-circuits, so it always takes the `runtime error:`
form; `mapaccess`/`mapdelete` take the `mapKeyError` shortcut — the colon
form — only while `h == nil || h.count == 0`. A map emptied by `delete`
returns to the colon form, so the predicate is the live entry count. -/
def hashPanicMessage (typeName : String) (alwaysHashes : Bool) : String :=
  if alwaysHashes then
    s!"runtime error: hash of unhashable type {typeName}"
  else
    s!"hash of unhashable type: {typeName}"

/-- The hashability precheck Go performs BEFORE any comparison. `nonEmpty`
is the map's live entry count being nonzero; `isInsert` marks `mapassign`,
which never short-circuits. Split out of `mapEntryIndex?` so the NIL-map
paths (which never reach the entry scan) can run it too — Go panics there
as well. -/
def checkKeyHashable (state : ExecState) (key : GoValue)
    (isInsert : Bool) (nonEmpty : Bool) : Except GoError Unit :=
  match valueHashability state key with
  | .unhashable name => throw (.panic (hashPanicMessage name (isInsert || nonEmpty)))
  | .unknown name => unsupported s!"map key hashability for unknown defined type {name}"
  | .hashable => pure ()

-- Not recursive; total now that valueEq is. The for-loop is fine in a plain def.
def mapEntryIndex? (state : ExecState) (keyTy : Ty) (entries : Array (GoValue × GoValue))
    (key : GoValue) (isInsert : Bool := false) : Except GoError (Option Nat) := do
  checkKeyHashable state key isInsert (!entries.isEmpty)
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

/-! ### Operator result helpers

Value-level result computation for the arithmetic/bitwise/shift operators.
Moved here from `Eval.lean` (reshape S1 motion, 2026-07-23) so the
fine-grained machine (`Machine.lean`) can share them with the interpreter
without depending on the big-step module slated for deletion. Pure motion —
no behavior change. -/

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

/-- Read the visible elements of a slice, in order. Moved here from `Eval.lean`'s
mutual cluster (it was never recursive — it only loads through the slice's
backing locations), same motion commit as the helpers above. -/
def sliceVisibleValues (state : ExecState) (slice : SliceValue) :
    Except GoError (Array GoValue) := do
  validateSlice slice
  let mut values := #[]
  for i in [:slice.len] do
    values := values.push (← loadLoc state (← sliceIndexLoc slice (Int.ofNat i)))
  return values

/-! The following were also never recursive; moved out of `Eval.lean`'s mutual
cluster (reshape S2 motion, 2026-07-23) for sharing with `Machine`/`stepFn`.
Pure motion — no behavior change. -/

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
  -- A NIL map still hashes the key: Go panics `hash of unhashable type: X`
  -- (the `h == nil` arm of mapKeyError; probed 2026-07-31) before returning
  -- the zero value.
  | none => do
      checkKeyHashable state key (isInsert := false) (nonEmpty := false)
      return (← defaultValue state valueTy, false)
  | some (_, entries) =>
      match ← mapEntryIndex? state keyTy entries key with
      | some i =>
          match entries[i]? with
          | some (_, value) => return (value, true)
          | none => stuck s!"missing map entry at index {i}"
      | none => return (← defaultValue state valueTy, false)

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

def dynamicDispatch? (state : ExecState) (func : Func) (argValues : Array GoValue) :
    Except GoError (Option (Func × Array GoValue)) := do
  match methodInfoByFuncId? state func.id with
  | none => return none
  | some method =>
      match methodRecvInterfaceName? state method with
      | none => return none
      | some _ =>
          match argValues[0]? with
          | some (GoValue.interface dynTy inner) =>
              match concreteMethodForDynamic? state dynTy method.name with
              | some (concrete, needsDeref) =>
                  let targetFunc ←
                    match findFunctionIn? state.functions concrete.funcId with
                    | some func => pure func
                    | none => stuck s!"GoCore dynamic method target not found: {concrete.funcId.key}"
                  -- A pointer box dispatching to a value-receiver method
                  -- auto-dereferences the receiver (Go's *T ⊇ T method
                  -- set; nil pointer panics as a nil dereference).
                  let recvValue ←
                    if needsDeref then
                      match inner with
                      | .addr loc => loadLoc state loc
                      | .nil => throw (.panic "runtime error: invalid memory address or nil pointer dereference")
                      | other => stuck s!"pointer-box receiver expected address, got {repr other}"
                    else
                      pure inner
                  return some (targetFunc, argValues.set! 0 recvValue)
              | none => stuck s!"dynamic type {goTypeNameForMessage state dynTy} has no method {method.name}"
          -- Calling a method on a NIL interface: Go's runtime nil
          -- dereference panic (probe-pinned; the stub body behind this
          -- is unreachable and fails stuck if a bug ever reaches it).
          | some GoValue.nil =>
              throw (.panic "runtime error: invalid memory address or nil pointer dereference")
          | _ => return none

/-- Structurally-recursive insertion into a `le`-sorted list (de-WF,
2026-08-03): `List.mergeSort` is well-founded-compiled in core Lean, hence
KERNEL-irreducible — it blocked `Terminates` discharge on every sorting
program while the elaborator's smart unfolding hid the problem. -/
def insertLe {α : Type _} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertLe le x ys

/-- Structural insertion sort — the machine's `sortSlice` sort.

Relation to the previous `List.mergeSort`, stated honestly (audit wording,
2026-08-03): both produce `le`-sorted permutations of the input, and by
sorted-permutation uniqueness (`Laws/Values.eq_of_perm_of_pairwise`) the
outputs are EQUAL whenever equal-keyed elements are equal — which holds at
the machine's call site because an int slice's backing array is normalized
to one element kind on store, making the loaded `(Int × IntKind)` pairs
equal-kinded. That argument is carried by the lemma layer
(`sortLe_pairs_eq_of_perm` mirrors `mergeSort_pairs_eq_of_perm`), not by a
theorem literally equating the two sorts; the differential (fresh 873/873
after the swap) checks the behavior against real Go. Complexity note,
accepted: O(n²) worst case vs mergeSort's O(n log n) — irrelevant at
corpus/raft sizes and invisible to the oracle. -/
def sortLe {α : Type _} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertLe le x (sortLe le xs)

/-! ## Elaborator sealing of the value-walk WRAPPERS (de-WF, 2026-08-03)

The fuel families above are structurally recursive so the KERNEL can
evaluate the interpreter (`Terminates` discharge; the old well-founded
compilation's `Acc.rec` reduced nowhere). Left fully reducible, though, the
ELABORATOR's `whnf`/`isDefEq` dives into 1024-literal fuel towers during
unification — heartbeat blowups and perturbed `go_walk` matching. Sealing
the FUEL functions is unworkable (equation-lemma generation is per-module
and blocked by irreducibility), so the WRAPPERS are sealed instead: goals
only ever contain wrapper applications (via `storeLoc`/`applyStrictOp`/…),
so defeq stops before any literal budget is exposed, while
`simp [<wrapper>, <fuel fn>, typeResolutionFuel]` still unfolds both by
their equations. Kernel evaluation is unaffected (attributes are invisible
to the kernel); an elaboration site that genuinely wants full reduction
opts in with `with_unfolding_all`. -/
attribute [irreducible] Ty.mentionsUnsupported normalizeValueForTy
  defaultValue valueEq isNormalForTy

-- POST-SEAL pins: the exact wrapper+worker+budget simp pattern every
-- downstream proof site relies on (sub-branch audit, 2026-08-03 — the
-- per-family pins above exercise only the workers at small literals; these
-- exercise the sealed wrappers at the real seed, so a change to the seal
-- design or the equation-generation behavior fails HERE, in the defining
-- module, not at some distant proof).
example (σ : ExecState) (kind : IntKind) (v : Int) :
    normalizeValueForTy σ (.int kind) (.int v kind)
      = .ok (.int (kind.normalize v) kind) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
  rfl
example (σ : ExecState) (kind : IntKind) :
    defaultValue σ (.int kind) = .ok (.int 0 kind) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]
  rfl
example (σ : ExecState) (a b : Bool) :
    valueEq σ .bool (.bool a) (.bool b) = .ok (a == b) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]
  rfl
example : Ty.mentionsUnsupported (.pointer .bool) = false := by
  simp [Ty.mentionsUnsupported, Ty.mentionsUnsupportedFuel, typeResolutionFuel]
