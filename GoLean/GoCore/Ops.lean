import GoLean.GoCore.FloatBits
import GoLean.GoCore.State

namespace GoLean.GoCore

open GoLean

/-! ## Type-directed operations: the index descent (C-arc C2, 2026-09-05)

Every operation below that walks a type through the type table
(`defaultValue`, `tySizeAlign`, `tyUncomparable`, `normalizeValueForTy`,
`isNormalForTy`, `convertValueToTy`, `buildStructValue`, `valueEq`) used
to be a FUEL tower: structural on a `Nat` budget seeded at
`typeResolutionFuel = 1024`, refusing on exhaustion (the 2026-07-18
totality decision, `docs/2026-07-18_totality-fuel-decision.md`; the
2026-08-03 de-WF restructure). Gate G-C2 (`docs/2026-09-05_c-arc-c2-
design.md`) replaces the budget with the TABLE'S OWN STRUCTURE:

* `Ty.defined i` names table entry `i`, and the table is dependency-
  ordered (`TypeEnv.WellFounded`, decided at decode): every entry
  depends only on SMALLER indices.
* A type-directed recursion therefore has two layers. The `…Ty` layer is
  STRUCTURAL on the type (only `.array` descends into a subterm; pointer/
  slice/map/chan/func/interface are leaves) and hands `.defined i` to a
  callback. The `…At` layer resolves an INDEX: structural on a `bound`
  that counts the table indices still available to the descent — one is
  consumed per resolution, and the body found is walked by the `…Ty`
  layer with the callback at the smaller bound. Seeded at `types.size`
  (`Ops.lean`'s public wrappers), the descent never exhausts on a well-
  founded table: a dependency chain from index `i` has at most `i + 1`
  entries, and `i < types.size`. The `0` arm is a NAMED refusal ("not
  dependency-ordered"), reachable only from a hand-built table the
  decoder would have refused — never a default.
* `convertValueToTy` and `buildStructValue` do not recurse at all once
  `.defined` indirections are followed (`TypeEnv.resolve`); `valueEq`
  recurses on the VALUE (Go's `==` on interfaces compares the DYNAMIC
  values, whose types are discovered, not walked), with `TypeEnv.resolve`
  reading the declared body at each step.
* The two structural equalities (`Ty.eqb`, `GoValue.eqb`, `Value.lean`)
  are mutual structural recursions over the nested inductives.

Everything is kernel-reducible (`Nat.rec`/`brecOn`, no `WellFounded.fix`),
so `decide`/`rfl` evaluate closed instances — the property the de-WF
restructure bought with fuel, kept without it. The elaborator seal
(`attribute [irreducible]` on the wrappers) went with the literal budgets
it guarded against. -/

/-- The declared BODY behind a type head, `.defined` indirections
followed through the table: a `TyBody.plain` head is never `.defined`
(it may mention `.defined` BELOW — an array element, a pointer target —
which the consumer resolves when it gets there). -/
inductive TyBody where
  /-- A non-`.defined` head. -/
  | plain (ty : Ty)
  /-- A declared struct: its key (the value tag) and fields. -/
  | struct (name : TypeId) (fields : Array FieldDef)
  /-- A `.defined` naming an interface DECLARATION (a lowering that put
  an interface behind `named`); consumers refuse at it by name. -/
  | interfaceDecl (name : TypeId)
  /-- A `.defined` naming an opaque declaration; consumers refuse with
  the recorded reason. -/
  | opaque (name : TypeId) (reason : String)
  deriving Repr

/-- Follow `.defined` indirections to the declared body. `bound`-structural
(the index descent; seeded at `types.size` by the callers). A
`.defined`-over-`.defined` chain cannot arrive from the frontend
(go/types' `Underlying()` is never a named type), so on a wire program
this resolves in one step; the descent is what keeps it total on ANY
table. -/
def TypeEnv.resolve (types : TypeEnv) (bound : Nat) (ty : Ty) : Except Stop TyBody :=
  -- The type is matched FIRST so a non-`.defined` head resolves without
  -- inspecting `bound` (the equation `resolve types b .bool = .ok (.plain
  -- .bool)` holds for a SYMBOLIC `b`, which is what downstream unfolding
  -- needs); the descent on `bound` is confined to the `.defined` arm.
  match ty with
  | .defined i =>
      match bound with
      | 0 =>
          unsupported s!"type index {i}: the defined-type chain exceeds the table size — typeDefs not dependency-ordered (refused at decode; unreachable on an accepted program)"
      | bound + 1 =>
          match types[i]? with
          | none => unsupported s!"unknown type index {i} (no entry in the type table)"
          | some (name, .struct fields) => pure (.struct name fields)
          | some (_, .defined underlying) => TypeEnv.resolve types bound underlying
          | some (name, .interfaceDef _) => pure (.interfaceDecl name)
          | some (name, .opaqueDecl reason) => pure (.opaque name reason)
  | ty => pure (.plain ty)

/-- Induction on a `Ty` along its ARRAY spine — the one recursive position
of every type layer above (`…Ty`): `.array n e` descends into `e`, every
other constructor is a leaf (the `List Ty` inside `funcType` included).
`Ty` is a nested inductive, which the `induction` tactic refuses; this
is the principle the type-layer lemmas use (`induction ty using
Ty.arrayInduction`). -/
theorem Ty.arrayInduction {motive : Ty → Prop}
    (array : ∀ n e, motive e → motive (.array n e))
    (leaf : ∀ t, (∀ n e, t ≠ .array n e) → motive t) : ∀ t, motive t :=
  Ty.rec (motive_1 := motive) (motive_2 := fun _ => True)
    (leaf _ (by simp)) (fun _ => leaf _ (by simp)) (fun _ => leaf _ (by simp)) (leaf _ (by simp))
    (fun n e ih => array n e ih)
    (fun _ _ => leaf _ (by simp)) (fun _ _ _ _ => leaf _ (by simp)) (fun _ _ _ => leaf _ (by simp))
    (fun _ _ => leaf _ (by simp)) (fun _ _ _ _ _ => leaf _ (by simp)) (fun _ => leaf _ (by simp))
    (fun _ => leaf _ (by simp)) (fun _ => leaf _ (by simp)) (fun _ => leaf _ (by simp))
    trivial (fun _ _ _ _ => trivial)

/-- The refusal every index descent's exhaustion arm raises (unreachable
on a well-founded table, see the section note). -/
def typeIndexExhausted {α : Type} (what : String) (i : TypeIdx) : Except Stop α :=
  unsupported s!"{what}: type index {i} unresolvable within the table's bound — typeDefs not dependency-ordered (refused at decode; unreachable on an accepted program)"

/-! ## Float kind dispatch (floats slice F2, 2026-08-05)

Width dispatch from `FloatKind` into the `FloatBits` kernel. Float
operands are STRICT about kinds everywhere below: Go has no implicit
float conversions, so a kind mismatch (or a float32 bits pattern under a
float64 kind) is a lowering bug and fails closed — never a silent
reinterpretation. This is a deliberate divergence from the int arms'
flexible-kind adoption (`IntKind.compatibleResult` exists for UNTYPED
int literals; float literals always arrive typed). -/

/-- The correctly-rounded rational→format kernel at this kind (constants
and int→float, design note decision 5; float32 single-rounds, never via
binary64). -/
def FloatKind.ratToBits : FloatKind → Int → Nat → Nat
  | .float64, num, den => FloatBits.ratToFloat64 num den
  | .float32, num, den => FloatBits.ratToFloat32 num den

/-- IEEE negation — the sign-bit flip (`fneg`), never `0 - x`. -/
def FloatKind.negBits : FloatKind → Nat → Nat
  | .float64, bits => FloatBits.fneg64 bits
  | .float32, bits => FloatBits.fneg32 bits

/-- Per-op-rounded arithmetic result at matching float kinds (the §3.1
envelope point: every operation rounds to the operand type). float32
computes by exact widening through binary64 and one rounding back —
softfloat64.go:506-517's own definition (innocuous double rounding for
`+ - * /`; design note §6). -/
def floatBinaryResult (opName : String) (op64 op32 : Nat → Nat → Nat)
    (left right : GoValue) : Except Stop GoValue := do
  match left, right with
  | .float lb lk, .float rb rk =>
      if lk == rk then
        match lk with
        | .float64 => return .float (FloatKind.float64.normalizeBits (op64 lb rb)) .float64
        | .float32 => return .float (FloatKind.float32.normalizeBits (op32 lb rb)) .float32
      else
        stuck s!"mismatched {opName} float kinds: {lk.name} and {rk.name}"
  | _, _ => stuck s!"mismatched {opName} operands: {repr left} and {repr right}"

/-- **The `float-bits` primitive** (stdlib slice 3, 2026-09-04; `FloatBitsOp`,
Syntax.lean): `math.Float64bits` and its three siblings as a bit
reinterpretation over the machine's OWN representation. A float IS its
bit pattern (`GoValue.float bits kind`, `bits < 2^kind.bits` by
`FloatKind.normalizeBits` at every construction site), so `*bits` is
`.int bits .uint64`/`.uint32` and `*frombits` is `.float bits kind` — no
arithmetic, no rounding, no canonicalization: NaN payloads (quiet AND
signalling), the sign of zero and the infinities round-trip BIT-EXACT
in both directions, which is the admission condition the audit
attached (`docs/stdlib-admission-register.md`, slice-2 log: «preserve NaN
payloads exactly (deps.go:29 builds nan() from payload
0x7FF8000000000001) and ±0 / quiet/signaling round-trip probes»).

ONE fail-closed arm, disclosed [AGENT]: `*bits` REFUSES the machine's
DEFAULT NaN under EITHER sign (`FloatBits.nan64` = 0x7FF8000000000000 and
its negation 0xFFF8000000000000; `nan32` = 0x7FC00000 / 0xFFC00000).
Latitude inventory R7 narrows every NaN the machine PRODUCES (arithmetic,
conversion) to that one payload — softfloat64.go's own rule, `return
nan64` at every NaN-producing case — while the oracle platform (gc/amd64,
SSE) realizes hardware payloads (first NaN operand's payload;
0xFFF8… "real indefinite" for invalid operations). R7's whole argument
was "payloads are unobservable in-language"; this primitive makes them
observable, so a default-NaN observation is exactly the point where the
machine's narrowing would present as a wrong answer (`Float64bits(zero/zero)`:
machine 0x7FF8000000000000, gc 0xFFF8000000000000). The guard is
SIGN-INSENSITIVE because the machine DOES produce the negated default:
`fneg64` is a bare sign flip (`-(zero/zero)` = 0xFFF8… on the machine,
0x7FF8… in gc — audit fix round A1, 2026-09-05, closed a reported wrong
answer here). The producible-NaN set is therefore exactly {nan64, -nan64}
(and the 32-bit pair): every OTHER NaN pattern can only have entered
through `*frombits` — `floatMinMaxBits` preserves this by returning the
DEFAULT NaN whenever either operand is one (so it refuses downstream) and
transcribing gc/amd64's payload-OR idiom only over frombits payloads
(A1's second family: `Float64bits(min(Float64frombits(0x7FF8…01), 2.5))`
= 0x7FFC000000000001 on both sides). The over-refusal
(`Float64bits(Float64frombits(0x7FF8000000000000))` / `…(0xFFF8…)`, a
legitimate round-trip) is rowed (`builtins/float-bits/{canonical-nan-refused,
neg-canonical-refused}`, BUG-094) and is R7's re-envelope obligation, not
this slice's. -/
def floatBitsApply (op : FloatBitsOp) (v : GoValue) : Except Stop GoValue :=
  match op, v with
  | .f64bits, .float bits .float64 =>
      -- Sign-insensitive: the default NaN and its negation both refuse.
      if bits &&& 0x7FFFFFFFFFFFFFFF == FloatBits.nan64 then
        unsupported s!"{op.name} of the machine's default NaN (0x7FF8000000000000 or its negation): the payload of a machine-PRODUCED NaN is latitude the machine narrows (inventory R7) and gc/amd64 realizes differently — refused rather than reported (rows builtins/float-bits/canonical-nan-refused and neg-canonical-refused)"
      else
        return .int (Int.ofNat bits) .uint64
  | .f32bits, .float bits .float32 =>
      if bits &&& 0x7FFFFFFF == FloatBits.nan32 then
        unsupported s!"{op.name} of the machine's default NaN (0x7FC00000 or its negation): the payload of a machine-PRODUCED NaN is latitude the machine narrows (inventory R7) and gc/amd64 realizes differently — refused rather than reported (rows builtins/float-bits/canonical-nan-refused and neg-canonical-refused)"
      else
        return .int (Int.ofNat bits) .uint32
  | .f64frombits, .int bits .uint64 =>
      -- A uint64 cell is normalized non-negative; a negative here is a
      -- lowering-contract breach, never silently absorbed by `toNat`.
      if bits < 0 then stuck s!"{op.name}: negative operand {bits} at kind uint64 (normalization contract breached)"
      else return .float (FloatKind.float64.normalizeBits bits.toNat) .float64
  | .f32frombits, .int bits .uint32 =>
      if bits < 0 then stuck s!"{op.name}: negative operand {bits} at kind uint32 (normalization contract breached)"
      else return .float (FloatKind.float32.normalizeBits bits.toNat) .float32
  | op, other => stuck s!"{op.name}: operand {repr other} is not of the pinned kind (float64/uint64 or float32/uint32)"

/-- IEEE comparison at matching float kinds: NaN is UNORDERED — every
ordering answers false on a NaN operand (note §4; the corpus pin is
`floats/nan-comparisons`). -/
def floatCompareResult (opName : String) (cmp64 cmp32 : Nat → Nat → Bool)
    (left right : GoValue) : Except Stop Bool := do
  match left, right with
  | .float lb lk, .float rb rk =>
      if lk == rk then
        match lk with
        | .float64 => return cmp64 lb rb
        | .float32 => return cmp32 lb rb
      else
        stuck s!"mismatched {opName} float kinds: {lk.name} and {rk.name}"
  | _, _ => stuck s!"mismatched {opName} operands: {repr left} and {repr right}"

/-- Is any operand a float value? Dispatch guard for `min`/`max`: float
operands take the IEEE fold (`floatMinMax` below), everything else the
`valueLess` fold. (Until triage L3, 2026-08-19, the float side was a
fail-closed refusal — the design-note §9 reason, "a `valueLess`-based
fold would silently get NaN wrong", is exactly why the float fold uses
the softfloat comparison kernel instead.) -/
def anyFloatOperand (vs : List GoValue) : Bool :=
  vs.any fun v => match v with | .float _ _ => true | _ => false

/-- IEEE `min`/`max` selection over two float operands (triage L3,
spec §Min_and_max's special-case table, pinned by
`spec-examples-stmt/min-max-float-specials`), BIT-TRANSCRIBED since the
stdlib-slice-3 audit fix round A1 (2026-09-05) from gc/amd64's lowering
(`cmd/compile/internal/ssa/_gen/AMD64.rules` @ go1.26.5, "Floating-point
min is tricky"):

    t1  = MINSD x y      -- SSE MINSD: x < y ? x : y  (unordered or equal → y)
    t2  = MINSD t1 x
    min = POR t1 t2      -- bitwise OR
    max = -min(-x, -y)

which realizes the spec's table — a NaN operand propagates, `min(-0, +0)`
is `-0` (the OR keeps the sign bit), `max(-0, +0)` is `+0` — AND fixes the
NaN PAYLOAD gc reports through `math.Float64bits`: the OR of the two
operands' bits (`min(Float64frombits(0x7FF8000000000001), 2.5)` =
0x7FFC000000000001), where the previous "return the NaN operand" rule
reported 0x7FF8000000000001 — a wrong answer once `float-bits` made
payloads observable (audit A1). The pure-Go `runtime.fmin` (other
ports) returns the NaN operand instead: this is a (b)-pin to the oracle
platform, inventory R7's amendment. THE DEFAULT-NaN PRE-CHECK: if EITHER
operand is the machine's default NaN (either sign — the only NaNs the
machine produces, `floatBitsApply`'s doc), the result is the default NaN
itself, NOT the OR: gc's default NaN carries the OPPOSITE sign
(0xFFF8…), so an OR over it would report a sign-wrong pattern the
downstream `*bits` guard could not recognize; returning the default NaN
keeps the producible-NaN set at {nan64, -nan64} and lets the guard refuse
it by name. Value semantics are unchanged either way (a NaN is a NaN).
Non-float or kind-mismatched pairs are stuck (go/types makes them
unreachable from typed Go). -/
def floatMinMaxBits (isMin : Bool) (kind : FloatKind) (a b : Nat) : Nat :=
  let (isNaN, defaultNaN, neg, lt) :=
    match kind with
    | .float64 =>
        ((fun x => (FloatBits.fcmp64 x x).2), FloatBits.nan64, FloatBits.fneg64,
          fun x y => FloatBits.flt64 x y)
    | .float32 =>
        ((fun x => (FloatBits.fcmp32 x x).2), FloatBits.nan32, FloatBits.fneg32,
          fun x y => FloatBits.flt32 x y)
  let signMask : Nat := match kind with | .float64 => 0x7FFFFFFFFFFFFFFF | .float32 => 0x7FFFFFFF
  if (isNaN a && a &&& signMask == defaultNaN) || (isNaN b && b &&& signMask == defaultNaN) then
    defaultNaN
  else
    -- MINSD x y = x < y ? x : y (unordered or equal yields the SECOND operand).
    let minsd := fun (x y : Nat) => if lt x y then x else y
    let amd64Min := fun (x y : Nat) =>
      let t1 := minsd x y
      let t2 := minsd t1 x
      t1 ||| t2
    if isMin then amd64Min a b else neg (amd64Min (neg a) (neg b))

def floatMinMax (isMin : Bool) : GoValue → GoValue → Except Stop GoValue
  | .float a ka, .float b kb =>
      if ka == kb then return .float (floatMinMaxBits isMin ka a b) ka
      else stuck s!"mismatched min/max float kinds: {ka.name} and {kb.name}"
  | l, r => stuck s!"mismatched min/max float operands: {repr l} and {repr r}"

def indexOutOfRangePanic (index : Int) (length : Nat) : Except Stop α :=
  if index < 0 then
    panic s!"runtime error: index out of range [{index}]"
  else
    panic s!"runtime error: index out of range [{index}] with length {length}"

def arrayIndexNat (values : Array GoValue) (index : Int) : Except Stop Nat := do
  if index < 0 then
    indexOutOfRangePanic index values.size
  let i := index.toNat
  if i < values.size then
    return i
  else
    indexOutOfRangePanic index values.size

def arrayGet (values : Array GoValue) (index : Int) : Except Stop GoValue := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some value => return value
  | none => indexOutOfRangePanic index values.size

def arraySet (values : Array GoValue) (index : Int) (value : GoValue) :
    Except Stop (Array GoValue) := do
  let i ← arrayIndexNat values index
  -- No per-element coercion (A3): the ROOT store normalizes the whole
  -- array at the cell's declared type, which is where element typing lives.
  match values[i]? with
  | some _ => return values.set! i value
  | none => indexOutOfRangePanic index values.size

def natFromNonnegativeInt (context : String) (value : Int) : Except Stop Nat := do
  if value < 0 then
    panic context
  return value.toNat

/-! ## The R16 pins, read from THE platform (A5)

The maximum allocatable size and the channel header size are fields of
`gcAmd64` (`Platform.lean`), where their envelope statements live
(fidelity decision 5(b), [USER] 2026-08-31; probe matrix
`docs/evidence/2026-09-02_t5-maxalloc-probes/`). The three names below are
what the machine's arms read. -/

/-- `platform.maxAllocBytes` (R16). -/
def maxAllocBytes : Nat := platform.maxAllocBytes

/-- `platform.chanHeaderBytes` (R16's channel half). -/
def chanHeaderBytes : Nat := platform.chanHeaderBytes

/-- `platform.intExclusiveUpperBound` (R1's width: 2^63 at 64 bits). -/
def intExclusiveUpperBound : Nat := platform.intExclusiveUpperBound

/-- Round `offset` up to a multiple of `align` (`align ≥ 1`). -/
def alignUpTo (offset align : Nat) : Nat :=
  if align == 0 then offset else (offset + align - 1) / align * align

/-- gc's struct layout (`gcSizes.Offsetsof` + `Sizeof`'s struct arm):
fields in order, each at its alignment; the struct's alignment is the
max field alignment; a ZERO-SIZE final field at a non-zero offset
occupies one byte (`if offs > 0 && size == 0 { size = 1 }`, so
`struct{a int64; z struct{}}` is 16 bytes, not 8); the total is rounded
up to the struct's alignment. `fieldSize` is the size/alignment oracle
for a field's TYPE — the caller passes the type layer at the struct's
own index bound (`tySizeAlignTy p (tySizeAlignAt p types bound)`, the
`defaultFieldsWith` recipe), so this loop is structural on the field
list and the field COUNT never touches the descent (audit fix round F1,
2026-09-02: a previous shared-fuel loop refused flat structs of ≥1023
fields as "nesting too deep"). Accumulators: end offset of the fields
laid so far, max alignment so far, and the LAST field's offset and size
(the final-field rule needs both). Non-empty field lists only (the
caller handles `struct{}` = (0, 1)). -/
def structSizeAlignWith (fieldSize : Ty → Except Stop (Nat × Nat)) :
    List FieldDef → Nat → Nat → Nat → Nat → Except Stop (Nat × Nat)
  | [], _, maxAlign, lastOffset, lastSize =>
      let lastSize := if lastOffset > 0 && lastSize == 0 then 1 else lastSize
      pure (alignUpTo (lastOffset + lastSize) maxAlign, maxAlign)
  | field :: rest, offset, maxAlign, _, _ => do
      let (size, align) ← fieldSize field.typ
      let fieldOffset := alignUpTo offset align
      structSizeAlignWith fieldSize rest (fieldOffset + size) (max maxAlign align)
        fieldOffset size

/-- Size and alignment of a type in BYTES under platform `p`'s layout
(go/types `gcSizes` with `WordSize = p.wordBytes`, `MaxAlign = p.maxAlign`
— `deps/go/src/go/types/gcsizes.go`, transcribed arm for arm: pointer-
shaped types are one word, strings and interfaces two, slices three; the
`sync` primitives are gc's struct sizes, `unsafe.Sizeof`-probed, which do
not depend on the word size — their fields are fixed-width). The R16
pin's LAYOUT half (envelope on `gcAmd64`, `Platform.lean`). The TYPE
layer of the index descent (section note): structural on the type, a
struct's field list walked by `structSizeAlignWith`, `.defined` handed to
`atDefined`. FAIL-CLOSED: an `.unsupported` type, an unknown defined
type or an untyped integer kind is a cause-naming refusal, never a
guessed size. -/
def tySizeAlignTy (p : Platform) (atDefined : TypeIdx → Except Stop (Nat × Nat)) :
    Ty → Except Stop (Nat × Nat)
  | .bool => pure (1, 1)
  | .int kind =>
      match kind.bitsAt p with
      | some bits => pure (bits / 8, bits / 8)
      | none => unsupported s!"allocation-size computation: untyped integer kind {kind.name}"
  | .float kind => pure (kind.bits / 8, kind.bits / 8)
  | .string => pure (2 * p.wordBytes, p.maxAlign)
  | .array n elem => do
      let (size, align) ← tySizeAlignTy p atDefined elem
      pure (n * size, align)
  | .slice _ => pure (3 * p.wordBytes, p.maxAlign)
  | .map _ _ => pure (p.wordBytes, p.maxAlign)
  | .chan _ _ => pure (p.wordBytes, p.maxAlign)
  | .pointer _ => pure (p.wordBytes, p.maxAlign)
  | .funcType _ _ _ => pure (p.wordBytes, p.maxAlign)
  | .interface _ => pure (2 * p.wordBytes, p.maxAlign)
  | .defined i => atDefined i
  | .unsupported feature => unsupported s!"allocation-size computation: {feature}"
  | .sync .mutex => pure (8, 4)
  | .sync .rwmutex => pure (24, 4)
  | .sync .waitGroup => pure (16, 8)
  | .sync .once => pure (12, 4)

/-- The INDEX layer of `tySizeAlignTy`: size/alignment of the type
declared at index `i`, descending only to smaller indices (`bound`-
structural; section note). -/
def tySizeAlignAt (p : Platform) (types : TypeEnv) : Nat → TypeIdx → Except Stop (Nat × Nat)
  | 0, i => typeIndexExhausted "allocation-size computation" i
  | bound + 1, i =>
      match types[i]? with
      | some (_, .struct fields) =>
          if fields.isEmpty then pure (0, 1)
          else structSizeAlignWith (tySizeAlignTy p (tySizeAlignAt p types bound)) fields.toList 0 1 0 0
      | some (_, .defined underlying) => tySizeAlignTy p (tySizeAlignAt p types bound) underlying
      | some (_, .interfaceDef _) => pure (2 * p.wordBytes, p.maxAlign)
      | some (_, .opaqueDecl feature) =>
          unsupported s!"allocation-size computation: {feature}"
      | none => unsupported s!"allocation-size computation: unknown type index {i}"

/-- Size and alignment under platform `p`, over the type table (the
descent seeded at `types.size`). -/
def tySizeAlign (p : Platform) (types : TypeEnv) (ty : Ty) : Except Stop (Nat × Nat) :=
  tySizeAlignTy p (tySizeAlignAt p types types.size) ty

/-- The byte size of a type under the R16 pin (`tySizeAlign` at THE
platform). -/
def tySizeBytes (types : TypeEnv) (ty : Ty) : Except Stop Nat := do
  let (size, _) ← tySizeAlign platform types ty
  pure size

/-- Go's TWO-index slice-expression bounds check, with the runtime's exact
messages and check ORDER (oracle-pinned 2026-07-25, arc
`wrong-answers-builtins`): the HIGH bound first — negative renders `[:h]`
with no suffix, over the limit renders `[:h] with <limitName> <limit>` —
then the LOW: negative renders `[l:]` (Go omits the high there), else
`[l:h]`. `limitName` is `length` for strings/arrays, `capacity` for
slices. Returns the checked bounds. -/
def checkSliceBounds (limitName : String) (limit : Nat) (low high : Int) :
    Except Stop (Nat × Nat) := do
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
    Except Stop (Nat × Nat) := do
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
    Except Stop Nat := do
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

/-- The full rune decode of a string: `decodeRuneAt` at successive
offsets until the bytes are exhausted — spec §Conversions to and from a
string type, "Converting a value of a string type to a slice of runes
type yields a slice containing the individual Unicode code points of
the string" (invalid encodings yield U+FFFD, one byte at a time, per
the same accept-range table as range-over-string). Total: the offset
strictly advances (every decode width is ≥ 1, and `max 1 w` makes that
structural for the termination checker without changing any value). -/
def runesOfStringAux (s : GoString) (off : Nat) (acc : Array Int) : Array Int :=
  if _h : off < s.length then
    runesOfStringAux s (off + max 1 (decodeRuneAt s off).2)
      (acc.push (decodeRuneAt s off).1)
  else acc
termination_by s.length - off
decreasing_by
  have : 1 ≤ max 1 (decodeRuneAt s off).2 := Nat.le_max_left _ _
  omega

def runesOfString (s : GoString) : Array Int :=
  runesOfStringAux s 0 #[]

def stringByteGet (value : GoString) (index : Int) : Except Stop GoValue := do
  if index < 0 then
    indexOutOfRangePanic index value.length
  let i := index.toNat
  match value.byte? i with
  | some byte => return .int (Int.ofNat byte.toNat) .uint8
  | none => indexOutOfRangePanic index value.length

def stringSlice (value : GoString) (low high : Int) (max : Option Int) :
    Except Stop GoValue := do
  if max.isSome then
    stuck "full slice expression over string"
  let (low, high) ← checkSliceBounds "length" value.length low high
  return .string (value.slice low high)

def validateSlice (slice : SliceValue) : Except Stop Unit := do
  if slice.len > slice.cap then
    stuck s!"malformed GoCore slice: len {slice.len} > cap {slice.cap}"
  match slice.base with
  | some _ => return ()
  | none =>
      if slice.offset == 0 && slice.len == 0 && slice.cap == 0 then
        return ()
      else
        stuck s!"malformed GoCore nil slice: {repr slice}"

def sliceIndexLoc (slice : SliceValue) (index : Int) : Except Stop Loc := do
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
    Except Stop GoValue := do
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
    Except Stop GoValue := do
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

-- `resolveDefinedAliases` / `canonicalTy` deleted (C2, 2026-09-05): both
-- resolved `.alias` chains, and `TypeDef.alias` is gone — the frontend
-- inlines aliases at every use, so every `Ty` on the machine IS its own
-- canonical form (S3's "canonical dynamic type" is now the identity).

mutual

/-- Does the type mention an `.unsupported` leaf? Used to fail closed at
boxing time (an unrenderable dynamic type must never become a tag).
Structural over the type and its nested parameter/result lists (C2; was
fuel-bounded, failing CLOSED (`true`) on exhaustion). -/
def Ty.mentionsUnsupported : Ty → Bool
  | .unsupported _ => true
  | .pointer e => Ty.mentionsUnsupported e
  | .slice e => Ty.mentionsUnsupported e
  | .array _ e => Ty.mentionsUnsupported e
  | .chan _ e => Ty.mentionsUnsupported e
  | .map k v => Ty.mentionsUnsupported k || Ty.mentionsUnsupported v
  | .funcType ps rs _ => Ty.mentionsUnsupportedList ps || Ty.mentionsUnsupportedList rs
  | _ => false

/-- `Ty.mentionsUnsupported` over a parameter/result list. -/
def Ty.mentionsUnsupportedList : List Ty → Bool
  | [] => false
  | t :: ts => Ty.mentionsUnsupported t || Ty.mentionsUnsupportedList ts

end

-- Downstream-unfolding pin: closed instances evaluate by `decide` (the
-- kernel-reducibility the section note promises) and unfold by `simp`.
example : Ty.mentionsUnsupported (.pointer .bool) = false := by decide
example : Ty.mentionsUnsupported (.funcType [.int, .unsupported "x"] [] false) = true := by
  simp [Ty.mentionsUnsupported, Ty.mentionsUnsupportedList]

/-- The dynamic-type tag for boxing, fail-closed: the static type itself
(alias-free by construction, so canonical), refused when it mentions an
`.unsupported` leaf — identity must never be decided on an unrenderable
type. (Was `canonicalDynamicTy`, which also resolved aliases.) -/
def checkedDynamicTy (typ : Ty) : Except Stop Ty := do
  if typ.mentionsUnsupported then
    unsupported s!"interface conversion for dynamic type {repr typ}"
  else
    return typ

/-- Is the type uncomparable in Go's runtime sense (a slice, map, or func
anywhere in its resolved structure)? Drives the `comparing uncomparable
type` panic on interface equality and the map hash panic. Struct fields
and array elements recurse; interfaces themselves are comparable (their
comparison may panic deeper, at their own dynamic types).

Three-valued on purpose: `none` is UNKNOWN — a `.defined` index with an
opaque declaration (today: any imported/stdlib named type, since the
frontend emits declarations only for the analyzed program) or no entry.
Callers must fail CLOSED on `none`; the old `Bool` version answered
"comparable", which silently accepted `m[sort.IntSlice{1,2}] = 1` where Go
panics (pre-merge audit 2026-07-31, finding 11). The TYPE layer of the
index descent (section note). -/
def tyUncomparableTy (atDefined : TypeIdx → Option Bool) : Ty → Option Bool
  | .slice _ => some true
  | .map _ _ => some true
  | .funcType _ _ _ => some true
  | .defined i => atDefined i
  | .array _ e => tyUncomparableTy atDefined e
  | _ => some false

/-- The INDEX layer of `tyUncomparableTy` (`bound`-structural; the `0`
arm is the fail-closed UNKNOWN). -/
def tyUncomparableAt (types : TypeEnv) : Nat → TypeIdx → Option Bool
  | 0, _ => none
  | bound + 1, i =>
      match types[i]? with
      | some (_, .defined t) => tyUncomparableTy (tyUncomparableAt types bound) t
      | some (_, .struct fields) =>
          -- Any DEFINITELY-uncomparable field decides it; otherwise an
          -- unknown field leaves the whole struct unknown.
          fields.foldl
            (fun acc f =>
              match acc, tyUncomparableTy (tyUncomparableAt types bound) f.typ with
              | some true, _ => some true
              | _, some true => some true
              | none, _ => none
              | _, none => none
              | some false, some false => some false)
            (some false)
      -- An interface-typed field is itself comparable (its own dynamic
      -- type decides at comparison time); an OPAQUE declaration and an
      -- absent entry are unknown.
      | some (_, .interfaceDef _) => some false
      | some (_, .opaqueDecl _) => none
      | none => none

def tyUncomparable (state : ExecState) (typ : Ty) : Option Bool :=
  tyUncomparableTy (tyUncomparableAt state.types state.types.size) typ

/-- The canonical EMPTY interface: satisfied by every type BY DESIGN (Go's
`any`), so it needs no wire declaration and renders as `interface {}`.
`"any"` is what the native frontend emits; `"empty_interface"` is the legacy
key still used by hand-written GoCore terms in `Tests/` and the proof
layer. -/
def isEmptyInterfaceName (id : TypeId) : Bool :=
  id.key == "any" || id.key == "empty_interface"

/-- The display record of a `TypeId` (design note 2026-09-05 §3): a
lookup, never a parse of the key. Since C2 the machine's type table is
INDEX-keyed (`Ty.defined (idx : TypeIdx)`), and the record of a defined
type is found through the key read back from its entry
(`displayNameOf` → `TypeEnv.nameOf?` → here): the decoder builds one
record per table entry IN TABLE ORDER and refuses duplicate TypeIds, so
the record a key finds is the record of the entry the index resolves to.
Interface leaves (`Ty.interface (id : TypeId)`) are name-keyed by design
and look their record up directly. -/
def typeDisplay? (state : ExecState) (id : TypeId) : Option TypeDisplay :=
  state.typeDisplays.foldl
    (fun found entry =>
      match found with
      | some _ => found
      | none => if entry.1 == id then some entry.2 else none)
    none

/-- gc's type string for a `TypeId`, from its display record. NO record
renders a VISIBLE marker — never the key: the key is path-qualified
identity (`red/inner.T`) and gc prints the package NAME (`inner.T`), so
rendering the key was exactly BUG-059's fail-open text. The
machine-minted `$runtime.Error` renders `runtimeErrorDisplayMarker`
(Syntax.lean, beside the reserved prefix whose display record carries
the same text — a program that `recover()`s and asserts the payload
reaches it inside the BUG-009/BUG-053 refusal text); otherwise the
no-record arm is reachable only from hand-built programs, which must
state their displays (the decoder requires a record per TypeDef). -/
def displayNameOfId (state : ExecState) (id : TypeId) : String :=
  match typeDisplay? state id with
  | some d => d.name
  | none =>
      if id == runtimeErrorTypeId then runtimeErrorDisplayMarker
      else s!"<TypeId {id.key} has no display record>"

/-- gc's type string for a DEFINED type by its table index (C2 × design
note 2026-09-05 §3.2): the reserved runtime-error index renders its
marker FIRST (`runtimeErrorTypeIdx` is a machine constant — the same
first check `renderPanicPayload` makes), every other index reads its
entry's key back (`TypeEnv.nameOf?`) and renders that key's display
record; an index the table does not have renders a visible marker, never
a guessed name (unreachable on a decoded program). -/
def displayNameOf (state : ExecState) (idx : TypeIdx) : String :=
  if idx == runtimeErrorTypeIdx then runtimeErrorDisplayMarker
  else
    match state.types.nameOf? idx with
    | some id => displayNameOfId state id
    | none => s!"<unknown type index {idx}>"

mutual

/-- Go's spelling of a type in a runtime panic message. Structural over
the type and its nested lists (C2; was fuel-bounded). Named and
anonymous-interface leaves render their DISPLAY record (design note
2026-09-05 §3.2 — gc's type string, package-NAME qualified: `inner.T`
for `red/inner.T`), never their key; a `.defined` reaches its record
through the table index (`displayNameOf`); an index the table does not
have renders as a visible marker (unreachable on a decoded program). -/
def goTypeNameForMessage (state : ExecState) : Ty → String
  | .bool => "bool"
  | .int kind => kind.name
  | .float kind => kind.name
  | .string => "string"
  | .pointer elem => s!"*{goTypeNameForMessage state elem}"
  | .slice elem => s!"[]{goTypeNameForMessage state elem}"
  | .map key value => s!"map[{goTypeNameForMessage state key}]{goTypeNameForMessage state value}"
  | .chan .both elem => s!"chan {goTypeNameForMessage state elem}"
  | .chan .send elem => s!"chan<- {goTypeNameForMessage state elem}"
  | .chan .recv elem => s!"<-chan {goTypeNameForMessage state elem}"
  | .interface name => if isEmptyInterfaceName name then "interface {}" else displayNameOfId state name
  | .defined i => displayNameOf state i
  | .array length elem => s!"[{length}]{goTypeNameForMessage state elem}"
  | .funcType params results variadic =>
      -- Go renders the signature: `func()`, `func(int) bool`,
      -- `func() (int, error)` (message-fidelity, 2026-07-30). A
      -- variadic signature's LAST parameter renders `...E`
      -- (`func(...int) int` — gc's failed-assert message names it;
      -- BUG-067 carried the bit here). A variadic marker on a
      -- non-slice last param cannot arrive from the emitter
      -- (go/types types it []E); if it ever does, the plain render
      -- is a message blemish, never a semantic answer.
      let names :=
        if variadic then goTypeNamesForMessageVariadic state params
        else goTypeNamesForMessage state params
      let ps := ", ".intercalate names
      let base := s!"func({ps})"
      match results with
      | [] => base
      | [r] => s!"{base} {goTypeNameForMessage state r}"
      | rs => s!"{base} ({", ".intercalate (goTypeNamesForMessage state rs)})"
  | .unsupported feature => feature
  | .sync kind => s!"sync.{kind.name}"

/-- The rendered parameter/result list. -/
def goTypeNamesForMessage (state : ExecState) : List Ty → List String
  | [] => []
  | t :: ts => goTypeNameForMessage state t :: goTypeNamesForMessage state ts

/-- The rendered parameter list of a VARIADIC signature: the last
parameter, a slice `[]E` by go/types' typing, renders `...E`. -/
def goTypeNamesForMessageVariadic (state : ExecState) : List Ty → List String
  | [] => []
  | [.slice e] => [s!"...{goTypeNameForMessage state e}"]
  | [t] => [goTypeNameForMessage state t]
  | t :: ts => goTypeNameForMessage state t :: goTypeNamesForMessageVariadic state ts

end

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
def methodRecvInterfaceName? (_state : ExecState) (method : MethodInfo) : Option String :=
  match method.recv with
  | .interface id => some id.key
  | _ => none

/-- A concrete method's receiver as the dynamic-type key (Ty-keyed
identity, interfaces campaign S3 — was a rendered name string; alias-free
by construction since C2, so no canonicalization). `none` for interface
receivers (those are requirements, not implementations). -/
def methodRecvDynamicTy? (_state : ExecState) (method : MethodInfo) : Option Ty :=
  match method.recv with
  | .interface _ => none
  | recv => some recv

/-- The DECLARED method set of an interface name, or `none` when the program
records no declaration for it — the distinction a `Bool`-shaped requirement
list structurally could not make (pre-merge audit 2026-07-31, finding 0). -/
def interfaceDeclaredMethods? (state : ExecState) (id : TypeId) : Option (Array MethodSig) :=
  match state.types.lookupName? id with
  | some (_, .interfaceDef methods) => some methods
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
      some ((f.args.extract 1 f.args.size).map (fun p => p.typ),
            f.results.map (fun p => p.typ),
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
          params == req.params && results == req.results && variadic == req.variadic
      | none => false
  | none => false

/-- The method-CARRIER key of a dynamic type's base — `some key` exactly
when the base is a kind that CAN carry methods in Go, `none` when the
LANGUAGE forbids it (class closure of BUG-053,
`docs/2026-08-10_method-set-record-contract.md` §2, gc-probed): methods
are declarable only on defined non-pointer non-interface types, so the
carriers are `.defined` (every named type) and `.sync` (models the gc
defined types `sync.Mutex`/…); unnamed type literals — basics, slices,
maps, arrays, chans, funcs, `**T`, pointer-to-interface — carry
nothing, and that emptiness is a language fact no registration can
invalidate. One pointer level inherits the pointee's set (`*T` ⊇ T's
value-receiver methods; the deref here mirrors the lookup base). Any
FUTURE `Ty` kind modeling a defined Go type must join the carrier arms;
forgetting its records then yields visible refusals, never answers —
the inversion of the retired blanket-`true` taxonomy arm, which read
"not `.defined` ⇒ no methods" and silently answered wrong "no"s for
`.sync` (BUG-053's exact mechanism).

A `.defined i` whose index the table does not have is a CARRIER whose
key is unknown — never a non-carrier: it maps to the marker key
`$unresolved-type-index.<i>`, which no record can carry (`$` cannot
appear in a Go identifier or import path, the frontend mints every
record key from one, and the decoder's only synthesized record is
`struct{}`), so every consumer finds NO record and REFUSES. Mapping it
to `none` would have read "unresolvable ⇒ empty method set by the
language" — the BUG-053 mechanism again (audit fix R1, 2026-09-05).
Unreachable on a decoded program (every `named` reference is minted an
index < `types.size`); the reasoning consumer constructs `Program`s. -/
def methodCarrierKey? (state : ExecState) (dynTy : Ty) : Option String :=
  let base := match dynTy with
    | .pointer elem => elem
    | other => other
  match base with
  | .defined i =>
      match state.types.nameOf? i with
      | some name => some name.key
      | none => some s!"$unresolved-type-index.{i}"
  | .sync kind => some s!"sync.{kind.name}"
  | _ => none

/-- The recorded coverage of a carrier key, or `none` when the wire
carries NO record — in which case satisfaction/dispatch must REFUSE,
never answer (the record table is the ONLY source; TypeDef presence,
stub presence, and type-kind taxonomy no longer decide). -/
def methodSetCoverage? (state : ExecState) (key : String) :
    Option MethodSetCoverage :=
  state.methodSets.foldl
    (fun found record =>
      match found with
      | some _ => found
      | none => if record.key == key then some record.coverage else none)
    none

/-- Is `dynTy`'s METHOD SET recorded on the wire? `true` for every
non-carrier kind (§2 of the contract note: emptiness by the LANGUAGE)
and exactly for carriers with a `MethodSetRecord` (empty-but-present
means genuinely empty). Absence of a record for a carrier means
UNKNOWN, not empty: answering `false` from it was a definite answer
derived from nothing — the wrong comma-ok boolean and a FABRICATED
`missing method` panic on a program Go runs to completion (pre-merge
audit 2026-07-31 finding 8 = BUG-008/BUG-009 for imported `.defined`
names; BUG-053 for `.sync`, which the retired taxonomy arm waved
through). A `.defined` index the table does not have is a carrier
with the unrecordable marker key (`methodCarrierKey?`), so it answers
`false` here — refuse, never "empty" (audit fix R1). -/
def dynamicMethodSetRecorded (state : ExecState) (dynTy : Ty) : Bool :=
  match methodCarrierKey? state dynTy with
  | some key => (methodSetCoverage? state key).isSome
  | none => true

/-- Is `dynTy` recorded at EXPORTED-only coverage (D5 imported markers,
the sync primitives)? Cross-package UNEXPORTED method identity is
inexpressible on the name-keyed wire, so a definite-"no" that hinges on
an unexported requirement refuses instead of answering. Keyed on the
RECORD's coverage — the old check sniffed the TypeDef kind
(`.unsupported` marker), which could not see carriers without TypeDefs
at all. -/
def dynamicMethodSetExportedOnly (state : ExecState) (dynTy : Ty) : Bool :=
  match methodCarrierKey? state dynTy with
  | some key => methodSetCoverage? state key == some .exported
  | none => false

/-- Go exportedness, decided CONSTRUCTIVELY at the byte level: the first
UTF-8 byte is an ASCII upper-case letter. Core's char-level String APIs
(`toList`/`front`/`get`) depend on `Classical.choice` through their UTF-8
decoding proofs, and the machine-correspondence theorems are pinned
constructive (proofs/Audit.lean) — the same constraint the abort renderer
records at `asciiString?`. Recorded narrowing: a NON-ASCII exported
method name (Unicode upper-case first rune) answers `false` here, which
makes the imported-marker satisfaction guard REFUSE rather than answer —
fail-closed, never wrong. -/
def isExportedName (s : String) : Bool :=
  match s.toUTF8[0]? with
  | some b => 65 ≤ b && b ≤ 90
  | none => false

/-- The FIRST requirement of `interfaceName` that `dynTy` does not meet, in
the interface's own (name-sorted) method order — `none` means it satisfies
the interface. Go names exactly this method in its assert-panic message.

Fails CLOSED, never vacuously true, in two situations:
  * no declaration is recorded for a non-empty interface name (the wire
    carries one for every interface it mentions; an absent one means the
    program used an interface the frontend did not export);
  * the answer would be "unsatisfied" on a type whose method set is not
    RECORDED at all (an imported/stdlib named type — BUG-008/BUG-009).

The second guards the `some name` (definite-FALSE) answer specifically:
satisfaction found is still sound, since a recorded matching method really
is in the method set. A third guard — types with EMBEDDED fields, whose
method set unmodeled promotion could extend (BUG-007) — was retired
2026-08-05 (general-coverage slice 2, design note D2): the wire contract
now requires the emitted method table to carry the FULL method set of
every declared named type, promoted methods included (the frontend
synthesizes forwarding wrappers), so a missing method on an
embedded-field type is real information. -/
def firstUnsatisfiedMethod? (state : ExecState) (dynTy : Ty) (interfaceName : TypeId) :
    Except Stop (Option String) := do
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
            -- The CLASS refusal (BUG-053 closure, contract note §3): a
            -- method-CARRYING type with no method-set record on the
            -- wire. `missing method` would be an answer derived from no
            -- information — refuse visibly instead (BUG-008/BUG-009's
            -- polarity, now keyed on record presence for EVERY carrier
            -- kind, not on the `.defined` taxonomy arm).
            unsupported s!"interface satisfaction for {goTypeNameForMessage state dynTy}: \
its method set has NO record on the wire (a method-carrying type without \
a MethodSetRecord), so `missing method {name}' would be an answer derived \
from no information (BUG-009/BUG-053 class)"
          else if dynamicMethodSetExportedOnly state dynTy && !isExportedName name then
            -- EXPORTED-only coverage (D5 markers, sync primitives): an
            -- unexported requirement could still be met inside the
            -- type's own package — refuse rather than answer (D5).
            unsupported s!"interface satisfaction for {goTypeNameForMessage state dynTy}: \
requirement {name} is UNEXPORTED and the dynamic type's record covers \
exported methods only — cross-package unexported method identity is not \
modeled"
          else
            return (some name)

def dynamicImplementsInterface (state : ExecState) (dynTy : Ty) (interfaceName : TypeId) :
    Except Stop Bool := do
  return (← firstUnsatisfiedMethod? state dynTy interfaceName).isNone

/-- Apply the element normalizer to each list element in order;
fail-closed on the first error. Structural on the LIST and parameterized
over `f` rather than mutually recursive — the de-WF recipe (2026-08-03):
the old mutual block had no common structural argument, so Lean compiled
it well-founded, and `Acc.rec` reduces nowhere — which blocked kernel
evaluation of the interpreter (`docs/2026-08-03_sem-adequacy-arc.md`,
slice-1 spike). Since C2 the parameter is the type layer of the index
descent at the enclosing bound; element COUNT never touches the descent. -/
def normalizeListWith (f : GoValue → Except Stop GoValue) :
    List GoValue → Except Stop (Array GoValue)
  | value :: rest => do
      let head ← f value
      let tail ← normalizeListWith f rest
      return #[head] ++ tail
  | [] => return #[]

/-- Normalize struct field values pairwise with the given normalizer,
checking field-name alignment. -/
def normalizeFieldsWith (f : Ty → GoValue → Except Stop GoValue) :
    List FieldDef → List (String × GoValue) →
    Except Stop (Array (String × GoValue))
  | field :: fieldRest, (actualField, value) :: valueRest => do
      if actualField != field.name then
        stuck s!"struct value field mismatch: expected {field.name}, got {actualField}"
      let head ← f field.typ value
      let tail ← normalizeFieldsWith f fieldRest valueRest
      return #[(field.name, head)] ++ tail
  | _, _ => return #[]

/-- Go ASSIGNABILITY at the one UNNAMED struct type the wire can carry
(BUG-011, fixed 2026-08-05 — design note D4): the canonical anonymous
empty struct `struct{}` is assignable to/from any defined type whose
underlying type is `struct{}` (identical underlying types, at least one
side not a defined type). Both field lists empty ⟺ identical underlying
here, so the check is exact. At the NORMALIZATION site (one candidate tag
against the target) two DIFFERENT defined types never take this escape —
Go requires an explicit conversion for those; the EQUALITY site layers an
extra operand-tag condition on top, because there the context type can
itself be the canonical `struct{}` (audit F4, 2026-08-05). -/
def emptyStructAssignable (actual name : TypeId)
    (fields : Array FieldDef) (fieldsValue : Array (String × GoValue)) : Bool :=
  (actual.key == "struct{}" || name.key == "struct{}") &&
    fields.isEmpty && fieldsValue.isEmpty

/-- Struct-shape checks for normalization at a defined struct type, with the
given field normalizer. A mismatched tag is accepted
only through the empty-struct ASSIGNABILITY escape (retagged copy — Go's
assignment); anything else stays stuck. -/
def normalizeStructValueWith (f : Ty → GoValue → Except Stop GoValue)
    (name : TypeId) (fields : Array FieldDef) : GoValue → Except Stop GoValue
  | .struct actual fieldsValue => do
      if actual != name then
        if emptyStructAssignable actual name fields fieldsValue then
          return .struct name #[]
        else
          stuck s!"struct value type mismatch: expected {name.key}, got {actual.key}"
      if fieldsValue.size != fields.size then
        stuck s!"struct value field count mismatch: expected {fields.size}, got {fieldsValue.size}"
      .struct name <$> normalizeFieldsWith f fields.toList fieldsValue.toList
  | value => stuck s!"expected struct {name.key} value, got {repr value}"

/-- Normalize a value at a type: the TYPE layer of the index descent
(section note). Structural on the type — an array's elements are
normalized at the element type through `normalizeListWith`, a `.defined`
is handed to `atDefined` — and kernel-reducible. The public
`normalizeValueForTy` seeds the descent at `types.size`. -/
def normalizeValueForTyTy (atDefined : TypeIdx → GoValue → Except Stop GoValue) :
    Ty → GoValue → Except Stop GoValue
  | .int kind, .int value _ => return .int (kind.normalize value) kind
  | .int kind, value => stuck s!"expected {kind.name} value, got {repr value}"
  -- Kind-strict (F2 header note): mask-enforce the width invariant, never
  -- adopt a mismatched kind (LOCKSTEP with isNormalForTyTy's arm).
  | .float kind, .float bits k =>
      if k == kind then return .float (kind.normalizeBits bits) kind
      else stuck s!"expected {kind.name} value, got {k.name}"
  | .float kind, value => stuck s!"expected {kind.name} value, got {repr value}"
  | .array length elem, .array values => do
      if values.size != length then
        stuck s!"array value length mismatch: expected {length}, got {values.size}"
      .array <$> normalizeListWith (normalizeValueForTyTy atDefined elem) values.toList
  | .array length _, value => stuck s!"expected array({length}) value, got {repr value}"
  | .interface _, value => return value
  -- Func values carry their own identity; nil is the zero value.
  | .funcType _ _ _, .funcVal fid captured => return .funcVal fid captured
  | .funcType _ _ _, .nil => return .nil
  | .funcType _ _ _, value => stuck s!"expected func value, got {repr value}"
  -- Channel cells canonicalize the nil representation (channels arc
  -- slice 1): a raw `.nil` reaching a channel-typed slot (an untyped
  -- `return nil`, a nil literal the frontend left untyped) becomes the
  -- machine's own nil channel, the same value the typed nil literal and
  -- `defaultValue` produce — the map/slice conversion-arm precedent
  -- (delta-review D3). Anything else non-channel fails closed.
  | .chan _ _, .chan cv => return .chan cv
  | .chan _ _, .nil => return .chan { base := none }
  | .chan _ _, value => stuck s!"expected channel value, got {repr value}"
  -- Sync cells (spec-parity slice 2): only kind-matching primitive
  -- state is normal at a sync type — there is no nil sync struct and
  -- no cross-kind coercion; anything else fails closed.
  | .sync kind, .syncData p =>
      if p.kind == kind then return .syncData p
      else stuck s!"expected sync.{kind.name} state, got {repr (GoValue.syncData p)}"
  | .sync kind, value => stuck s!"expected sync.{kind.name} state, got {repr value}"
  | .defined i, value => atDefined i value
  | .unsupported feature, _ => unsupported s!"normalizing {feature}"
  | _, value => return value

/-- The INDEX layer of normalization: normalize a value at the type
declared at index `i`, descending only to smaller indices (`bound`-
structural; section note). -/
def normalizeValueForTyAt (types : TypeEnv) : Nat → TypeIdx → GoValue → Except Stop GoValue
  | 0, i, _ => typeIndexExhausted "normalizing" i
  | bound + 1, i, value =>
      match types[i]? with
      | some (name, .struct fields) =>
          normalizeStructValueWith (normalizeValueForTyTy (normalizeValueForTyAt types bound))
            name fields value
      | some (_, .defined target) =>
          normalizeValueForTyTy (normalizeValueForTyAt types bound) target value
      | some (_, .opaqueDecl feature) => unsupported s!"normalizing {feature}"
      | some (name, .interfaceDef _) => unsupported s!"normalizing at interface type {name.key}"
      | none => unsupported s!"normalizing unknown type index {i}"

-- Downstream-unfolding pins: the leaf arm unfolds without touching the
-- table; a closed table walk evaluates by `decide`.
example (f : TypeIdx → GoValue → Except Stop GoValue) (kind : IntKind) :
    normalizeValueForTyTy f (.int kind) (.int 3 kind)
      = .ok (.int (kind.normalize 3) kind) := by
  simp [normalizeValueForTyTy]; rfl
example :
    normalizeValueForTyAt #[(⟨"main.T"⟩, .defined (.int .int))] 1 0 (.int 3 .int)
      = .ok (.int 3 .int) := rfl

/-- Normalize a value at a type over the state's type table (the descent
seeded at `types.size`). -/
def normalizeValueForTy (state : ExecState) (ty : Ty) (value : GoValue) :
    Except Stop GoValue :=
  normalizeValueForTyTy (normalizeValueForTyAt state.types state.types.size) ty value

/-! ### Self-normalization check (sem-adequacy arc slice 3, 2026-08-04)

`isNormalForTy types ty v` decides `normalizeValueForTy σ ty v = .ok v`
(for any `σ` with `σ.types = types`) WITHOUT a generic `GoValue`
equality: it mirrors the normalizer arm-for-arm and compares only at the
leaves (`Int`/`IntKind`/`TypeId`/`String` — all `DecidableEq`, so the
whole family is kernel-reducible; the derived `BEq GoValue` is
WF-compiled/opaque and must never sit on a kernel-evaluation path). It is
deliberately parameterized by the TYPE ENVIRONMENT, not the state: the
normalizer provably reads nothing else, and taking `TypeEnv` makes the
well-formedness component built on this check invariant along
types-preserving steps BY REWRITING rather than by a congruence lemma.

The proved direction is soundness (`isNormalForTyTy_sound`/`isNormalForTy_sound`,
`StateWf.lean`): check true ⇒ the normalizer returns the value UNCHANGED.
The converse (the check never rejects a value the normalizer would fix)
is not needed by any theorem; the machine's snapshot validation built on
this check is differential-validated instead (arc doc, slice-3 entry). -/

/-- Element-wise check, parameterized over the element checker — the
de-WF recipe's shape, mirroring `normalizeListWith`. -/
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

/-- Does `normalizeValueForTyTy atDefined ty v` return `.ok v` — i.e. is
`v` self-normalized at `ty`? The TYPE layer, mirroring the normalizer
arm-for-arm (`isNormalForTyTy_sound`, `StateWf.lean`). -/
def isNormalForTyTy (atDefined : TypeIdx → GoValue → Bool) : Ty → GoValue → Bool
  | .int kind, .int value k =>
      decide (kind.normalize value = value) && decide (kind = k)
  | .int _, _ => false
  | .float kind, .float bits k =>
      decide (kind.normalizeBits bits = bits) && decide (kind = k)
  | .float _, _ => false
  | .array length elem, .array values =>
      decide (values.size = length)
        && isNormalListWith (isNormalForTyTy atDefined elem) values.toList
  | .array _ _, _ => false
  | .interface _, _ => true
  | .funcType _ _ _, .funcVal _ _ => true
  | .funcType _ _ _, .nil => true
  | .funcType _ _ _, _ => false
  -- LOCKSTEP with the normalizer's chan arms: only a `.chan` value is
  -- self-normalized (a raw `.nil` normalizes to the canonical form).
  | .chan _ _, .chan _ => true
  | .chan _ _, _ => false
  -- LOCKSTEP with the normalizer's sync arms.
  | .sync kind, .syncData p => p.kind == kind
  | .sync _, _ => false
  | .defined i, value => atDefined i value
  | .unsupported _, _ => false
  | _, _ => true

/-- The INDEX layer of the self-normalization check, in lockstep with
`normalizeValueForTyAt` (`bound`-structural; the `0` arm fails closed). -/
def isNormalForTyAt (types : TypeEnv) : Nat → TypeIdx → GoValue → Bool
  | 0, _, _ => false
  | bound + 1, i, value =>
      match types[i]? with
      | some (name, .struct fields) =>
          match value with
          | .struct actual fieldsValue =>
              decide (actual = name) && decide (fieldsValue.size = fields.size)
                && isNormalFieldsWith (isNormalForTyTy (isNormalForTyAt types bound))
                    fields.toList fieldsValue.toList
          | _ => false
      | some (_, .defined target) => isNormalForTyTy (isNormalForTyAt types bound) target value
      | some (_, .opaqueDecl _) => false
      | some (_, .interfaceDef _) => false
      | none => false

/-- Is `v` self-normalized at `ty` over the type table (`normalizeValueForTy
σ ty v = .ok v` for any `σ` with `σ.types = types`)? -/
def isNormalForTy (types : TypeEnv) (ty : Ty) (value : GoValue) : Bool :=
  isNormalForTyTy (isNormalForTyAt types types.size) ty value

/-- Field access at a CONVERTIBLE mint tag (triage L7, 2026-08-19 —
spec#Conversions' struct-tag clause): a pointer conversion `(*B)(a)`
aliases the cell, which keeps its MINT tag, so a field access may
arrive at a TypeId differing from the stored one. Go permits exactly
the tag-convertible case — identical underlying struct types; the wire
strips tags, so identity is wire `FieldDef`-list equality (the same
rule the struct VALUE-conversion arm uses; embeddedness compared,
spec-exact per arc-final audit F20). Anything else — unknown TypeIds
included — answers false and the access stays stuck. -/
def structTagCompatible (state : ExecState) (actual expected : TypeId) : Bool :=
  match state.types.lookupName? actual, state.types.lookupName? expected with
  | some (_, .struct fa), some (_, .struct fb) => fa == fb
  | _, _ => false

-- Total: structural recursion on the `Loc` argument (field/index bases are
-- strict subterms). loadLoc depends only on itself and total helpers, so it is
-- a genuine `def` — the premise of the eventual `wp_load` proof rule.
def loadLoc (state : ExecState) : Loc → Except Stop GoValue
  | loc@(.base _) =>
      match Heap.lookup state.heap loc with
      | some (.value _ v) => return v
      | some (.mapPayload ..) => stuck s!"value load from a map payload cell {repr loc}"
      | some (.chanPayload ..) => stuck s!"value load from a channel payload cell {repr loc}"
      | none => stuck s!"unbound GoCore heap location: {repr loc}"
  | .field base typeId fieldName => do
      match ← loadLoc state base with
      | .struct actualType fields =>
          if actualType != typeId && !structTagCompatible state actualType typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return value
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct base for field load, got {repr other}"
  | .index base index => do
      match ← loadLoc state base with
      | .array values => arrayGet values index
      | other => stuck s!"expected array base for index load, got {repr other}"

/-- Store through a location. Total: structural recursion on the `Loc`
argument (field/index bases are strict subterms); its non-structural
callee (`normalizeValueForTy`) is itself total. The premise of `wp_store`.

ONE store discipline (A3): the root cell is a VALUE cell at a declared
type and the incoming value is normalized at that type — there are no
untyped cells and no value-shape coercion any more. A payload cell (map/
channel) at the root is an ill-shaped operand (`.stuck`); a missing cell
is BUG-085's `.internal` (through `ExecState.updateCell`, the one root
write path: `Array.set` under its bound — the phantom-cell arm is
unrepresentable by type). -/
def storeLoc (state : ExecState) : Loc → GoValue → Except Stop ExecState
    | .base a, value =>
        state.updateCell a fun
          | .value ty _ => do
              let value ← normalizeValueForTy state ty value
              pure (.value ty value)
          | .mapPayload .. => stuck s!"value store into a map payload cell {repr (Loc.base a)}"
          | .chanPayload .. => stuck s!"value store into a channel payload cell {repr (Loc.base a)}"
    | .field base typeId fieldName, value => do
        match ← loadLoc state base with
        | .struct actualType fields =>
            if actualType != typeId && !structTagCompatible state actualType typeId then
              stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
            let updated ← StructFields.set fields fieldName value
            -- The cell KEEPS its mint tag (`actualType`) — the
            -- conversion aliases, never retags (triage L7).
            storeLoc state base (.struct actualType updated)
        | other => stuck s!"expected struct base for field store, got {repr other}"
    | .index base index, value => do
        match ← loadLoc state base with
        | .array values => storeLoc state base (.array (← arraySet values index value))
        | other => stuck s!"expected array base for index store, got {repr other}"

-- `lookup` deleted (reshape S4): variable reads are `Machine.Step.evalVar`
-- (control-side env lookup + `loadLoc`), never a state-side name lookup.

/-- Go's conversion `T(v)` at runtime. NOT recursive (C2): the target's
`.defined` indirections are followed once by `TypeEnv.resolve`, and every
arm below is a leaf — the old fuel existed only for the alias chain. -/
def convertValueToTy (state : ExecState) (typ : Ty) (value : GoValue) :
    Except Stop GoValue :=
  match state.types.resolve state.types.size typ, value with
  | .error e, _ => .error e
  | .ok (.plain (.int kind)), .int value _ => return .int (kind.normalize value) kind
  -- Float → int (design note §3.3, decision 4): the spec pins truncation
  -- toward zero; an out-of-range or NaN source is IMPLEMENTATION-
  -- DEPENDENT in Go (amd64 1<<63, arm64 saturates), so it FAILS CLOSED
  -- at runtime — never a modeled platform value. In-range means the
  -- exact truncation is representable in the TARGET kind unchanged.
  | .ok (.plain (.int kind)), .float bits fk =>
      let n? := match fk with
        | .float64 => FloatBits.f64truncInt? bits
        | .float32 => FloatBits.f32truncInt? bits
      match n? with
      | some n =>
          if kind.normalize n == n then return .int n kind
          else unsupported
            "float-to-int conversion out of range/NaN (implementation-dependent in Go)"
      | none => unsupported
          "float-to-int conversion out of range/NaN (implementation-dependent in Go)"
  | .ok (.plain (.int kind)), other => stuck s!"expected integer operand for conversion to {kind.name}, got {repr other}"
  -- Float targets (floats slice F2): float↔float via the softfloat
  -- (widening exact, narrowing the ONE rounding); int→float via the
  -- rational kernel's den=1 case — the single correctly-rounded step
  -- (float32 targets NEVER round via binary64; note §6).
  | .ok (.plain (.float kind)), .float bits fk =>
      (match kind, fk with
       | .float64, .float64 => return .float (kind.normalizeBits bits) kind
       | .float32, .float32 => return .float (kind.normalizeBits bits) kind
       | .float64, .float32 => return .float (kind.normalizeBits (FloatBits.f32to64 bits)) kind
       | .float32, .float64 => return .float (kind.normalizeBits (FloatBits.f64to32 bits)) kind)
  | .ok (.plain (.float kind)), .int value _ =>
      return .float (kind.normalizeBits (kind.ratToBits value 1)) kind
  | .ok (.plain (.float kind)), other =>
      stuck s!"expected numeric operand for conversion to {kind.name}, got {repr other}"
  | .ok (.struct name targetFields), value =>
      -- Struct VALUE conversion (2026-08-05, slice-2 stage 7, design
      -- note D6): legal exactly when the underlying struct types are
      -- identical. The wire strips tags (Go's conversions IGNORE
      -- them), so wire `FieldDef` equality is the identity rule —
      -- with `embedded` flags compared too, which is SPEC-EXACT
      -- (corrected, arc-final audit F20 2026-08-06: §Type identity
      -- requires fields "either both embedded or both not embedded",
      -- §Conversions relaxes ONLY struct tags, and go/types compares
      -- embeddedness unconditionally even under IdenticalIgnoreTags
      -- — the old docstring called this a "conservative narrowing
      -- (the spec ignores embeddedness for identity)", inviting a
      -- future relaxation that would accept conversions gc rejects).
      -- The result is a retagged COPY, Go's value-conversion
      -- semantics. The SOURCE struct is found by its value tag (a
      -- name-keyed lookup: the tag is a `TypeId`).
      match value with
      | .struct actual actualFields =>
          if actual == name then
            return value
          else
            match state.types.lookupName? actual with
            | some (_, .struct sourceFields) =>
                if sourceFields == targetFields then
                  return .struct name actualFields
                else
                  unsupported s!"conversion to struct type {name.key} \
from {actual.key} (non-identical underlying)"
            | _ => unsupported s!"conversion to struct type {name.key} from {actual.key}"
      | _ => unsupported s!"conversion to struct type {name.key}"
  | .ok (.opaque _ feature), _ => unsupported s!"conversion to {feature}"
  | .ok (.interfaceDecl name), _ => unsupported s!"conversion to interface type {name.key}"
  -- Identity conversions Go permits at runtime with no representation
  -- change (`string(s)` — surfaced by interfaces/error-interface's
  -- `string(e.Error())` shape, 2026-07-30).
  | .ok (.plain .string), .string s => return .string s
  -- Unnamed-composite conversion targets (BUG-020, arc-final audit F10,
  -- 2026-08-06): a conversion whose RESOLVED target shape is a pointer,
  -- slice, map, or func — the spec's own canonical examples
  -- `(*Point)(p)`, `(func() int)(x)`, `(*int)(nil)` — is legal exactly
  -- when the underlying types are identical, which go/types has already
  -- checked (both directions through defined types resolve here via
  -- `TypeEnv.resolve`). The runtime representation is unchanged: pass the
  -- value through; any other value shape falls to the fail-closed
  -- catch-all (so string→[]rune/[]byte stay refused here — real
  -- conversion logic, not a retag). The pointee-retag hazard the old
  -- struct-arm comment feared ((*B)(pa) aliasing one cell under two
  -- tags) stays fail-closed DOWNSTREAM: every field load/store checks
  -- the stored struct tag (structs/tag-pointer-conversion stays red).
  -- Slice→array / slice→array-pointer conversions (triage L2a,
  -- 2026-08-19): spec#Conversions_from_slice_to_array_or_array_pointer
  -- — "if the length of the slice is less than the length of the
  -- array, a run-time panic occurs". The length-check PANIC is
  -- gc-exact (probe go1.26.5) and fires before any element is touched,
  -- so these arms read no state. The SUCCEEDING forms stay REFUSED
  -- (triage L2b, category (b)): the array-pointer form must ALIAS the
  -- slice's backing segment and `Loc` has no subarray-view
  -- constructor; the value-copy form rides the same frontier row
  -- (spec-examples-decl/slice-to-array/ok-forms pins both red).
  | .ok (.plain (.array n _)), .slice slice =>
      if slice.len < n then
        panic s!"runtime error: cannot convert slice with length {slice.len} \
to array or pointer to array with length {n}"
      else
        unsupported "slice-to-array value conversion (succeeding form; triage L2b frontier)"
  | .ok (.plain (.pointer (.array n _))), .slice slice =>
      if slice.len < n then
        panic s!"runtime error: cannot convert slice with length {slice.len} \
to array or pointer to array with length {n}"
      else
        unsupported "slice-to-array-pointer conversion (aliasing view over slice storage; triage L2b frontier)"
  | .ok (.plain (.pointer _)), value@(.addr _) => return value
  | .ok (.plain (.pointer _)), .nil => return .nil
  | .ok (.plain (.slice _)), value@(.slice _) => return value
  -- A nil operand at a slice/map target produces the machine's OWN
  -- nil-slice/nil-map representation — exactly what the typed nil
  -- literal (`.nilLit`, via `defaultValue`) produces — NOT the raw
  -- `.nil` (delta-review D3, 2026-08-06: the first arms returned raw
  -- nil, so `[]byte(nil)`/`map[K]V(nil)` still failed at first use;
  -- pointer/func targets are different — raw nil IS their
  -- representation).
  | .ok (.plain (.slice _)), .nil =>
      return .slice { base := none, offset := 0, len := 0, cap := 0 }
  | .ok (.plain (.map _ _)), value@(.map _) => return value
  | .ok (.plain (.map _ _)), .nil => return .map { base := none }
  -- Channel conversions: the only runtime-legal ones change DIRECTION
  -- (or retag through a defined type) — the reference is unchanged
  -- (spec §Conversions; probe p12: a directional conversion of the same
  -- channel remains ==-equal). A nil operand produces the machine's own
  -- nil-channel representation, like the map/slice arms above.
  | .ok (.plain (.chan _ _)), value@(.chan _) => return value
  | .ok (.plain (.chan _ _)), .nil => return .chan { base := none }
  | .ok (.plain (.funcType _ _ _)), value@(.funcVal _ _) => return value
  | .ok (.plain (.funcType _ _ _)), .nil => return .nil
  -- Conversion INTO an interface type at a machine site (map key slots,
  -- assert results): a box or nil interface passes as-is (the frontend's
  -- to-interface wrap already built the box); a raw value here is a
  -- lowering bug — fail closed, never silently box without a dynamic
  -- type (interfaces campaign, 2026-07-30).
  | .ok (.plain (.interface _)), value@(.interface _ _) => return value
  | .ok (.plain (.interface _)), .nil => return .nil
  | .ok (.plain (.interface id)), value =>
      stuck s!"raw value reached interface conversion to {id.key}: {repr value}"
  | .ok (.plain (.unsupported feature)), _ => unsupported s!"conversion to {feature}"
  | .ok (.plain other), _ => unsupported s!"conversion to {repr other}"

/-- Default value for each struct field with the given default builder,
in declaration order. Structural on the list; part of the
de-WF recipe (see `normalizeListWith`). -/
def defaultFieldsWith (f : Ty → Except Stop GoValue) :
    List FieldDef → Except Stop (Array (String × GoValue))
  | field :: rest => do
      let head ← f field.typ
      let tail ← defaultFieldsWith f rest
      return #[(field.name, head)] ++ tail
  | [] => return #[]

/-- The zero value of a type: the TYPE layer of the index descent
(section note). The array case computes the element default once and
replicates it (`defaultValue` is pure, so all elements are equal); the
`length == 0` guard preserves the original behavior of not evaluating
the element type for an empty array. -/
def defaultValueTy (atDefined : TypeIdx → Except Stop GoValue) : Ty → Except Stop GoValue
  | .bool => return .bool false
  | .int kind => return .int 0 kind
  | .float kind => return .float 0 kind  -- +0 bits
  | .string => return .string GoString.empty
  | .array length elem => do
      if length == 0 then
        return .array #[]
      let elemDefault ← defaultValueTy atDefined elem
      return .array (Array.replicate length elemDefault)
  | .slice _ => return .slice { base := none, offset := 0, len := 0, cap := 0 }
  | .map _ _ => return .map { base := none }
  | .chan _ _ => return .chan { base := none }
  -- The zero sync value IS the ready-to-use primitive ("The zero value
  -- for a Mutex is an unlocked mutex"; likewise RWMutex/WaitGroup/Once).
  | .sync kind => return .syncData kind.zero
  | .pointer _ => return .nil
  | .funcType _ _ _ => return .nil
  | .interface _ => return .nil
  | .defined i => atDefined i
  | .unsupported feature => unsupported s!"default value for {feature}"

/-- The INDEX layer of `defaultValueTy`: the zero value of the type
declared at index `i` (`bound`-structural; section note). -/
def defaultValueAt (types : TypeEnv) : Nat → TypeIdx → Except Stop GoValue
  | 0, i => typeIndexExhausted "default value" i
  | bound + 1, i =>
      match types[i]? with
      | some (name, .struct fields) =>
          .struct name <$> defaultFieldsWith (defaultValueTy (defaultValueAt types bound)) fields.toList
      | some (_, .defined target) => defaultValueTy (defaultValueAt types bound) target
      | some (_, .opaqueDecl feature) => unsupported s!"default value for {feature}"
      | some (name, .interfaceDef _) => unsupported s!"default value at interface type {name.key}"
      | none => unsupported s!"default value for unknown type index {i}"

-- Downstream-unfolding pins (leaf arm by `simp`; a closed table walk —
-- a struct over a defined type over an array of structs — by `decide`).
example (f : TypeIdx → Except Stop GoValue) (kind : IntKind) :
    defaultValueTy f (.int kind) = .ok (.int 0 kind) := by
  simp [defaultValueTy]; rfl
example :
    defaultValueAt
      #[(⟨"main.P"⟩, .struct #[{ name := "x", typ := .int }]),
        (⟨"main.A"⟩, .defined (.array 2 (.defined 0))),
        (⟨"main.Q"⟩, .struct #[{ name := "a", typ := .defined 1 }, { name := "b", typ := .bool }])]
      3 2
      = .ok (.struct ⟨"main.Q"⟩
          #[("a", .array #[.struct ⟨"main.P"⟩ #[("x", .int 0 .int)], .struct ⟨"main.P"⟩ #[("x", .int 0 .int)]]),
            ("b", .bool false)]) := rfl

/-- The zero value of a type over the state's type table (the descent
seeded at `types.size`). -/
def defaultValue (state : ExecState) (ty : Ty) : Except Stop GoValue :=
  defaultValueTy (defaultValueAt state.types state.types.size) ty

/-- Build a struct value field-by-field from positional literal args, normalizing
each against its field type. Not recursive with `buildStructValue` (it only calls
the total `normalizeValueForTy`); callers guarantee the checked length. -/
def buildStructFields (state : ExecState) :
    List FieldDef → List GoValue → Except Stop (Array (String × GoValue))
  | field :: fieldRest, value :: valueRest => do
      let head ← normalizeValueForTy state field.typ value
      let tail ← buildStructFields state fieldRest valueRest
      return #[(field.name, head)] ++ tail
  | _, _ => return #[]

/-- Build a struct value from positional literal args at a struct type.
NOT recursive (C2): the type's `.defined` indirection is followed by
`TypeEnv.resolve`; a struct literal at a NON-struct named type fails
closed (identity tagging for defined-over-defined-struct is unresolved;
see the `TypeDef.defined` docstring). -/
def buildStructValue (state : ExecState) (typ : Ty) (args : Array GoValue) :
    Except Stop GoValue :=
  match state.types.resolve state.types.size typ with
  | .error e => .error e
  | .ok (.struct name fields) => do
      if fields.size != args.size then
        stuck s!"struct {name.key} literal expected {fields.size} field value(s), got {args.size}"
      .struct name <$> buildStructFields state fields.toList args.toList
  | .ok (.interfaceDecl name) => unsupported s!"struct literal for interface type {name.key}"
  | .ok (.opaque _ feature) => unsupported s!"struct literal for {feature}"
  | .ok (.plain (.unsupported feature)) => unsupported s!"struct literal for {feature}"
  | .ok (.plain other) => unsupported s!"struct literal for non-struct type {repr other}"

-- Not recursive: it calls only the now-total defaultValue / normalizeValueForTy,
-- so the for-loops are fine in a plain def.
def buildArrayValue (state : ExecState) (length : Nat) (elem : Ty)
    (args : Array (Int × GoValue)) : Except Stop GoValue := do
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
    | some _ => values := values.set! key.toNat (← normalizeValueForTy state elem value)
    | none => stuck s!"GoCore array literal index out of range: {key}"
  return .array values

def buildDefaultArrayValue (state : ExecState) (length : Nat) (elem : Ty) :
    Except Stop GoValue :=
  buildArrayValue state length elem #[]

-- Not recursive; total now that defaultValue / resolveDefinedAliases are.
def typeAssertValue (state : ExecState) (value : GoValue) (targetTy : Ty) :
    Except Stop (GoValue × Bool) := do
  let failed ← defaultValue state targetTy
  match value with
  | .nil => return (failed, false)
  | .interface dynTy inner =>
      match targetTy with
      | .interface interfaceName =>
          if ← dynamicImplementsInterface state dynTy interfaceName then
            return (.interface dynTy inner, true)
          else
            return (failed, false)
      | _ =>
          -- Concrete target: dynamic-type identity (S3 — structural
          -- BEq, no name rendering, so slice/map/array dynamic types
          -- assert correctly too; alias-free since C2).
          if dynTy == targetTy then
            return (inner, true)
          else
            return (failed, false)
  | other => unsupported s!"type assertion from non-interface value {repr other}"

def dynamicTypeNameForMessage (state : ExecState) : GoValue → String
  | .interface dynTy _ => goTypeNameForMessage state dynTy
  | .nil => "nil"
  | other => s!"{repr other}"

/-- Does `*T` (for a defined `T`) carry a NON-EMPTY method set on the
wire — some `MethodInfo` with receiver `T` (value receivers, which `*T`
inherits) or `*T` (pointer receivers)? Promoted methods are flattened
onto the embedding type at emission, so they are entries too. -/
def pointerMethodSetNonEmpty (state : ExecState) (elem : Ty) : Bool :=
  state.methods.any (fun m =>
    match methodRecvDynamicTy? state m with
    | some recv => recv == elem || recv == .pointer elem
    | none => false)

/-- The declaring package path a type-assertion text compares — gc's
`rtype.pkgpath()` (`runtime/type.go`), fed by `reflectdata`'s
`uncommonSize`/`typePkg` (`cmd/compile/internal/reflectdata/reflect.go`
@ go1.26.5): a type has a package path exactly when it has an UNCOMMON
section — every NAMED type, and an UNNAMED type whose method set is
NON-EMPTY — and `typePkg` of `*T` is `T`'s package. Audit fix round R1
(2026-09-05 [AGENT]; the first cut answered `""` for EVERY non-TypeId
`Ty`, so `*inner.Q, not *inner.Q` got ` (types from different scopes)`
where gc prints ` (types from different packages)` whenever `Q` has a
method). Arms:
* `.defined`/`.interface` → the display record's `pkg`; NO record
  REFUSES by name (the record is required per TypeDef — its absence is
  a hand-built-program defect; the retired `.getD ""` was a fail-open
  default beside a fail-noisy renderer, audit R10).
* `*T`, `T` defined non-pointer non-interface → `pkg(T)` when some
  method of `T` or `*T` is on the wire; when NONE is, the method-set
  record decides: `full` ⇒ the set is genuinely empty ⇒ `""` (gc: no
  uncommon section, pointer kind ⇒ `""`); `exported`-only or ABSENT ⇒
  the emptiness is UNKNOWN (unexported methods are off the wire /
  nothing recorded) ⇒ REFUSE by name rather than guess.
* `*sync.X` → `"sync"` (the primitives are gc's named types with
  methods; `sync.Mutex` and friends live in package `sync`).
* every other unnamed type — slices, maps, arrays, chans, funcs,
  `**T`, `*I` — → `""`: no methods, and neither struct nor interface
  kind (`pkgpath`'s two kind arms; the machine's one unnamed struct,
  `struct{}`, is a `.defined` TypeDef whose record says `""`, and an
  anonymous interface's record says `""` — gc: `t.Sym() == nil ⇒ tpkg
  = nil`, reflect.go's TINTER arm). -/
def typePkgForMessage (state : ExecState) (typ : Ty) : Except Stop String :=
  let recordPkg (id : TypeId) : Except Stop String :=
    match typeDisplay? state id with
    | some d => pure d.pkg
    | none => unsupported s!"type-assertion text: TypeId {id.key} has no display record, so its \
declaring package path (gc's pkgpath(), the `(types from different packages|scopes)' \
suffix) cannot be derived (design note 2026-09-05 §3.2: no record is a defect, never `\"\"')"
  -- A `.defined` index reaches its record through the entry's key (C2);
  -- an index the table does not have REFUSES by name (never `""`).
  let entryKey (idx : TypeIdx) : Except Stop TypeId :=
    match state.types.nameOf? idx with
    | some id => pure id
    | none => unsupported s!"type-assertion text: type index {idx} is not in the type table \
(size {state.types.size}), so its declaring package path cannot be derived (unreachable on a \
decoded program; fail closed)"
  -- (No alias resolution: every `Ty` on the machine is its canonical form, C2.)
  match typ with
  | .defined idx => do recordPkg (← entryKey idx)
  | .interface id => recordPkg id
  | .pointer elem =>
      match elem with
      | .defined idx => do
          let id ← entryKey idx
          if pointerMethodSetNonEmpty state (.defined idx) then recordPkg id
          else
            match methodSetCoverage? state id.key with
            | some .full => pure ""
            | some .exported =>
                unsupported s!"type-assertion text: whether *{displayNameOf state idx} has a method set \
(gc's pkgpath() of a pointer type is its element's package iff the pointer's method set is \
non-empty) is UNDECIDABLE from an exported-only method-set record with no exported method on \
the wire — refused rather than guessed (BUG-009/BUG-053 class)"
            | none =>
                unsupported s!"type-assertion text: *{displayNameOf state idx} — {id.key} has NO \
method-set record on the wire, so whether *T's method set is empty (gc's pkgpath() rule) is \
unknown; refused rather than guessed (BUG-009/BUG-053 class)"
      | .sync _ => pure "sync"
      | _ => pure ""
  | _ => pure ""

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
    (sourceTy : Option Ty) (missingMethod : Option String) : Except Stop String := do
  -- The machine-minted runtime-error payload has ONE synthetic dynamic
  -- type where gc has several concrete ones (`runtimeErrorDisplayMarker`):
  -- a text naming it (`r := recover(); r.(int)`) cannot be gc's — refuse
  -- by name rather than print a marker as an observation (audit fix
  -- round R3, 2026-09-05 [AGENT]; the interface-target arm never gets
  -- here — satisfaction refuses first on the missing method-set record).
  if let .interface (.defined dynIdx) _ := value then
    if dynIdx == runtimeErrorTypeIdx then
      unsupported s!"type-assertion panic text names the dynamic type of a recovered runtime \
error, which the machine models as one synthetic id ({runtimeErrorTypeId.key}, reserved table \
index {runtimeErrorTypeIdx}) where gc has a \
concrete runtime type per fault (runtime.errorString / runtime.boundsError / \
*runtime.TypeAssertionError / …) — no byte-exact text exists (BUG-009/BUG-053 class)"
  let sourceName :=
    match sourceTy with
    | some t => goTypeNameForMessage state t
    | none => "interface {}"
  match targetTy, value with
  | .interface _, .nil =>
      pure ("interface conversion: interface is nil, not " ++ goTypeNameForMessage state targetTy)
  | .interface _, _ =>
      let missing :=
        match missingMethod with
        | some m => s!": missing method {m}"
        | none => ""
      pure ("interface conversion: " ++ dynamicTypeNameForMessage state value ++
        " is not " ++ goTypeNameForMessage state targetTy ++ missing)
  | _, _ =>
      let base := "interface conversion: " ++ sourceName ++ " is " ++
        dynamicTypeNameForMessage state value ++ ", not " ++
        goTypeNameForMessage state targetTy
      -- gc's disambiguating suffix (`runtime/error.go`
      -- `TypeAssertionError.Error`, probed go1.26.5 — design note
      -- 2026-09-05 §1/§3.2): this arm is reached only when the dynamic
      -- and asserted types DIFFER, so equal displays are gc's deliberate
      -- name-ambiguity — `inner.T, not inner.T (types from different
      -- packages)` when the declaring paths differ, `main.L, not main.L
      -- (types from different scopes)` when they agree (two functions'
      -- local `L`; two anonymous types). The paths come from
      -- `typePkgForMessage` (gc's `pkgpath()`), which REFUSES when the
      -- wire cannot decide them — the refusal propagates, never a guess.
      match value with
      | .interface dynTy _ =>
          if goTypeNameForMessage state dynTy == goTypeNameForMessage state targetTy then
            if (← typePkgForMessage state dynTy) != (← typePkgForMessage state targetTy) then
              pure (base ++ " (types from different packages)")
            else
              pure (base ++ " (types from different scopes)")
          else pure base
      | _ => pure base

def valueAsInt : GoValue → Except Stop Int
  | .int value _ => return value
  | other => stuck s!"expected int value, got {repr other}"

def valueAsIntValue : GoValue → Except Stop (Int × IntKind)
  | .int value kind => return (value, kind)
  | other => stuck s!"expected int value, got {repr other}"

def valueAsBool : GoValue → Except Stop Bool
  | .bool value => return value
  | other => stuck s!"expected bool value, got {repr other}"

def valueAsSlice : GoValue → Except Stop SliceValue
  | .slice value => return value
  | other => stuck s!"expected slice value, got {repr other}"

def valueAsMap : GoValue → Except Stop MapValue
  | .map value => return value
  | other => stuck s!"expected map value, got {repr other}"

def valueAsChan : GoValue → Except Stop ChanValue
  | .chan value => return value
  | other => stuck s!"expected channel value, got {repr other}"

/-- gc's nil-dereference `runtime.Error` text — the one message the
machine raises at every nil-address use (`valueAsLoc`, the nil-callee
invocations, the nil-box dispatch). -/
def nilDerefPanicText : String :=
  "runtime error: invalid memory address or nil pointer dereference"

def valueAsLoc : GoValue → Except Stop Loc
  | .addr loc => return loc
  | .nil => panic nilDerefPanicText
  | other => stuck s!"expected address value, got {repr other}"

mutual

/-- Go's `==` at static type `ty`. Structural on the LEFT operand (C2,
section note): array elements and struct fields are its subterms, and the
interface arm compares the boxed DYNAMIC values — subterms too — at the
dynamic type (a type DISCOVERED from the value, which is why this walk is
value-directed where `normalizeValueForTy` is type-directed).
`TypeEnv.resolve` reads the declared body behind a `.defined` at each
step. -/
def valueEq (state : ExecState) : Ty → GoValue → GoValue → Except Stop Bool
  | ty, left, right =>
    match state.types.resolve state.types.size ty, left, right with
    | .error e, _, _ => .error e
    | .ok (.plain .bool), .bool l, .bool r => return l == r
    | .ok (.plain .bool), l, r => stuck s!"bool equality expected bool operands, got {repr l} and {repr r}"
    | .ok (.plain (.int _)), .int l _, .int r _ => return l == r
    | .ok (.plain (.int kind)), l, r => stuck s!"{kind.name} equality expected int operands, got {repr l} and {repr r}"
    -- Go == on floats is IEEE equality (note §4): NaN ≠ NaN even at
    -- identical bits, +0 == -0 across different bits — NEVER bit
    -- equality (that is `GoValue.eqb`, the structural identity).
    | .ok (.plain (.float kind)), .float lb lk, .float rb rk =>
        if lk == kind && rk == kind then
          match kind with
          | .float64 => return FloatBits.feq64 lb rb
          | .float32 => return FloatBits.feq32 lb rb
        else
          stuck s!"{kind.name} equality on mismatched float kinds: {lk.name} and {rk.name}"
    | .ok (.plain (.float kind)), l, r => stuck s!"{kind.name} equality expected float operands, got {repr l} and {repr r}"
    | .ok (.plain .string), .string l, .string r => return l == r
    | .ok (.plain .string), l, r => stuck s!"string equality expected string operands, got {repr l} and {repr r}"
    -- Go: func values are comparable only against nil.
    | .ok (.plain (.funcType _ _ _)), .nil, .nil => return true
    | .ok (.plain (.funcType _ _ _)), .funcVal _ _, .nil => return false
    | .ok (.plain (.funcType _ _ _)), .nil, .funcVal _ _ => return false
    | .ok (.plain (.funcType _ _ _)), l, r =>
        stuck s!"func values are not comparable: {repr l} and {repr r}"
    | .ok (.plain (.pointer _)), .addr l, .addr r => return l == r
    | .ok (.plain (.pointer _)), .nil, .nil => return true
    | .ok (.plain (.pointer _)), .addr _, .nil => return false
    | .ok (.plain (.pointer _)), .nil, .addr _ => return false
    | .ok (.plain (.pointer _)), l, r => stuck s!"pointer equality expected pointer/nil operands, got {repr l} and {repr r}"
    | .ok (.plain (.array length elem)), .array ⟨l⟩, .array ⟨r⟩ => do
        if l.length != length then
          stuck s!"left array equality length mismatch: expected {length}, got {l.length}"
        if r.length != length then
          stuck s!"right array equality length mismatch: expected {length}, got {r.length}"
        valueEqList state elem l r
    | .ok (.plain (.array length _)), l, r =>
        stuck s!"array equality expected array({length}) operands, got {repr l} and {repr r}"
    | .ok (.plain (.slice _)), .slice l, .slice r => do
        validateSlice l
        validateSlice r
        match l.base, r.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil slices are not comparable"
    | .ok (.plain (.slice _)), .slice l, .nil => do
        validateSlice l
        return l.base.isNone
    | .ok (.plain (.slice _)), .nil, .slice r => do
        validateSlice r
        return r.base.isNone
    | .ok (.plain (.slice _)), l, r => stuck s!"slice equality expected slice/nil operands, got {repr l} and {repr r}"
    | .ok (.plain (.map _ _)), .map l, .map r =>
        match l.base, r.base with
        | none, none => return true
        | none, some _ => return false
        | some _, none => return false
        | some _, some _ => stuck "non-nil maps are not comparable"
    | .ok (.plain (.map _ _)), .map l, .nil => return l.base.isNone
    | .ok (.plain (.map _ _)), .nil, .map r => return r.base.isNone
    | .ok (.plain (.map _ _)), l, r => stuck s!"map equality expected map/nil operands, got {repr l} and {repr r}"
    -- Channel == is REFERENCE identity (spec: "equal if they were created
    -- by the same call to make or if both have value nil"; probe p12) —
    -- the derived ChanValue BEq is exactly base-loc equality, nil = base
    -- none. Unlike maps, non-nil channels ARE comparable.
    | .ok (.plain (.chan _ _)), .chan l, .chan r => return l == r
    | .ok (.plain (.chan _ _)), .chan l, .nil => return l.base.isNone
    | .ok (.plain (.chan _ _)), .nil, .chan r => return r.base.isNone
    | .ok (.plain (.chan _ _)), .nil, .nil => return true
    | .ok (.plain (.chan _ _)), l, r => stuck s!"channel equality expected channel/nil operands, got {repr l} and {repr r}"
    | .ok (.plain (.interface _)), .nil, .nil => return true
    | .ok (.plain (.interface _)), .nil, _ => return false
    | .ok (.plain (.interface _)), _, .nil => return false
    -- Box-vs-box (S3, Perennial `go_eq_interface` shape): different
    -- dynamic types → false, no value comparison. Same dynamic type → Go
    -- first checks the DYNAMIC type's comparability (resolved through
    -- defined types: slices/maps/funcs anywhere inside panic at runtime
    -- under the DYNAMIC name — `comparing uncomparable type main.T`),
    -- then compares the payloads AT the dynamic type.
    | .ok (.plain (.interface _)), .interface dynL innerL, .interface dynR innerR =>
        if dynL != dynR then
          return false
        else
          match tyUncomparable state dynL with
          | some true =>
              throw (.panic s!"runtime error: comparing uncomparable type {goTypeNameForMessage state dynL}")
          -- UNKNOWN comparability (an opaque declaration) falls through
          -- to the walk at the dynamic type, whose `.defined` handling
          -- fails closed with the precise reason.
          | _ => valueEq state dynL innerL innerR
    | .ok (.plain (.interface _)), l, r => unsupported s!"interface equality for {repr l} and {repr r}"
    -- Go's == is DEFINED on the sync structs (plain comparable fields),
    -- but comparing sync primitives is copy-class misuse (they "must
    -- not be copied after first use") with no in-scope consumer — fail
    -- closed rather than pin an equality semantics nothing exercises
    -- (recorded, design note §9).
    | .ok (.plain (.sync kind)), _, _ =>
        unsupported s!"equality at sync type sync.{kind.name} (unmodeled; sync values fail closed under ==)"
    | .ok (.struct name fields), .struct leftType ⟨leftFields⟩, .struct rightType ⟨rightFields⟩ => do
        -- A mixed comparison is legal exactly when one operand is
        -- ASSIGNABLE to the other's type; the wire's only unnamed
        -- struct is the canonical `struct{}` (BUG-011 escape).
        -- The escape is PAIR-level (audit F4 + delta-review R1,
        -- 2026-08-05): a mismatching operand is admitted when the
        -- operand PAIR is Go-comparable — equal tags, or EITHER
        -- side tagged the canonical `struct{}` (the frontend emits
        -- the LEFT operand's static type as the context, so the
        -- anonymous literal can sit on either side of the
        -- mismatch). Two DIFFERENT defined types never compare,
        -- at any context — F4's target, still held.
        if leftType != name &&
            !(emptyStructAssignable leftType name fields ⟨leftFields⟩ &&
              (leftType == rightType || leftType.key == "struct{}" ||
                rightType.key == "struct{}")) then
          stuck s!"left struct equality type mismatch: expected {name.key}, got {leftType.key}"
        if rightType != name &&
            !(emptyStructAssignable rightType name fields ⟨rightFields⟩ &&
              (leftType == rightType || leftType.key == "struct{}" ||
                rightType.key == "struct{}")) then
          stuck s!"right struct equality type mismatch: expected {name.key}, got {rightType.key}"
        if leftFields.length != fields.size then
          stuck s!"left struct equality field count mismatch: expected {fields.size}, got {leftFields.length}"
        if rightFields.length != fields.size then
          stuck s!"right struct equality field count mismatch: expected {fields.size}, got {rightFields.length}"
        valueEqFields state fields.toList leftFields rightFields
    | .ok (.struct name _), l, r => stuck s!"struct equality expected struct {name.key} operands, got {repr l} and {repr r}"
    | .ok (.opaque _ feature), _, _ => unsupported s!"equality for {feature}"
    | .ok (.interfaceDecl name), _, _ => unsupported s!"equality at interface type {name.key}"
    | .ok (.plain (.unsupported feature)), _, _ => unsupported s!"equality for {feature}"
    -- `TypeEnv.resolve` never returns a `.plain (.defined _)`; the arm
    -- exists for exhaustiveness and fails closed.
    | .ok (.plain other), l, r => stuck s!"equality at unresolved type {repr other}: {repr l} and {repr r}"

/-- Compare array elements pairwise at the element type; callers
guarantee equal, checked lengths. -/
def valueEqList (state : ExecState) (elem : Ty) : List GoValue → List GoValue → Except Stop Bool
  | leftValue :: leftRest, rightValue :: rightRest => do
      if ← valueEq state elem leftValue rightValue then
        valueEqList state elem leftRest rightRest
      else
        return false
  | _, _ => return true

/-- Compare struct fields pairwise at their declared types, checking
field-name alignment on both sides. -/
def valueEqFields (state : ExecState) :
    List FieldDef → List (String × GoValue) → List (String × GoValue) → Except Stop Bool
  | field :: fieldRest, (leftName, leftValue) :: leftRest, (rightName, rightValue) :: rightRest => do
      if leftName != field.name then
        stuck s!"left struct equality field mismatch: expected {field.name}, got {leftName}"
      if rightName != field.name then
        stuck s!"right struct equality field mismatch: expected {field.name}, got {rightName}"
      if ← valueEq state field.typ leftValue rightValue then
        valueEqFields state fieldRest leftRest rightRest
      else
        return false
  | _, _, _ => return true

end

-- Downstream-unfolding pin: a closed comparison — struct over a defined
-- int, through an interface box — evaluates by `decide`.
example :
    valueEq { types := #[(⟨"main.T"⟩, .defined (.int .int)),
                        (⟨"main.S"⟩, .struct #[{ name := "x", typ := .defined 0 }, { name := "i", typ := .interface ⟨"any"⟩ }])] }
      (.defined 1)
      (.struct ⟨"main.S"⟩ #[("x", .int 3 .int), ("i", .interface (.defined 0) (.int 4 .int))])
      (.struct ⟨"main.S"⟩ #[("x", .int 3 .int), ("i", .interface (.defined 0) (.int 4 .int))])
      = .ok true := rfl

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
    (isInsert : Bool) (nonEmpty : Bool) : Except Stop Unit :=
  match valueHashability state key with
  | .unhashable name => throw (.panic (hashPanicMessage name (isInsert || nonEmpty)))
  | .unknown name => unsupported s!"map key hashability for unknown defined type {name}"
  | .hashable => pure ()

-- Not recursive; total now that valueEq is. The for-loop is fine in a plain def.
-- Key-retention latitude note: the index this returns feeds
-- `mapAssignValue`'s always-replace `entries.set!` — the E10 pinned
-- latitude; the site caveat (envelope, observable key kinds, transfer
-- limit) lives at `mapAssignValue` (Machine.lean).
def mapEntryIndex? (state : ExecState) (keyTy : Ty)
    (entries : Array (Nat × GoValue × GoValue))
    (key : GoValue) (isInsert : Bool := false) : Except Stop (Option Nat) := do
  checkKeyHashable state key isInsert (!entries.isEmpty)
  let mut i := 0
  for (_, entryKey, _) in entries do
    if ← valueEq state keyTy entryKey key then
      return some i
    i := i + 1
  return none

-- The float arms are IEEE-unordered on NaN (note §4): a NaN operand
-- makes < <= > >= ALL false, so > is lt with swapped operands and >= is
-- le swapped — NOT the negation of <=/<.
def valueLess : GoValue → GoValue → Except Stop Bool
  | .int left _, .int right _ => return left < right
  | left@(.float _ _), right => floatCompareResult "<" FloatBits.flt64 FloatBits.flt32 left right
  | .string left, .string right => return GoString.compare left right == .lt
  | left, right => stuck s!"mismatched < operands: {repr left} and {repr right}"

def valueAtMost : GoValue → GoValue → Except Stop Bool
  | .int left _, .int right _ => return left <= right
  | left@(.float _ _), right => floatCompareResult "<=" FloatBits.fle64 FloatBits.fle32 left right
  | .string left, .string right => return GoString.compare left right != .gt
  | left, right => stuck s!"mismatched <= operands: {repr left} and {repr right}"

def valueGreater : GoValue → GoValue → Except Stop Bool
  | .int left _, .int right _ => return left > right
  | left@(.float _ _), right =>
      floatCompareResult ">" (fun l r => FloatBits.flt64 r l) (fun l r => FloatBits.flt32 r l) left right
  | .string left, .string right => return GoString.compare left right == .gt
  | left, right => stuck s!"mismatched > operands: {repr left} and {repr right}"

def valueAtLeast : GoValue → GoValue → Except Stop Bool
  | .int left _, .int right _ => return left >= right
  | left@(.float _ _), right =>
      floatCompareResult ">=" (fun l r => FloatBits.fle64 r l) (fun l r => FloatBits.fle32 r l) left right
  | .string left, .string right => return GoString.compare left right != .lt
  | left, right => stuck s!"mismatched >= operands: {repr left} and {repr right}"

/-! ### Operator result helpers

Value-level result computation for the arithmetic/bitwise/shift operators.
Moved here from `Eval.lean` (reshape S1 motion, 2026-07-23) so the
fine-grained machine (`Machine.lean`) can share them with the interpreter
without depending on the big-step module slated for deletion. Pure motion —
no behavior change. -/

def intBinaryResult (opName : String) (op : Int → Int → Int) (left right : GoValue) :
    Except Stop GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let (rightValue, rightKind) ← valueAsIntValue right
  let kind ←
    match IntKind.compatibleResult leftKind rightKind with
    | some kind => pure kind
    | none => stuck s!"mismatched {opName} integer kinds: {leftKind.name} and {rightKind.name}"
  return .int (kind.normalize (op leftValue rightValue)) kind

def intKindBitWidth (opName : String) (kind : IntKind) : Except Stop Nat := do
  match kind.bits? with
  | some bits => return bits
  | none => unsupported s!"{opName} for unbounded integer kind {kind.name}"

def intKindUnsignedNat (kind : IntKind) (value : Int) : Except Stop Nat := do
  let bits ← intKindBitWidth "bitwise operator" kind
  let modulus : Int := (2 : Int) ^ bits
  return (value % modulus).toNat

def intBitwiseBinaryResult (opName : String) (op : Nat → Nat → Nat) (left right : GoValue) :
    Except Stop GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let (rightValue, rightKind) ← valueAsIntValue right
  let kind ←
    match IntKind.compatibleResult leftKind rightKind with
    | some kind => pure kind
    | none => stuck s!"mismatched {opName} integer kinds: {leftKind.name} and {rightKind.name}"
  let leftBits ← intKindUnsignedNat kind leftValue
  let rightBits ← intKindUnsignedNat kind rightValue
  return .int (kind.normalize (Int.ofNat (op leftBits rightBits))) kind

def intBitClearResult (left right : GoValue) : Except Stop GoValue := do
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

def intBitNegResult (value : GoValue) : Except Stop GoValue := do
  let (intValue, kind) ← valueAsIntValue value
  let bits ← intKindBitWidth "^" kind
  let mask := (2 ^ bits) - 1
  let valueBits ← intKindUnsignedNat kind intValue
  return .int (kind.normalize (Int.ofNat (Nat.xor valueBits mask))) kind

def shiftCountNat (count : GoValue) : Except Stop Nat := do
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

/-- A shift count at or past the operand's width leaves no operand bit in
place (spec#Operators: shifts "behave as if the left operand is shifted n
times by 1"): 0 for every left shift and for an unsigned right shift, the
sign fill (-1 / 0) for a signed right shift. The saturation is decided
BEFORE `2 ^ count` is formed — over `Int` the power is unbounded, and a
count such as `1 << 32` made Lean's `Nat.pow` guard ABORT the process
(no observation, no refusal) where Go answers 0 (BUG-096). The width
lookup refuses an unbounded kind by name; none reaches the machine (the
decoder never produces one), so this is the fail-closed arm, not a
regression. ORDER IS LOAD-BEARING: `shiftCountNat` (the negative-count
panic, `runtime error: negative shift amount`) runs BEFORE the width lookup
and the saturation test — saturating on a `Nat` obtained from a negative
count would answer a value where Go panics; `Tests/GoCoreEval.lean`'s
`coreNegativeShiftFunction` pins the panic (audit fix R6, 2026-09-05). -/
def intShiftLeftResult (left right : GoValue) : Except Stop GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let count ← shiftCountNat right
  let bits ← intKindBitWidth "<<" leftKind
  if bits ≤ count then
    return .int 0 leftKind
  return .int (leftKind.normalize (leftValue * ((2 : Int) ^ count))) leftKind

def intShiftRightResult (left right : GoValue) : Except Stop GoValue := do
  let (leftValue, leftKind) ← valueAsIntValue left
  let count ← shiftCountNat right
  let bits ← intKindBitWidth ">>" leftKind
  if bits ≤ count then
    -- Every operand bit is shifted out: the sign fill remains (BUG-096).
    return .int (if leftKind.signed && leftValue < 0 then -1 else 0) leftKind
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
    Except Stop (Array GoValue) := do
  validateSlice slice
  let mut values := #[]
  for i in [:slice.len] do
    values := values.push (← loadLoc state (← sliceIndexLoc slice (Int.ofNat i)))
  return values

/-! The following were also never recursive; moved out of `Eval.lean`'s mutual
cluster (reshape S2 motion, 2026-07-23) for sharing with `Machine`/`stepFn`.
Pure motion — no behavior change. -/

/-- The ranged/indexed map's cell contents: base cell, stamped entries
`(id, key, value)` in cell order, and the map's `nextId` counter
(entry-identity stamps, B1); `none` for a nil map. -/
def mapEntries (state : ExecState) (map : MapValue) :
    Except Stop (Option (Loc × Array (Nat × GoValue × GoValue) × Nat)) := do
  match map.base with
  | none => return none
  | some baseLoc =>
      let p ← mapPayload? state baseLoc
      return some (baseLoc, p.1, p.2)

def mapLookupValue (state : ExecState) (map : MapValue) (key : GoValue)
    (keyTy valueTy : Ty) : Except Stop (GoValue × Bool) := do
  match ← mapEntries state map with
  -- A NIL map still hashes the key: Go panics `hash of unhashable type: X`
  -- (the `h == nil` arm of mapKeyError; probed 2026-07-31) before returning
  -- the zero value.
  | none => do
      checkKeyHashable state key (isInsert := false) (nonEmpty := false)
      return (← defaultValue state valueTy, false)
  | some (_, entries, _) =>
      match ← mapEntryIndex? state keyTy entries key with
      | some i =>
          match entries[i]? with
          | some (_, _, value) => return (value, true)
          | none => stuck s!"missing map entry at index {i}"
      | none => return (← defaultValue state valueTy, false)

/-- gc's amortized growth POLICY (runtime/slice.go `nextslicecap`,
element-size-independent part): the CENTER of the spill envelope and the
default-stream (strict-lane) point. gc's REALIZED capacity additionally
depends on element size (size-class rounding, stack buffering) — the
envelope below, not this formula, is the admitted set. -/
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

/-- ENVELOPE upper end for the append-spill capacity choice (arc-final
audit F2 / BUG-021, 2026-08-06; spec §Appending: append "allocates a
new, sufficiently large underlying array" — ANY capacity ≥ newLen is
conforming, so the envelope is a pragmatic SUBSET of that latitude).
The admitted set is `[newLen, appendSpillUpper]`:
- LOWER end `newLen` — the spec floor, and gc realizes it (probe
  go1.26.5: nil []string + 2 elems → cap 2, below the growth formula's
  max(4,newLen); nil []struct{3 ints} + 1 → cap 1).
- UPPER end `max 32 (2 * growth)` — contains BOTH of gc's
  element-size-dependent mechanisms, which the element-size-free
  formula cannot see:
  (a) the compiler's 32-BYTE STACK BUFFER for small non-escaping
      appends: at most 32 bytes / elemsize ≤ 32 elements (probe: []byte
      cap 3 → len 4 realizes cap 32; []bool nil + 1 → 32);
  (b) SIZE-CLASS ROUNDING (runtime `roundupsize`): for allocations
      ≤ 32 bytes the realized capacity is ≤ 32 bytes / elemsize ≤ 32
      elements, covered by the floor; above 32 bytes the worst class
      step ratio is 48/33 < 1.5 < 2, so realized ≤ 2·growth (probes:
      []int cap 100 → len 101 realizes 224 ≤ 400; []int cap 130 → 131
      realizes 288 ≤ 520; []string cap 256 → 257 realizes 591 ≤ 1024).
Version-tracked by the membership pins slices/append-spill-* (the three
escaping regimes) and slices/full-slice-cap-zero (the formula point).
Widen deliberately if a toolchain leaves this window; never narrow to
one compiler mode. -/
def appendSpillUpper (oldCap newLen : Nat) : Nat :=
  max 32 (2 * appendGrowthCap oldCap newLen)

/-- The append-spill site's stream bound: |[newLen, upper]|. -/
def appendSpillWidth (oldCap newLen : Nat) : Nat :=
  appendSpillUpper oldCap newLen - newLen + 1

def buildAppendBackingValue (state : ExecState) (elem : Ty)
    (oldValues elemValues : Array GoValue) (newCap : Nat) : Except Stop GoValue := do
  let mut values := #[]
  for value in oldValues ++ elemValues do
    values := values.push (← normalizeValueForTy state elem value)
  if values.size > newCap then
    stuck s!"append backing capacity {newCap} smaller than length {values.size}"
  for _ in [:newCap - values.size] do
    values := values.push (← defaultValue state elem)
  return .array values

/-- gc's `panicwrap` text (runtime/error.go `panicwrap`, go1.26.5),
rendered from the method's receiver TypeId key and the method name:
`value method <pkg>.<T>.<M> called using nil *<T> pointer`. gc derives
`pkg` and `T` from the wrapper's SYMBOL name `<pkgpath>.(*T).M`, so the
qualifier is the import PATH (probe at the pin: `probe087/sub.T.Val …
nil *T pointer`; `main.Inner.Val … nil *Inner pointer` for the command
package) — exactly the frontend's path-qualified `TypeId.key`
(`qualifiedTypeName`, `pkgQualifier`), so this text is NOT in BUG-059's
name-vs-path class. A generic receiver's type arguments print as
`[...]` (`funcNamePiecesForPrint`, traceback.go: the wrapper symbol's
`[…]` span collapses; probe: `main.Box[...].Val … nil *Box[...]
pointer`), so the key's bracket span collapses the same way. Evidence:
`docs/evidence/2026-09-03_bug087-paniktext/`. Since the identity/display
split (2026-09-05, design note §3.2) this is the ONE message rendered from
the KEY, not the display record: the text is symbol-derived, and the
full-run re-pin showed the pinned `pkgs/valuer.T.Val` witness
(`multipkg/nil-value-method-text`) go red under the display —
`symbolKeyForMessage` below renders the receiver's key. -/
def panicwrapText (recvKey methodName : String) : String :=
  let (base, generic) :=
    match recvKey.splitOn "[" with
    | b :: _ :: _ => (b, true)
    | _ => (recvKey, false)
  let suffix := if generic then "[...]" else ""
  let typ := (base.splitOn ".").getLastD base
  s!"value method {base}{suffix}.{methodName} called using nil *{typ}{suffix} pointer"

/-- The receiver spelling `panicwrapText` consumes: the TypeId KEY (gc's
wrapper SYMBOL is path-qualified, `<pkgpath>.(*T).M`), pointers as `*`,
structural leaves as the message renderer spells them. -/
def symbolKeyForMessage (state : ExecState) (typ : Ty) : String :=
  match typ with
  | .defined idx =>
      match state.types.nameOf? idx with
      | some id => id.key
      | none => goTypeNameForMessage state typ   -- the visible unknown-index marker
  | .interface id => id.key
  | .pointer (.defined idx) =>
      match state.types.nameOf? idx with
      | some id => s!"*{id.key}"
      | none => goTypeNameForMessage state typ
  | other => goTypeNameForMessage state other

/-- **The BUG-087 envelope statement** (latitude inventory R9a; [USER]
ruling 2026-09-03 «demonic choice so both are admitted», relayed —
record in `docs/2026-08-31_qrow-rulings.md`): `some text` exactly when
a frame entry `fid args` would reach `dynamicDispatch?`'s `.nil` arm
below through gc's "simple `*T` wrapper around a `T` method" family
(`cmd/compile/internal/noder/reader.go` `methodWrapper`: `wrapper.IsPtr()
&& types.Identical(wrapper.Elem(), wrappee)`, `wrappee := method.Type.
Recv().Type`) — the anchor `fid` is an interface-receiver method, the
receiver argument is an interface box holding a NIL pointer, the
dispatch resolves with `needsDeref = true` (a value-receiver method
whose receiver type is EXACTLY the pointee — `concreteMethodForDynamic?`'s
pointer arm), and the target is a user-declared method, NOT a
synthesized promotion wrapper (`Func.wrapper` — a promoted method's
wrappee is the EMBEDDED type, never identical to the pointee, so gc
dereferences and gives the ordinary nil-dereference text; probed at the
pin for value-embedding, pointer-embedding and the value box: all
nil-deref). The text is member 1 of the two-member set the machine
admits at `ChoiceSite.nilValueMethodText`; member 0 is the nil-deref
text the arm below raises. Everything the predicate mirrors is checked
in the same order `enterFrame`/`dynamicDispatch?` check it (function
found, arity, anchor, box, resolution, target found), so `some` implies
the entry panics with the nil-deref text and `none` implies the entry
is not in the family — a `none` shape consumes nothing at the site.
The `go`-statement twin of the entry (`spawnStep`, Multi.lean) draws the
same pick (audit fix F1, 2026-09-03: `go v.M()` on a nil `*T` box gives
gc's panicwrap text under default/`-l`/`-N -l`). -/
def nilValueMethodText? (state : ExecState) (fid : FuncId) (args : List GoValue) :
    Option String :=
  match findFunctionIn? state.functions fid with
  | none => none
  | some func =>
    if func.args.size != args.length then none
    else
      match methodInfoByFuncId? state func.id with
      | none => none
      | some method =>
          match methodRecvInterfaceName? state method with
          | none => none
          | some _ =>
              match args.head? with
              | some (GoValue.interface dynTy .nil) =>
                  match concreteMethodForDynamic? state dynTy method.name with
                  | some (concrete, true) =>
                      match findFunctionIn? state.functions concrete.funcId with
                      | some target =>
                          if target.wrapper then none
                          else some (panicwrapText
                            (symbolKeyForMessage state concrete.recv) concrete.name)
                      | none => none
                  | _ => none
              | _ => none

def dynamicDispatch? (state : ExecState) (func : Func) (argValues : Array GoValue) :
    Except Stop (Option (Func × Array GoValue)) := do
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
                  -- set; nil pointer panics as a nil dereference). The
                  -- TEXT raised here is member 0 of BUG-087's two-member
                  -- set; on the wrapper family (`nilValueMethodText?`
                  -- above — the envelope statement) the frame-entry
                  -- funnel (`enterFramePick`, Machine.lean) draws the
                  -- `nilValueMethodText` pick and may substitute member
                  -- 1, gc's `panicwrap` text. This arm itself stays
                  -- stream-free (no `Choices` reach `Except`-land).
                  let recvValue ←
                    if needsDeref then
                      match inner with
                      | .addr loc => loadLoc state loc
                      | .nil => throw (.panic nilDerefPanicText)
                      | other => stuck s!"pointer-box receiver expected address, got {repr other}"
                    else
                      pure inner
                  return some (targetFunc, argValues.set! 0 recvValue)
              | none =>
                  -- No concrete method found. With a RECORD, that is a
                  -- machine invariant break (satisfaction should have
                  -- refused the box's construction path or the frontend
                  -- lied) — fail stuck. WITHOUT a record it is the
                  -- BUG-053 class (absence read as an answer): refuse
                  -- visibly instead (contract note §3, dispatch half).
                  -- One `throw` over a conditional payload — both arms
                  -- are errors, keeping the proof layer's error-arm
                  -- discharge shape (`dynamicDispatch?_locSup`).
                  throw (if dynamicMethodSetRecorded state dynTy then
                    Stop.stuck s!"dynamic type {goTypeNameForMessage state dynTy} has no method {method.name}"
                  else
                    Stop.unsupported s!"interface dispatch of {method.name} on \
{goTypeNameForMessage state dynTy}: its method set has NO record on the \
wire (a method-carrying type without a MethodSetRecord) — refusing \
rather than dispatching from no information (BUG-009/BUG-053 class)")
          -- Calling a method on a NIL interface: Go's runtime nil
          -- dereference panic (probe-pinned; the stub body behind this
          -- is unreachable and fails stuck if a bug ever reaches it).
          | some GoValue.nil =>
              throw (.panic nilDerefPanicText)
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

/-! ## The seal is gone (C2, 2026-09-05)

The value-walk wrappers used to be `@[irreducible]` (de-WF, 2026-08-03):
left reducible, the ELABORATOR's `whnf`/`isDefEq` dove into the
1024-literal fuel towers during unification. There is no literal budget
any more — the descents are seeded at `types.size`, a projection of the
state — so there is nothing for defeq to dive into and nothing to seal.
The pins below hold the unfolding pattern downstream proofs use: the
wrapper unfolds to its two layers by `simp`, and a closed instance
evaluates by `rfl`/`decide`. -/
example (σ : ExecState) (kind : IntKind) (v : Int) :
    normalizeValueForTy σ (.int kind) (.int v kind)
      = .ok (.int (kind.normalize v) kind) := by
  simp [normalizeValueForTy, normalizeValueForTyTy]
  rfl
example (σ : ExecState) (kind : IntKind) :
    defaultValue σ (.int kind) = .ok (.int 0 kind) := by
  simp [defaultValue, defaultValueTy]
  rfl
example (σ : ExecState) (a b : Bool) :
    valueEq σ .bool (.bool a) (.bool b) = .ok (a == b) := by
  unfold valueEq
  simp [TypeEnv.resolve, pure, Except.pure]
example : Ty.mentionsUnsupported (.pointer .bool) = false := rfl
