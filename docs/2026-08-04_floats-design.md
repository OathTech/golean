# Floats fidelity design note — slice 4 of the general-coverage arc (2026-08-04)

Status: DECIDED (2026-08-05) — all recommendations adopted; the
resolutions are recorded in §11 and bind slice 4's implementation.
Decided at coordinator level within the arc's delegated authority
(every resolution follows from already-established doctrine, argued
per point in §11); the whole note is flagged for re-argument at the
arc-final user-authorized audit, envelope statements especially.
Points are tagged **[FACT]** (verified against a primary source, cited) or
**[RECOMMENDATION]** (adopted per §11).
Written from an isolated worktree; sources read at the paths given.
Charter: `docs/2026-08-04_general-coverage-arc.md` slice 4. Binding
doctrine: `docs/2026-08-04_nondeterminism-doctrine.md` (envelope
statements, possibilistic claims), CLAUDE.md (fail-closed, guardrails
first, proof-facing totality, kernel reducibility).

Oracle toolchain at time of writing: go1.26.5 linux/amd64
(`/usr/local/go`). Lean toolchain: v4.31.0. Spec quotes below are
verbatim from `/usr/local/go/doc/go_spec.html` (the go1.26.5 spec).

---

## 1. What the corpus pins (behavior inventory)

**[FACT]** 40 red case ids: 20 under `floats/` (12 non-generic + 8
`floats/generic-type-set/*`), 20 under `complex/` (11 non-generic + 9
`complex/generic-type-set/*`). All are `frontend-export` FAILs — the
frontend fails closed at `emitBasic` (no float32/float64 arm,
`tools/nativefrontend/wire.go:200-238`) and `emitConstValue` (no
`constant.Float` arm, `emit.go:2534-2566`). Two complex cases already
PASS (`complex/constant-real-imag`, `complex/real-imag-real-args`)
because go/types constant-folds them entirely to ints/bools before the
frontend ever sees a float — constant folding already flows through the
frontend for every type.

**[FACT]** Every float/complex subject returns `int` — scores built from
comparisons and conversions. No corpus case observes a float value
directly, prints one, or passes one as an argument. The observation
channel currently has no float shape on either side (Go harness
`tools/coverageharness/main.go:279-341` hits `default:` → "unsupported
Go observation kind" for `reflect.Float64`; `GoLean/CLI.lean` has no
float tag). So Go's shortest-representation printing never enters the
current trust surface; §5 below decides the format for when
float-returning subjects arrive.

What the 12 implementable (non-generic) floats cases require of the
semantics, case by case:

| case | pins |
|---|---|
| `finite-arithmetic` | exact binary64 `+ - * /`, `<`, `==` on dyadic rationals |
| `division-specials` | `1/0=+Inf`, `-1/0=-Inf`, `0/0=NaN`, **no panic**; Inf ordering; `NaN != NaN` |
| `nan-comparisons` | `NaN` unordered: `<`, `>`, `==` all false; `!=` true |
| `signed-zero` | `+0 == -0`; `1/+0=+Inf`, `1/-0=-Inf`; **unary `-` on a variable holding `+0` yields `-0`** |
| `precision-rounding` | round-to-nearest-even at both widths: `2^24+1→2^24` (f32 add), `2^53+1→2^53` (f64 add), `2^53+2` exact |
| `float32-conversion-rounding` | f64→f32 conversion rounding (`16777217.0 → 16777216`) |
| `float32-specials` | binary32 overflow→`+Inf` (`maxf32*2`); subnormal underflow→`0` (min-subnormal `/2`, ties-to-even) |
| `to-int-truncation` | float→int truncation toward zero, incl. negatives |
| `to-uint-truncation` | float→uint8 in-range truncation |
| `compound-assign` | `/= += *=` on float32 with untyped-constant RHS adaptation; `int(f*10)` |
| `defined-type-ops` | defined type over float64: ops at underlying, `==` at the defined type, constant operand (`a * 2`) |
| `typed-constant-adaptation` | untyped constant expressions folded exactly, then typed at float32/float64 (single rounding at the typing boundary) |

The 8 `floats/generic-type-set/*` cases pin the same behaviors under
type-parameter instantiation and are **double-blocked**: they need this
slice's float semantics AND arc slice 6 (generics). The floats slice
alone can flip at most 12 of the 20 floats reds. Same split for
complex (11 + 9). Exit-criteria accounting should say so explicitly.

**[FACT]** Notably absent from the corpus (candidates for the
guardrails-first step, §8 slice F0): float map keys (NaN-key insertion
multiplicity, ±0-key overwrite), FMA-shaped expressions (`x*y + z` with
fusion-sensitive values), out-of-range float→int conversion,
`f++`/`f--`, float `min`/`max` builtins, int64/uint64→float rounding at
magnitudes above 2^53/2^24.

---

## 2. The numerics model — options against the two hard constraints

The constraints, treated as HARD per the charter and the de-WF
discipline (arc plan, "no opaque derived instances on semantic paths —
the `GoValue.eqb` lesson"):

- **Logical definedness**: no semantic path through a function whose
  logical value in Lean is unspecified.
- **Kernel evaluability**: `Terminates`-style discharges kernel-reduce
  the interpreter, so float ops must reduce in the kernel.

### (a) Lean's builtin `Float` — REJECTED (fails both constraints)

**[FACT]** In Lean core v4.31.0
(`~/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Init/Data/Float.lean`),
`Float` is `structure Float where val : floatSpec.float` over an
`opaque floatSpec : FloatSpec` whose stated inhabitant is `Unit`. Every
operation is an `opaque` constant with an `@[extern]` C implementation;
the docstrings say it outright: "This function does not reduce in the
kernel. It is compiled to the C addition operator." (`Float.add`,
`Float.ofBits`, all of them). `Float32` (Init/Data/Float32.lean) is the
same shape. So Lean `Float` is *logically* a completely unspecified
function on a completely unspecified type — the compiled behavior is
IEEE binary64, the logical model is nothing. This is exactly the
opaque-stub class the arc-final audit just purged from `GoValue.eqb`
(`Value.lean:433-447`): the differential would validate the compiled
function while theorems quantify an arbitrary inhabitant. It also
cannot kernel-reduce, so `Terminates` discharges over any float-touching
program would be impossible. Dead on both counts; no mitigation exists.

### (b) Bit-precise IEEE-754 over integer bit patterns — RECOMMENDED

**[FACT]** Nothing usable exists at our toolchain without new deps: the
root `GoLean` package has **zero** Lake dependencies
(`lake-manifest.json`: `"packages": []` — GoCore must stay
self-contained), and `proofs/` depends only on iris, batteries, Qq —
Batteries has no IEEE-754 formalization; Mathlib (not a dep, and not
addable for this) has only the toy `Mathlib.Data.FP.Basic`. So
bit-precise means **written in-repo**.

**[FACT]** A complete, trusted reference implementation exists in Go
itself: `runtime/softfloat64.go` (~545 lines, used for softfloat
targets, fuzz-tested against hardware in `softfloat64_test.go`). It
covers exactly the operation set the corpus needs: `funpack64/32`,
`fpack64/32` (round-to-nearest-even with sticky bits), `fadd64`,
`fsub64` (= add of `fneg64`), `fneg64` (sign-bit XOR — the correct `-x`),
`fmul64`, `fdiv64`, `fcmp64`, `f64to32`, `f32to64`, `f64toint`
(truncation, `ok=false` out of range), `fintto64`, `fintto32`
(single-rounded with sticky — it does *not* go via binary64), and the
32-bit arithmetic ops computed by round-tripping through binary64
(`fadd32 = f64to32(fadd64(f32to64 x, f32to64 y))`).

**[RECOMMENDATION]** Transcribe this into a new `GoLean/GoCore/
FloatBits.lean`: pure functions over bit patterns, no floats anywhere.
Represent bits as `Nat` (invariant `< 2^64` / `< 2^32`, enforced by a
`FloatKind.normalizeBits` mask exactly parallel to `IntKind.normalize`,
`Value.lean:58-68`) rather than `UInt64`: the kernel has GMP-accelerated
`Nat` arithmetic, so kernel reduction of the softfloat is fast, and it
matches the existing int-model idiom. Everything is structural
recursion or bounded loops (the normalize loops in funpack/fintto32 are
bounded by 64 iterations — write them fuel-structural on a 64 budget or
as `Nat.log2`-style arithmetic); total, no `partial`, no `WellFounded`,
kernel-reducible. Estimated 600–800 lines of Lean including docstrings.

Why transcription rather than de novo: the semantic domain is
identical (it IS Go's own definition of Go floats for softfloat
targets), it minimizes design freedom in 600 lines of bit fiddling, and
its test vectors can be exported as our eval-test vectors. Per the
trust-tools memory this is a *reference to transcribe*, never a vendored
dependency; the transcription is validated by the differential plus
oracle-generated bit-level vectors (§8).

Scope of the operation set: **exactly what §1 needs** — neg, add, sub,
mul, div, compare (eq/lt/le), f64↔f32, int↔float, plus one
rational→float rounding kernel (§7). Not full IEEE: no sqrt, no FMA op,
no remainder, no decimal conversions, no exceptions/flags (Go the
language exposes none of them), no rounding modes other than
nearest-even (Go has no rounding-mode control).

### (c) Rationals/reals with rounding — REJECTED as the value model

Honest but the wrong layer: Go values ARE bit patterns (NaN, -0, Inf,
subnormals are not rationals), so a rational value model needs sentinel
side-channels that reinvent the bit representation badly. However, a
**rational→float correctly-rounded conversion kernel** is needed anyway
(constants, §7; int→float is the `den = 1` case), so option (c)
survives as one function inside option (b), not as the model.

---

## 3. The latitude points and their envelope statements

The nondeterminism doctrine binds: every modeling of implementation
latitude needs a spec-anchored envelope statement. Floats have **four**
latitude points, not one. Spec text verbatim (§Floating-point
operators, §Conversions):

1. **Fusion**: "An implementation may combine multiple floating-point
   operations into a single fused operation, possibly across
   statements, and produce a result that differs from the value
   obtained by executing and rounding the instructions individually. An
   explicit floating-point type conversion rounds to the precision of
   the target type, preventing fusion that would discard that
   rounding."
2. **Extra precision**: "the value of a variable x of type float32 may
   be stored using additional precision beyond that of an IEEE 754
   32-bit number, but float32(x) represents the result of rounding x's
   value to 32-bit precision. Similarly, x + 0.1 may use more than 32
   bits of precision, but float32(x + 0.1) does not."
3. **Division-by-zero panic**: "The result of a floating-point or
   complex division by zero is not specified beyond the IEEE 754
   standard; whether a run-time panic occurs is
   implementation-specific."
4. **Out-of-range conversions**: "In all non-constant conversions
   involving floating-point or complex values, if the result type
   cannot represent the value the conversion succeeds but the result
   value is implementation-dependent."

### 3.1 Fusion + extra precision: pin strict per-op rounding — an envelope NARROWING, not a Choices site

**[FACT]** What gc actually does (grounded in the compiler source):
FMA fusion of `x*y ± z` is a platform property — ARM64
(`cmd/compile/internal/ssa/_gen/ARM64.rules:1771-1776`), RISCV64
(`RISCV64.rules:805-807`), and AMD64 **only when `GOAMD64 >= v3`**
(`AMD64.rules:1521`); `useFMA` is otherwise unconditional
(`ssa/func.go:850`, modulo the `fmahash` debug knob). Default
`GOAMD64` is v1, so **our oracle (linux/amd64, default) never fuses**.
gc keeps declared-type precision for every stored value and every
individual op on all currently supported targets (the x87 extra-
precision era is gone), so latitude point 2 is exercised by no gc
target we can run.

**[RECOMMENDATION]** Do **not** add a Choices consumption site for
fusion. Model every operation as individually rounded to the operand
type (strict IEEE per-op), deterministically. Reasons:

- A faithful fusion choice-site is not well-posed as a small named
  site: the spec allows fusing "possibly across statements", so the
  choice space is over *rewritings of the whole expression/statement
  DAG*, not a per-op coin. That breaks the doctrine's "consumption
  sites are named and few" structure and would contaminate the
  stream-obliviousness kit for a behavior no test can meaningfully
  enumerate.
- The precedent is the append-capacity envelope, verbatim from the
  doctrine: "a PRAGMATIC SUBSET of the spec's latitude: sound for
  transfer as long as real Go's policy lands inside, which the
  membership lane version-tracks; widen deliberately if a toolchain
  leaves the window." Same shape here, with *platform* in place of
  *version*.

**Envelope statement (fusion + extra precision)** — to ship in the
FloatBits module docstring:

> The Go spec permits fused floating-point operations (possibly across
> statements) and extra intermediate precision; explicit conversions
> force rounding. GoCore resolves this latitude to a single point:
> every operation rounds to the operand type, no fusion, no extra
> precision — IEEE-754 round-to-nearest-even per op. This is a
> deliberate envelope NARROWING (a strict subset of conforming
> behaviors), matching gc on linux/amd64 with default GOAMD64 (which
> emits no FMA and no extra precision) — the differential oracle's
> platform. Transfer soundness: ∀-stream theorems transfer to real Go
> executions whose toolchain+platform also resolves the latitude to
> per-op rounding; gc/arm64 and gc/amd64-v3 executions of programs
> containing fusable patterns (`x*y ± z` shapes without an intervening
> explicit conversion) are OUTSIDE the envelope, and claims do not
> transfer to them. Tracked by: the `floats/fma-shape` corpus tripwire
> (fails visibly if the oracle platform ever fuses); widen deliberately
> (per-site fused/unfused choice at the frontend-identified fusable
> shapes) if a supported target requires it.

This is the honest form: the too-narrow direction is normally the
soundness-relevant one, but here it is *detectable and platform-scoped*
(the differential itself explores it densely on the oracle platform),
and the alternative — admitting all fusions — would make every float
result a set and destroy the equality lane for zero corpus benefit.
The envelope-fidelity audit dimension should re-argue this against the
spec text at the next pre-merge audit.

**[RECOMMENDATION]** Add the `floats/fma-shape` guardrail case (values
where fused and unfused differ, e.g. computed by a Go probe comparing
`x*y+z` against `math.FMA(x,y,z)`), with a case comment stating it is
platform-sensitive by design: green on the amd64 oracle, and its going
red on a future arm64 runner is the tripwire firing, not noise.

### 3.2 Division by zero: pin no-panic — envelope narrowing

**[RECOMMENDATION]** gc never panics on float division by zero (the
`division-specials` case's `expected_status ok` pins this against the
real oracle). Model: IEEE results (`±Inf`, `NaN`), never a panic.
Envelope statement: spec allows a panic; we resolve to no-panic,
matching gc everywhere; a conforming-but-panicking implementation is
outside the envelope (none is known to exist). Note the machine
consequence: the current `.div` arm (`Machine.lean:211-215`) checks
`divisor == 0` via `valueAsInt` and panics — the float arm must dispatch
on value shape *before* that integer-only check.

### 3.3 Out-of-range float→int conversion: FAIL CLOSED

**[FACT]** The result is spec-implementation-dependent, and really does
diverge across gc targets (amd64 `CVTTSD2SI` yields `0x8000...0`;
arm64 `FCVTZS` saturates; NaN differs likewise). Go's own softfloat
returns `ok=false` and lets the caller decide (`softfloat64.go:374`).

**[RECOMMENDATION]** In-range conversions truncate toward zero
(spec-pinned: "the fraction is discarded (truncation towards zero)").
Out-of-range or NaN sources → explicit
`.unsupported "float-to-int conversion out of range/NaN
(implementation-dependent in Go)"` — a *runtime, value-dependent*
fail-closed refusal. Rationale: no portable meaning exists, modeling
the amd64 value would be over-fitting the oracle box, and a Choices
site over per-platform values is machinery with no consumer. Pin with
a **negative-corpus** case (expected-unsupported) so the refusal itself
is guarded. Revisit only if a real target (raft does not) depends on it.

### 3.4 What is NOT latitude

Comparisons ("Floating-point types are comparable and ordered. Two
floating-point values are compared as defined by the IEEE 754
standard."), conversion rounding ("rounded to the precision specified
by the destination type"), truncation direction, and constant typing
(§7) are all pinned by the spec — no envelope needed, fully
deterministic, equality-lane testable. **No new Choices consumption
site is proposed anywhere in this slice**; `applyStmtOpCore` stays
choices-free and the stream-obliviousness kit is untouched.

---

## 4. NaN, signed zero, map keys, equality layering

Three distinct equalities must not be conflated (this is where a naive
design ships a BUG-002-class error):

1. **Go `==` (IEEE equality)** — `valueEq` (`Ops.lean:1130`), keyed on
   `Ty`: new `.float` arm with `NaN != NaN` (even at identical bits)
   and `+0 == -0` (different bits). NOT bit equality. Ordering ops
   (`valueLess` etc., `Ops.lean:1322-1340`) get `.float` arms where any
   NaN operand makes `< <= > >=` all false.
2. **Structural `GoValue.eqb`** — stays BIT equality on floats
   (`NaN == NaN` true, `+0 ≠ -0`). It is proof/infrastructure
   equality, never Go `==`. Audit checklist item: no semantic path may
   route float `==` through `eqb` (today's only semantic-adjacent use,
   the `renderPanicHead` recovered-collapse identity check, is
   *correct* with bit equality — it asks "same panic value", where
   bit-identity is the conservative truth).
3. **Observation equality** — bit-exact modulo NaN canonicalization
   (§5).

**Map keys — the model is already right.** **[FACT]** Map key identity
routes through `valueEq` (`mapEntryIndex?`, `Ops.lean:1312`), so with
the IEEE `.float` arm: a NaN key never matches any entry — every
`m[NaN] = v` **appends a distinct entry** (`Machine.lean:621-623`,
`none → entries.push`), lookups and deletes of NaN find nothing.
That is exactly Go's documented NaN-map behavior, for free. Signed
zero: `+0` and `-0` are one key; on update the model *overwrites the
stored key* (`Machine.lean:622`, `entries.set! i (key, value)`), which
matches gc's `needkeyupdate = true` for float kinds (assigning
`m[-0.0]` after `m[+0.0]` leaves `-0.0` as the stored key). Both
behaviors need guardrail cases (§8 F0) since none exist — observed via
entry counts and `1/k` sign probes, both int-valued.

Hashability: floats fall into `valueHashability`'s `.hashable`
catch-all (`Ops.lean:1259-1267`) — correct, floats are hashable in Go.

**Internal NaN production.** **[RECOMMENDATION]** All GoCore-produced
NaNs are the canonical quiet NaN (f64 `0x7FF8_0000_0000_0000`, f32
`0x7FC0_0000` — softfloat64.go's `nan64`/`nan32` sans its low-bit
quirk; decide the exact constant when transcribing and pin it in eval
tests). Go the *language* cannot observe NaN payloads (only
`math.Float64bits` can, and math is out of scope), so this is
unobservable internally; it becomes observable only at the observation
boundary, handled next.

**Unary minus is currently mislowered for floats.** **[FACT]**
`NativeToIR.lean:216` lowers `-x` to `.sub (intLit 0) x`. For floats
`0 - x` is wrong at `x = +0` (gives `+0`; Go gives `-0` — IEEE negation
is a sign-bit flip, `fneg64`). The `signed-zero` case pins exactly this
(`negZero := -posZero`). **[RECOMMENDATION]** Add a proper negation
form (`Expr.neg`/`StrictOp.neg`, value-directed: int → `0 - v` as
today, float → sign-bit XOR) rather than making the frontend emit a
type-dispatched subtraction.

---

## 5. The observation channel: bits, never decimal strings

**[RECOMMENDATION]** When float-returning subjects arrive, the
observation JSON carries the **bit pattern**, not a printed decimal:

- Lean side (`CLI.lean` `goValueJson`):
  `{"tag":"float","kind":"float64","bits":<Nat as JSON integer>}`
  (and `"float32"` with the 32-bit pattern). `StrictJson` decode arm
  with exact-key checking, `bits` range-checked per kind — fail closed.
- Go side (`coverageharness` `_goleanReflectValue`): `reflect.Float64`
  → `math.Float64bits`, `reflect.Float32` → `math.Float32bits`
  (uint64/uint32 encode exactly as JSON integers; both JSON libraries
  handle full-range integers exactly).

Why bits: equality becomes bit-exact — signed zeros distinguishable
(they must be: `1/z` distinguishes them in Go), Inf exact, and Go's
shortest-representation `strconv` printing (subtle, version-sensitive,
and lossy to compare through) never enters the trust surface at all.
`fmt`-based observation stays out entirely; the harness observes
returned values, not stdout.

**NaN canonicalization at the boundary — required, not optional.**
**[FACT]** NaN bit patterns are platform- and path-dependent in real Go
(amd64 `DIVSD 0/0` produces `0xFFF8...` with the sign bit set; arm64
produces `0x7FF8...`; Go's own softfloat produces a third constant).
Since the language proper cannot observe payload or sign of NaN, both
encoders canonicalize: `IsNaN → 0x7FF8_0000_0000_0000` (f64) /
`0x7FC0_0000` (f32) before emission. Signed zero is NOT canonicalized.
Record in the encoder docstring: if `math.Float64bits` ever enters the
supported surface, payload propagation becomes observable and this
decision must be revisited (then: fail closed on NaN-payload-observing
programs rather than model per-platform payloads).

---

## 6. The float32 story

**[RECOMMENDATION]** `float32` is a first-class kind, not a view of
binary64:

- Values carry 32-bit patterns (invariant: bits < 2^32, enforced by
  `FloatKind.normalizeBits` at every store/coerce site, mirroring
  `IntKind.normalize`; malformed high bits fail closed in
  `isNormalForTy`).
- Arithmetic: transcribe Go's own approach — 32-bit operands widen
  exactly (`f32to64`), compute at binary64, round back (`f64to32`).
  **[FACT]** This is correct (not a double-rounding hazard) for
  `+ - * /` because binary64's 53 significand bits ≥ 2·24+2 (the
  innocuous-double-rounding condition), and it is literally what
  `runtime/softfloat64.go:506-517` does — Go itself defines float32
  softfloat arithmetic this way. Transcribing it verbatim minimizes
  transcription risk versus writing a parallel format-parameterized
  32-bit path.
- Where double rounding IS a hazard and must be avoided: **conversions
  into float32 from wide values**. `int64/uint64 → float32` and
  exact-rational → float32 must round ONCE at binary32. Go's
  `fintto32` (`softfloat64.go:417`) already single-rounds with a sticky
  bit (verified — it does not go via binary64); our rational kernel
  (§7) is parameterized by target format for the same reason. Never
  implement `float32(bigInt)` as `f64to32(fintto64(...))`.
- `float64 ↔ float32` conversion: `f64to32`/`f32to64` — the
  `float32-conversion-rounding` case pins the rounding, and widening is
  exact.
- Overflow at binary32 → `±Inf`, subnormal underflow with ties-to-even
  (`float32-specials` pins both; funpack/fpack handle subnormals).

---

## 7. Constant expressions: exact until the typing boundary

**[FACT]** Spec: constants are exact arbitrary-precision values ("there
are no constants denoting the IEEE 754 negative zero, infinity, and
not-a-number values"); implementations must carry ≥ 256-bit mantissas
and ≥ 16-bit exponents, error on constant overflow, and round to
nearest on precision limits. Typing a constant uses "IEEE 754
round-to-even rules but with an IEEE negative zero further simplified
to an unsigned zero". All untyped-constant *arithmetic* happens in
go/types/go/constant — which implements exactly this — and the frontend
already forwards folded results (that is why two complex cases pass
today, and why the int path emits `tv.Value.ExactString()`).

**[RECOMMENDATION — the one real wire-format decision in this note]**
Two options for how a (folded, possibly untyped-adapted) float constant
travels to GoCore:

- **(i) Frontend emits bits** (Goose's choice, `goose.go:2333-2339`:
  `math.Float64bits(constant.Float64Val(...))`). Cheapest; but the
  spec-mandated *rounding step* — a semantic decision — then lives in
  the frontend TCB, unvalidated by the differential (both sides would
  inherit go/constant's rounding).
- **(ii) Frontend emits the exact value** (numerator/denominator
  decimal strings from `ExactString()` — every literal, decimal or hex,
  and every go/constant result is exactly a rational), and **GoCore
  performs the single rounding** at the typing boundary via a
  correctly-rounded rational→format kernel (~100 lines: scale by
  bit-lengths, integer divide with remainder→sticky, round-to-even,
  `-0 → +0` per the spec's simplification).

Recommend **(ii)**: it keeps the rounding inside the differentially
validated core (a go/constant rounding quirk would surface as a red
case instead of being silently shared), it is the same kernel int→float
conversion needs anyway (`den = 1`), and the incremental frontend trust
stays what it already is for ints — go/types' *folding*, not its
rounding. The 256-bit story then needs no GoCore machinery at all:
exactness in, one rounding out. Option (i) is a legitimate cheaper
fallback if the coordinator prefers Goose-parity; flagging for the
arc-level call.

Note `typed-constant-adaptation` and the `distance(2.5)`-style operands
exercise this path; the frontend attaches the underlying float kind the
same way the int literal path attaches `IntKind` (`emit.go:2537-2548`).

---

## 8. Implementation sketch, in slices

New/changed surface (GoCore stays pure; nothing frontend-specific
enters it):

- `Ty.float (kind : FloatKind)`, `FloatKind = float32 | float64`
  (deriving the usual; `Ty.eqbFuel`, `dynamicName` ("float32"/
  "float64" — `reflect.Type.Name()` contract), `Ty.mentionsUnsupported`
  arms).
- `GoValue.float (bits : Nat) (kind : FloatKind)` — single constructor
  with normalize-enforced width invariant, mirroring `.int`
  (alternative: two constructors `.float64/.float32` with `UInt64`/
  `UInt32`; rejected for symmetry with the `IntKind` idiom, but cheap
  to flip — note in review).
- `FloatBits.lean`: the transcribed softfloat kernel + rational
  rounding (§2b, §7).
- Arms in: `coerceStoredValue`, `normalizeValueForTyFuel` +
  `isNormalForTyFuel` (**lockstep arm-for-arm** — the
  `typeResolutionFuel` docstring, `Ops.lean:7-27`, makes this a stated
  obligation), `defaultValueFuel` (`+0` bits = 0), `convertValueToTyFuel`
  (float↔float, int↔float, fail-closed out-of-range §3.3), `valueEqFuel`
  (IEEE `==`), `valueLess/AtMost/Greater/AtLeast`, `applyStrictOp`
  (`.add/.sub/.mul/.div` float dispatch before the integer
  div-by-zero check; new `.neg`), `GoValue.eqbFuel` (bit equality),
  hashability (already correct).
- Frontend: `emitBasic` float arms; `emitConstValue` `constant.Float`
  arm (per §7 decision); `Expr.neg` lowering for `-x` on floats;
  IncDec's synthetic `1` literal must become float-kinded for float
  operands (`emit.go:1420,1488` currently int-kind-aware only);
  `NativeToIR` decode arms, fail closed on malformed.
- Observation: §5, both sides + `StrictJson` decode + `observation-eq`.

Slices (each with full `scripts/ci --diff`; one semantic concern per
commit; baseline re-pin only in the slice that legitimately moves
cases):

- **F0 — guardrails first** (no runtime code): new corpus cases —
  `floats/nan-map-key` (insert NaN twice, observe `len`),
  `floats/signed-zero-map-key` (overwrite, probe stored-key sign via
  iteration + `1/k`), `floats/fma-shape` (§3.1 tripwire),
  `floats/incdec`, `floats/int64-to-float-rounding` (magnitudes >
  2^53 / 2^24, incl. an int64→float32 double-rounding discriminator
  found by probe), negative-corpus `floats/to-int-out-of-range`
  (expected-unsupported, §3.3). All must classify `frontend-export`
  red (or expected-negative) before any implementation lands.
- **F1 — FloatBits kernel** + eval tests: bit-level vectors generated
  by a Go oracle probe (grid of special values × ops, plus random
  vectors, plus `softfloat64_test.go`'s cases), and a kernel-reduction
  smoke (`example : … = … := by decide`-class over a nontrivial op) so
  the Terminates story is checked at birth. No interpreter wiring yet
  — no case moves.
- **F2 — GoCore wiring + observation** (the list above): corpus still
  red at `frontend-export`, but `gocore-eval-tests` exercises the arms.
- **F3 — frontend**: literals, types, neg, conversions. The 12
  non-generic floats cases flip green; re-pin the baseline in the same
  change with the reason. The 8 generic ones stay red until arc slice 6
  (state this in the re-pin header).
- **F4 (separate, later per the arc plan) — complex**: see §9.

Proof-facing cost, stated honestly: every proof that cases on `GoValue`
or `Ty` (StateWf, MachineSound, the normalization-soundness kit) grows
arms; the softfloat itself needs *no* theorems for this slice (it is
differentially validated interpreter code), but it becomes part of the
statement TCB — theorem statements over float programs mean a reviewer
must be able to read ~700 lines of bit manipulation. Mitigation: the
transcription provenance (comment every function with its
`softfloat64.go` counterpart) plus oracle vectors. If a headline
statement changes, the comparator-judge landmark applies as usual.

---

## 9. Out of scope, with reasons

- **complex64/complex128** (20 reds): follows this model in a later
  slice, per the arc plan. Reasons to split: (a) complex mult/div in gc
  lower to specific runtime algorithms whose NaN/Inf corner behavior is
  not spec-pinned ("not specified beyond the IEEE 754 standard" applies
  to complex division too) — it needs its own probe campaign to pin
  gc's algorithm before modeling; (b) everything it needs downstream
  (`FloatBits`, observation bits, constant rationals as
  real/imag pairs) is built by this slice. The two constant-folded
  complex cases stay green throughout.
- **math stdlib** (`math.NaN`, `Inf`, `Float64bits`, `Sqrt`, `FMA`, …):
  extern-policy territory (`docs/2026-07-30_quorum-extern-policy.md`),
  not language semantics; stays fail-closed. Note `math.Float64bits`
  specifically would make NaN payloads observable (§5) — do not admit
  it casually.
- **float `min`/`max` builtins**: legal Go, spec-pinned semantics
  (NaN-propagating, `-0 < +0`), zero corpus coverage today. Stays
  fail-closed (`minOf/maxOf` float operands → stuck) until a guardrail
  case lands; cheap to add in F2+ if the coordinator wants it, but it
  is scope creep against the 40 reds.
- **`fmt` printing of floats / strconv**: never enters (§5).
- **Out-of-range float→int values**: fail-closed by decision (§3.3),
  not omission.
- **Generics-dependent cases** (8 floats + 9 complex): arc slice 6's.

---

## 10. Goose/Perennial comparison

**[FACT]** Goose translates float literals to bit patterns
(`math.Float64bits`/`Float32bits` → `w64`/`w32` integers,
`goose.go:2333-2339`) and untyped float constants that reach int
contexts via `untypedFloatToInt`. Perennial's model of the *operations*
is an abstract typeclass — `FloatOps`
(`deps/perennial/new/golang/defn/postlang.v:83-101`): uninterpreted
`float64_add : w64 → w64 → w64` etc., plus `float64_leb`, with **no
concrete instance anywhere in `perennial/new`** — no IEEE facts, no
execution, not even commutativity. Their floats exist to be carried,
not computed.

Divergences from Go found by reading their definitions (both
reconstructed-from-source, tagged with file:line; worth independent
verification before repeating them externally):

- **Equality is bit equality**: `go_eq_float64 ::
  go.IsStrictlyComparable go.float64 w64`
  (`predeclared.v` Float64Semantics block, ~line 518) decides float
  `==` at `w64` — making `NaN == NaN` true and `+0 == -0` false, both
  contrary to IEEE/Go.
- **Ordering derived as `leb ∧ bit-≠`**: `lt_float64 v1 v2 =
  float64_leb v1 v2 && bool_decide (v1 ≠ v2)` (`predeclared.v:518`) —
  even under a perfect `leb` instance this makes `-0 < +0` true
  (IEEE: false).
- **Untyped float constants double-round into float32**:
  `UntypedFloatSemantics` carries untyped floats at binary64 and
  converts with `float64_to_float32` (`predeclared.v:503-511`),
  i.e. exact→64→32; the spec requires a single rounding from the exact
  value. (Goose's *typed* Float32 constant path single-rounds via
  `constant.Float32Val` — the divergence is the untyped-adaption path.)

Where we exceed them, if the recommendation stands: concrete,
executable, kernel-reducible IEEE-754 semantics validated
differentially against gc, with IEEE-correct equality/ordering,
single-rounded constants, correct NaN-map behavior, and explicit
envelope statements for all four spec latitude points. Where they are
lighter: an abstract class costs nothing to maintain and can never be
wrong about an op it never defines — our 700 lines can be, which is
what the vector suite and the differential are for.

---

## 11. Decisions of record (2026-08-05, coordinator)

All eight resolved as recommended. Each resolution's authority is the
doctrine that forces it, cited so the arc-final audit can re-argue
from the same ground:

1. **Numerics model: bit-precise in-repo softfloat, transcribed from
   `runtime/softfloat64.go`, `Nat`-backed.** Forced by the two hard
   constraints (§2): executability of the semantics — the project's
   stated foundational requirement — and kernel evaluability
   (`Terminates` discharges). Lean `Float` fails both (§2a);
   transcription over de novo minimizes design freedom in the bit
   fiddling and imports Go's own test vectors. The reference is read,
   never vendored or modified (trust-tools rule).
2. **Fusion/extra-precision: no Choices site; strict per-op rounding
   as a platform-tracked envelope NARROWING + `fma-shape` tripwire.**
   Per the nondeterminism doctrine's "consumption sites are named and
   few" and the append-capacity precedent (§3.1); a fusion choice-site
   is not well-posed as a small named site.
3. **Division by zero: no-panic pin** (envelope narrowing matching gc
   everywhere; §3.2).
4. **Out-of-range float→int: runtime fail-closed + negative-corpus
   pin** (§3.3). Fail-closed doctrine: no portable meaning exists;
   modeling the amd64 value would over-fit the oracle box.
5. **Constant wire format: exact rational on the wire, GoCore-side
   single rounding** (option (ii), §7). Forced by GoCore purity +
   differential validation: the spec-mandated rounding is a semantic
   decision and must live in the differentially validated core, not
   the frontend TCB (a shared go/constant quirk would otherwise be
   silently invisible to the oracle). The frontend's trust surface
   stays what it is for ints — go/types' folding, never its rounding.
   The same kernel serves int→float (`den = 1`).
6. **`GoValue.float` single constructor with `Nat` width invariant**
   (§8), mirroring the `IntKind` idiom; cheap to flip if review
   prefers two constructors.
7. **Observation: bit patterns + kind, NaN canonicalized at the
   boundary, signed zero exact** (§5). Keeps Go's
   shortest-representation printing out of the trust surface.
8. **Scope: complex deferred to its own slice (needs its own gc
   division-algorithm probe campaign); math stdlib and float
   `min`/`max` stay fail-closed** (§9).

Rider decided with §4: the `-x` mislowering (`NativeToIR.lean:216`,
`0 - x`, wrong at `+0`) is fixed in slice F3 via a proper negation
form, pinned by the existing `signed-zero` case — recorded here as
the bug's file-of-record until then.

---

## Build log — slice 4 implementation (2026-08-05, recorded as it happened)

Branch `general-coverage-floats`, stages F0–F3 per §8; deviations and
discoveries only (what went exactly as designed is not repeated).

- **F0.** `to-int-out-of-range` landed as TWO rows (`range`, `nan`) —
  distinct refusal branches, one package. Both return a constant after
  the conversion so the platform-dependent converted value never enters
  the observation (amd64/arm64 would otherwise disagree on the Go side
  of the NaN row). FMA discriminator probed: x = y = 1 + 2⁻²⁷,
  z = −(1 + 2⁻²⁶) (unfused r = 0, fused r = 2⁻⁵⁴); values scaled by an
  argument to defeat compile-time constant folding on EVERY platform, so
  the tripwire tests codegen, not the folder. int64→float32
  double-rounding discriminator probed: 9007199791611905 =
  (2²⁴+1)·2²⁹ + 1 (single: 0x5A000001; via binary64: 0x5A000000).
- **F1 transcription notes.** `mullu`/`divlu` (the Hacker's Delight limb
  algorithms) are NOT transcribed: with `Nat` the 128-bit product and
  the 128/64 division are exact single operations — the same
  mathematical functions on the used domain, recorded at both call
  sites (`fdiv64` keeps `divlu`'s u1 ≥ v overflow arm verbatim although
  unreachable for unpacked operands). Loops are fuel-structural with
  bounds derived from the width invariant in comments (`normUp` 64,
  `normDownSticky` 64, `denormShift` 128). go1.26.5's `nan64` constant
  is exactly the canonical 0x7FF8_0000_0000_0000 — the "low-bit quirk"
  §4 hedged about is gone in this toolchain; `by decide` examples pin
  both canonical NaN constants. The kernel-reduction smoke (20
  decide-class examples over divide/round/denormal/rational paths)
  passed at birth with no OOM (probe-compiled under `ulimit -v 16GiB`).
- **F1 oracle discovery.** gc's CONSTANT typing simplifies an
  underflowed negative zero to +0 (probed: `var f float32 = -1e-103`
  has bits 0) — the spec's "-0 further simplified to an unsigned zero"
  — while `strconv.ParseFloat` keeps −0. The vector generator applies
  the same simplification to the rational vectors' expected side; the
  RUNTIME `float64→float32` conversion keeps −0 (also probed) and is a
  different code path (`f64to32`), unaffected.
- **F1 vectors.** 28 571 vectors (`Tests/FloatVectors.lean`, generated
  by `tools/floatvectors`, seed 20260805): softfloat64_test.go's base
  list + value-class specials on a full grid, seeded randoms against a
  core subset, ParseFloat as the independent correctly-rounded oracle
  for the rational kernel. All passed against the transcription on the
  first complete run (after the −0 generator fix above). A first
  checker draft validated in the Option monad and silently PASSED on
  parse failure; rewritten fail-closed before shipping (parse failure =
  vector failure) with the count pinned against truncation.
- **F2 deviations.** (a) The float arms of `coerceStoredValue` /
  `normalizeValueForTyFuel` are kind-STRICT (mismatch fails closed)
  where the int arms adopt the target kind — ints need flexibility for
  UNTYPED literals; float literals always arrive typed, so a mismatch
  is a lowering bug and a mask would silently reinterpret bits.
  (b) `Expr.neg` is value-directed for INTS TOO (`0 − v` at the
  operand's kind) — the old frontend lowering minted the zero literal
  at a type-attachment-dependent kind; `.neg` is strictly more robust
  and the diff gate showed zero movement. (c) The min/max float guard
  is a top-level if-else (not a do-guard) so `applyStrictOp_wf` splits
  it cleanly (`guard_ite_eq_ok`). Metatheory absorb: StateWf/
  MachineSound arm additions only — `proofs/` needed ZERO changes
  (verified by the proofs build in the gate).
- **F3 discovery — go/constant stores 3.0 with Int KIND.** `var f
  float64 = 3` has `tv.Value.Kind() == constant.Int`, so float-constant
  detection must key on the TYPE (`Info()&IsFloat`), never the value
  kind; keying on kind would have emitted untyped INT literals into
  float slots (caught in design, before the differential could).
  `exactRational` splits `ExactString()` ("n" or "n/d", sign always in
  the numerator); the Lean decoder re-parses and fails closed on
  malformed shapes (zero den, non-integer strings, missing kind).
- **F3 accounting correction.** §1 called all 8
  `floats/generic-type-set/*` ids double-blocked; `zero-value` is NOT —
  its subject never calls a generic function (defined-over-float64 zero
  value + comparison), and per-declaration quarantine means it was only
  floats-blocked. It flipped green with this slice: 13 flips total
  (12 non-generic + zero-value), 7 generic ids stay red for arc
  slice 6.
- **F0/F3 ledger note.** The two `to-int-out-of-range` rows moved
  frontend-export → lean-observation/`unsupported` at F3 and stay there
  PERMANENTLY (the §3.3 refusal pin). They enter check-bugs' untriaged
  surface mechanically, so the ceiling moves 13 → 15 with the
  justification naming them as deliberate fail-closed refusal pins, not
  untriaged fidelity bugs; the machine half of the same pin is the
  `float_to_int_refusal_F` eval test.
