namespace GoLean.GoCore.FloatBits

/-!
# Bit-precise IEEE-754 softfloat (floats slice F1, 2026-08-05)

GoCore's float semantics: pure functions over `Nat` bit patterns,
TRANSCRIBED from Go's own software floating point,
`/usr/local/go/src/runtime/softfloat64.go` (go1.26.5) — Go's definition
of Go floats for softfloat targets, fuzz-tested there against hardware.
Design of record: `docs/2026-08-04_floats-design.md` (all §11 decisions);
this module is decision 1 (numerics model) and decision 5's rounding
kernel. The reference is READ, never vendored or modified; every function
carries its `softfloat64.go` provenance, and the transcription is
validated by oracle-generated bit vectors (`Tests/FloatVectors.lean`,
hardware-computed on the differential oracle's platform) plus the full
differential.

Representation: bit patterns are `Nat` with the width invariant
`< 2^64` / `< 2^32` (enforced at value-construction sites by
`FloatKind.normalizeBits`, mirroring `IntKind.normalize`; nothing in this
module re-masks its float inputs — Go's `uint64` arithmetic and `Nat`
arithmetic agree on the operations used HERE only under that invariant,
argued per site below). Everything is total, structural or
fuel-structural recursion (each loop's fuel bound is derived from the
width invariant in a comment at the loop), kernel-reducible — no
`partial`, no `WellFounded`, no opaque instances (`Terminates`-class
discharges kernel-evaluate the interpreter, so these functions must
reduce in the kernel; checked at birth by the reduction smokes at the
bottom of this file).

## Envelope statement — fusion + extra precision (design note §3.1, verbatim)

The Go spec permits fused floating-point operations (possibly across
statements) and extra intermediate precision; explicit conversions
force rounding. GoCore resolves this latitude to a single point:
every operation rounds to the operand type, no fusion, no extra
precision — IEEE-754 round-to-nearest-even per op. This is a
deliberate envelope NARROWING (a strict subset of conforming
behaviors), matching gc on linux/amd64 with default GOAMD64 (which
emits no FMA and no extra precision) — the differential oracle's
platform. Transfer soundness: ∀-stream theorems transfer to real Go
executions whose toolchain+platform also resolves the latitude to
per-op rounding; gc/arm64 and gc/amd64-v3 executions of programs
containing fusable patterns (`x*y ± z` shapes without an intervening
explicit conversion) are OUTSIDE the envelope, and claims do not
transfer to them. Tracked by: the `floats/fma-shape` corpus tripwire
(fails visibly if the oracle platform ever fuses); widen deliberately
(per-site fused/unfused choice at the frontend-identified fusable
shapes) if a supported target requires it.

The other resolved latitude points (division-by-zero no-panic narrowing,
out-of-range float→int fail-closed) live at their consumption sites in
`Ops.lean`/`Machine.lean`; see the design note §3.2–§3.3.

Operation scope (note §2b): neg/add/sub/mul/div, compare, f64↔f32,
float→int truncation, and the correctly-rounded rational→format kernel
(constants and int→float, decision 5). NOT full IEEE: no sqrt/FMA/
remainder, no decimal conversion, no flags, no rounding modes other than
nearest-even — Go the language exposes none of them.
-/

/-! ## Constants — softfloat64.go:11-27 -/

def mantbits64 : Nat := 52
def expbits64 : Nat := 11
def bias64 : Int := -1023  -- -1<<(expbits64-1) + 1

/-- The canonical quiet NaN, zero payload — softfloat64.go:16
`(1<<expbits64-1)<<mantbits64 + 1<<(mantbits64-1)` = 0x7FF8_0000_0000_0000.
Every GoCore-produced NaN is this constant (design note §4; go1.26.5's
constant has no low-bit set — pinned by the eval examples below). -/
def nan64 : Nat := 0x7FF8000000000000

def inf64 : Nat := 0x7FF0000000000000  -- (1<<expbits64 - 1) << mantbits64
def neg64 : Nat := 0x8000000000000000  -- 1 << (expbits64 + mantbits64)

def mantbits32 : Nat := 23
def expbits32 : Nat := 8
def bias32 : Int := -127

/-- Canonical quiet NaN at binary32 — softfloat64.go:24 = 0x7FC0_0000. -/
def nan32 : Nat := 0x7FC00000

def inf32 : Nat := 0x7F800000
def neg32 : Nat := 0x80000000

/-! ## Loop helpers (fuel-structural)

softfloat64.go writes three small `for` loops; each is transcribed as a
fuel-structural helper whose budget provably exceeds the loop's iteration
count for every input satisfying the width invariant (bound argued at
each call site). On fuel exhaustion the current state is returned — the
loop's own exit shape — which no in-range input reaches; the oracle
vector suite exercises the loops densely. -/

/-- `for mant < bound { mant <<= 1; exp-- }` (funpack's subnormal
normalization and fpack's normalize-up loop). For `mant ∈ [1, 2^k)` and
`bound = 2^k` this runs at most `k ≤ 52` times; budget 64. -/
def normUp (bound : Nat) : Nat → Nat → Int → Nat × Int
  | 0, mant, exp => (mant, exp)
  | fuel + 1, mant, exp =>
      if mant < bound then normUp bound fuel (mant <<< 1) (exp - 1)
      else (mant, exp)

/-- `for mant >= bound { trunc |= mant & 1; mant >>= 1; exp++ }` (fpack's
normalize-down loop, sticky-collecting). For `mant < 2^64` and
`bound = 4<<mantbits` this runs at most `64 - 54 = 10` (f64) /
`32 - 25` (f32; fintto32's variant sees mant < 2^64 → ≤ 32) times;
budget 64. -/
def normDownSticky (bound : Nat) : Nat → Nat → Int → Nat → Nat × Int × Nat
  | 0, mant, exp, trunc => (mant, exp, trunc)
  | fuel + 1, mant, exp, trunc =>
      if mant ≥ bound then
        normDownSticky bound fuel (mant >>> 1) (exp + 1) (trunc ||| (mant &&& 1))
      else (mant, exp, trunc)

/-- `for exp < bias { trunc |= mant & 1; mant >>= 1; exp++ }` (fpack's
denormal repeat loop). Entered only when the normalized exponent is in
`[bias - mantbits, bias]`, and the original `exp0` differs from the
normalized one by at most the other loops' iteration counts (≤ 62), so
the count is ≤ `52 + 62`; budget 128. -/
def denormShift (bias : Int) : Nat → Nat → Int → Nat → Nat × Int × Nat
  | 0, mant, exp, trunc => (mant, exp, trunc)
  | fuel + 1, mant, exp, trunc =>
      if exp < bias then
        denormShift bias fuel (mant >>> 1) (exp + 1) (trunc ||| (mant &&& 1))
      else (mant, exp, trunc)

/-! ## Unpack — softfloat64.go:29-91 -/

/-- `funpack64/32`'s result tuple `(sign, mant, exp, inf, nan)`. `sign`
is the sign BIT in place (0 or `neg64`/`neg32`), as in Go. For finite
nonzero values `mant` carries the implicit leading bit (normals) or is
shifted up to it (subnormals) and `exp` is unbiased; for zeros
`mant = 0, exp = 0` (raw); for Inf/NaN the raw fields are returned with
the flag set. -/
structure Unpacked where
  sign : Nat
  mant : Nat
  exp : Int
  inf : Bool
  nan : Bool

/-- softfloat64.go:29 `funpack64`. -/
def funpack64 (f : Nat) : Unpacked :=
  let sign := f &&& (1 <<< (mantbits64 + expbits64))
  let mant := f &&& ((1 <<< mantbits64) - 1)
  let exp := (f >>> mantbits64) &&& ((1 <<< expbits64) - 1)
  if exp == (1 <<< expbits64) - 1 then
    if mant != 0 then ⟨sign, mant, (exp : Int), false, true⟩
    else ⟨sign, mant, (exp : Int), true, false⟩
  else if exp == 0 then
    -- denormalized
    if mant != 0 then
      -- ≤ 52 iterations (mant ∈ [1, 2^52)); see normUp
      let (mant, e) := normUp (1 <<< mantbits64) 64 mant (bias64 + 1)
      ⟨sign, mant, e, false, false⟩
    else ⟨sign, mant, 0, false, false⟩
  else
    -- add implicit top bit
    ⟨sign, mant ||| (1 <<< mantbits64), (exp : Int) + bias64, false, false⟩

/-- softfloat64.go:61 `funpack32`. -/
def funpack32 (f : Nat) : Unpacked :=
  let sign := f &&& (1 <<< (mantbits32 + expbits32))
  let mant := f &&& ((1 <<< mantbits32) - 1)
  let exp := (f >>> mantbits32) &&& ((1 <<< expbits32) - 1)
  if exp == (1 <<< expbits32) - 1 then
    if mant != 0 then ⟨sign, mant, (exp : Int), false, true⟩
    else ⟨sign, mant, (exp : Int), true, false⟩
  else if exp == 0 then
    if mant != 0 then
      let (mant, e) := normUp (1 <<< mantbits32) 64 mant (bias32 + 1)
      ⟨sign, mant, e, false, false⟩
    else ⟨sign, mant, 0, false, false⟩
  else
    ⟨sign, mant ||| (1 <<< mantbits32), (exp : Int) + bias32, false, false⟩

/-! ## Pack (round-to-nearest-even) — softfloat64.go:93-193 -/

/-- softfloat64.go:93 `fpack64`: pack `sign/mant/exp/trunc` into a
binary64 pattern, rounding to nearest-even with `trunc` as the sticky
"bits already discarded" flag, handling overflow (→ ±Inf), subnormals,
and underflow (→ ±0). The value represented is
`(-1)^sign · (mant + sticky-fraction) · 2^(exp - mantbits64)`.
Callers pass `mant < 2^64`; only nonzero-ness of `trunc` is ever
consumed. -/
def fpack64 (sign mant0 : Nat) (exp0 : Int) (trunc0 : Nat) : Nat :=
  if mant0 == 0 then sign
  else
    let (mant, exp) := normUp (1 <<< mantbits64) 64 mant0 exp0
    let (mant, exp, trunc) :=
      normDownSticky (4 <<< mantbits64) 64 mant exp trunc0
    let (mant, exp) :=
      if mant ≥ 2 <<< mantbits64 then
        let (mant, exp) :=
          if mant &&& 1 != 0 && (trunc != 0 || mant &&& 2 != 0) then
            let mant := mant + 1
            if mant ≥ 4 <<< mantbits64 then (mant >>> 1, exp + 1) else (mant, exp)
          else (mant, exp)
        (mant >>> 1, exp + 1)
      else (mant, exp)
    if exp ≥ (1 <<< expbits64 : Int) - 1 + bias64 then
      sign ^^^ inf64
    else if exp < bias64 + 1 then
      if exp < bias64 - (mantbits64 : Int) then sign
      else
        -- repeat expecting denormal, from the ORIGINAL inputs
        let (mant, _exp, trunc) := denormShift bias64 128 mant0 exp0 trunc0
        let mant :=
          if mant &&& 1 != 0 && (trunc != 0 || mant &&& 2 != 0) then mant + 1
          else mant
        let mant := mant >>> 1
        if mant < 1 <<< mantbits64 then sign ||| mant
        else
          -- rounding carried into the normal range: exp = bias64 + 1 here
          sign ||| (1 <<< mantbits64) ||| (mant &&& ((1 <<< mantbits64) - 1))
    else
      sign ||| ((exp - bias64).toNat <<< mantbits64)
        ||| (mant &&& ((1 <<< mantbits64) - 1))

/-- softfloat64.go:144 `fpack32` (structure identical to `fpack64` at
23 mantissa bits, 8 exponent bits, bias -127). -/
def fpack32 (sign mant0 : Nat) (exp0 : Int) (trunc0 : Nat) : Nat :=
  if mant0 == 0 then sign
  else
    let (mant, exp) := normUp (1 <<< mantbits32) 64 mant0 exp0
    let (mant, exp, trunc) :=
      normDownSticky (4 <<< mantbits32) 64 mant exp trunc0
    let (mant, exp) :=
      if mant ≥ 2 <<< mantbits32 then
        let (mant, exp) :=
          if mant &&& 1 != 0 && (trunc != 0 || mant &&& 2 != 0) then
            let mant := mant + 1
            if mant ≥ 4 <<< mantbits32 then (mant >>> 1, exp + 1) else (mant, exp)
          else (mant, exp)
        (mant >>> 1, exp + 1)
      else (mant, exp)
    if exp ≥ (1 <<< expbits32 : Int) - 1 + bias32 then
      sign ^^^ inf32
    else if exp < bias32 + 1 then
      if exp < bias32 - (mantbits32 : Int) then sign
      else
        let (mant, _exp, trunc) := denormShift bias32 128 mant0 exp0 trunc0
        let mant :=
          if mant &&& 1 != 0 && (trunc != 0 || mant &&& 2 != 0) then mant + 1
          else mant
        let mant := mant >>> 1
        if mant < 1 <<< mantbits32 then sign ||| mant
        else
          sign ||| (1 <<< mantbits32) ||| (mant &&& ((1 <<< mantbits32) - 1))
    else
      sign ||| ((exp - bias32).toNat <<< mantbits32)
        ||| (mant &&& ((1 <<< mantbits32) - 1))

/-! ## Arithmetic — softfloat64.go:195-315 -/

/-- softfloat64.go:254 `fneg64`: IEEE negation is a sign-bit flip — the
correct `-x` (design note §4: `0 - x` is WRONG at `x = +0`). -/
def fneg64 (f : Nat) : Nat := f ^^^ (1 <<< (mantbits64 + expbits64))

/-- `fneg32`: `fneg64`'s shape at binary32. -/
def fneg32 (f : Nat) : Nat := f ^^^ (1 <<< (mantbits32 + expbits32))

/-- softfloat64.go:195 `fadd64`. Nat-vs-uint64 notes, both derived from
the swap invariant `(fe,fm) ≥lex (ge,gm)`:
* `fm - gm` cannot underflow: after `<<< 2` and the `>>> shift`, the
  shifted `gm` is ≤ `fm` (equal exponents compare mantissas directly;
  a larger exponent leaves `fm <<< 2 ≥ 2^54 >` any `gm <<< 2 >>> 1`),
  so Nat subtraction equals Go's wraparound-free subtraction;
* `fm - 1` after it: `trunc ≠ 0` implies the shift dropped bits, so the
  difference is ≥ 1;
* Go's `gm >> shift` / mask for `shift ≥ 64` is 0 / all-ones, and Nat
  `>>> shift` / the unbounded mask agree (gm < 2^56 < 2^shift). -/
def fadd64 (f g : Nat) : Nat :=
  let uf := funpack64 f
  let ug := funpack64 g
  -- Special cases.
  if uf.nan || ug.nan then nan64                     -- NaN + x or x + NaN = NaN
  else if uf.inf && ug.inf && uf.sign != ug.sign then nan64 -- +Inf + -Inf = NaN
  else if uf.inf then f                              -- ±Inf + g = ±Inf
  else if ug.inf then g                              -- f + ±Inf = ±Inf
  else if uf.mant == 0 && ug.mant == 0 && uf.sign != 0 && ug.sign != 0 then f -- -0 + -0
  else if uf.mant == 0 then                          -- 0 + g = g but 0 + -0 = +0
    (if ug.mant == 0 then g ^^^ ug.sign else g)
  else if ug.mant == 0 then f                        -- f + 0 = f
  else
    let (fs, fm, fe, gs, gm, ge) :=
      if uf.exp < ug.exp || (uf.exp == ug.exp && uf.mant < ug.mant) then
        (ug.sign, ug.mant, ug.exp, uf.sign, uf.mant, uf.exp)
      else
        (uf.sign, uf.mant, uf.exp, ug.sign, ug.mant, ug.exp)
    let shift := (fe - ge).toNat
    let fm := fm <<< 2
    let gm := gm <<< 2
    let trunc := gm &&& ((1 <<< shift) - 1)
    let gm := gm >>> shift
    let (fm, fs) :=
      if fs == gs then (fm + gm, fs)
      else
        let fm := fm - gm
        let fm := if trunc != 0 then fm - 1 else fm
        if fm == 0 then (fm, 0) else (fm, fs)
    fpack64 fs fm (fe - 2) trunc

/-- softfloat64.go:250 `fsub64 = fadd64 (fneg64 g)`. -/
def fsub64 (f g : Nat) : Nat := fadd64 f (fneg64 g)

/-- softfloat64.go:258 `fmul64`. The `mullu` helper (64×64→128,
Hacker's Delight, softfloat64.go:439) is exact multiplication; with
`Nat` the 106-bit product is formed directly — the same mathematical
function, so the goto-free transcription bypasses the limb algorithm. -/
def fmul64 (f g : Nat) : Nat :=
  let uf := funpack64 f
  let ug := funpack64 g
  if uf.nan || ug.nan then nan64                        -- NaN * g = f * NaN = NaN
  else if uf.inf && ug.inf then f ^^^ ug.sign           -- Inf * Inf (sign adjusted)
  else if (uf.inf && ug.mant == 0) || (uf.mant == 0 && ug.inf) then nan64 -- 0 * Inf
  else if uf.mant == 0 then f ^^^ ug.sign               -- 0 * x = 0 (sign adjusted)
  else if ug.mant == 0 then g ^^^ uf.sign               -- x * 0 = 0 (sign adjusted)
  else
    -- 53-bit * 53-bit = 107- or 108-bit
    let prod := uf.mant * ug.mant
    let shift := mantbits64 - 1
    let trunc := prod &&& ((1 <<< shift) - 1)
    let mant := prod >>> shift
    fpack64 (uf.sign ^^^ ug.sign) mant (uf.exp + ug.exp - 1) trunc

/-- softfloat64.go:288 `fdiv64`. The `divlu` helper (128/64→64,
Hacker's Delight, softfloat64.go:458) computes quotient and remainder of
`fm·2^54 / gm` with an `u1 ≥ v` overflow guard; with `Nat` the division
is exact on the same domain, so the goto-free transcription bypasses the
limb algorithm. The guard is preserved verbatim although unreachable for
unpacked operands (`fm < 2^53 ⇒ fm >> 10 < 2^43 < 2^52 ≤ gm`). -/
def fdiv64 (f g : Nat) : Nat :=
  let uf := funpack64 f
  let ug := funpack64 g
  if uf.nan || ug.nan then nan64                        -- NaN / g = f / NaN = NaN
  else if uf.inf && ug.inf then nan64                   -- ±Inf / ±Inf = NaN
  else if !uf.inf && !ug.inf && uf.mant == 0 && ug.mant == 0 then nan64 -- 0 / 0
  else if uf.inf || (!ug.inf && ug.mant == 0) then      -- Inf / g = f / 0 = Inf
    uf.sign ^^^ ug.sign ^^^ inf64
  else if ug.inf || uf.mant == 0 then                   -- f / Inf = 0 / g = 0
    uf.sign ^^^ ug.sign ^^^ 0
  else
    -- 53-bit<<54 / 53-bit = 53- or 54-bit.
    let shift := mantbits64 + 2
    if uf.mant >>> (64 - shift) ≥ ug.mant then
      -- divlu's overflow arm (softfloat64.go:461), unreachable here
      fpack64 (uf.sign ^^^ ug.sign) ((1 <<< 64) - 1) (uf.exp - ug.exp - 2) ((1 <<< 64) - 1)
    else
      let dividend := uf.mant <<< shift
      let q := dividend / ug.mant
      let r := dividend % ug.mant
      fpack64 (uf.sign ^^^ ug.sign) q (uf.exp - ug.exp - 2) r

/-! ## Comparison — softfloat64.go:343-372, 519-547 -/

/-- softfloat64.go:343 `fcmp64`: `(cmp, isnan)` with cmp ∈ {-1,0,1}.
±0 compare equal; same-sign finite values compare by raw encoding
(reversed under the sign). Inputs must satisfy the width invariant (the
raw `f < g` comparisons assume 64-bit patterns). -/
def fcmp64 (f g : Nat) : Int × Bool :=
  let uf := funpack64 f
  let ug := funpack64 g
  if uf.nan || ug.nan then (0, true)
  else if !uf.inf && !ug.inf && uf.mant == 0 && ug.mant == 0 then (0, false) -- ±0 == ±0
  else if uf.sign > ug.sign then (-1, false)  -- f < 0, g > 0
  else if uf.sign < ug.sign then (1, false)   -- f > 0, g < 0
  else if (uf.sign == 0 && f < g) || (uf.sign != 0 && f > g) then (-1, false)
  else if (uf.sign == 0 && f > g) || (uf.sign != 0 && f < g) then (1, false)
  else (0, false)

/-- softfloat64.go:534 `feq64`: IEEE `==` — false on any NaN. -/
def feq64 (f g : Nat) : Bool :=
  let (cmp, isnan) := fcmp64 f g
  cmp == 0 && !isnan

/-- IEEE `<` from `fcmp64` (softfloat64.go:539 `fgt64` with the argument
order flipped): false on any NaN — the unordered semantics `valueLess`
needs (design note §4). -/
def flt64 (f g : Nat) : Bool :=
  let (cmp, isnan) := fcmp64 f g
  cmp < 0 && !isnan

/-- IEEE `<=` (softfloat64.go:544 `fge64`, flipped). -/
def fle64 (f g : Nat) : Bool :=
  let (cmp, isnan) := fcmp64 f g
  cmp ≤ 0 && !isnan

/-! ## Conversions between widths — softfloat64.go:317-341 -/

/-- softfloat64.go:317 `f64to32`: the ONE rounding of a binary64 value
to binary32. NaN → canonical `nan32`. -/
def f64to32 (f : Nat) : Nat :=
  let uf := funpack64 f
  if uf.nan then nan32
  else
    let fs32 := uf.sign >>> 32
    if uf.inf then fs32 ^^^ inf32
    else
      let d := mantbits64 - mantbits32 - 1  -- 28
      fpack32 fs32 (uf.mant >>> d) (uf.exp - 1) (uf.mant &&& ((1 <<< d) - 1))

/-- softfloat64.go:330 `f32to64`: exact widening. NaN → canonical
`nan64`. -/
def f32to64 (f : Nat) : Nat :=
  let d := mantbits64 - mantbits32  -- 29
  let uf := funpack32 f
  if uf.nan then nan64
  else
    let fs64 := uf.sign <<< 32
    if uf.inf then fs64 ^^^ inf64
    else fpack64 fs64 (uf.mant <<< d) uf.exp 0

/-! ## Binary32 arithmetic — softfloat64.go:506-532

Go's own softfloat computes float32 arithmetic by exact widening,
binary64 computation, and one rounding back: correct (not a
double-rounding hazard) for `+ - * /` because binary64's 53 significand
bits ≥ 2·24 + 2, and transcribing it verbatim minimizes transcription
risk (design note §6). Conversions INTO float32 from wide values must
NOT take this path — the rational kernel below single-rounds. -/

def fadd32 (x y : Nat) : Nat := f64to32 (fadd64 (f32to64 x) (f32to64 y))
def fsub32 (x y : Nat) : Nat := fadd32 x (fneg32 y)
def fmul32 (x y : Nat) : Nat := f64to32 (fmul64 (f32to64 x) (f32to64 y))
def fdiv32 (x y : Nat) : Nat := f64to32 (fdiv64 (f32to64 x) (f32to64 y))

/-- softfloat64.go:520 `fcmp` at 32 bits: widening is exact, so
comparison too. -/
def fcmp32 (x y : Nat) : Int × Bool := fcmp64 (f32to64 x) (f32to64 y)

def feq32 (x y : Nat) : Bool := feq64 (f32to64 x) (f32to64 y)
def flt32 (x y : Nat) : Bool := flt64 (f32to64 x) (f32to64 y)
def fle32 (x y : Nat) : Bool := fle64 (f32to64 x) (f32to64 y)

/-! ## Float → integer truncation — softfloat64.go:374 -/

/-- Exact truncation toward zero of a binary64 pattern: `none` for
Inf/NaN, otherwise the mathematical integer part (unbounded — derived
from `f64toint`'s shift loops, softfloat64.go:374, with the int64 range
clamp REMOVED: the machine checks the TARGET int kind's range and fails
closed out of range, design note §3.3 / decision 4, so the clamp is
replaced by exact arithmetic). Shifting out the fraction truncates the
MAGNITUDE, which is toward-zero for both signs — the spec's "fraction is
discarded" rule. -/
def f64truncInt? (f : Nat) : Option Int :=
  let uf := funpack64 f
  if uf.inf || uf.nan then none
  else
    let mag : Nat :=
      if uf.exp ≥ (mantbits64 : Int) then uf.mant <<< (uf.exp - mantbits64).toNat
      else uf.mant >>> ((mantbits64 : Int) - uf.exp).toNat
    some (if uf.sign != 0 then -(mag : Int) else (mag : Int))

/-- Truncation of a binary32 pattern via the exact widening. -/
def f32truncInt? (f : Nat) : Option Int := f64truncInt? (f32to64 f)

/-! ## The correctly-rounded rational → format kernel (design note §7,
decision 5)

Constants travel as EXACT rationals on the wire (go/constant
`ExactString`); GoCore performs the SINGLE spec-mandated rounding here.
int→float is the `den = 1` case. float32 conversions from wide values
round ONCE at binary32 (never via binary64 — the sticky bit plays
`fintto32`'s role, softfloat64.go:417). Shape: scale the quotient to
have a couple of bits beyond the target precision plus a sticky
remainder, then let `fpack` do the one round-to-nearest-even (its
normalize-down loop folds the surplus bits into the sticky). -/

/-- Bit length worker: structural on the fuel, which only bounds the
recursion (`n+1` always suffices since `n + 1 ≥ log2 n + 1`); the
recursion itself runs `log2 n + 1` steps. Kernel-reducible replacement
for core's `Nat.log2` (well-founded, hence `Acc.rec`-stuck in the
kernel — the de-WF discipline). -/
def bitLenFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 then 0 else bitLenFuel fuel (n >>> 1) + 1

/-- Number of binary digits of `n` (0 for 0). -/
def bitLen (n : Nat) : Nat := bitLenFuel (n + 1) n

/-- Correctly-rounded `num / den` at binary64. `den = 0` is malformed on
the wire and refused by the decoder; the arm here is a defensive NaN.
`-0 → +0` per the spec's constant-typing simplification ("an IEEE
negative zero [is] further simplified to an unsigned zero") — reachable
only when a nonzero rational underflows to zero, which the constant
corpus can express (`-1e-5000`); int→float (`den = 1`) never underflows.

Rounding argument: with `e0 = bitLen n - bitLen den`, the true value
`n/den ∈ (2^(e0-1), 2^(e0+1))`; scaling by `2^s` with `s = 56 - e0`
puts the scaled value in `(2^55, 2^57)`, so `q = ⌊n·2^s/den⌋ ≥ 2^55`
carries ≥ 56 significant bits — at least two below the 53-bit target —
and the remainder is exactly the sticky information. `fpack64` then
performs the single round-to-nearest-even. -/
def ratToFloat64 (num : Int) (den : Nat) : Nat :=
  if den == 0 then nan64
  else if num == 0 then 0
  else
    let sign : Nat := if num < 0 then neg64 else 0
    let n := num.natAbs
    let e0 : Int := (bitLen n : Int) - (bitLen den : Int)
    let s : Int := 56 - e0
    let (nn, dd) :=
      if s ≥ 0 then (n <<< s.toNat, den) else (n, den <<< (-s).toNat)
    let q := nn / dd
    let r := nn % dd
    let bits := fpack64 sign q ((mantbits64 : Int) - s) (if r == 0 then 0 else 1)
    if bits == neg64 then 0 else bits

/-- Correctly-rounded `num / den` at binary32 — the SINGLE rounding
(`s = 27 - e0` puts `q` in `[2^26, 2^28)`, two-plus bits below the
24-bit target). Never composed through `ratToFloat64`. -/
def ratToFloat32 (num : Int) (den : Nat) : Nat :=
  if den == 0 then nan32
  else if num == 0 then 0
  else
    let sign : Nat := if num < 0 then neg32 else 0
    let n := num.natAbs
    let e0 : Int := (bitLen n : Int) - (bitLen den : Int)
    let s : Int := 27 - e0
    let (nn, dd) :=
      if s ≥ 0 then (n <<< s.toNat, den) else (n, den <<< (-s).toNat)
    let q := nn / dd
    let r := nn % dd
    let bits := fpack32 sign q ((mantbits32 : Int) - s) (if r == 0 then 0 else 1)
    if bits == neg32 then 0 else bits

/-! ## Kernel-reduction smokes (Terminates-compatibility checked at birth)

`decide`-class examples over nontrivial paths: the KERNEL evaluates each
(Nat.decEq on the fully reduced bit pattern), so a regression to
well-founded compilation anywhere in this module fails HERE, in the
defining file. Values chosen to cross the interesting paths: full
normalize/round in `fpack64`, the divide path, the subnormal repeat
loop, and the rational kernel with a nontrivial denominator. -/

-- 1.0 + 2.0 = 3.0
example : fadd64 0x3FF0000000000000 0x4000000000000000 = 0x4008000000000000 := by decide
-- 1.0 / 3.0 (full divide + round path)
example : fdiv64 0x3FF0000000000000 0x4008000000000000 = 0x3FD5555555555555 := by decide
-- 0/0 = the canonical quiet NaN, exact constant (design note §4)
example : fdiv64 0 0 = nan64 := by decide
-- 1/0 = +Inf; -1/0 = -Inf (the §3.2 no-panic results)
example : fdiv64 0x3FF0000000000000 0 = inf64 := by decide
example : fdiv64 0xBFF0000000000000 0 = neg64 ||| inf64 := by decide
-- min-subnormal / 2 = 0 (ties-to-even at the denormal repeat loop)
example : fdiv64 0x0000000000000001 0x4000000000000000 = 0 := by decide
-- -0 negation and +0 == -0, NaN /= NaN
example : fneg64 0 = neg64 := by decide
example : feq64 0 neg64 = true := by decide
example : feq64 nan64 nan64 = false := by decide
-- f64→f32 conversion rounding: 16777217.0 → 16777216.0f
example : f64to32 0x4170000010000000 = 0x4B800000 := by decide
-- rational kernel: 1/10 at both widths (the classic non-dyadic constant)
example : ratToFloat64 1 10 = 0x3FB999999999999A := by decide
example : ratToFloat32 1 10 = 0x3DCCCCCD := by decide
-- int→float (den = 1): 2^53 + 1 ties to even; 2^53 + 3 rounds up
example : ratToFloat64 9007199254740993 1 = 0x4340000000000000 := by decide
example : ratToFloat64 9007199254740995 1 = 0x4340000000000002 := by decide
-- int64→float32 single rounding: the probed double-rounding
-- discriminator (float32(9007199791611905) = 0x5A000001, not the
-- via-binary64 0x5A000000)
example : ratToFloat32 9007199791611905 1 = 0x5A000001 := by decide
-- truncation toward zero, both signs
example : f64truncInt? 0x4008000000000000 = some 3 := by decide  -- 3.0
example : f64truncInt? 0xC00921FB54442D18 = some (-3) := by decide -- -π
example : f64truncInt? nan64 = none := by decide
example : f64truncInt? inf64 = none := by decide

end GoLean.GoCore.FloatBits
