// floatvectors generates Tests/FloatVectors.lean: hardware-computed
// oracle vectors for the transcribed softfloat kernel
// (GoLean/GoCore/FloatBits.lean; floats slice F1,
// docs/2026-08-04_floats-design.md §8). The oracle is this machine's
// IEEE-754 hardware — the same semantics the differential's `go run`
// oracle executes on linux/amd64 (per-op round-to-nearest-even; the
// pinned envelope point) — plus strconv.ParseFloat (correctly-rounded
// decimal→binary, the independent oracle for the rational kernel).
//
// Deterministic: fixed seed, no time/env input. Regenerate with
//
//	GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off \
//	  go run ./tools/floatvectors > Tests/FloatVectors.lean
//
// Vector line grammar (one vector per line, space-separated decimal):
//
//	a64|s64|m64|d64 x y z    -- fadd64/fsub64/fmul64/fdiv64 x y = z
//	a32|s32|m32|d32 x y z    -- the binary32 wrappers
//	c64|c32 x y c            -- compare: c = eq + 2*lt + 4*le
//	t32 x z                  -- f64to32 x = z
//	t64 x z                  -- f32to64 x = z
//	n64 x z                  -- fneg64 x = z
//	i64 x n                  -- f64truncInt? x = some n (full int64 range)
//	i32 x n                  -- f32truncInt? x = some n (full int64 range)
//	r64|r32 num den z        -- ratToFloat64/32 num/den = z (num signed)
//
// NaN outputs are canonicalized to 0x7FF8000000000000 / 0x7FC00000 on
// BOTH sides (hardware NaN bit patterns are platform/path-dependent;
// the language proper cannot observe payloads — design note §4/§5).
// The value lists seed from runtime/softfloat64_test.go's base list
// (the transcription source's own vectors) plus float32-relevant
// specials and seeded pseudo-random values, including raw-bit patterns
// (subnormals, NaN payloads).
package main

import (
	"fmt"
	"math"
	"math/rand"
	"strings"
)

const canon64 = 0x7FF8000000000000
const canon32 = 0x7FC00000

func c64(u uint64) uint64 {
	f := math.Float64frombits(u)
	if math.IsNaN(f) {
		return canon64
	}
	return u
}

func c32(u uint32) uint32 {
	f := math.Float32frombits(u)
	if f != f {
		return canon32
	}
	return u
}

func main() {
	var sb strings.Builder
	out := func(format string, args ...any) {
		fmt.Fprintf(&sb, format, args...)
	}

	// softfloat64_test.go:29 base list, verbatim.
	base := []float64{
		0,
		math.Copysign(0, -1),
		-1,
		1,
		math.NaN(),
		math.Inf(+1),
		math.Inf(-1),
		0.1,
		1.5,
		1.9999999999999998,     // all 1s mantissa
		1.3333333333333333,     // 1.010101010101...
		1.1428571428571428,     // 1.001001001001...
		1.112536929253601e-308, // first normal
		2,
		4,
		8,
		16,
		32,
		64,
		128,
		256,
		3,
		12,
		1234,
		123456,
		-0.1,
		-1.5,
		-1.9999999999999998,
		-1.3333333333333333,
		-1.1428571428571428,
		-2,
		-3,
		1e-200,
		1e-300,
		1e-310,
		5e-324,
		1e-105,
		1e-305,
		1e+200,
		1e+306,
		1e+307,
		1e+308,
	}
	// Additions: subnormal edges, NaN payloads, float32-relevant magnitudes.
	extra := []uint64{
		0x0000000000000001, // min subnormal
		0x000FFFFFFFFFFFFF, // max subnormal
		0x8000000000000001,
		0x7FF8000000000001,     // NaN, payload 1
		0xFFF8000000000000,     // negative NaN (amd64's 0/0)
		0x7FF0000000000001 + 1, // signaling-range NaN payload
		math.Float64bits(3.4028234663852886e+38),  // max float32
		math.Float64bits(-3.4028234663852886e+38), //
		math.Float64bits(1.401298464324817e-45),   // min subnormal32
		math.Float64bits(1.1754943508222875e-38),  // min normal32
		math.Float64bits(16777216),                // 2^24
		math.Float64bits(16777217),
	}
	rng := rand.New(rand.NewSource(20260805))
	// The GRID list: base + extras (every value class; the full cross
	// product runs over these). Random values are paired against the
	// CORE subset below instead of the full grid — same class coverage,
	// tractable tracked-file size.
	vals := []uint64{}
	for _, f := range base {
		vals = append(vals, math.Float64bits(f))
	}
	vals = append(vals, extra...)
	rand64 := []uint64{}
	for i := 0; i < 24; i++ {
		rand64 = append(rand64, math.Float64bits(rng.NormFloat64()))
	}
	for i := 0; i < 12; i++ {
		rand64 = append(rand64, rng.Uint64()) // raw patterns: every class
	}
	// Truncation-range coverage 2^25..2^63 (audit A2, 2026-08-05: the
	// base list had nothing between ~2^25 and 2^62, so f64truncInt?'s
	// LEFT-SHIFT branch — exponent past the mantissa — had zero
	// vectors). Includes the audit verifier's probed boundaries
	// (2^52±, 2^53±, 2^62, MinInt64) and the largest float64 below
	// 2^63. Appended to rand64: full unary/i64 coverage plus
	// core-paired binop coverage.
	for _, f := range []float64{
		33554432.5,           // 2^25 + 0.5: shift-right branch, big magnitude
		4503599627370495.5,   // 2^52 - 0.5
		4503599627370496,     // 2^52
		4503599627370497,     // 2^52 + 1 (odd, exact)
		9007199254740991,     // 2^53 - 1
		9007199254740992,     // 2^53: first even-only magnitude
		1e15, -1e18,          // decimal magnitudes inside the gap
		4611686018427387904,  // 2^62
		-4611686018427387904, // -2^62
		9223372036854774784,  // largest float64 below 2^63
		-9223372036854775808, // MinInt64 = -2^63 exactly (in range)
	} {
		rand64 = append(rand64, math.Float64bits(f))
	}
	// Core subset for random pairing: zero, -0, ±1, NaN, ±Inf, a
	// non-dyadic, first normal, min subnormal, a large and a tiny power.
	core := []uint64{}
	for _, f := range []float64{0, math.Copysign(0, -1), 1, -1, math.NaN(),
		math.Inf(1), math.Inf(-1), 0.1, 1.112536929253601e-308, 5e-324,
		1e+300, 1e-300} {
		core = append(core, math.Float64bits(f))
	}

	// binary32 value list: the 64-bit list rounded down, plus specials.
	vals32 := []uint32{}
	seen32 := map[uint32]bool{}
	add32 := func(u uint32) {
		if !seen32[u] {
			seen32[u] = true
			vals32 = append(vals32, u)
		}
	}
	for _, u := range vals {
		add32(math.Float32bits(float32(math.Float64frombits(u))))
	}
	add32(0x00000001) // min subnormal32
	add32(0x007FFFFF) // max subnormal32
	add32(0x80000001)
	add32(0x7F800001) // NaN payload
	add32(0xFFC00000)
	// Truncation-range float32 values (audit A2): 2^23+1 (last odd
	// magnitude), 2^24±, 2^31, 2^62, ±2^63-adjacent.
	for _, f := range []float32{
		8388609, 16777215, 16777218, 2147483648, 4611686018427387904,
		9223371487098961920, // largest float32 below 2^63
		-9223372036854775808,
	} {
		add32(math.Float32bits(f))
	}
	rand32 := []uint32{}
	for i := 0; i < 12; i++ {
		rand32 = append(rand32, rng.Uint32())
	}
	core32 := []uint32{}
	for _, u := range core {
		v := math.Float32bits(float32(math.Float64frombits(u)))
		core32 = append(core32, v)
	}

	count := 0
	pair64 := func(x, y uint64) {
		fx := math.Float64frombits(x)
		fy := math.Float64frombits(y)
		out("a64 %d %d %d\n", x, y, c64(math.Float64bits(fx+fy)))
		out("s64 %d %d %d\n", x, y, c64(math.Float64bits(fx-fy)))
		out("m64 %d %d %d\n", x, y, c64(math.Float64bits(fx*fy)))
		out("d64 %d %d %d\n", x, y, c64(math.Float64bits(fx/fy)))
		cmp := 0
		if fx == fy {
			cmp |= 1
		}
		if fx < fy {
			cmp |= 2
		}
		if fx <= fy {
			cmp |= 4
		}
		out("c64 %d %d %d\n", x, y, cmp)
		count += 5
	}
	pair32 := func(x, y uint32) {
		fx := math.Float32frombits(x)
		fy := math.Float32frombits(y)
		out("a32 %d %d %d\n", x, y, c32(math.Float32bits(fx+fy)))
		out("s32 %d %d %d\n", x, y, c32(math.Float32bits(fx-fy)))
		out("m32 %d %d %d\n", x, y, c32(math.Float32bits(fx*fy)))
		out("d32 %d %d %d\n", x, y, c32(math.Float32bits(fx/fy)))
		cmp := 0
		if fx == fy {
			cmp |= 1
		}
		if fx < fy {
			cmp |= 2
		}
		if fx <= fy {
			cmp |= 4
		}
		out("c32 %d %d %d\n", x, y, cmp)
		count += 5
	}
	// 64-bit binary ops: full grid over base+extras; randoms vs core,
	// both orders.
	for _, x := range vals {
		for _, y := range vals {
			pair64(x, y)
		}
	}
	for _, x := range rand64 {
		for _, y := range core {
			pair64(x, y)
			pair64(y, x)
		}
	}
	// 32-bit binary ops: same structure.
	for _, x := range vals32 {
		for _, y := range vals32 {
			pair32(x, y)
		}
	}
	for _, x := range rand32 {
		for _, y := range core32 {
			pair32(x, y)
			pair32(y, x)
		}
	}
	// Unary over the 64-bit lists (grid + randoms). The i64 guard is the
	// FULL int64 range (audit A2 — the old `|fx| < 2^62` guard silently
	// dropped the 2^62..2^63 boundary): every float64 in [-2^63, 2^63)
	// truncates in range, and both bounds are exact float64 values.
	for _, x := range append(append([]uint64{}, vals...), rand64...) {
		fx := math.Float64frombits(x)
		out("t32 %d %d\n", x, uint64(c32(math.Float32bits(float32(fx)))))
		out("n64 %d %d\n", x, math.Float64bits(fx)^(1<<63))
		count += 2
		if !math.IsNaN(fx) && !math.IsInf(fx, 0) &&
			fx >= -9223372036854775808 && fx < 9223372036854775808 {
			out("i64 %d %d\n", x, int64(fx))
			count++
		}
	}
	// Widening + DIRECT f32truncInt? vectors over the 32-bit lists
	// (audit A2: truncation from float32 previously had only indirect
	// coverage through the widening class).
	for _, x := range append(append([]uint32{}, vals32...), rand32...) {
		fx := math.Float32frombits(x)
		out("t64 %d %d\n", x, c64(math.Float64bits(float64(fx))))
		count++
		if fx == fx && !math.IsInf(float64(fx), 0) &&
			float64(fx) >= -9223372036854775808 && float64(fx) < 9223372036854775808 {
			out("i32 %d %d\n", x, int64(fx))
			count++
		}
	}
	// Rational kernel, den = 1 (int→float): boundaries + random int64.
	ints := []int64{
		0, 1, -1, 1 << 24, 1<<24 + 1, -(1<<24 + 1), 1 << 53, 1<<53 + 1,
		1<<53 + 3, -(1<<53 + 1), 1<<63 - 1, -(1 << 62), math.MinInt64,
		9007199791611905, // the probed int64→float32 double-rounding discriminator
	}
	for i := 0; i < 40; i++ {
		ints = append(ints, int64(rng.Uint64()))
	}
	for _, v := range ints {
		out("r64 %d 1 %d\n", v, math.Float64bits(float64(v)))
		out("r32 %d 1 %d\n", v, uint64(math.Float32bits(float32(v))))
		count += 2
	}
	// Rational kernel, decimal rationals: strconv/ParseFloat is the
	// correctly-rounded independent oracle (compiled float literals go
	// through the same gc path). num/10^k from random digit strings,
	// spanning normals, subnormals, and (at binary32) underflow-to-zero.
	// NOT spanned here (arc-final audit F17, 2026-08-06): overflow —
	// |digits| < 1e18 and den = 10^k, k >= 0, so |value| < 1e18, below
	// both widths' overflow thresholds (and 0 of the checked-in rational
	// vectors expect an infinity); binary64 underflow-to-zero — the
	// deepest r64 vector is a subnormal (~2.2e-322), and the r64
	// zero-flush path is pinned by the `decide` example in
	// FloatBits.lean instead. fpack's overflow arms are exercised by the
	// pair-arithmetic families (hundreds of finite-operand d/m/a/s
	// vectors), so no kernel arm rests on this family; a rational
	// constant that overflows its float type is a compile error in Go,
	// so the arm is unreachable from valid Go via ratToFloat anyway.
	for i := 0; i < 300; i++ {
		digits := rng.Int63n(1_000_000_000_000_000_000)
		if rng.Intn(2) == 0 {
			digits = -digits
		}
		k := rng.Intn(340) // 10^0 .. 10^339: deep past both underflow edges
		den := "1" + strings.Repeat("0", k)
		f, err := parseRat(digits, k)
		if err != nil {
			panic(err)
		}
		// Constant-typing oracle adjustment: the rational kernel implements
		// the spec's "-0 further simplified to an unsigned zero" (constant
		// typing; probed 2026-08-05 — `var f float32 = -1e-103` is +0 under
		// gc), while ParseFloat keeps -0 on underflow. Simplify here too.
		e64 := math.Float64bits(f)
		if e64 == 1<<63 {
			e64 = 0
		}
		out("r64 %d %s %d\n", digits, den, c64(e64))
		f32v, err := parseRat32(digits, k)
		if err != nil {
			panic(err)
		}
		e32 := math.Float32bits(f32v)
		if e32 == 1<<31 {
			e32 = 0
		}
		out("r32 %d %s %d\n", digits, den, uint64(c32(e32)))
		count += 2
	}

	fmt.Printf(`-- GENERATED by tools/floatvectors (go run ./tools/floatvectors >
-- Tests/FloatVectors.lean) — do not edit by hand. Hardware-oracle bit
-- vectors for GoLean/GoCore/FloatBits.lean; see the generator header
-- for the grammar and provenance (seed 20260805, %d vectors).
namespace Tests.FloatVectors

def expectedCount : Nat := %d

def lines : String := "%s"

end Tests.FloatVectors
`, count, count, sb.String())
}

func parseRat(digits int64, k int) (float64, error) {
	s := fmt.Sprintf("%de-%d", digits, k)
	var f float64
	_, err := fmt.Sscanf(s, "%g", &f)
	return f, err
}

func parseRat32(digits int64, k int) (float32, error) {
	s := fmt.Sprintf("%de-%d", digits, k)
	var f float32
	_, err := fmt.Sscanf(s, "%g", &f)
	return f, err
}
