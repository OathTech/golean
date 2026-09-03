// noodler probes — literal forms and constant arithmetic
// (spec#Integer_literals, spec#Floating-point_literals, spec#Rune_literals,
// spec#Constant_expressions, spec#Constants).
package main

// Every integer literal form.
func integerLiteralForms() (int, int, int, int, int, int) {
	return 0b1010, 0o17, 017, 0x_FF, 1_000_000, 0o7
}

// Hex float literals and exponent forms.
func floatLiteralForms() (float64, float64, float64, float32) {
	return 0x1p-2, 1e3, .5, 0x1.8p1
}

// Rune literal escapes.
func runeLiteralEscapes() (rune, rune, rune, rune, rune) {
	return '\x41', 'é', '\U0001F600', '\377', '\''
}

// Untyped constant arithmetic is exact: 0.1+0.2 == 0.3 as constants,
// not at runtime.
func constantExactness() (bool, bool) {
	const a, b, c = 0.1, 0.2, 0.3
	x, y, z := 0.1, 0.2, 0.3
	return a+b == c, x+y == z
}

// Big constant shifts collapse exactly.
func bigConstantShift() (int, float64) {
	const huge = 1 << 100
	const back = huge >> 98
	return back, float64(huge) / float64(1<<99)
}

// TYPED float32 constant arithmetic rounds to float32 after every
// operation (spec#Constant_expressions: typed constant values "must
// always be accurately representable by values of the constant type"),
// so a typed chain equals the runtime chain; an UNTYPED chain is exact
// and rounds once at the conversion, which differs (gc-probed:
// artifacts p3 — true false false true).
func typedFloat32Constants() (bool, bool, bool, bool) {
	const c float32 = 0.1
	var v float32 = 0.1
	const typed7 = c * c * c * c * c * c * c
	const untyped7 = 0.1 * 0.1 * 0.1 * 0.1 * 0.1 * 0.1 * 0.1
	w7 := v * v * v * v * v * v * v
	f := float32(untyped7)
	var g float32 = 0.1 * 10
	t := v + v + v + v + v + v + v + v + v + v
	return typed7 == w7, f == w7, g == t, g == 1
}

// len of constant strings and arrays is a constant.
func lenConstants() (int, int, int) {
	const s = "héllo"
	var arr [len(s)]int
	return len(s), len(arr), len("é\xff")
}

// Rune constant arithmetic and string conversion.
func runeConstantArithmetic() (string, int, bool) {
	const c = 'a' + 1
	var check any = c
	_, isRune := check.(rune)
	return string(c), c, isRune
}

// Untyped constant division truncates for integers, exact for floats.
func constantDivision() (int, float64, int) {
	const a = 7 / 2
	const b = 7 / 2.0
	const c = -7 / 2
	return a, b, c
}

// iota in expressions with skipped and repeated lines.
func iotaPatterns() (int, int, int, int) {
	const (
		_  = iota
		KB = 1 << (10 * iota)
		MB
		GB
	)
	const (
		a = iota * 10
		b
		_
		d
	)
	return KB, MB, GB, a + b + d
}

// Typed constant conversions at boundaries: MaxUint8 via typed const.
func typedConstantBoundaries() (uint8, int8, uint64) {
	const m uint8 = 255
	const n int8 = -128
	const big uint64 = 1<<64 - 1
	return m, n, big
}

// String literal forms: raw with newline, interpreted escapes.
func stringLiteralForms() (int, int, byte) {
	raw := `a\nb
c`
	esc := "a\nb\tc\x00"
	return len(raw), len(esc), esc[5]
}

// A float constant representable exactly as int converts; int(1e3).
func floatConstantToInt() (int, int64) {
	const f = 1e3
	const g = 2.0 * 3
	return int(f), int64(g)
}

// Boolean constants and comparisons at compile time.
func booleanConstants() (bool, bool) {
	const t = 1 < 2
	const u = "a" < "b" && !t
	return t, u
}

// Complex-free: an untyped constant assigned to an interface takes its
// default type.
func defaultTypesIntoInterface() (bool, bool, bool, bool) {
	var a any = 1
	var b any = 1.0
	var c any = 'x'
	var d any = 1 << 40
	_, ia := a.(int)
	_, fb := b.(float64)
	_, rc := c.(int32)
	_, id := d.(int)
	return ia, fb, rc, id
}

// Integer division of untyped constants mixed with typed variable.
func constantMixedWithVariable() (int, float64) {
	x := 3
	f := 3.0
	return x * 7 / 2, f * 7 / 2
}

// Shift of an untyped constant by a variable in a float context is
// illegal; in an int context fine — and the count can be a constant
// expression.
func constantShiftByConstant() (uint16, int) {
	const s = 3
	var u uint16 = 1 << s
	return u << s, 1<<s + 1<<(s+1)
}

func main() {}
