// noodler probes — integer arithmetic at the representation edges
// (spec#Integer_operators, spec#Arithmetic_operators, spec#Operators).
package main

// MinInt64 / -1 overflows to MinInt64 with no panic; % gives 0
// (spec#Integer_operators: "x / -1 is equal to -x ... due to overflow").
func minIntDivNegOne() (int64, int64, int8, int8) {
	var m int64 = -1 << 63
	var d int64 = -1
	var m8 int8 = -128
	var d8 int8 = -1
	return m / d, m % d, m8 / d8, m8 % d8
}

// Truncated division: quotient toward zero, remainder takes the sign of
// the dividend.
func truncatedDivisionSigns() (int, int, int, int, int, int) {
	a, b := -7, 2
	c, d := 7, -2
	e, f := -7, -2
	return a / b, a % b, c / d, c % d, e / f, e % f
}

// Arithmetic right shift of negatives rounds toward -inf.
func arithmeticShiftNegative() (int, int, int64, int8) {
	x := -7
	var y int64 = -1
	var z int8 = -128
	return x >> 1, x >> 60, y >> 63, z >> 7
}

// Shift counts >= width: left gives 0; right gives 0 or -1 by sign.
func shiftPastWidth() (uint8, int8, int8, uint64, int64) {
	var u uint8 = 0xff
	var p int8 = 1
	var n int8 = -1
	var w uint64 = 1
	var v int64 = -5
	s := 8
	big := 200
	return u << s, p << s, n >> s, w << 64, v >> big
}

// The untyped constant 1 in `1 << s` takes the type it would have
// without the shift (spec#Operators: "the shift expression ... is
// converted to the type it would assume if the shift were replaced by
// its left operand alone").
func untypedOneShiftContext() (int8, int32, uint8, int64, int8) {
	s := 7
	var a int8 = 1 << s         // int8(1) << 7 = -128
	var b int32 = 1 << s        // 128
	var c uint8 = 1 << (s + 1)  // uint8(1) << 8 = 0
	var d int64 = 1 << (s + 56) // 1<<63 = MinInt64
	var e int8 = 1 << s >> s    // (int8(1) << 7) >> 7 = -128 >> 7 = -1, not 1
	return a, b, c, d, e
}

// A shift with a signed count that is non-negative is fine (Go 1.13).
func signedShiftCount() (int, uint) {
	var c int8 = 3
	var d int64 = 62
	return 1 << c, uint(1) << d
}

// Increment past MaxInt32 wraps; decrement of uint zero wraps.
func incDecWraps() (int32, uint16, int64) {
	var x int32 = 1<<31 - 1
	x++
	var y uint16
	y--
	var z int64 = -1 << 63
	z--
	return x, y, z
}

// Multiplication overflow wraps deterministically.
func mulOverflowWrap() (int32, uint32, int64) {
	var a int32 = 1 << 30
	var b uint32 = 1 << 31
	var c int64 = 1 << 62
	return a * 4, b * 2, c * 4
}

// Unary minus on unsigned wraps; bit complement.
func unaryOnUnsigned() (uint8, uint8, uint32, int8) {
	var a uint8 = 1
	var b uint8 = 0
	var c uint32 = 5
	var d int8 = -128
	return -a, ^b, ^c, -d
}

// AND NOT and compound bit ops.
func bitClearOps() (int, uint8) {
	x := 0b1111_0000
	x &^= 0b0011_0000
	var y uint8 = 0o377
	y &^= 0x0f
	return x, y
}

// Mixed shift + mask idiom, count taken from a masked variable.
func maskedShiftCount() (uint64, int) {
	var v uint64 = 1
	c := 70
	return v << (c & 63), -1 >> (c & 63)
}

// Compound assignment `a[i()] op= f()` evaluates the index operand once
// and the operands left-to-right (calls ordered).
var trace []int

func idx() int {
	trace = append(trace, 1)
	return 1
}

func val() int {
	trace = append(trace, 2)
	return 5
}

func compoundIndexAssignOrder() (int, int, int, int) {
	trace = nil
	a := []int{10, 20, 30}
	a[idx()] += val()
	return a[1], len(trace), trace[0], trace[1]
}

// Division by a variable that is zero panics with gc's exact text;
// modulo has the same text.
func moduloByZero(x int) int {
	z := x - x
	return 7 % z
}

// Division of MinInt by a runtime -1 in the 16-bit width.
func minInt16DivNegOne() (int16, int16) {
	var m int16 = -32768
	var d int16 = -1
	return m / d, m % d
}

// Constant vs runtime: (a*b)/b where a*b overflows.
func overflowThenDivide() int32 {
	var a int32 = 1 << 30
	var b int32 = 4
	return (a * b) / b
}

// Comparison chains between differently-signed values after conversion.
func signedUnsignedCompare() (bool, bool, bool) {
	var s int32 = -1
	var u uint32 = 1
	return uint32(s) > u, int64(u) > int64(s), s < 0
}

// Unsigned subtraction never panics: 3 - 5 wraps.
func unsignedSubWrap() (uint, uint8, uint32) {
	var a uint = 3
	var b uint8 = 3
	var c uint32 = 0
	return a - 5, b - 5, c - 1
}

// Left shift of a negative value.
func shiftNegativeLeft() (int8, int32, int) {
	var a int8 = -1
	var b int32 = -1
	c := -3
	return a << 7, b << 31, c << 2
}

// int8 loop counter wrap: the loop terminates because the counter
// wraps to negative.
func int8CounterWrapTerminates() int {
	count := 0
	for i := int8(120); i > 0; i++ {
		count++
	}
	return count
}

func main() {}
