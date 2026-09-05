package main

// BUG-096 (docs/BUGS.md): shift counts at and past the operand's width.
// spec#Operators: "The shift operators shift the left operand by the shift
// count ... They implement arithmetic shifts if the left operand is a
// signed integer and logical shifts if it is an unsigned integer. There is
// no upper limit on the shift count. Shifts behave as if the left operand
// is shifted n times by 1" — so a count >= the width yields 0 for every
// left shift and every unsigned right shift, and the sign fill (-1 / 0)
// for a signed right shift; a negative count panics at run time. On main
// the machine formed `2 ^ count` over `Int` before normalizing to the
// width, and a count like 1<<32 tripped Lean's `Nat.pow` guard — the
// PROCESS aborted (no observation at all) where gc answers 0.

// shiftCountBoundLeftHuge: gc 0 0 0 0.
func shiftCountBoundLeftHuge() (int, uint64, int32, uint8) {
	var i uint64 = 1 << 32
	x := 12345
	var u uint64 = 1
	var s int32 = -7
	var b uint8 = 255
	return x << i, u << i, s << i, b << i
}

// shiftCountBoundRightHugeSigned: gc 0 -1 -1 -1.
func shiftCountBoundRightHugeSigned() (int, int, int64, int8) {
	var i uint64 = 1 << 40
	x := 12345
	var n int64 = -12345
	var m int8 = -1
	return x >> i, -x >> i, n >> i, m >> i
}

// shiftCountBoundRightHugeUnsigned: gc 0 0 0.
func shiftCountBoundRightHugeUnsigned() (uint, uint64, uint8) {
	var i uint = 1 << 33
	var a uint = 1<<63 + 5
	var b uint64 = 1<<64 - 1
	var c uint8 = 200
	return a >> i, b >> i, c >> i
}

// shiftCountBoundWidth: the count EXACTLY at the width — gc 0 0 0 0 -1 -1.
func shiftCountBoundWidth() (int64, uint64, int8, uint8, int64, int32) {
	var w64 uint = 64
	var w8 uint = 8
	var a int64 = 1
	var b uint64 = 1<<64 - 1
	var c int8 = 1
	var d uint8 = 1
	var e int64 = -5
	var f int32 = -5
	return a << w64, b >> w64, c << w8, d << w8, e >> w64, f >> (w64 / 2)
}

// shiftCountBoundWidthMinusOne: the last in-width count still computes —
// gc -9223372036854775808 9223372036854775808 -128 -1.
func shiftCountBoundWidthMinusOne() (int64, uint64, int8, int32) {
	var s63 uint = 63
	var s7 uint = 7
	var s31 uint = 31
	var a int64 = 1
	var b uint64 = 1
	var c int8 = 1
	var d int32 = -1
	return a << s63, b << s63, c << s7, d >> s31
}

// shiftCountBoundIntCount: a SIGNED count type (int, Go 1.13+), huge and
// in-width — gc 0 9223372036854775808.
func shiftCountBoundIntCount() (int, uint64) {
	var n int = 1 << 40
	var m int = 63
	x := 3
	var u uint64 = 1
	return x << n, u << m
}

// shiftCountBoundNegativePanic: a hugely negative count is still the
// negative-count panic, never a saturated 0.
func shiftCountBoundNegativePanic() int {
	var n int = -(1 << 40)
	x := 3
	return x << n
}

// shiftCountBoundUntypedConst: an UNTYPED constant left operand of a
// non-constant shift takes the type it would have without the shift
// (spec#Operators) — so the width that saturates is that type's.
// gc 1099511627776 0 -2147483648 0.
func shiftCountBoundUntypedConst() (uint64, uint8, int32, int) {
	var n uint = 40
	var m uint = 8
	var k uint = 31
	var big uint = 1 << 35
	var u uint64 = 1 << n
	var b uint8 = 1 << m
	var c int32 = 1 << k
	d := 1 << big
	return u, b, c, d
}

func main() {
	shiftCountBoundLeftHuge()
	shiftCountBoundRightHugeSigned()
	shiftCountBoundRightHugeUnsigned()
	shiftCountBoundWidth()
	shiftCountBoundWidthMinusOne()
	shiftCountBoundIntCount()
	shiftCountBoundUntypedConst()
}
