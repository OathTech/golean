package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group D: the bitwise operators and the
// complement on SIGNED values (two's complement at the kind's width) and at the unsigned maxima;
// run-time operands. Sites intBitwiseBinaryResult / intBitClearResult / intBitNegResult.
func bitwiseInt8() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var a int8 = -1
	var b int8 = 15
	var c int8 = -8
	var d int8 = 5
	var mn int8 = -128
	var mx int8 = 127
	var z int8 = 0
	var s6 int8 = -6
	var s3 int8 = -3
	r1 := a & b
	r2 := c | d
	r3 := a ^ 1
	r4 := a &^ b
	r5 := d &^ a
	r6 := ^a
	r7 := ^mn
	r8 := ^mx
	r9 := ^z
	r10 := mn | 1
	r11 := mn & a
	r12 := s6 ^ s3
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12
}

func bitwiseInt16() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var a int16 = -1
	var b int16 = 15
	var c int16 = -8
	var d int16 = 5
	var mn int16 = -32768
	var mx int16 = 32767
	var z int16 = 0
	var s6 int16 = -6
	var s3 int16 = -3
	r1 := a & b
	r2 := c | d
	r3 := a ^ 1
	r4 := a &^ b
	r5 := d &^ a
	r6 := ^a
	r7 := ^mn
	r8 := ^mx
	r9 := ^z
	r10 := mn | 1
	r11 := mn & a
	r12 := s6 ^ s3
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12
}

func bitwiseInt32() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var a int32 = -1
	var b int32 = 15
	var c int32 = -8
	var d int32 = 5
	var mn int32 = -2147483648
	var mx int32 = 2147483647
	var z int32 = 0
	var s6 int32 = -6
	var s3 int32 = -3
	r1 := a & b
	r2 := c | d
	r3 := a ^ 1
	r4 := a &^ b
	r5 := d &^ a
	r6 := ^a
	r7 := ^mn
	r8 := ^mx
	r9 := ^z
	r10 := mn | 1
	r11 := mn & a
	r12 := s6 ^ s3
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12
}

func bitwiseInt64() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var a int64 = -1
	var b int64 = 15
	var c int64 = -8
	var d int64 = 5
	var mn int64 = -9223372036854775808
	var mx int64 = 9223372036854775807
	var z int64 = 0
	var s6 int64 = -6
	var s3 int64 = -3
	r1 := a & b
	r2 := c | d
	r3 := a ^ 1
	r4 := a &^ b
	r5 := d &^ a
	r6 := ^a
	r7 := ^mn
	r8 := ^mx
	r9 := ^z
	r10 := mn | 1
	r11 := mn & a
	r12 := s6 ^ s3
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12
}

func bitwiseInt() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var a int = -1
	var b int = 15
	var c int = -8
	var d int = 5
	var mn int = -9223372036854775808
	var mx int = 9223372036854775807
	var z int = 0
	var s6 int = -6
	var s3 int = -3
	r1 := a & b
	r2 := c | d
	r3 := a ^ 1
	r4 := a &^ b
	r5 := d &^ a
	r6 := ^a
	r7 := ^mn
	r8 := ^mx
	r9 := ^z
	r10 := mn | 1
	r11 := mn & a
	r12 := s6 ^ s3
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12
}

func bitwiseUint8() (uint8, uint8, uint8, uint8, uint8, uint8) {
	var mx uint8 = 255
	var z uint8 = 0
	var one uint8 = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return r1, r2, r3, r4, r5, r6
}

func bitwiseUint16() (uint16, uint16, uint16, uint16, uint16, uint16) {
	var mx uint16 = 65535
	var z uint16 = 0
	var one uint16 = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return r1, r2, r3, r4, r5, r6
}

func bitwiseUint32() (uint32, uint32, uint32, uint32, uint32, uint32) {
	var mx uint32 = 4294967295
	var z uint32 = 0
	var one uint32 = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return r1, r2, r3, r4, r5, r6
}

func bitwiseUint64() (uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uint64 = 18446744073709551615
	var z uint64 = 0
	var one uint64 = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return r1, r2, r3, r4, r5, r6
}

func bitwiseUint() (uint, uint, uint, uint, uint, uint) {
	var mx uint = 18446744073709551615
	var z uint = 0
	var one uint = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return r1, r2, r3, r4, r5, r6
}

func bitwiseUintptr() (uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uintptr = 18446744073709551615
	var z uintptr = 0
	var one uintptr = 1
	r1 := ^z
	r2 := ^mx
	r3 := mx &^ one
	r4 := mx ^ one
	r5 := mx | one
	r6 := ^one
	return uint64(r1), uint64(r2), uint64(r3), uint64(r4), uint64(r5), uint64(r6)
}

func bitwiseCompoundInt8() (int8, int8, int8, int8, int8) {
	var a int8 = -1
	a &= 15
	var b int8 = -8
	b |= 5
	var c int8 = -1
	c ^= 1
	var d int8 = -1
	d &^= 15
	var e int8 = -128
	e ^= -1
	return a, b, c, d, e
}

func bitwiseConstOperands() (int8, int16, int32, int64, uint8, uint64) {
	var a int8 = -1
	var b int16 = -1
	var c int32 = -1
	var d int64 = -1
	var e uint8 = 1
	var f uint64 = 1
	return a & 0x7F, b &^ 0x7FFF, c ^ 0x7FFFFFFF, d | 0x7FFFFFFFFFFFFFFF, ^e, ^f
}

func main() {
	bitwiseInt8()
	bitwiseInt16()
	bitwiseInt32()
	bitwiseInt64()
	bitwiseInt()
	bitwiseUint8()
	bitwiseUint16()
	bitwiseUint32()
	bitwiseUint64()
	bitwiseUint()
	bitwiseUintptr()
	bitwiseCompoundInt8()
	bitwiseConstOperands()
}
