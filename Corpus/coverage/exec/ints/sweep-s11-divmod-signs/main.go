package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group B: integer division truncates toward
// zero and the remainder takes the dividend's sign at EVERY kind (spec#Integer_operators); the
// most negative value / -1 wraps and % -1 is 0; unsigned forms at the maximum.
func divModInt8() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var a int8 = -7
	var b int8 = 2
	var mn int8 = -128
	var m1 int8 = -1
	r1 := a / b
	r2 := a % b
	r3 := (-a) / (-b)
	r4 := (-a) % (-b)
	r5 := a / (-b)
	r6 := a % (-b)
	r7 := mn % m1
	r8 := (mn + 1) / m1
	r9 := mn / m1
	r10 := a / a
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
}

func divModInt16() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var a int16 = -7
	var b int16 = 2
	var mn int16 = -32768
	var m1 int16 = -1
	r1 := a / b
	r2 := a % b
	r3 := (-a) / (-b)
	r4 := (-a) % (-b)
	r5 := a / (-b)
	r6 := a % (-b)
	r7 := mn % m1
	r8 := (mn + 1) / m1
	r9 := mn / m1
	r10 := a / a
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
}

func divModInt32() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var a int32 = -7
	var b int32 = 2
	var mn int32 = -2147483648
	var m1 int32 = -1
	r1 := a / b
	r2 := a % b
	r3 := (-a) / (-b)
	r4 := (-a) % (-b)
	r5 := a / (-b)
	r6 := a % (-b)
	r7 := mn % m1
	r8 := (mn + 1) / m1
	r9 := mn / m1
	r10 := a / a
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
}

func divModInt64() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var a int64 = -7
	var b int64 = 2
	var mn int64 = -9223372036854775808
	var m1 int64 = -1
	r1 := a / b
	r2 := a % b
	r3 := (-a) / (-b)
	r4 := (-a) % (-b)
	r5 := a / (-b)
	r6 := a % (-b)
	r7 := mn % m1
	r8 := (mn + 1) / m1
	r9 := mn / m1
	r10 := a / a
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
}

func divModInt() (int, int, int, int, int, int, int, int, int, int) {
	var a int = -7
	var b int = 2
	var mn int = -9223372036854775808
	var m1 int = -1
	r1 := a / b
	r2 := a % b
	r3 := (-a) / (-b)
	r4 := (-a) % (-b)
	r5 := a / (-b)
	r6 := a % (-b)
	r7 := mn % m1
	r8 := (mn + 1) / m1
	r9 := mn / m1
	r10 := a / a
	return r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
}

func divModUint8() (uint8, uint8, uint8, uint8, uint8, uint8) {
	var mx uint8 = 255
	var three uint8 = 3
	var seven uint8 = 7
	var z uint8 = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return r1, r2, r3, r4, r5, r6
}

func divModUint16() (uint16, uint16, uint16, uint16, uint16, uint16) {
	var mx uint16 = 65535
	var three uint16 = 3
	var seven uint16 = 7
	var z uint16 = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return r1, r2, r3, r4, r5, r6
}

func divModUint32() (uint32, uint32, uint32, uint32, uint32, uint32) {
	var mx uint32 = 4294967295
	var three uint32 = 3
	var seven uint32 = 7
	var z uint32 = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return r1, r2, r3, r4, r5, r6
}

func divModUint64() (uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uint64 = 18446744073709551615
	var three uint64 = 3
	var seven uint64 = 7
	var z uint64 = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return r1, r2, r3, r4, r5, r6
}

func divModUint() (uint, uint, uint, uint, uint, uint) {
	var mx uint = 18446744073709551615
	var three uint = 3
	var seven uint = 7
	var z uint = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return r1, r2, r3, r4, r5, r6
}

func divModUintptr() (uint64, uint64, uint64, uint64, uint64, uint64) {
	var mx uintptr = 18446744073709551615
	var three uintptr = 3
	var seven uintptr = 7
	var z uintptr = 0
	r1 := mx / three
	r2 := mx % seven
	r3 := mx / mx
	r4 := z / mx
	r5 := mx % mx
	r6 := (mx - 1) % three
	return uint64(r1), uint64(r2), uint64(r3), uint64(r4), uint64(r5), uint64(r6)
}

type dInt32 int32

func divModDefinedInt32() (dInt32, dInt32, dInt32, dInt32) {
	var a dInt32 = -7
	var b dInt32 = 2
	var mn dInt32 = -2147483648
	return a / b, a % b, mn / -1, mn % -1
}

func divModCompound() (int8, int8, int16, int16, int64, int64) {
	var a int8 = -7
	a /= 2
	var b int8 = -7
	b %= 2
	var c int16 = -32768
	c /= -1
	var d int16 = -32768
	d %= -1
	var e int64 = 7
	e /= -2
	var f int64 = 7
	f %= -2
	return a, b, c, d, e, f
}

func divModConstDividend(d int) (int, int, int, int) {
	return -7 / d, -7 % d, 7 / d, 7 % d
}

func main() {
	divModInt8()
	divModInt16()
	divModInt32()
	divModInt64()
	divModInt()
	divModUint8()
	divModUint16()
	divModUint32()
	divModUint64()
	divModUint()
	divModUintptr()
	divModDefinedInt32()
	divModCompound()
	divModConstDividend(2)
	divModConstDividend(2)
}
