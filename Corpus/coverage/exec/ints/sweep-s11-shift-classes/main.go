package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group C1: shifts by EVERY count class at
// every integer kind and direction (spec#Operators: no upper limit on the count; a count at or
// past the width leaves 0 for << and an unsigned >>, the sign fill for a signed >>). Counts
// {0, 1, w-2, w-1, w, w+1, 2w, 63, 64, 65, 1<<20, 1<<40} as run-time uint values; the operand
// a positive bit pattern, its negation and -1 (signed kinds). BUG-096's site (intShift*Result).
func shlInt8Pos() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = 90
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt8Neg() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = -90
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt8Negone() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt8Pos() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = 90
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt8Neg() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = -90
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt8Negone() (int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8, int8) {
	var x int8 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt16Pos() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = 23130
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt16Neg() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = -23130
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt16Negone() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt16Pos() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = 23130
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt16Neg() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = -23130
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt16Negone() (int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16, int16) {
	var x int16 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt32Pos() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = 1515870810
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt32Neg() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = -1515870810
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt32Negone() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt32Pos() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = 1515870810
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt32Neg() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = -1515870810
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt32Negone() (int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32, int32) {
	var x int32 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt64Pos() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = 6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt64Neg() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = -6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlInt64Negone() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt64Pos() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = 6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt64Neg() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = -6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrInt64Negone() (int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64, int64) {
	var x int64 = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlIntPos() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = 6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlIntNeg() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = -6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlIntNegone() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrIntPos() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = 6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrIntNeg() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = -6510615555426900570
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrIntNegone() (int, int, int, int, int, int, int, int, int, int, int, int) {
	var x int = -1
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUint8Pos() (uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8) {
	var x uint8 = 165
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrUint8Pos() (uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8) {
	var x uint8 = 165
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 6
	var c3 uint = 7
	var c4 uint = 8
	var c5 uint = 9
	var c6 uint = 16
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUint16Pos() (uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16) {
	var x uint16 = 42405
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrUint16Pos() (uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16, uint16) {
	var x uint16 = 42405
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 14
	var c3 uint = 15
	var c4 uint = 16
	var c5 uint = 17
	var c6 uint = 32
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUint32Pos() (uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32) {
	var x uint32 = 2779096485
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrUint32Pos() (uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32, uint32) {
	var x uint32 = 2779096485
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 30
	var c3 uint = 31
	var c4 uint = 32
	var c5 uint = 33
	var c6 uint = 64
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUint64Pos() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var x uint64 = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrUint64Pos() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var x uint64 = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUintPos() (uint, uint, uint, uint, uint, uint, uint, uint, uint, uint, uint, uint) {
	var x uint = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shrUintPos() (uint, uint, uint, uint, uint, uint, uint, uint, uint, uint, uint, uint) {
	var x uint = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11
}

func shlUintptrPos() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var x uintptr = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x << c0
	r1 := x << c1
	r2 := x << c2
	r3 := x << c3
	r4 := x << c4
	r5 := x << c5
	r6 := x << c6
	r7 := x << c7
	r8 := x << c8
	r9 := x << c9
	r10 := x << c10
	r11 := x << c11
	return uint64(r0), uint64(r1), uint64(r2), uint64(r3), uint64(r4), uint64(r5), uint64(r6), uint64(r7), uint64(r8), uint64(r9), uint64(r10), uint64(r11)
}

func shrUintptrPos() (uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64) {
	var x uintptr = 11936128518282651045
	var c0 uint = 0
	var c1 uint = 1
	var c2 uint = 62
	var c3 uint = 63
	var c4 uint = 64
	var c5 uint = 65
	var c6 uint = 128
	var c7 uint = 63
	var c8 uint = 64
	var c9 uint = 65
	var c10 uint = 1048576
	var c11 uint = 1099511627776
	r0 := x >> c0
	r1 := x >> c1
	r2 := x >> c2
	r3 := x >> c3
	r4 := x >> c4
	r5 := x >> c5
	r6 := x >> c6
	r7 := x >> c7
	r8 := x >> c8
	r9 := x >> c9
	r10 := x >> c10
	r11 := x >> c11
	return uint64(r0), uint64(r1), uint64(r2), uint64(r3), uint64(r4), uint64(r5), uint64(r6), uint64(r7), uint64(r8), uint64(r9), uint64(r10), uint64(r11)
}

func main() {
	shlInt8Pos()
	shlInt8Neg()
	shlInt8Negone()
	shrInt8Pos()
	shrInt8Neg()
	shrInt8Negone()
	shlInt16Pos()
	shlInt16Neg()
	shlInt16Negone()
	shrInt16Pos()
	shrInt16Neg()
	shrInt16Negone()
	shlInt32Pos()
	shlInt32Neg()
	shlInt32Negone()
	shrInt32Pos()
	shrInt32Neg()
	shrInt32Negone()
	shlInt64Pos()
	shlInt64Neg()
	shlInt64Negone()
	shrInt64Pos()
	shrInt64Neg()
	shrInt64Negone()
	shlIntPos()
	shlIntNeg()
	shlIntNegone()
	shrIntPos()
	shrIntNeg()
	shrIntNegone()
	shlUint8Pos()
	shrUint8Pos()
	shlUint16Pos()
	shrUint16Pos()
	shlUint32Pos()
	shrUint32Pos()
	shlUint64Pos()
	shrUint64Pos()
	shlUintPos()
	shrUintPos()
	shlUintptrPos()
	shrUintptrPos()
}
