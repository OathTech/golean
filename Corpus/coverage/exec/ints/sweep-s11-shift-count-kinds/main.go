package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, groups C2–C4 and C6: the shift COUNT's kind
// (spec#Operators: any integer type or an untyped constant representable by uint) at the width
// boundary — uint8, int8, int16, int64, uint64, uintptr, rune, byte, a defined count type, both
// directions and compound; a CONSTANT count at or past the operand's width on a non-constant
// operand (gc compiles `x << 70` for a variable x: the width saturates at run time); an untyped
// constant LEFT operand of a non-constant shift takes the type it would have without the shift
// (`var u uint8 = 1 << n` saturates at 8, `x := 1 << n` is an int); shifts at defined types and
// through a map compound, a pointer and a struct field. The negative counts are sweep-s10-shift-kinds.

type shCount uint16
type shOp uint16

type holder struct {
	i8 int8
	u8 uint8
}

func countKindsAtWidth() (int32, int32, uint8, uint8, int32, uint8, int32, int32, uint8, uint8, int32, uint8) {
	var x int32 = -2147483648
	var y uint8 = 0x80
	var c8 uint8 = 31
	var c8w uint8 = 32
	var i8 int8 = 7
	var i8w int8 = 8
	var i16 int16 = 31
	var u64 uint64 = 8
	var p uintptr = 31
	var r rune = 7
	var b byte = 32
	var d shCount = 8
	return x >> c8, x >> c8w, y << i8, y << i8w, x << i16, y >> u64, x >> p, x << r, y << b, y >> d, x >> 31 << 1, y >> 7 << 7
}

func countKindsCompound() (int32, uint8, uint64, int8) {
	var x int32 = -2147483648
	var c8 uint8 = 31
	x >>= c8
	var y uint8 = 0x80
	var i64 int64 = 8
	y <<= i64
	var z uint64 = 1
	var p uintptr = 64
	z <<= p
	var w int8 = -128
	var d shCount = 7
	w >>= d
	return x, y, z, w
}

func constantCountsPastWidth() (int32, int32, uint8, uint8, int64, int64, int8, uint16) {
	var x int32 = -1
	var y uint8 = 0xFF
	var z int64 = -9223372036854775808
	var w int8 = -128
	var v uint16 = 0xFFFF
	return x << 31, x << 32, y << 8, y >> 70, z >> 64, z << 63, w >> 100, v << 16
}

func untypedLeftOperand(n int) (uint8, uint8, int8, uint64, uint64, int64, int, int, int, int) {
	var a uint8 = 1 << n
	var b uint8 = 1 << (n + 1)
	var c int8 = 1 << n
	var d uint64 = 1 << (n * 9)
	var e uint64 = 1 << (n*9 + 1)
	var f int64 = 1 << (n * 9)
	g := 1 << (n*9 + 1)
	h := 1 << (n * 9)
	s := make([]int, 300)
	s[1<<n] = 5
	i := s[1<<n]
	j := 0
	if 1<<(n+1) == 256 {
		j = 1
	}
	return a, b, c, d, e, f, g, h, i, j
}

func untypedLeftExplicitConversion(n int) (uint8, int, int, uint16) {
	u := uint8(1) << n
	v := len("abc") << n
	w := int(1) << (n * 9)
	var x uint16 = 1 << n
	x <<= n
	x <<= n
	return u, v, w, x
}

func shiftsAtDefinedAndRoutes() (shOp, shOp, uint8, int8, int8, uint8) {
	var a shOp = 1
	var b shOp = 0x8000
	var c shCount = 16
	m := map[string]uint8{"k": 1}
	m["k"] <<= 9
	var p int8 = -128
	q := &p
	*q >>= 1
	h := holder{i8: -1, u8: 0x80}
	h.i8 <<= 7
	h.u8 >>= 8
	return a << c, b >> 15, m["k"], p, h.i8, h.u8
}

func main() {
	countKindsAtWidth()
	countKindsCompound()
	constantCountsPastWidth()
	untypedLeftOperand(7)
	untypedLeftExplicitConversion(7)
	shiftsAtDefinedAndRoutes()
}
