package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group E: conversions between EVERY pair of
// integer kinds (spec#Conversions: sign extension or truncation to the target's width) from each
// source kind's minimum, maximum, a 64-bit pattern 0x876543218FEDCBA9 truncated into the source
// (the sign bit set at every width) and -1 (signed sources). Run-time sources; the uintptr target
// is observed through uint64. Site convertValueToTy's int arm (IntKind.normalize).
func convInt8Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int8 = -128
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt8Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int8 = 127
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt8Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int8 = -87
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt8Negone() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int8 = -1
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt16Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int16 = -32768
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt16Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int16 = 32767
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt16Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int16 = -13399
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt16Negone() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int16 = -1
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt32Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int32 = -2147483648
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt32Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int32 = 2147483647
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt32Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int32 = -1880241239
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt32Negone() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int32 = -1
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt64Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int64 = -9223372036854775808
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt64Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int64 = 9223372036854775807
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt64Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int64 = -8690466094513796183
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convInt64Negone() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int64 = -1
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convIntMin() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int = -9223372036854775808
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convIntMax() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int = 9223372036854775807
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convIntPattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int = -8690466094513796183
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convIntNegone() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x int = -1
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint8Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint8 = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint8Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint8 = 255
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint8Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint8 = 169
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint16Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint16 = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint16Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint16 = 65535
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint16Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint16 = 52137
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint32Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint32 = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint32Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint32 = 4294967295
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint32Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint32 = 2414726057
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint64Min() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint64 = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint64Max() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint64 = 18446744073709551615
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUint64Pattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint64 = 9756277979195755433
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintMin() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintMax() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint = 18446744073709551615
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintPattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uint = 9756277979195755433
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintptrMin() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uintptr = 0
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintptrMax() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uintptr = 18446744073709551615
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

func convUintptrPattern() (int8, int16, int32, int64, int, uint8, uint16, uint32, uint64, uint, uint64) {
	var x uintptr = 9756277979195755433
	return int8(x), int16(x), int32(x), int64(x), int(x), uint8(x), uint16(x), uint32(x), uint64(x), uint(x), uint64(uintptr(x))
}

type dInt8 int8
type dUint32 uint32
type dInt64 int64

func convDefinedSources() (int64, uint64, int8, uint8, uint64, int32) {
	var a dInt8 = -1
	var b dUint32 = 4294967295
	var c dInt64 = -9223372036854775808
	return int64(a), uint64(a), int8(b), uint8(c), uint64(c), int32(b)
}

func convDefinedTargets() (dInt8, dUint32, dInt64, dInt8) {
	var a uint8 = 255
	var b int8 = -1
	var c uint64 = 18446744073709551615
	var d int64 = -9223372036854775808
	return dInt8(a), dUint32(b), dInt64(c), dInt8(d)
}

func convAliases() (byte, rune, int8, uint32) {
	var a int16 = -1
	var b uint32 = 4294967295
	var c byte = 200
	var d rune = -1
	return byte(a), rune(b), int8(c), uint32(d)
}

func convChained() (uint8, int8, int64, uint16) {
	var a int8 = -1
	var b uint16 = 65535
	var c uint8 = 200
	var d int64 = -1
	return uint8(int8(uint16(a))), int8(uint8(int16(b))), int64(int32(uint32(uint8(c)))), uint16(int8(uint64(d)))
}

func convConstantsAtDefined() (dInt8, dUint32, int64, uint64) {
	const k dInt8 = -1
	const u dUint32 = 1<<32 - 1
	return k, u, int64(k), uint64(u)
}

func main() {
	convInt8Min()
	convInt8Max()
	convInt8Pattern()
	convInt8Negone()
	convInt16Min()
	convInt16Max()
	convInt16Pattern()
	convInt16Negone()
	convInt32Min()
	convInt32Max()
	convInt32Pattern()
	convInt32Negone()
	convInt64Min()
	convInt64Max()
	convInt64Pattern()
	convInt64Negone()
	convIntMin()
	convIntMax()
	convIntPattern()
	convIntNegone()
	convUint8Min()
	convUint8Max()
	convUint8Pattern()
	convUint16Min()
	convUint16Max()
	convUint16Pattern()
	convUint32Min()
	convUint32Max()
	convUint32Pattern()
	convUint64Min()
	convUint64Max()
	convUint64Pattern()
	convUintMin()
	convUintMax()
	convUintPattern()
	convUintptrMin()
	convUintptrMax()
	convUintptrPattern()
	convDefinedSources()
	convDefinedTargets()
	convAliases()
	convChained()
	convConstantsAtDefined()
}
