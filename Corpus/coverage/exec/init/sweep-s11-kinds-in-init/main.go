package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group Q2: the shape's values computed at
// PACKAGE INITIALIZATION — package-level variables of each kind initialized by a wrapping
// expression, a shift past the width, a float → int conversion in range, an int → float's bits, a
// NaN comparison, a min of ±0, a `--` at zero in init() — observed after init. The init ORDER is
// S19's; here only the values at each width.

import "math"

var gMax int8 = 127
var gWrap = gMax + 1
var gShift uint8 = 1
var gCount uint = 9
var gShifted = gShift << gCount
var gSrc int64 = 9007199254740993
var gBits = math.Float64bits(float64(gSrc))
var gNaN = func() float64 { z := 0.0; return z / z }()
var gNaNCmp = gNaN != gNaN
var gF float64 = -2147483648.9
var gConv int32
var gMinZero uint64
var gU64 uint64 = 0
var gU16 uint16 = 65535
var gProd = gU16 * gU16
var gNeg int64 = -9223372036854775808
var gNegDiv = gNeg / -1
var gF32 float32 = 0.1
var gF32Sum = math.Float32bits(gF32 + 0.2)

func init() {
	z := 0.0
	nz := -z
	gMinZero = math.Float64bits(min(z, nz))
	gConv = int32(gF)
	gU64--
}

func initKinds() (int8, uint8, uint64, bool, uint64, int32, uint64, uint16, int64, uint32) {
	return gWrap, gShifted, gBits, gNaNCmp, gMinZero, gConv, gU64, gProd, gNegDiv, gF32Sum
}

func main() {
	initKinds()
}
