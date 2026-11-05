package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group Q3 (BUG-173's position): a BLANK target
// discarding a value of each kind — a call result of every scalar kind, a float32, a float64, a
// string, a bool, a struct, a pointer, a slice, an interface; the non-int components of multi-value
// calls in every blank position; a received channel element of a narrow kind; a plain variable of
// each kind — every discard temp typed by the wire's resultTypes, never by the default int.

type pt struct{ x, y int }

func retI8() int8        { return -5 }
func retU64() uint64     { return 1<<64 - 1 }
func retUptr() uintptr   { return 7 }
func retF32() float32    { return 0.1 }
func retF64() float64    { return 2.5 }
func retStr() string     { return "s" }
func retBool() bool      { return true }
func retStruct() pt      { return pt{1, 2} }
func retPtr() *int       { x := 3; return &x }
func retSlice() []int    { return []int{1} }
func retIface() any      { return uint16(9) }
func two() (float32, int8) { return 1.5, -7 }
func three() (uint8, string, int64) { return 255, "t", -1 << 63 }

func discardScalars() int {
	_ = retI8()
	_ = retU64()
	_ = retUptr()
	_ = retF32()
	_ = retF64()
	_ = retStr()
	_ = retBool()
	return 11
}

func discardComposites() int {
	_ = retStruct()
	_ = retPtr()
	_ = retSlice()
	_ = retIface()
	return 22
}

func discardMultiValue() (int8, float32, string, int64, uint8) {
	_, x := two()
	y, _ := two()
	_, _ = two()
	_, s, _ := three()
	u, _, v := three()
	a, _, _ := three()
	_, _, _ = three()
	return x, y, s, v, u + a
}

func discardReceiveAndVars() (uint8, float32) {
	ch := make(chan uint8, 2)
	ch <- 255
	ch <- 1
	_ = <-ch
	var u uint8 = 200
	_ = u
	var f float32 = 0.5
	_ = f
	var p uintptr = 9
	_ = p
	var s string = "q"
	_ = s
	return <-ch, f
}

func main() {
	discardScalars()
	discardComposites()
	discardMultiValue()
	discardReceiveAndVars()
}
