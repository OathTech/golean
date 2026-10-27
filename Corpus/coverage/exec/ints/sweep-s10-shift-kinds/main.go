package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: a NEGATIVE shift count
// at every signed count kind (spec#Operators: «If the shift count is negative
// at run time, a run-time panic occurs»; ints/negative-shift and
// ints/shift-count-bound pin the `int` count), both directions, compound
// forms, an unsigned left operand, a defined count type, the most negative
// count, under recover. The count arrives as the entry argument.

type shiftCount int8

func shlCountInt8(z int) int {
	x := 3
	c := int8(z)
	return x << c
}

func shrCountInt8(z int) int {
	x := 3
	c := int8(z)
	return x >> c
}

func shlCountInt16(z int) int {
	x := 3
	c := int16(z)
	return x << c
}

func shrCountInt16(z int) int {
	x := 3
	c := int16(z)
	return x >> c
}

func shlCountInt32(z int) int {
	x := 3
	c := int32(z)
	return x << c
}

func shrCountInt32(z int) int {
	x := 3
	c := int32(z)
	return x >> c
}

func shlCountInt64(z int) int {
	x := 3
	c := int64(z)
	return x << c
}

func shrCountInt64(z int) int {
	x := 3
	c := int64(z)
	return x >> c
}

func shlAssign(z int) int {
	x := 3
	x <<= z
	return x
}

func shrAssign(z int) int {
	x := 3
	x >>= z
	return x
}

func unsignedLeftOperand(z int) int {
	var x uint32 = 3
	return int(x << z)
}

func definedCount(z int) int {
	x := 3
	c := shiftCount(z)
	return x << c
}

func minCount(z int) int {
	x := 3
	c := int8(z)
	return x >> c
}

func shiftRecovered(z int) int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		r = 3 << z
	}()
	return r + 1
}

func main() {}
