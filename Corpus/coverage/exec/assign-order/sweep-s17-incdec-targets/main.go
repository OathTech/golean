package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-141's line): IncDec statements at the target spellings the corpus
// did not hold — a nested value field, a field of a slice element, a
// parenthesised and a bare dereference, a float operand, the nil-pointer
// and out-of-range panics at the read-modify-write, and an IncDec in a
// generic body over a wrapping kind. Expected = gc go1.26.5.

type pt struct{ x, y int }

type outer struct{ in pt }

// A5.3
func nestedFieldIncdec() int {
	var s outer
	s.in.x++
	s.in.x++
	s.in.y--
	return s.in.x*10 + s.in.y // 19
}

func sliceElemStructFieldIncdec() int {
	ss := []pt{{1, 2}}
	ss[0].x++
	ss[0].y--
	return ss[0].x*10 + ss[0].y // 21
}

func derefParenIncdec() int {
	x := 4
	p := &x
	(*p)++
	return x // 5
}

func derefBareIncdec() int {
	x := 4
	p := &x
	*p++
	*p++
	return x // 6
}

// A5.5
func floatIncdec() int {
	f := 1.5
	f++
	f--
	f++
	return int(f * 10) // 25
}

// A5.6
func nilPtrFieldIncdecPanic() int {
	var p *pt
	p.x++
	return p.x
}

func sliceOobIncdecPanic() int {
	s := []int{1}
	s[1]++
	return s[0]
}

// A5.9
func incG[T int | int8](x T) T {
	x++
	x++
	return x
}

func incdecInGeneric() int {
	return int(incG(int8(126)))*10 + incG(1) // -1280 + 3 = -1277
}

func main() {
	println(nestedFieldIncdec(), sliceElemStructFieldIncdec(), derefParenIncdec(), derefBareIncdec(), floatIncdec(),
		incdecInGeneric())
}
