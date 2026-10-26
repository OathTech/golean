// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K13 defined-over-defined: `type A int; type B A` — B is identical to neither A nor int; an
// alias `type C = B` is B; a cross-package `type D ri.T` is neither ri.T nor ri.U; the readout
// names the outermost defined type.

import ri "red/inner"

type A int
type B A
type C = B
type D ri.T
type E ri.N

// R1
func definedAssert() int {
	s := 0
	if _, ok := any(B(1)).(A); ok {
		s += 1
	}
	if _, ok := any(B(1)).(int); ok {
		s += 10
	}
	if _, ok := any(B(1)).(C); ok {
		s += 100
	}
	if _, ok := any(A(1)).(B); ok {
		s += 1000
	}
	if _, ok := any(C(1)).(B); ok {
		s += 10000
	}
	if _, ok := any(D{1}).(ri.T); ok {
		s += 100000
	}
	if _, ok := any(ri.T{1}).(D); ok {
		s += 1000000
	}
	if _, ok := any(D{1}).(ri.U); ok {
		s += 10000000
	}
	if _, ok := any(E(1)).(ri.N); ok {
		s += 100000000
	}
	if _, ok := any(E(1)).(ri.M); ok {
		s += 1000000000
	}
	return s // 10100
}

// R3
func definedSwitch() int {
	r := 0
	for _, v := range []any{int(1), A(1), B(1), C(1), D{}, ri.T{}, ri.U{}, E(1), ri.M(1)} {
		d := 0
		switch v.(type) {
		case int:
			d = 1
		case A:
			d = 2
		case B:
			d = 3
		case D:
			d = 4
		case ri.T:
			d = 5
		case ri.U:
			d = 6
		case E:
			d = 7
		case ri.M:
			d = 8
		}
		r = r*10 + d
	}
	return r // 123345678
}

// R4
func definedEqual() int {
	s := 0
	if any(B(1)) == any(A(1)) {
		s += 1
	}
	if any(B(1)) == any(C(1)) {
		s += 10
	}
	if any(B(1)) == any(int(1)) {
		s += 100
	}
	if any(D{1}) == any(ri.T{1}) {
		s += 1000
	}
	if any(D{1}) == any(D{1}) {
		s += 10000
	}
	if any(E(1)) == any(ri.N(1)) {
		s += 100000
	}
	return s // 10010
}

// R5
func definedMapKeys() int {
	m := map[any]int{}
	m[A(1)] = 1
	m[B(1)] = 2
	m[C(1)] = 3
	m[int(1)] = 4
	m[D{1}] = 5
	m[ri.T{1}] = 6
	m[ri.U{1}] = 7
	m[E(1)] = 8
	m[ri.N(1)] = 9
	m[ri.M(1)] = 10
	return len(m)*10 + m[B(1)] // 93
}

// R6
func definedReadoutB() any     { return B(1) }  // B
func definedReadoutC() any     { return C(1) }  // B
func definedReadoutD() any     { return D{1} }  // D
func definedReadoutU() any     { return ri.U{1} } // U
func definedReadoutE() any     { return E(1) }  // E

// R8
func definedWrappers() int {
	s := 0
	if _, ok := any([]B{}).([]A); ok {
		s += 1
	}
	if _, ok := any([]B{}).([]C); ok {
		s += 10
	}
	if _, ok := any(new(B)).(*A); ok {
		s += 100
	}
	if _, ok := any(new(D)).(*ri.T); ok {
		s += 1000
	}
	if _, ok := any(map[B]D{}).(map[C]D); ok {
		s += 10000
	}
	return s // 10010
}

// R2
func definedPanic() int {
	var x any = B(1)
	return int(x.(A))
}

func definedPanicCross() int {
	var x any = D{1}
	return x.(ri.T).Tag
}

func definedPanicImported() int {
	var x any = ri.U{1}
	return x.(ri.T).Tag
}

func main() {}
