// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K9 aliases are identity-transparent: `type A = int` is int at every runtime route; a named
// alias `type M = N` is N; a cross-package alias `type RT = ri.T` and ri.Alias are ri.T; a
// generic alias `type L[T any] = []T` is []T; an alias of an instantiation is it; a local
// alias is its target; the readout name is the TARGET's name.

import ri "red/inner"

type A = int
type N struct{ X int }
type M = N
type RT = ri.T
type L[T any] = []T
type Box[T any] struct{ v T }
type BI = Box[int]
type RG = ri.Gen[int]

// R1
func aliasAssert() int {
	s := 0
	if _, ok := any(A(1)).(int); ok {
		s += 1
	}
	if _, ok := any(int(1)).(A); ok {
		s += 10
	}
	if _, ok := any(M{1}).(N); ok {
		s += 100
	}
	if _, ok := any(RT{1}).(ri.T); ok {
		s += 1000
	}
	if _, ok := any(ri.Alias{1}).(RT); ok {
		s += 10000
	}
	if _, ok := any(L[int]{1}).([]int); ok {
		s += 100000
	}
	if _, ok := any(BI{1}).(Box[int]); ok {
		s += 1000000
	}
	if _, ok := any(RG{}).(ri.Gen[int]); ok {
		s += 10000000
	}
	if _, ok := any(ri.GenAlias[int]{}).(ri.Gen[int]); ok {
		s += 100000000
	}
	return s // 111111111
}

// A local alias.
func aliasLocal() int {
	type LA = int
	type LN = N
	s := 0
	if _, ok := any(LA(1)).(int); ok {
		s += 1
	}
	if _, ok := any(LN{1}).(N); ok {
		s += 10
	}
	if _, ok := any(N{1}).(LN); ok {
		s += 100
	}
	return s // 111
}

// R3
func aliasSwitch() int {
	r := 0
	for _, v := range []any{int(1), N{}, ri.T{}, Box[int]{}} {
		d := 0
		switch v.(type) {
		case A:
			d = 1
		case M:
			d = 2
		case RT:
			d = 3
		case BI:
			d = 4
		}
		r = r*10 + d
	}
	return r // 1234
}

// R4
func aliasEqual() int {
	s := 0
	if any(A(1)) == any(int(1)) {
		s += 1
	}
	if any(M{1}) == any(N{1}) {
		s += 10
	}
	if any(RT{1}) == any(ri.T{1}) {
		s += 100
	}
	if any(BI{1}) == any(Box[int]{1}) {
		s += 1000
	}
	if any(A(1)) == any(int64(1)) {
		s += 10000
	}
	return s // 1111
}

// R5
func aliasMapKeys() int {
	m := map[any]int{}
	m[A(1)] = 1
	m[int(1)] = 2
	m[M{1}] = 3
	m[N{1}] = 4
	m[RT{1}] = 5
	m[ri.T{1}] = 6
	m[BI{1}] = 7
	m[Box[int]{1}] = 8
	return len(m)*10 + m[A(1)] // 42
}

// R6: the readout names the TARGET.
func aliasReadoutNamed() any { return M{1} }   // N
func aliasReadoutCross() any { return RT{1} }  // T
func aliasReadoutInst() any  { return BI{1} }  // Box[int]
func aliasReadoutBasic() any { return A(1) }   // int (the harness's kind)

// R8
func aliasWrappers() int {
	s := 0
	if _, ok := any([]A{}).([]int); ok {
		s += 1
	}
	if _, ok := any(map[A]M{}).(map[int]N); ok {
		s += 10
	}
	if _, ok := any(func(A) A { return 0 }).(func(int) int); ok {
		s += 100
	}
	if _, ok := any(new(RT)).(*ri.T); ok {
		s += 1000
	}
	if _, ok := any([]A{}).([]int64); ok {
		s += 10000
	}
	return s // 1111
}

// R2
func aliasPanic() int {
	var x any = A(1)
	return int(x.(int64))
}

func aliasPanicNamed() int {
	var x any = M{1}
	_ = x.(Box[int])
	return 0
}

func main() {}
