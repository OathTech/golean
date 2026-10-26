// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K3 function-local types. A local type is identical only to itself: two functions' `type L`
// are two types; one function's L is one type across invocations; two blocks' L are two
// types; a closure's local is its own; a package-level func literal's local is its own; an
// init-time local is its own.

func mkA() (any, func(any) bool) {
	type L int
	return L(1), func(x any) bool { _, ok := x.(L); return ok }
}

func mkB() (any, func(any) bool) {
	type L int
	return L(1), func(x any) bool { _, ok := x.(L); return ok }
}

// R1: cross-assert between two functions' L.
func localAssertCross() int {
	va, isA := mkA()
	vb, isB := mkB()
	s := 0
	if isA(va) {
		s += 1
	}
	if isA(vb) {
		s += 10
	}
	if isB(vb) {
		s += 100
	}
	if isB(va) {
		s += 1000
	}
	return s // 101
}

func mkSwA() (any, func(any) int) {
	type L int
	return L(1), func(x any) int {
		switch x.(type) {
		case L:
			return 1
		case int:
			return 2
		}
		return 0
	}
}

func mkSwB() (any, func(any) int) {
	type L int
	return L(1), func(x any) int {
		switch x.(type) {
		case int:
			return 2
		case L:
			return 1
		}
		return 0
	}
}

// R3: a type switch with a local case type.
func localSwitch() int {
	va, swA := mkSwA()
	vb, swB := mkSwB()
	return swA(va)*1000 + swA(vb)*100 + swB(vb)*10 + swB(va) // 1010
}

// R5: map keys — the same function's L twice is one key.
func localMapKeys() int {
	va, _ := mkA()
	vb, _ := mkB()
	va2, _ := mkA()
	m := map[any]int{}
	m[va] = 1
	m[vb] = 2
	m[va2] = 3
	return len(m)*10 + m[va] // 23
}

// R4: one local type across two invocations.
func localSameAcrossCalls() bool {
	va, _ := mkA()
	va2, _ := mkA()
	return va == va2 // true
}

// Two blocks of one function.
func localTwoBlocks() int {
	var a, b any
	var isA, isB func(any) bool
	{
		type L int
		a = L(1)
		isA = func(x any) bool { _, ok := x.(L); return ok }
	}
	{
		type L int
		b = L(1)
		isB = func(x any) bool { _, ok := x.(L); return ok }
	}
	s := 0
	if a == b {
		s += 1
	}
	if isA(b) {
		s += 10
	}
	if isB(b) {
		s += 100
	}
	if isA(a) {
		s += 1000
	}
	return s // 1100
}

// A closure's local type against its enclosing function's.
func localInClosure() int {
	type L int
	f := func() any {
		type L int
		return L(1)
	}
	s := 0
	if any(L(1)) == f() {
		s += 1
	}
	if _, ok := f().(L); ok {
		s += 10
	}
	if f() == f() {
		s += 100
	}
	return s // 100
}

var mkP = func() any { type P int; return P(1) }
var mkQ = func() any { type P int; return P(1) }

// Package-level func literals' locals.
func localInPkgFuncLit() int {
	s := 0
	if mkP() == mkQ() {
		s += 1
	}
	if mkP() == mkP() {
		s += 10
	}
	return s // 10
}

var initVal any

func init() {
	type L int
	initVal = L(1)
}

type L int

// A local declared in init vs the package-level L and a function's L.
func localInInit() int {
	s := 0
	if _, ok := initVal.(L); ok {
		s += 1
	}
	if initVal == any(L(1)) {
		s += 10
	}
	va, isA := mkA()
	if isA(initVal) {
		s += 100
	}
	if initVal == va {
		s += 1000
	}
	return s // 0
}

// R6: the readout name of a local type (reflect Name() = "Loc").
func localReadoutA() any {
	type Loc struct{ V int }
	return Loc{1}
}

func localReadoutB() any {
	type Loc struct{ V int }
	return Loc{2}
}

func mkSliceA() (any, func(any) bool) {
	type L int
	return []L{1}, func(x any) bool { _, ok := x.([]L); return ok }
}

func mkSliceB() (any, func(any) bool) {
	type L int
	return []L{1}, func(x any) bool { _, ok := x.([]L); return ok }
}

func mkPtrA() (any, func(any) bool) {
	type L int
	return new(L), func(x any) bool { _, ok := x.(*L); return ok }
}

func mkPtrB() (any, func(any) bool) {
	type L int
	return new(L), func(x any) bool { _, ok := x.(*L); return ok }
}

// R8: the local identity inside slices and pointers.
func localWrappers() int {
	sa, isSA := mkSliceA()
	sb, isSB := mkSliceB()
	pa, isPA := mkPtrA()
	pb, isPB := mkPtrB()
	s := 0
	if isSA(sa) {
		s += 1
	}
	if isSA(sb) {
		s += 10
	}
	if isSB(sb) {
		s += 100
	}
	if isPA(pa) {
		s += 1000
	}
	if isPA(pb) {
		s += 10000
	}
	if isPB(pb) {
		s += 100000
	}
	return s // 101101
}

// A local type with the same name as the package-level L, cross-asserted (R1) — the
// shadow-panic row covers R2; this is the comma-ok side plus the package-level direction.
func localShadowAssert() int {
	type L int
	s := 0
	var x any = L(1)
	var y any = any(0)
	_ = y
	if _, ok := x.(L); ok {
		s += 1
	}
	var p any = pkgL()
	if _, ok := p.(L); ok {
		s += 10
	}
	if x == p {
		s += 100
	}
	return s // 1
}

func pkgL() any { return L(1) }

func main() {}
