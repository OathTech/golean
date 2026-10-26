// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K6 anonymous interfaces are STRUCTURAL: method order and embedding spelling do not matter,
// parameter names do not matter, exported methods across packages are one type, UNEXPORTED
// methods across packages are two types, a named interface is never identical to the literal,
// `any` ≡ `interface{}`, `error` ≢ `interface{ Error() string }`. An interface type is never a
// dynamic type, so the runtime route is a func / slice / pointer type OVER it (R8), plus the
// satisfaction route (R7) and the display of such a type in a panic text (R2/R4).

import ri "red/inner"

type J interface{ M() }
type X interface{ A() }
type T struct{}

func (T) get() int { return 2 }
func (T) M()       {}

// Method order in the literal.
func anonOrder() int {
	s := 0
	var x any = func(interface{ A(); B() }) {}
	if _, ok := x.(func(interface{ B(); A() })); ok {
		s += 1
	}
	if _, ok := x.(func(interface{ A(); B() })); ok {
		s += 10
	}
	if _, ok := x.(func(interface{ A() })); ok {
		s += 100
	}
	return s // 11
}

// Embedded-interface flattening.
func anonFlatten() int {
	s := 0
	var x any = func(interface{ X; B() }) {}
	if _, ok := x.(func(interface{ A(); B() })); ok {
		s += 1
	}
	if _, ok := x.(func(interface{ X })); ok {
		s += 10
	}
	var y any = func(interface{ X }) {}
	if _, ok := y.(func(interface{ A() })); ok {
		s += 100
	}
	if _, ok := y.(func(X)); ok {
		s += 1000
	}
	return s // 101
}

// Parameter names inside the method signatures.
func anonParamNames() int {
	s := 0
	var x any = func(interface{ A(x int) (n int) }) {}
	if _, ok := x.(func(interface{ A(int) int })); ok {
		s += 1
	}
	if _, ok := x.(func(interface{ A(int) })); ok {
		s += 10
	}
	return s // 1
}

// Exported methods across packages: one type.
func anonExportedCrossPkg() int {
	s := 0
	var x any = ri.FnM()
	if _, ok := x.(func(interface{ M() })); ok {
		s += 1
	}
	if _, ok := x.(func(J)); ok {
		s += 10
	}
	if _, ok := ri.SliceM().([]interface{ M() }); ok {
		s += 100
	}
	return s // 101
}

// Unexported methods across packages: two types.
func anonUnexportedCrossPkg() int {
	s := 0
	var x any = ri.FnGet()
	if _, ok := x.(func(interface{ get() int })); ok {
		s += 1
	}
	var y any = func(interface{ get() int }) {}
	if _, ok := y.(func(interface{ get() int })); ok {
		s += 10
	}
	if _, ok := ri.SliceGet().([]interface{ get() int }); ok {
		s += 100
	}
	return s // 10
}

// R7: satisfaction of each package's `interface{ get() int }` by each package's T.
func anonUnexportedSatisfaction() int {
	s := 0
	if ri.IsGet(ri.T{}) {
		s += 1
	}
	if ri.IsGet(T{}) {
		s += 10
	}
	if _, ok := any(ri.T{}).(interface{ get() int }); ok {
		s += 100
	}
	if _, ok := any(T{}).(interface{ get() int }); ok {
		s += 1000
	}
	return s // 1001
}

// A named interface is never identical to the literal with the same set.
func anonVsNamed() int {
	s := 0
	var x any = func(J) {}
	if _, ok := x.(func(interface{ M() })); ok {
		s += 1
	}
	var y any = func(interface{ M() }) {}
	if _, ok := y.(func(J)); ok {
		s += 10
	}
	if _, ok := x.(func(J)); ok {
		s += 100
	}
	if _, ok := any([]J{}).([]interface{ M() }); ok {
		s += 1000
	}
	if _, ok := any(map[string]J{}).(map[string]interface{ M() }); ok {
		s += 10000
	}
	return s // 100
}

// `any` ≡ `interface{}`; `error` ≢ its literal.
func anonAnyAndError() int {
	s := 0
	var x any = func(any) {}
	if _, ok := x.(func(interface{})); ok {
		s += 1
	}
	if _, ok := any([]any{}).([]interface{}); ok {
		s += 10
	}
	var e any = func(error) {}
	if _, ok := e.(func(interface{ Error() string })); ok {
		s += 100
	}
	if _, ok := e.(func(error)); ok {
		s += 1000
	}
	if _, ok := any([]error{}).([]interface{ Error() string }); ok {
		s += 10000
	}
	return s // 1011
}

// A pointer to an anonymous interface type.
func anonPointer() int {
	s := 0
	p := new(interface{ M() })
	if _, ok := any(p).(*interface{ M() }); ok {
		s += 1
	}
	if _, ok := any(p).(*J); ok {
		s += 10
	}
	return s // 1
}

func mkFA() (any, func(any) bool) {
	type L int
	return func(interface{ Get() L }) {}, func(x any) bool { _, ok := x.(func(interface{ Get() L })); return ok }
}

func mkFB() (any, func(any) bool) {
	type L int
	return func(interface{ Get() L }) {}, func(x any) bool { _, ok := x.(func(interface{ Get() L })); return ok }
}

// A local type inside the literal, through the func-type route.
func anonLocalInside() int {
	fa, isA := mkFA()
	fb, isB := mkFB()
	s := 0
	if isA(fa) {
		s += 1
	}
	if isA(fb) {
		s += 10
	}
	if isB(fb) {
		s += 100
	}
	return s // 101
}

// R2/R4: the display of an anonymous interface inside a func type (the uncomparable panic).
func anonUncomparablePanic() bool {
	var x any = func(interface{ M() }) {}
	return x == x
}

// R2: the display in an assertion panic text.
func anonAssertPanic() int {
	var x any = func(interface{ M() }) {}
	_ = x.(func(J))
	return 0
}

func main() {}
