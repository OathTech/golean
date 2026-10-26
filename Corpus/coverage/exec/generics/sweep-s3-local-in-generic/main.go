// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K4 a type declared inside a generic function: one type per instantiation (gc names it
// box[int]); the same instantiation is one type; a second generic function's same-named local
// is another type; a local not mentioning T is still per-instantiation; a local in a generic
// TYPE's method and in a nested closure follow the same rule.
//
// Shape note: the assertion against the local type must sit lexically inside the declaring
// generic function, and a closure WITH a parameter inside a stencil is refused whole-wire by
// the decoder (B6 c4, recorded in BUG-124's entry) — so each generic takes a `probe any`
// parameter and answers the assertion itself; the first call mints the value, the second
// judges it.

func wrap2[T any](x T, probe any) (any, bool) {
	type box struct{ v T }
	_, ok := probe.(box)
	return box{x}, ok
}

// R1 at two instantiations, and the same instantiation twice.
func lgAssert() int {
	vi, _ := wrap2[int](1, nil)
	vs, _ := wrap2[string]("a", nil)
	vi2, _ := wrap2[int](2, nil)
	s := 0
	if _, ok := wrap2[int](0, vi); ok {
		s += 1
	}
	if _, ok := wrap2[int](0, vs); ok {
		s += 10
	}
	if _, ok := wrap2[string]("", vs); ok {
		s += 100
	}
	if _, ok := wrap2[string]("", vi); ok {
		s += 1000
	}
	if _, ok := wrap2[int](0, vi2); ok {
		s += 10000
	}
	return s // 10101
}

func is[T any](x any) bool {
	type box struct{ v T }
	_, ok := x.(box)
	return ok
}

// Two generic functions declaring the same local name: distinct types.
func lgTwoGenerics() int {
	vi, _ := wrap2[int](1, nil)
	s := 0
	if is[int](vi) {
		s += 1
	}
	if is[string](vi) {
		s += 10
	}
	return s // 0
}

func sw[T any](x T, probe any) (any, int) {
	type box struct{ v T }
	r := 0
	switch probe.(type) {
	case box:
		r = 1
	case T:
		r = 2
	}
	return box{x}, r
}

// R3 at two instantiations.
func lgSwitch() int {
	vi, _ := sw[int](1, nil)
	vs, _ := sw[string]("a", nil)
	_, a := sw[int](0, vi)
	_, b := sw[int](0, vs)
	_, c := sw[string]("", vs)
	_, d := sw[string]("", any(1))
	_, e := sw[int](0, any(7))
	return a*10000 + b*1000 + c*100 + d*10 + e // 10102
}

// R4 == of boxes.
func lgEqual() int {
	vi, _ := wrap2[int](1, nil)
	vi2, _ := wrap2[int](1, nil)
	vs, _ := wrap2[string]("a", nil)
	vi3, _ := wrap2[int](3, nil)
	s := 0
	if vi == vi2 {
		s += 1
	}
	if vi == vs {
		s += 10
	}
	if vi == vi3 {
		s += 100
	}
	return s // 1
}

// R5 map keys.
func lgMapKeys() int {
	vi, _ := wrap2[int](1, nil)
	vi2, _ := wrap2[int](1, nil)
	vs, _ := wrap2[string]("a", nil)
	m := map[any]int{}
	m[vi] = 1
	m[vi2] = 2
	m[vs] = 3
	return len(m)*10 + m[vi] // 22
}

func wrap[T any](x T) any {
	type box struct{ v T }
	return box{x}
}

// R6 the readout name at a second instantiation.
func lgReadoutString() any { return wrap[string]("s") } // Name() box[string]

func wrapNoT[T any](x T) any {
	type tag struct{ n int }
	return tag{1}
}

// A local that does not mention T is still per-instantiation.
func lgNoT() int {
	s := 0
	if wrapNoT[int](1) == wrapNoT[string]("") {
		s += 1
	}
	if wrapNoT[int](1) == wrapNoT[int](2) {
		s += 10
	}
	return s // 10
}

func lgReadoutNoT() any { return wrapNoT[int](1) } // Name() tag[int]

type G[T any] struct{ z T }

func (G[T]) mk() any {
	type inner struct{ n int }
	return inner{1}
}

// A local in a generic TYPE's method.
func lgMethodLocal() int {
	s := 0
	if (G[int]{}).mk() == (G[string]{}).mk() {
		s += 1
	}
	if (G[int]{}).mk() == (G[int]{}).mk() {
		s += 10
	}
	return s // 10
}

func lgReadoutMethodLocal() any { return (G[int]{}).mk() } // Name() inner[int]

func wrapC[T any](x T) any {
	f := func() any {
		type cb struct{ v T }
		return cb{x}
	}
	return f()
}

// A local in a nested (parameterless) closure of a generic function.
func lgClosureLocal() int {
	s := 0
	if wrapC[int](1) == wrapC[int](1) {
		s += 1
	}
	if wrapC[int](1) == wrapC[string]("") {
		s += 10
	}
	return s // 1
}

func lgReadoutClosureLocal() any { return wrapC[int](1) } // Name() cb[int]

func wrapS[T any](x T, probe any) (any, bool) {
	type box struct{ v T }
	_, ok := probe.([]box)
	return []box{{x}}, ok
}

// R8 a slice of the local at two instantiations.
func lgWrappers() int {
	si, _ := wrapS[int](1, nil)
	ss, _ := wrapS[string]("a", nil)
	s := 0
	if _, ok := wrapS[int](0, si); ok {
		s += 1
	}
	if _, ok := wrapS[int](0, ss); ok {
		s += 10
	}
	if _, ok := wrapS[string]("", ss); ok {
		s += 100
	}
	return s // 101
}

func wrapP[T any](x T, probe any) (any, T) {
	type box struct{ v T }
	if probe == nil {
		return box{x}, x
	}
	return box{x}, probe.(box).v
}

// R2 the panic text at a cross-instantiation assertion of the SAME local (gc names both
// instantiations: main.box[string], not main.box[int]).
func lgAssertPanic() int {
	vs, _ := wrapP[string]("a", nil)
	_, got := wrapP[int](0, vs)
	return got
}

func main() {}
