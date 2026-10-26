// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K7 func types: parameter and result NAMES are not identity; the variadic bit is (BUG-067),
// also in nested positions; a named func type is never the unnamed one.

type F func()

// Names of parameters and results.
func funcNames() int {
	s := 0
	var x any = func(a int) int { return a }
	if _, ok := x.(func(int) int); ok {
		s += 1
	}
	var y any = func() (n int) { return }
	if _, ok := y.(func() int); ok {
		s += 10
	}
	var z any = func(a, b int) (n, m int) { return }
	if _, ok := z.(func(int, int) (int, int)); ok {
		s += 100
	}
	if _, ok := z.(func(int, int) int); ok {
		s += 1000
	}
	return s // 111
}

// Named vs unnamed func type.
func funcNamedVsUnnamed() int {
	s := 0
	var x any = F(func() {})
	if _, ok := x.(func()); ok {
		s += 1
	}
	if _, ok := x.(F); ok {
		s += 10
	}
	var y any = func() {}
	if _, ok := y.(F); ok {
		s += 100
	}
	if _, ok := y.(func()); ok {
		s += 1000
	}
	return s // 1010
}

// The variadic bit in nested positions (R8).
func funcNestedVariadic() int {
	s := 0
	if _, ok := any([]func(...int){}).([]func([]int)); ok {
		s += 1
	}
	if _, ok := any([]func(...int){}).([]func(...int)); ok {
		s += 10
	}
	if _, ok := any(func(func(...int)) {}).(func(func([]int))); ok {
		s += 100
	}
	if _, ok := any(func(func(...int)) {}).(func(func(...int))); ok {
		s += 1000
	}
	if _, ok := any(map[string]func(...int){}).(map[string]func([]int)); ok {
		s += 10000
	}
	f := func(...int) {}
	if _, ok := any(&f).(*func([]int)); ok {
		s += 100000
	}
	if _, ok := any(&f).(*func(...int)); ok {
		s += 1000000
	}
	if _, ok := any(func() func(...int) { return nil }).(func() func([]int)); ok {
		s += 10000000
	}
	return s // 1001010
}

// R3: a type switch over func types.
func funcSwitch() int {
	r := 0
	for _, v := range []any{func(...int) int { return 0 }, func([]int) int { return 0 }, F(func() {}), func() {}} {
		d := 0
		switch v.(type) {
		case func([]int) int:
			d = 1
		case func(...int) int:
			d = 2
		case func():
			d = 3
		case F:
			d = 4
		}
		r = r*10 + d
	}
	return r // 2143
}

// R4: boxes of DIFFERENT func types compare false without a panic.
func funcEqualDistinct() int {
	s := 0
	if any(func(...int) {}) == any(func([]int) {}) {
		s += 1
	}
	if any(F(func() {})) == any(func() {}) {
		s += 10
	}
	if any(func() {}) == any(0) {
		s += 100
	}
	return s // 0
}

// R4/R2: boxes of the SAME func type panic, naming the type with its variadic spelling.
func funcEqualSamePanic() bool {
	var a any = func(...int) {}
	var b any = func(...int) {}
	return a == b
}

// R5/R2: a func key panics as unhashable, naming the type.
func funcMapKeyPanic() int {
	m := map[any]int{}
	m[func(...int) {}] = 1
	return len(m)
}

// R2: a named func type's display.
func funcNamedPanic() int {
	var x any = F(func() {})
	_ = x.(func())
	return 0
}

func main() {}
