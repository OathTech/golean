// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K14 structural wrappers over named / local / interface element types: *T ≢ *U, **T ≢ *T,
// []T ≢ []U, map[string]T ≢ map[string]U, map[T]int ≢ map[U]int; typed nil pointers of two
// types are two boxes; *L for two functions' local L; map[string]I at a named vs anonymous
// interface.

type T struct{}
type U struct{}
type I interface{ M() }

// R1
func wrapAssert() int {
	s := 0
	if _, ok := any(new(*T)).(*T); ok {
		s += 1
	}
	if _, ok := any(new(*T)).(**T); ok {
		s += 10
	}
	if _, ok := any([]T{}).([]U); ok {
		s += 100
	}
	if _, ok := any(map[string]T{}).(map[string]U); ok {
		s += 1000
	}
	if _, ok := any(map[T]int{}).(map[U]int); ok {
		s += 10000
	}
	if _, ok := any(map[T]int{}).(map[T]int); ok {
		s += 100000
	}
	if _, ok := any(map[string]I{}).(map[string]interface{ M() }); ok {
		s += 1000000
	}
	if _, ok := any(map[string]I{}).(map[string]I); ok {
		s += 10000000
	}
	if _, ok := any([]*T{}).([]*U); ok {
		s += 100000000
	}
	return s // 10100010
}

// R3 over typed nil pointers.
func wrapSwitch() int {
	var pt *T
	var pu *U
	var ppt **T
	r := 0
	for _, v := range []any{pt, pu, ppt, []T{}, map[T]int{}} {
		d := 0
		switch v.(type) {
		case *U:
			d = 1
		case *T:
			d = 2
		case **T:
			d = 3
		case []T:
			d = 4
		case map[T]int:
			d = 5
		}
		r = r*10 + d
	}
	return r // 21345
}

// R4 typed nil pointers of two types are two boxes.
func wrapEqual() int {
	var pt *T
	var pu *U
	s := 0
	if any(pt) == any(pu) {
		s += 1
	}
	if any(pt) == any((*T)(nil)) {
		s += 10
	}
	if any(pt) == nil {
		s += 100
	}
	var ppt **T
	if any(ppt) == any(pt) {
		s += 1000
	}
	return s // 10
}

// R5
func wrapMapKeys() int {
	var pt *T
	var pu *U
	m := map[any]int{}
	m[pt] = 1
	m[pu] = 2
	m[(*T)(nil)] = 3
	m[(**T)(nil)] = 4
	return len(m)*10 + m[pt] // 33
}

func mkPA() (any, func(any) bool) {
	type L int
	return new(L), func(x any) bool { _, ok := x.(*L); return ok }
}

func mkPB() (any, func(any) bool) {
	type L int
	return new(L), func(x any) bool { _, ok := x.(*L); return ok }
}

func mkMA() (any, func(any) bool) {
	type L int
	return map[L]int{}, func(x any) bool { _, ok := x.(map[L]int); return ok }
}

func mkMB() (any, func(any) bool) {
	type L int
	return map[L]int{}, func(x any) bool { _, ok := x.(map[L]int); return ok }
}

// Pointers and maps over two functions' local L.
func wrapLocal() int {
	pa, isPA := mkPA()
	pb, isPB := mkPB()
	ma, isMA := mkMA()
	mb, isMB := mkMB()
	s := 0
	if isPA(pa) {
		s += 1
	}
	if isPA(pb) {
		s += 10
	}
	if isPB(pb) {
		s += 100
	}
	if isMA(ma) {
		s += 1000
	}
	if isMA(mb) {
		s += 10000
	}
	if isMB(mb) {
		s += 100000
	}
	return s // 101101
}

// R2
func wrapPanic() int {
	var pt *T
	var x any = pt
	_ = x.(*U)
	return 0
}

func wrapPanicMap() int {
	var x any = map[string]I{}
	_ = x.(map[string]interface{ M() })
	return 0
}

func main() {}
