// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K12 array lengths and element types are type identity: [2]int ≢ [3]int ≢ [2]int64; [0]int is
// its own; nested arrays by each dimension; a named element type counts.

type T struct{}

// R1
func arrayAssert() int {
	s := 0
	if _, ok := any([2]int{}).([3]int); ok {
		s += 1
	}
	if _, ok := any([2]int{}).([2]int64); ok {
		s += 10
	}
	if _, ok := any([2]int{}).([2]int); ok {
		s += 100
	}
	if _, ok := any([0]int{}).([0]int); ok {
		s += 1000
	}
	if _, ok := any([0]int{}).([1]int); ok {
		s += 10000
	}
	if _, ok := any([2][2]int{}).([2][3]int); ok {
		s += 100000
	}
	if _, ok := any([2][2]int{}).([2][2]int); ok {
		s += 1000000
	}
	if _, ok := any([2]T{}).([2]struct{}); ok {
		s += 10000000
	}
	if _, ok := any([2]byte{}).([2]uint8); ok {
		s += 100000000
	}
	return s // 101001100
}

// R3
func arraySwitch() int {
	r := 0
	for _, v := range []any{[2]int{}, [3]int{}, [0]int{}, [2]int64{}, [2][2]int{}} {
		d := 0
		switch v.(type) {
		case [3]int:
			d = 1
		case [2]int:
			d = 2
		case [0]int:
			d = 3
		case [2]int64:
			d = 4
		case [2][2]int:
			d = 5
		}
		r = r*10 + d
	}
	return r // 21345
}

// R4
func arrayEqual() int {
	s := 0
	if any([2]int{1, 2}) == any([2]int{1, 2}) {
		s += 1
	}
	if any([2]int{}) == any([3]int{}) {
		s += 10
	}
	if any([0]int{}) == any([0]int{}) {
		s += 100
	}
	if any([2]int{}) == any([2]int64{}) {
		s += 1000
	}
	if any([2]byte{1}) == any([2]uint8{1}) {
		s += 10000
	}
	return s // 10101
}

// R5
func arrayMapKeys() int {
	m := map[any]int{}
	m[[2]int{}] = 1
	m[[3]int{}] = 2
	m[[2]int{}] = 3
	m[[0]int{}] = 4
	m[[2]int64{}] = 5
	m[[2]byte{}] = 6
	m[[2]uint8{}] = 7
	return len(m)*10 + m[[2]int{}] // 53
}

// R8
func arrayWrappers() int {
	s := 0
	if _, ok := any([][2]int{}).([][3]int); ok {
		s += 1
	}
	if _, ok := any([][2]int{}).([][2]int); ok {
		s += 10
	}
	if _, ok := any(&[2]int{}).(*[3]int); ok {
		s += 100
	}
	if _, ok := any(&[2]int{}).(*[2]int); ok {
		s += 1000
	}
	if _, ok := any(map[[2]int]int{}).(map[[3]int]int); ok {
		s += 10000
	}
	return s // 1010
}

// R2
func arrayPanic() int {
	var x any = [2]int{}
	_ = x.([3]int)
	return 0
}

func arrayPanicNested() int {
	var x any = [2][2]byte{}
	_ = x.([2][3]uint8)
	return 0
}

func main() {}
