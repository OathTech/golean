// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K5 anonymous structs: the canonical `struct{}` is its own (unnamed) type, distinct from a
// named empty struct `E`; two `struct{}` spellings are one type.

type E struct{}
type F struct{}

// R1
func emptyStructAssert() int {
	s := 0
	if _, ok := any(struct{}{}).(E); ok {
		s += 1
	}
	if _, ok := any(E{}).(struct{}); ok {
		s += 10
	}
	if _, ok := any(struct{}{}).(struct{}); ok {
		s += 100
	}
	if _, ok := any(E{}).(F); ok {
		s += 1000
	}
	if _, ok := any(E{}).(E); ok {
		s += 10000
	}
	return s // 10100
}

// R3
func emptyStructSwitch() int {
	r := 0
	for _, v := range []any{struct{}{}, E{}, F{}} {
		d := 0
		switch v.(type) {
		case E:
			d = 1
		case struct{}:
			d = 2
		case F:
			d = 3
		}
		r = r*10 + d
	}
	return r // 213
}

// R4
func emptyStructEqual() int {
	s := 0
	if any(struct{}{}) == any(struct{}{}) {
		s += 1
	}
	if any(struct{}{}) == any(E{}) {
		s += 10
	}
	if any(E{}) == any(F{}) {
		s += 100
	}
	if any(E{}) == any(E{}) {
		s += 1000
	}
	return s // 1001
}

// R5
func emptyStructMapKeys() int {
	m := map[any]int{}
	m[struct{}{}] = 1
	m[E{}] = 2
	m[struct{}{}] = 3
	m[F{}] = 4
	return len(m)*10 + m[struct{}{}] // 33
}

// R8
func emptyStructWrappers() int {
	s := 0
	if _, ok := any([]struct{}{}).([]E); ok {
		s += 1
	}
	if _, ok := any([]struct{}{}).([]struct{}); ok {
		s += 10
	}
	if _, ok := any(map[string]struct{}{}).(map[string]E); ok {
		s += 100
	}
	if _, ok := any(map[string]struct{}{}).(map[string]struct{}); ok {
		s += 1000
	}
	return s // 1010
}

// R2
func emptyStructPanic() int {
	var x any = struct{}{}
	_ = x.(E)
	return 0
}

func main() {}
