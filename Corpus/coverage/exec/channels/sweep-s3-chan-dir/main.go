// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K11 channel directions are type identity: chan int ≢ <-chan int ≢ chan<- int; a named chan
// type is its own; the element type counts; nested directions count.

type C chan int
type E struct{}

// R1
func chanDirAssert() int {
	c := make(chan int)
	s := 0
	if _, ok := any(c).(<-chan int); ok {
		s += 1
	}
	if _, ok := any((<-chan int)(c)).(chan int); ok {
		s += 10
	}
	if _, ok := any((<-chan int)(c)).(<-chan int); ok {
		s += 100
	}
	if _, ok := any((chan<- int)(c)).(<-chan int); ok {
		s += 1000
	}
	if _, ok := any((chan<- int)(c)).(chan<- int); ok {
		s += 10000
	}
	if _, ok := any(c).(chan int); ok {
		s += 100000
	}
	if _, ok := any(C(c)).(chan int); ok {
		s += 1000000
	}
	if _, ok := any(c).(C); ok {
		s += 10000000
	}
	if _, ok := any(C(c)).(C); ok {
		s += 100000000
	}
	if _, ok := any(make(chan E)).(chan struct{}); ok {
		s += 1000000000
	}
	return s // 100100100
}

// Nested directions and element types.
func chanNested() int {
	cc := make(chan (<-chan int))
	s := 0
	if _, ok := any(cc).(chan (chan int)); ok {
		s += 1
	}
	if _, ok := any(cc).(chan (<-chan int)); ok {
		s += 10
	}
	if _, ok := any(cc).(<-chan (<-chan int)); ok {
		s += 100
	}
	if _, ok := any((<-chan (<-chan int))(cc)).(<-chan (<-chan int)); ok {
		s += 1000
	}
	if _, ok := any(make(chan int64)).(chan int); ok {
		s += 10000
	}
	return s // 1010
}

// R3
func chanSwitch() int {
	c := make(chan int)
	r := 0
	for _, v := range []any{c, (<-chan int)(c), (chan<- int)(c), C(c), make(chan int64)} {
		d := 0
		switch v.(type) {
		case chan int:
			d = 1
		case <-chan int:
			d = 2
		case chan<- int:
			d = 3
		case C:
			d = 4
		case chan int64:
			d = 5
		}
		r = r*10 + d
	}
	return r // 12345
}

// R4: a directional view of ONE channel boxed is another type → false; the same type and
// channel → true.
func chanEqual() int {
	c := make(chan int)
	s := 0
	if any(c) == any((<-chan int)(c)) {
		s += 1
	}
	if any(c) == any(c) {
		s += 10
	}
	if any((<-chan int)(c)) == any((<-chan int)(c)) {
		s += 100
	}
	if any(C(c)) == any(c) {
		s += 1000
	}
	if any((<-chan int)(c)) == any((chan<- int)(c)) {
		s += 10000
	}
	return s // 110
}

// R5
func chanMapKeys() int {
	c := make(chan int)
	m := map[any]int{}
	m[c] = 1
	m[(<-chan int)(c)] = 2
	m[(chan<- int)(c)] = 3
	m[C(c)] = 4
	m[c] = 5
	return len(m)*10 + m[c] // 45
}

// R8
func chanWrappers() int {
	s := 0
	if _, ok := any([]chan int{}).([]<-chan int); ok {
		s += 1
	}
	if _, ok := any([]chan int{}).([]chan int); ok {
		s += 10
	}
	if _, ok := any(map[string]<-chan int{}).(map[string]chan int); ok {
		s += 100
	}
	if _, ok := any(func(chan<- int) {}).(func(chan int)); ok {
		s += 1000
	}
	if _, ok := any(func(chan<- int) {}).(func(chan<- int)); ok {
		s += 10000
	}
	return s // 10010
}

// R2
func chanPanicDir() int {
	c := make(chan int)
	var x any = c
	_ = x.(<-chan int)
	return 0
}

func chanPanicSendOnly() int {
	c := make(chan int)
	var x any = (chan<- int)(c)
	_ = x.(C)
	return 0
}

func main() {}
