package main

type T struct{ v int }

func (t T) M() int      { return t.v }
func (t *T) P() int     { return t.v }

// (e): a deferred method call whose receiver is an out-of-range slice element.
// Go evaluates the receiver AT DEFER TIME: s[5] panics before the defer is registered.
func deferOutOfRangeValueRecv() (r int) {
	defer func() {
		if e := recover(); e != nil {
			r = 1
		}
	}()
	s := make([]T, 2)
	i := 5
	defer s[i].M()
	return 0
}

// pointer receiver: &s[i] evaluated at defer time → panics at defer time too
func deferOutOfRangePtrRecv() (r int) {
	defer func() {
		if e := recover(); e != nil {
			r = 2
		}
	}()
	s := make([]T, 2)
	i := 5
	defer s[i].P()
	return 0
}

// the receiver is IN range at defer time; then the slice is re-sliced shorter and a panic unwinds:
// the deferred call runs during unwinding with an ADDRESS formed while in range.
func deferThenShrinkThenPanic() (r int) {
	defer func() {
		if e := recover(); e != nil {
			r += 100
		}
	}()
	s := make([]T, 3)
	s[2].v = 7
	defer func() { r += s[2].M() }() // closure keeps s; still fine
	defer s[2].P()                    // pointer to element 2 formed now
	s = s[:1]
	var z []int
	_ = z[3] // panic: index out of range
	return 0
}

// deferred method on an element pointer whose backing is later replaced via append (address stays valid)
func deferPtrRecvAfterAppend() (r int) {
	defer func() {
		if e := recover(); e != nil {
			r += 100
		}
	}()
	s := make([]T, 1, 1)
	s[0].v = 3
	defer func(p *T) { r += p.P() }(&s[0])
	s = append(s, T{9})
	s[0].v = 4
	panic("x")
}

func main() {
	println(deferOutOfRangeValueRecv(), deferOutOfRangePtrRecv(), deferThenShrinkThenPanic(), deferPtrRecvAfterAppend())
}
