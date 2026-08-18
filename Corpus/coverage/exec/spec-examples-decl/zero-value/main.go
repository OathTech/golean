package main

// spec#The_zero_value blocks The_zero_value-1-3e4f442c (var i int and
// var i int = 0 are equivalent), -2-91c9d45b (t := new(T) zeroes every
// field: t.i == 0, t.f == 0.0, t.next == nil), and -4-ac95c519 (var t T is
// the same). The zeroing is recursive per the section's prose.

type T struct {
	i    int
	f    float64
	next *T
}

func zeroValue() int {
	var i1 int
	var i2 int = 0
	t := new(T)
	var tv T
	n := 0
	if i1 == i2 && i1 == 0 {
		n++
	}
	if t.i == 0 && t.f == 0.0 && t.next == nil {
		n++
	}
	if tv.i == 0 && tv.f == 0.0 && tv.next == nil {
		n++
	}
	return n // 3
}
