package main

// spec#Allocation block Allocation-1-26a175c5: new(S) allocates storage for a
// variable of type S, initializes it (a is 0, b is 0.0), and returns a value
// of type *S pointing at it.

type S struct {
	a int
	b float64
}

func allocationNew() int {
	p := new(S)
	if p == nil {
		return -1
	}
	if p.a != 0 || p.b != 0.0 {
		return -2
	}
	return 1
}
