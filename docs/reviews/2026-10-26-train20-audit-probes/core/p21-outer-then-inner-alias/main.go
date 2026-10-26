package main

// The outer converted, then a pointer to the inner field taken through the
// alias and stored through whole; the original observes the inner.
type In struct{ V int }
type OA struct {
	I In
	N int
}
type OB struct {
	I In
	N int
}

func probe() int {
	o := OA{In{1}, 2}
	pob := (*OB)(&o)
	pin := &pob.I
	*pin = In{9}
	x := *pob
	if x == (OB{In{9}, 2}) && o.I.V == 9 && &o.I == pin {
		return 1
	}
	return 0
}

func main() { println(probe()) }
