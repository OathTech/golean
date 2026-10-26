package main

// The whole-struct deref as an operand of an UNSEQUENCED sweep (a call beside
// it), as a frozen-target store with a call on the right, and as the field read
// of a deref in a sweep: the unseq lane's own load/store route.
type A struct{ X, Y int }
type B struct{ X, Y int }

var g int

func bump() int { g++; return g }

func take(b B, n int) int { return b.X*10 + n }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	r := take(*pb, bump())   // 10 + 1
	s := bump() + (*pb).Y    // 2 + 2
	*pb = B{bump(), (*pb).Y} // a = {3, 2}
	return r*1000 + s*100 + a.X*10 + a.Y
}

func main() { println(probe()) }
