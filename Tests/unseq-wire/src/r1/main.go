package main

// R1: v := x + y + mut(), both captured. Unreduced {0, 1, 2, 3}; the refuted
// read-order reduction (read y after read x) loses 1.
func r1() int {
	x, y := 0, 0
	mut := func() int { x = 1; y = 2; return 0 }
	v := x + y + mut()
	return v
}

func main() { println(r1()) }
