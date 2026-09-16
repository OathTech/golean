package main

// R2 witness (nested guards, an earlier call, an event consuming the joined
// result): g precedes the || operation, whose region holds a && guard; k follows
// the || completion; a's read is unordered against g (spec#Order_of_evaluation:
// the evaluation of z «is not specified» relative to the calls). Two sweeps:
// b true → {g k / sink 1 true 7, g h k / sink 1 true 7}; b false → {g k / sink 1
// true 7, g k / sink 1 false 7}. h before g is forbidden.
func run(b bool) {
	a := false
	g := func() int { println("g"); a = true; return 1 }
	h := func() bool { println("h"); return true }
	k := func() int { println("k"); return 7 }
	sink := func(x int, v bool, n int) { println("sink", x, v, n) }
	sink(g(), a || (b && h()), k())
}

func main() {
	run(true)
	run(false)
}
