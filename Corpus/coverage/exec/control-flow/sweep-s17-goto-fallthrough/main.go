package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-172's line): fallthrough and goto at the shapes the corpus did not
// hold — a fallthrough from a multi-value case, from a default clause in
// the middle, in a tagless switch, in a switch with an init, inside a
// closure and inside a generic body; a goto inside a closure and inside a
// generic body. (The trailing-empty-statement and labeled-fallthrough
// spellings are probed in their own package.) Expected = gc go1.26.5.

// A13.4
func fallthroughMultiValueCase(x int) int {
	r := 0
	switch x {
	case 1, 2:
		r += 1
		fallthrough
	case 3:
		r += 10
	}
	return r
}

func fallthroughFromMiddleDefault(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
	default:
		r += 2
		fallthrough
	case 3:
		r += 10
	}
	return r
}

func fallthroughTagless() int {
	x := 1
	r := 0
	switch {
	case x > 0:
		r = 1
		fallthrough
	case x > 100:
		r += 10
	}
	return r // 11
}

func fallthroughWithInit() int {
	x := 1
	r := 0
	switch y := x + 1; y {
	case 2:
		r = 1
		fallthrough
	case 9:
		r += 10
	}
	return r // 11
}

// A13.6
func fallthroughInClosure() int {
	f := func(x int) int {
		r := 0
		switch x {
		case 1:
			r = 1
			fallthrough
		case 2:
			r += 10
		}
		return r
	}
	return f(1)*100 + f(2) // 1110
}

func ftG[T comparable](x, a, b T) int {
	r := 0
	switch x {
	case a:
		r = 1
		fallthrough
	case b:
		r += 10
	}
	return r
}

func fallthroughInGeneric() int {
	return ftG(1, 1, 2)*100 + ftG("b", "a", "b") // 1110
}

// A12.5
func gotoInClosure() int {
	f := func() int {
		n := 0
	L:
		n++
		if n < 3 {
			goto L
		}
		return n
	}
	return f() // 3
}

func gG[T int | int64](n T) T {
	var i T
L:
	i++
	if i < n {
		goto L
	}
	return i
}

func gotoInGeneric() int {
	return int(gG(4)) + int(gG(int64(2))) // 6
}

func main() {
	println(fallthroughMultiValueCase(2), fallthroughMultiValueCase(3), fallthroughFromMiddleDefault(5),
		fallthroughFromMiddleDefault(3), fallthroughTagless(), fallthroughWithInit(), fallthroughInClosure(),
		fallthroughInGeneric(), gotoInClosure(), gotoInGeneric())
}
