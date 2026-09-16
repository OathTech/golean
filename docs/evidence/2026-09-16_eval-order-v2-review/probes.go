package main

func main() {
	x, y := 0, 0
	mut := func() int { x = 1; y = 2; return 0 }
	println("reduction", x+y+mut())

	z := true
	h := func() bool { println("guard h"); return true }
	k := func() int { println("guard k"); return 7 }
	sink := func(b bool, n int) { println("guard result", b, n) }
	sink(z || h(), k())

	a := []int{10}
	f := func() int { a = []int{20}; return 0 }
	println("header", a[f()])

	b, left := false, false
	change := func() int { b = true; return 0 }
	logical := func(v bool, n int) { println("logical", v, n) }
	logical(left || b, change())
}
