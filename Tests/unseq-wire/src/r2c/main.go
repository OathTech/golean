package main

// R2c: sink3(g(), a || (b && h2()), k2()) — nested guards, an earlier call (g sets a).
// b=true: {"g k / sink 1 true 7", "g h k / sink 1 true 7"}; b=false: {"g k / sink 1 true 7", "g k / sink 1 false 7"}.
func sink3(g int, c bool, k int) { println("sink", g, c, k) }

func r2cTrue() {
	a := false
	b := true
	g := func() int { println("g"); a = true; return 1 }
	h2 := func() bool { println("h"); return true }
	k2 := func() int { println("k"); return 7 }
	sink3(g(), a || (b && h2()), k2())
}

func r2cFalse() {
	a := false
	b := false
	g := func() int { println("g"); a = true; return 1 }
	h2 := func() bool { println("h"); return true }
	k2 := func() int { println("k"); return 7 }
	sink3(g(), a || (b && h2()), k2())
}

func main() { r2cTrue(); r2cFalse() }
