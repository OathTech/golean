package main

type T struct{ x int }

func sink(l bool, c int) int {
	if l {
		return 100 + c
	}
	return c
}

func rec(f func() int) (r int) {
	defer func() {
		if e := recover(); e != nil {
			println("panic:", e.(error).Error())
			r = -1
		}
	}()
	return f()
}

// (n1) new(x) inside a guard region, a LATER call writes x: the && is ordered before w -> x read as 1 -> false; {0}
func newInGuardRegion() int {
	b := true
	x := 1
	w := func() int { x = 5; return 0 }
	return sink(b && *new(x) > 3, w())
}

// (n2) new(pr()) inside a guard region: pr is ordered before w (both calls, lexical order): prints "pr" then "w"
func newCallInGuardRegion() int {
	b := true
	pr := func() int { println("pr"); return 1 }
	w := func() int { println("w"); return 0 }
	return sink(b && *new(pr()) > 0, w())
}

// (n3) run-time negative make length in an admitted sweep: Go panics makeslice; must NOT be a decode refusal
func makeRuntimeNegative() int {
	n := -1
	x := 1
	m := func() int { x = 2; return 5 }
	return len(make([]int, n)) + x + m()
}

// (n4) string([]byte) inside a guard region, m writes an alias: && ordered before m -> "ab" -> true; {105}
func stringBytesInGuard() int {
	b := []byte("ab")
	c := b
	t := true
	m := func() int { c[0] = 'z'; return 5 }
	return sink(t && string(b) == "ab", m())
}

// (n5) new with a struct-literal argument whose payload a sibling call writes: {6, 15}
func newStructLitArg() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return (*new(T{x: x})).x + m()
}

// (n6) new(x) where x is private (not captured) beside a call: all-forced, 1 + 5 = 6
func newPrivateArg() int {
	x := 1
	m := func() int { return 5 }
	return *new(x) + m()
}

func main() {
	println(newInGuardRegion())
	println(newCallInGuardRegion())
	println(rec(makeRuntimeNegative))
	println(stringBytesInGuard())
	println(newStructLitArg())
	println(newPrivateArg())
}
