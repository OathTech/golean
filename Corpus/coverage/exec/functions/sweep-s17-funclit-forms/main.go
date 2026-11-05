package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-012's line): function literals at the shapes the corpus did not
// hold — named results written by the literal's own defer, a literal in an
// interface box, as a generic argument and as an array element, an
// immediate call with arguments and with a spread, a package-level literal,
// a literal whose body holds a switch / select / range / labeled loop /
// goto, and an empty-bodied literal. Expected = gc go1.26.5.

var pkgLit = func(x int) int { return x * 3 }

var pkgLitCalls = func() int { return 4 }()

func apply[T any](f func(T) T, x T) T { return f(x) }

// B2.2
func litNamedResultDefer() int {
	f := func() (r int) {
		defer func() { r *= 2 }()
		r = 5
		return r + 1
	}
	return f() // 12
}

// B2.3
func litInIfaceBox() int {
	var i any = func() int { return 6 }
	return i.(func() int)() // 6
}

func litAsGenericArg() int {
	return apply(func(x int) int { return x + 1 }, 6) + len(apply(func(s string) string { return s + s }, "ab")) // 7 + 4 = 11
}

func litArrayElem() int {
	fs := [2]func() int{func() int { return 1 }, func() int { return 2 }}
	return fs[0]()*10 + fs[1]() // 12
}

// B2.5
func litImmediateArgs() int {
	return func(a, b int) int { return a*10 + b }(1, 3) // 13
}

func litImmediateSpread() int {
	xs := []int{1, 2, 3}
	return func(ys ...int) int {
		n := 0
		for _, y := range ys {
			n += y
		}
		return n
	}(xs...) // 6
}

// B2.6
func pkgLevelLit() int {
	return pkgLit(5) + pkgLitCalls // 15 + 4 = 19
}

// B2.7
func litBodyControl() int {
	f := func(xs []int) int {
		ch := make(chan int, 1)
		n := 0
	outer:
		for i, x := range xs {
			switch {
			case x < 0:
				continue outer
			case x > 100:
				break outer
			}
			ch <- x
			select {
			case v := <-ch:
				n += v * (i + 1)
			default:
			}
		}
		if n > 1000 {
			goto done
		}
		n += 1000
	done:
		return n
	}
	return f([]int{1, -1, 2, 200, 3}) // 1*1 + 2*3 = 7 + 1000 = 1007
}

// B2.8
func litEmptyBody() int {
	f := func() {}
	g := func() { return }
	f()
	g()
	return 1
}

func main() {
	println(litNamedResultDefer(), litInIfaceBox(), litAsGenericArg(), litArrayElem(), litImmediateArgs(),
		litImmediateSpread(), pkgLevelLit(), litBodyControl(), litEmptyBody())
}
