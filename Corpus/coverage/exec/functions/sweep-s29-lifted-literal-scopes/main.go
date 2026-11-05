// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Lifted literals
// (`<fn>$lit<N>`) at every scope the name is keyed by: two on one line, two as call
// arguments, a literal returning a literal, same-name methods on two types, a method and a
// function of one name, two init functions in one file and a third in b.go, package-level
// initializers in two files, a generic function and a generic type's method at two
// instantiations, go and defer bodies; the wire must carry one function per literal;
// expected = gc go1.26.5.

package main

type tA struct{}
type tB struct{}
type tC struct{}

func (tA) mk() func() int { return func() int { return 1 } }
func (tB) mk() func() int { return func() int { return 2 } }
func (tC) mk() int        { f := func() int { return 4 }; return f() }

func mk() func() int { return func() int { return 3 } }

var pkgF = func() int { return 10 }

var initSum int

func init() {
	f := func() int { return 20 }
	initSum += f()
}

func init() {
	f := func() int { return 30 }
	initSum += f()
}

func twoLitsOneLine() int {
	a, b := func() int { return 1 }, func() int { return 2 }
	return a()*10 + b() // 12
}

func apply(f, g func() int) int { return f()*10 + g() }

func litsAsArgs() int {
	return apply(func() int { return 3 }, func() int { return 4 }) + func() func() int { return func() int { return 100 } }()() // 134
}

func litsInSameNameMethods() int {
	return tA{}.mk()()*1000 + tB{}.mk()()*100 + mk()()*10 + tC{}.mk() // 1234
}

func litsInInits() int {
	return initSum + pkgF() + pkgG() // 100 + 10 + 40 = 150
}

func litInGeneric[T any](v T) func() T { return func() T { return v } }

func litsInGenericTwoInsts() int {
	return litInGeneric(5)() + len(litInGeneric("abc")()) // 8
}

type gbox[T any] struct{ v T }

func (b gbox[T]) fn() func() T { return func() T { return b.v } }

func litsInGenericMethodTwoInsts() int {
	return gbox[int]{6}.fn()() + len(gbox[string]{"ab"}.fn()()) // 8
}

func litsInGoDefer() int {
	ch := make(chan int, 2)
	go func() { ch <- 1 }()
	go func() { ch <- 2 }()
	n := <-ch + <-ch
	func() {
		defer func() { n += 10 }()
		defer func() { n *= 2 }()
	}()
	return n // 16
}

func main() {
	println("twoLitsOneLine", twoLitsOneLine())
	println("litsAsArgs", litsAsArgs())
	println("litsInSameNameMethods", litsInSameNameMethods())
	println("litsInInits", litsInInits())
	println("litsInGenericTwoInsts", litsInGenericTwoInsts())
	println("litsInGenericMethodTwoInsts", litsInGenericMethodTwoInsts())
	println("litsInGoDefer", litsInGoDefer())
}
