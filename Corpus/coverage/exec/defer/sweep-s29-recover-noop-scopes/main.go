// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). BUG-031's no-op
// `$deferRecoverNoop` (one package-wide flag): `defer recover()` in two good functions,
// twice in one function, in a method, in a func literal, in init, in a generic function at
// two instantiations, and the no-op's semantics beside a real recover (a direct
// `defer recover()` recovers nothing: the panic propagates); expected = gc go1.26.5.

package main

var initMark int

func init() {
	defer recover()
	initMark = 3
}

type tR struct{ n int }

func (t *tR) bump() int {
	defer recover()
	t.n++
	return t.n
}

func noopFirst() int {
	defer recover()
	return 1
}

func noopSecond() int {
	defer recover()
	return 2
}

func noopTwiceAndLiteral() int {
	defer recover()
	defer recover()
	n := 0
	func() {
		defer recover()
		n = 5
	}()
	return n + initMark + (&tR{}).bump() // 9
}

func gNoop[T ~int](v T) T {
	defer recover()
	return v * 2
}

type myI int

func noopInGenericTwoInsts() int {
	return int(gNoop(3)) + int(gNoop(myI(4)))*10 // 86
}

func noopDoesNotRecover() int {
	got := 0
	func() {
		defer func() {
			if r := recover(); r != nil {
				got = r.(int) * 10
			}
		}()
		func() {
			defer recover()
			panic(7)
		}()
		got = 1
	}()
	return got // 70
}

func main() {
	println("noopFirst", noopFirst())
	println("noopSecond", noopSecond())
	println("noopTwiceAndLiteral", noopTwiceAndLiteral())
	println("noopInGenericTwoInsts", noopInGenericTwoInsts())
	println("noopDoesNotRecover", noopDoesNotRecover())
}
