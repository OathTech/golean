// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The per-declaration
// quarantine's rollback: good functions minting literals, closers and the recover no-op
// BETWEEN quarantined declarations that mint the same symbols (`complex` quarantines a
// declaration by name today), and the stencil error path (reflect.TypeOf in a generic
// function, FR-4's trigger) before a good stencil; every good subject's symbols must
// survive the rollbacks; expected = gc go1.26.5. The quarantined functions are not rowed
// (named refusals, gc runs them).

package main

import "reflect"

func goodA() int {
	f := func() int { return 1 }
	return f() // 1
}

func quarantined1() int {
	c := complex(1, 2)
	ch := make(chan int)
	defer close(ch)
	defer recover()
	f := func() int { return int(real(c)) }
	return f()
}

func goodB() int {
	f := func() int { return 2 }
	g := func() int { return 3 }
	return f()*10 + g() // 23
}

func quarantined2() int {
	c := complex(3, 4)
	f := func() int { return int(imag(c)) }
	return f()
}

func goodC() int {
	defer recover()
	f := func() int { return 4 }
	ch := make(chan int, 1)
	defer close(ch)
	ch <- 5
	return f() + <-ch // 9
}

func goodD() int {
	n := 0
	func() {
		defer recover()
		ch := make(chan int, 1)
		defer close(ch)
		n = 6
	}()
	return n // 6
}

func gBadLit[T any](v T) int {
	defer recover()
	f := func() T { return v }
	_ = reflect.TypeOf(f())
	return 1
}

func gGoodLit[T any](v T) int {
	defer recover()
	f := func() T { return v }
	_ = f()
	return 2
}

func demandBad() int { return gBadLit(1) }

func stencilGoodAfterBad() int {
	return gGoodLit(7) + gGoodLit("x") // 4
}

func main() {
	println("goodA", goodA())
	println("goodB", goodB())
	println("goodC", goodC())
	println("goodD", goodD())
	println("stencilGoodAfterBad", stencilGoodAfterBad())
}
