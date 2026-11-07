package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07): the dynamic twin of init/fix-e7-cut-generic-method — the
// same hidden read through an instantiated generic method, of a target with no static path (`g()`, a
// multi-statement body): gc assigns y at its InitOrder position too, both sides read 0, and the
// detector lets the program lower (gc 3, the machine 3).

type I interface{ m() int }
type T struct{}

func (T) m() int { return y }

type G[E any] struct{ e E }

func (G[E]) M() int { return I(T{}).m() }

var sink int

func g() int {
	for i := 0; i < 3; i++ {
		sink += i
	}
	return sink
}

var x = G[int]{}.M()
var y = g()

func genericMethodDynamic() int { return x*10 + y }

func main() { println(genericMethodDynamic()) }
