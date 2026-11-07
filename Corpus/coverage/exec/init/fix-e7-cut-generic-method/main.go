package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding 2 on BUG-340: the
// interface dispatch that performs the hidden read sits in a method of an INSTANTIATED generic type
// (`G[int]{}.M()`, and `h(G[string]{})` through a generic function). go/types resolves the call to the
// instance's *types.Func, which the detector's body index — keyed by the declarations' Defs objects —
// did not hold, so the read was followed nowhere and the program lowered silently: gc 44 (y = 4 folded
// into the data section, in place before x's initializer runs), the machine 4. The detector now follows
// the instance through its origin; RED (frontend-export, c-pin/hidden-dep-init-order) BY DESIGN on
// BUG-340's Cases line; expected = gc. The dynamic twin lowers: init/fix-e7-cut-generic-method-dynamic.

type I interface{ m() int }
type T struct{}

func (T) m() int { return y }

type G[E any] struct{ e E }

func (G[E]) M() int { return I(T{}).m() }

func h[E any](g G[E]) int { return g.M() }

var x = G[int]{}.M()
var x2 = h(G[string]{})
var y = 4

func genericMethod() int      { return x*10 + y }
func viaGenericFunction() int { return x2*10 + y }

func main() { println(genericMethod(), viaGenericFunction()) }
