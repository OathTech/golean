package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), beside init/fix-e7-cut-partial-static: the hidden read of a
// package variable initialized by an INLINABLE SINGLE RETURN of a composite literal with a dynamic element
// (`mkS()` = `return S{a: 1, b: g()}`). gc inlines the call and StaticAssign folds the literal by parts
// (staticAssignInlinedCall), so `y.a == 1` is in place before any init code runs: gc 1013; the machine
// would read 13. The classifier calls the single-return shape MAYBE-STATIC on both questions, so the E7
// detector refused this shape before and after the lane — pinned here as the inlined member of the
// partial-fold family. RED (frontend-export, c-pin/hidden-dep-init-order) BY DESIGN on BUG-340's Cases
// line; expected = gc.

type I interface{ m() int }
type T struct{}

type S struct{ a, b int }

var sink int

func g() int {
	for i := 0; i < 3; i++ {
		sink += i
	}
	return sink
}

func mkS() S { return S{a: 1, b: g()} }

func (T) m() int { return y.a*10 + y.b }

var x = I(T{}).m()
var y = mkS()

func inlinedLit() int { return x*100 + y.a*10 + y.b }

func main() { println(inlinedLit()) }
