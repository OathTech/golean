package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 — the defect-neighbourhood campaign's step 2 for BUG-060/061/
// 064/171: the stepwise variable schedule of spec#Package_initialization
// at the routes the existing init/ rows do not pin. Every cell carries
// its own digit trace (`tr* = tr*10 + mark`), so the cells coexist in
// one package: the stepwise rule's projection onto one cell's variables
// is the cell's own schedule. Expected values are gc go1.26.5's under the
// runners' pins; each was probed in isolation first.

// A1: zero-valued variables take no initialization step (they are absent
// from the schedule); the marked initializers run in declaration order.
var trA1 int

func mkA1(x int) int { trA1 = trA1*10 + x; return x }

var a1a = mkA1(1)
var a1z int
var a1b = mkA1(2)
var a1y, a1w int
var a1c = mkA1(3)

func zeroValuedTakeNoStep() int { return trA1*100 + a1a + a1b + a1c + a1z + a1y + a1w }

// A3: a dependency TRANSITIVE through two function bodies (x refers to f,
// f refers to g, g refers to y): y initializes first.
var trA3 int

func mkA3(x int) int { trA3 = trA3*10 + x; return x }

var a3x = a3f()
var a3y = mkA3(1)

func a3f() int { return a3g() + mkA3(2) }
func a3g() int { return a3y * 10 }

func transitiveThroughTwoBodies() int { return trA3*100 + a3x }

// A4: a dependency through a VALUE-receiver method body (`T{…}.get()`
// is a reference to method get of T): y initializes before x.
var trA4 int

func mkA4(x int) int { trA4 = trA4*10 + x; return x }

type a4T struct{ m int }

func (t a4T) get() int { return t.m*10 + a4y }

var a4x = a4T{mkA4(2)}.get()
var a4y = mkA4(1)

func throughValueMethod() int { return trA4*100 + a4x }

// A5: through a POINTER-receiver method, both on a temporary
// (`(&T{}).get()`) and on a pointer variable (`p.get()`, which also
// depends on p): the pointer variable p, which has no dependencies, is
// the earliest ready and goes first; then y, x, w.
var trA5 int

func mkA5(x int) int { trA5 = trA5*10 + x; return x }

type a5T struct{ m int }

func (t *a5T) get() int { return t.m*10 + a5y }

var a5x = (&a5T{mkA5(2)}).get()
var a5p = &a5T{mkA5(3)}
var a5w = a5p.get()
var a5y = mkA5(1)

func throughPointerMethod() int { return trA5*10000 + a5x*100 + a5w }

// A6: a method VALUE stored and never invoked during initialization
// still depends on what the method reads ("It is immaterial whether the
// resulting function value t.m is invoked"): y before mv.
var trA6 int

func mkA6(x int) int { trA6 = trA6*10 + x; return x }

type a6T struct{ m int }

func (t a6T) get() int { return t.m + a6y }

var a6mv = a6T{mkA6(2)}.get
var a6y = mkA6(1)

func methodValueStored() int { return trA6*100 + a6mv() }

// A7: a method EXPRESSION `T.get` is a reference too: me waits for y,
// and x waits for me.
var trA7 int

func mkA7(x int) int { trA7 = trA7*10 + x; return x }

type a7T struct{ m int }

func (t a7T) get() int { return t.m + a7y }

var a7me = a7T.get
var a7x = a7me(a7T{mkA7(2)})
var a7y = mkA7(1)

func methodExpression() int { return trA7*100 + a7x }

// A8: a closure literal STORED in a variable: the closure's body refers
// to y, so f depends on y and x (which calls f) depends on f.
var trA8 int

func mkA8(x int) int { trA8 = trA8*10 + x; return x }

var a8f = func() int { return a8y + mkA8(2) }
var a8x = a8f()
var a8y = mkA8(1)

func closureStoredThenCalled() int { return trA8*100 + a8x }

// A9: a closure literal INVOKED INLINE in the initializer: its body's
// reference to y is x's dependency.
var trA9 int

func mkA9(x int) int { trA9 = trA9*10 + x; return x }

var a9x = func() int { return a9y*10 + mkA9(2) }()
var a9y = mkA9(1)

func closureInvokedInline() int { return trA9*100 + a9x }

func main() {
	println(zeroValuedTakeNoStep(), transitiveThroughTwoBodies(), throughValueMethod(),
		throughPointerMethod(), methodValueStored(), methodExpression(),
		closureStoredThenCalled(), closureInvokedInline())
}
