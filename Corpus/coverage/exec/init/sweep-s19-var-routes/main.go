package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27: the stepwise variable schedule at further routes — generic
// instantiations, struct embedding, multi-name specs, blanks, iota,
// init-mutated state, operand positions, functions in composite
// literals, a callee that writes. Per-cell digit traces (see
// init/sweep-s19-var-schedule); expected values gc go1.26.5's.

// A10: a generic FUNCTION's body is followed, instantiated explicitly or
// by inference: y before x and w.
var trA10 int

func mkA10(x int) int { trA10 = trA10*10 + x; return x }

func a10G[T any](v T) int { return a10y + mkA10(2) }

var a10x = a10G[int](0)
var a10w = a10G(1.5)
var a10y = mkA10(1)

func genericFunction() int { return trA10*100 + a10x*10 + a10w }

// A11: a generic TYPE's method `P[int]{…}.get()` — go/types (hence the
// frontend) and gc (types2, the same analysis) both record NO dependency
// through the instantiated method's body: the lookup is by the
// instantiated method object, which is not a package-level object. x is
// therefore initialized BEFORE y and reads y's zero value. Both sides
// agree (gc 32102, probed 2026-10-27); the row pins the agreement — a
// gc behaviour at a point where the spec's "reference to a method" would
// read otherwise, version-tracked at the oracle pin.
var trA11 int

func mkA11(x int) int { trA11 = trA11*10 + x; return x }

type a11P[T any] struct{ v T }

func (p a11P[T]) get() int { return a11y + mkA11(2) }

var a11x = a11P[int]{mkA11(3)}.get()
var a11y = mkA11(1)

func genericTypeMethod() int { return trA11*100 + a11x }

// A12: a method PROMOTED through struct embedding (`S{T{…}}.get()`; the
// static type S is not an interface, get is in its method set): a
// reference to T.get, so y goes first.
var trA12 int

func mkA12(x int) int { trA12 = trA12*10 + x; return x }

type a12T struct{ m int }

func (t a12T) get() int { return t.m*10 + a12y }

type a12S struct{ a12T }

var a12x = a12S{a12T{mkA12(2)}}.get()
var a12y = mkA12(1)

func promotedThroughStruct() int { return trA12*100 + a12x }

// A13: a multi-name spec with one value PER name (`var a, b = f(c),
// mark(2)`) is two separate steps: b (ready) goes first, then c, then a.
var trA13 int

func mkA13(x int) int { trA13 = trA13*10 + x; return x }

var a13a, a13b = a13f(a13c), mkA13(2)
var a13c = mkA13(1)

func a13f(v int) int { return v*10 + mkA13(3) }

func multiNameSeparateSteps() int { return trA13*1000 + a13a*10 + a13b }

// A15: a BLANK variable with a dependency waits for it like any other
// (blanks are treated like other variables): a (1) before the blank (3).
var trA15 int

func mkA15(x int) int { trA15 = trA15*10 + x; return x }

var _ = mkA15(a15a + 2)
var a15a = mkA15(1)

func blankWithDependency() int { return trA15 }

// A16: a const group with iota takes no step and creates no dependency:
// the two marked initializers run in declaration order with the
// constants' values.
var trA16 int

func mkA16(x int) int { trA16 = trA16*10 + x; return x }

const (
	a16K0 = iota
	a16K1
	a16K2
)

var a16x = mkA16(a16K2)
var a16y = mkA16(a16K1)

func constIotaNoStep() int { return trA16*10 + a16K0 + a16x - a16y }

// A17: an `init` declared lexically FIRST still runs after EVERY variable
// initializer: x, which reads z through a function, sees z's zero value
// (init assigns 9 afterwards); the trace is x's mark, w's mark, init's.
func init() { a17z = 9; mkA17(3) }

var trA17 int

func mkA17(x int) int { trA17 = trA17*10 + x; return x }

var a17x = a17get()

func a17get() int { return a17z*10 + mkA17(1) }

var a17z int
var a17w = mkA17(2)

func initAfterAllVars() int { return trA17*1000 + a17x*10 + a17z + a17w - 2 }

// A19: operand positions are references: len(s), s[0], m["k"], *p, st.f
// each depend on the later-declared variable, and p on pv (`&pv`).
// Schedule: s(1) l(2) i(3) mp(7) m(4) pv(8) p d(5) st(9) f(6).
var trA19 int

func mkA19(x int) int { trA19 = trA19*10 + x; return x }

var a19l = len(a19s) + mkA19(2)
var a19i = a19s[0] + mkA19(3)
var a19m = a19mp["k"] + mkA19(4)
var a19d = *a19p + mkA19(5)
var a19f = a19st.f + mkA19(6)
var a19s = []int{mkA19(1) + 10}
var a19mp = map[string]int{"k": mkA19(7)}
var a19p = &a19pv
var a19pv = mkA19(8)

type a19ST struct{ f int }

var a19st = a19ST{mkA19(9)}

func operandPositions() int { return trA19*100 + a19l + a19i + a19m + a19d + a19f }

// A20: a function referenced from a composite literal stored in a
// variable: x depends on tbl, tbl on read, read on y.
var trA20 int

func mkA20(x int) int { trA20 = trA20*10 + x; return x }

var a20x = a20tbl[0]() + mkA20(3)
var a20tbl = []func() int{a20read}

func a20read() int { return a20y*10 + mkA20(2) }

var a20y = mkA20(1)

func functionInCompositeLiteral() int { return trA20*100 + a20x }

// A21: the callee of a's initializer WRITES b after b was initialized:
// b (1) first, then a's call overwrites it with 50.
var trA21 int

func mkA21(x int) int { trA21 = trA21*10 + x; return x }

var a21a = a21set()
var a21b = mkA21(1)

func a21set() int { a21b = 50; return mkA21(2) }

func calleeWritesDependency() int { return trA21*100 + a21b + a21a - 2 }

func main() {
	println(genericFunction(), genericTypeMethod(), promotedThroughStruct(), multiNameSeparateSteps(),
		blankWithDependency(), constIotaNoStep(), initAfterAllVars(), operandPositions(),
		functionInCompositeLiteral(), calleeWritesDependency())
}
