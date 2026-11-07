package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding 1 on BUG-340's
// fix: a hidden read (through an interface method) of a package variable whose initializer gc writes
// BY PARTS into the data section — a composite or pointer literal with a dynamic element, a conversion
// to an interface (the inlinable single return of a literal is init/fix-e7-cut-inlined-literal). gc has the static part (a field, a slice
// header, the literal's pointer, the itab word) in place before any init code runs; the machine assigns
// the whole value at its InitOrder position, so the read sees zero / nil / len 0 (the audit's p1 1013 vs
// 13, p2 2202 vs 2, p2b 202 vs 2, p3 113 vs 713, p3b 103 vs 703). The 2026-11-05 cut had read the
// BUG-061 NODE question ("does work remain") as the target question and lowered these silently. Since
// this lane the E7 detector refuses each by name — the whole package, the refusal being whole-export —
// RED (frontend-export, c-pin/hidden-dep-init-order) BY DESIGN on BUG-340's Cases line; the expected
// column keeps gc's truth. The no-static-path controls lower in init/fix-e7-cut-no-static-path.

type I interface{ m() int }
type T struct{}

type S struct{ a, b int }

type J interface{ v() int }
type S2 struct{ b int }

func (s S2) v() int { return s.b }

var sink int

func g() int {
	for i := 0; i < 3; i++ {
		sink += i
	}
	return sink
}

func (T) m() int {
	r := ys.a*10 + ys.b
	r = r*10 + len(ysl)*10 + cap(ysl)
	r = r*10 + len(yad)
	if yp != nil {
		r = r*10 + yp.a
	}
	if yi != nil {
		r = r*10 + 1
	}
	return r
}

var x = I(T{}).m()
var ys = S{a: 1, b: g()}
var ysl = []int{1, g()}
var yad = []int{g(), g()}
var yp = &S{a: 1, b: g()}
var yi J = S2{b: g()}

func structLit() int   { return x*100 + ys.a*10 + ys.b }
func sliceLit() int    { return x*100 + len(ysl) }
func sliceAllDyn() int { return x*100 + len(yad) }
func ptrLit() int      { return x*100 + yp.a*10 + yp.b }
func ifaceConv() int   { return x*100 + yi.v() }

func main() { println(structLit(), sliceLit(), sliceAllDyn(), ptrLit(), ifaceConv()) }
