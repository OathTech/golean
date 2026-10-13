package main

// F2 of the 2026-10-13 fresh-eyes fail-closed pass (BUG-078): the
// interpreter's materialization budgets are applied PER DECLARATION by
// the frontend (tools/nativefrontend/budgets.go), so one over-budget
// declaration no longer takes its whole package down — before, the
// decoder's refusal was per WIRE and every subject below answered
// `error`. Each over-budget declaration here is quarantined by its own
// unit; the UNRELATED subjects run and PASS.
//
//   bigLiteral     — a function whose body spells [70000]int: an H-3 stub
//                    (per-dimension budget, arrayLenBudget).
//   bigGlobal      — a package-level var of [70000]int with an initializer:
//                    FR-24 poison of the var (H-11 skips its effect-
//                    isolated initializer); the reader stubs.
//   Grid / gridSum — a declared type over the NESTED budget
//                    ([4096][4097]byte): the type ships as an existence-only
//                    marker; its method and its user stub.
//   bigMake        — make([][1024]byte, 1<<15): the constant-count make
//                    bound (behind gc's makeslice panic and sliceCapBudget).
//   makeMaxAlloc   — make([]byte, 1<<48+1): gc's OWN run-time panic, never
//                    pre-empted by the budget (the make site's order).
//   unrelated*     — PASS.

func bigLiteral() int {
	a := [70000]int{1: 5}
	return a[1]
}

var bigGlobal = [70000]int{3: 7}

func readBigGlobal() int {
	return bigGlobal[3]
}

type Grid [4096][4097]byte

func (g *Grid) Corner() byte { return g[4095][4096] }

func gridSum() int {
	var g Grid
	g[0][0] = 1
	return int(g[0][0])
}

func bigMake() int {
	b := make([][1024]byte, 1<<15)
	return len(b)
}

func makeMaxAlloc() (r string) {
	defer func() {
		if e := recover(); e != nil {
			r = "panicked"
		}
	}()
	b := make([]byte, 1<<48+1)
	return string(rune(len(b)))
}

func unrelatedSum() int {
	s := 0
	for i := 1; i <= 10; i++ {
		s += i
	}
	return s
}

func unrelatedSmallArray() int {
	var a [8]int
	for i := range a {
		a[i] = i * i
	}
	return a[7]
}

type small struct{ x, y int }

func unrelatedStruct() int {
	p := small{3, 4}
	return p.x*p.x + p.y*p.y
}

// alias-satisfaction (fix round 2026-10-13, review BLOCKER-1): an
// over-budget array in a METHOD SIGNATURE rides an opaque marker keyed by
// Go type IDENTITY — [N]byte ≡ [N]uint8, [N]rune ≡ [N]int32, an alias ≡
// its target, func parameter names ignored — so the requirement list and
// the stub name the same marker and satisfaction answers as gc does
// (a spelling key answered «no» where gc says yes: a silent wrong answer).
type MyByte = byte

type IByte interface{ M([70000]byte) }
type IRune interface{ R([70000]rune) }
type IAlias interface{ A([70000]MyByte) }
type IFunc interface{ F([70000]func(x int) int) }

type Impl struct{}

func (Impl) M([70000]uint8)           {}
func (Impl) R([70000]int32)           {}
func (Impl) A([70000]uint8)           {}
func (Impl) F([70000]func(y int) int) {}

func aliasSatisfaction() int {
	var x any = Impl{}
	r := 0
	if _, ok := x.(IByte); ok {
		r += 1
	}
	if _, ok := x.(IRune); ok {
		r += 10
	}
	if _, ok := x.(IAlias); ok {
		r += 100
	}
	if _, ok := x.(IFunc); ok {
		r += 1000
	}
	switch x.(type) {
	case IByte:
		r += 10000
	}
	return r
}

func main() {
	println(bigLiteral(), readBigGlobal(), gridSum(), bigMake(), makeMaxAlloc(),
		unrelatedSum(), unrelatedSmallArray(), unrelatedStruct(), aliasSatisfaction())
}
