package main

// The original six type declarations are in REVERSE dependency order
// (audit fix R11, C-arc C2,
// docs/2026-09-05_c-arc-c2-design.md §3): the frontend collects the type
// table in source order, so this table VIOLATES the G-C2 order contract
// as declared (Grid names Cell before Cell is declared; Cell names Pair
// and Codes; Codes and Raw name Code) and those six entries MOVE under
// orderTypeDefsByDependency (post-order: Code, Pair, Codes, Cell, Grid,
// Raw). The array-element edge is exercised at two depths — a nested
// array of structs (Grid) and a defined-over-array (Codes, Raw) — so the
// machine's index descent (zero values, equality, conversion, boxing)
// resolves through array elements at indices that were forward
// references on the wire before ordering. Later types extend the BUG-103
// conversion tests; they need not all move under this ordering.

type Grid [2][2]Cell

type Cell struct {
	p  Pair
	cs Codes
}

type Codes [3]Code

type Pair struct {
	a, b Code
}

type Raw [3]Code

type Code int

// Zero value of a nested array of structs whose fields are arrays of a
// defined type, then writes through every level.
func declOrderZeroValues() int {
	var g Grid
	g[1][0].p.b = 7
	g[0][1].cs[2] = 5
	return int(g[1][0].p.b)*100 + int(g[0][1].cs[2])*10 + int(g[1][1].p.a) + len(g[0][0].cs)
}

// Array equality descends struct fields and defined array elements.
func declOrderArrayEquality() bool {
	var x, y Grid
	x[0][0].cs[1] = 3
	eq1 := x == y
	y[0][0].cs[1] = 3
	eq2 := x == y
	x[1][1].p = Pair{a: 1, b: 2}
	eq3 := x == y
	return !eq1 && eq2 && !eq3
}

// Boxing a struct-with-array value, asserting it back, and interface
// equality at the defined struct type.
func declOrderInterfaceBox() int {
	var c Cell
	c.p.a = 4
	c.cs[0] = 9
	var v any = c
	w, ok := v.(Cell)
	if !ok {
		return -1
	}
	var u any = Cell{p: Pair{a: 4}, cs: Codes{9, 0, 0}}
	if v != u {
		return -2
	}
	if _, isPair := v.(Pair); isPair {
		return -3
	}
	return int(w.p.a)*10 + int(w.cs[0])
}

// Defined array types (Codes, Raw over [3]Code) as VALUES: literals,
// pass/return by value (a copy), indexing, equality, zero value — the
// defined-over-array edge resolved at zero value, copy and equality.
func declOrderDefinedArrayValues() int {
	cs := Codes{1, 2, 3}
	r := Raw{1, 2, 3}
	d := doubleRaw(r)
	n := 0
	if r == (Raw{1, 2, 3}) {
		n = 1
	}
	var z Raw
	if z == (Raw{}) {
		n += 2
	}
	return int(d[0]+d[1]+d[2])*100 + int(cs[2])*10 + n + len(z)
}

func doubleRaw(r Raw) Raw {
	r[0] *= 2
	r[1] *= 2
	r[2] *= 2
	return r
}

// BUG-103: conversions between two defined array types with identical
// underlying types (`Raw(cs)`) and to the unnamed array type (`[3]Code(r)`)
// produce independent array values. Before the fix, the first conversion
// fell into convertValueToTy's unsupported catch-all. gc: 104.
func declOrderConversionArrayTarget() int {
	cs := Codes{1, 2, 3}
	r := Raw(cs)
	arr := [3]Code(r)
	r[0] = 40
	return int(arr[0]+arr[1]+arr[2])*10 + int(r[0]) + len(r) + int(cs[0])
}

func declOrderConversionUnnamedTarget() int {
	x := [2]int{3, 5}
	y := [2]int(x)
	y[0] = 9
	return x[0]*100 + y[0]*10 + y[1]
}

type GridCopy [2][2]Cell

func declOrderConversionNestedCopy() int {
	var x Grid
	x[1][0].p.a = 4
	x[1][0].cs[2] = 7
	y := GridCopy(x)
	y[1][0].p.a = 9
	y[1][0].cs[2] = 8
	return int(x[1][0].p.a)*1000 + int(y[1][0].p.a)*100 + int(x[1][0].cs[2])*10 + int(y[1][0].cs[2])
}

type RefCell struct {
	p *int
	s []int
}

type RefArray [1]RefCell
type RefArrayCopy [1]RefCell

// Array/struct storage is copied, while pointer and slice references keep
// their identity. Replacing a reference in the copy does not replace the
// original's field, and mutating the old referent is visible through both.
func declOrderConversionSharedReferences() int {
	n := 2
	x := RefArray{{p: &n, s: []int{3}}}
	y := RefArrayCopy(x)
	*y[0].p = 5
	y[0].s[0] = 7
	m := 9
	y[0].p = &m
	y[0].s = []int{8}
	return *x[0].p*1000 + *y[0].p*100 + x[0].s[0]*10 + y[0].s[0]
}

type EmptyCodes [0]Code
type EmptyRaw [0]Code

func emptyCodesOnce(n *int) EmptyCodes {
	*n++
	return EmptyCodes{}
}

func declOrderConversionEmptyEvalOnce() int {
	n := 0
	x := EmptyRaw(emptyCodesOnce(&n))
	return n*10 + len(x)
}

type FloatCodes [2]float32
type FloatRaw [2]float32

func declOrderConversionFloatElements() int {
	x := FloatCodes{1.5, 2.25}
	y := FloatRaw(x)
	y[0] = 3.5
	return int(x[0]*4)*100 + int(y[0]*4)*10 + int(y[1]*4)
}

func main() {
	println(declOrderZeroValues())
	println(declOrderArrayEquality())
	println(declOrderInterfaceBox())
	println(declOrderDefinedArrayValues())
	println(declOrderConversionArrayTarget())
	println(declOrderConversionUnnamedTarget())
	println(declOrderConversionNestedCopy())
	println(declOrderConversionSharedReferences())
	println(declOrderConversionEmptyEvalOnce())
	println(declOrderConversionFloatElements())
}
