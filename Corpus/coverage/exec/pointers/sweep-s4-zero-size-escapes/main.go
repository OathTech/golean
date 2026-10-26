package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-170's mechanism (R15,
// the zero-size VARIABLE address latitude) at the routes beside
// pointers/zero-size-address/escaped-same: `new` of a zero-size type whose
// result escapes (gc: runtime.zerobase, so two `new`s are EQUAL), the same
// `[0]int`, the escaped pointers in a switch, in `any` boxes, as map keys and
// inside struct/array keys, variables escaping through closures and `[0]int`
// / `[0]struct{}` variables escaping through globals. The machine allocates
// a fresh cell per variable (the never-same member) and answers distinct on
// each: red rows on BUG-170's Cases line. Controls that agree at birth:
// non-escaping `new`s (distinct on both sides), a zero-size local returned
// by address from an inlined function (gc inlines, two stack variables,
// distinct), non-escaping `[0]int` variables, and two `new`s boxed straight
// into interface values (gc keeps them distinct).

type zsT struct{}

var g1, g2 *zsT
var g3, g4 *[0]int
var ga, gb *[0]int
var gs1, gs2 *[0]struct{}
var keepF []func() *zsT

type hold struct {
	P *zsT
	N int
}

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

// Two escaped `new(zsT)` (gc 1).
func zsNewEscaped() int {
	g1 = new(zsT)
	g2 = new(zsT)
	return bit(g1 == g2, 1)
}

// Two escaped `new([0]int)` (gc 1).
func zsNewEscapedArray0() int {
	g3 = new([0]int)
	g4 = new([0]int)
	return bit(g3 == g4, 1)
}

// The escaped pair in an expression switch (gc 1).
func zsNewEscapedSwitch() int {
	g1 = new(zsT)
	g2 = new(zsT)
	switch g1 {
	case g2:
		return 1
	default:
		return 2
	}
}

// Two zero-size variables escaping through closures (gc 11).
func zsClosureEscaped() int {
	var a, b zsT
	fa := func() *zsT { return &a }
	fb := func() *zsT { return &b }
	keepF = append(keepF, fa, fb)
	return bit(fa() == fb(), 1) + bit(keepF[0]() == keepF[1](), 10)
}

// `[0]int` variables escaping through globals (gc 1).
func zsArray0Escaped() int {
	var a, b [0]int
	ga, gb = &a, &b
	return bit(ga == gb, 1)
}

// `[0]struct{}` variables escaping through globals (gc 1).
func zsArray0StructEscaped() int {
	var e, f [0]struct{}
	gs1, gs2 = &e, &f
	return bit(gs1 == gs2, 1)
}

// The escaped pair compared as `any` boxes: same dynamic type `*zsT`, so the
// payloads compare (gc 111).
func zsIfaceBox() int {
	g1 = new(zsT)
	g2 = new(zsT)
	var i1, i2 any = g1, g2
	return bit(i1 == i2, 1) + bit(any(g1) == any(g2), 10) + bit(i1 == any(g1), 100)
}

// The escaped pair as `map[*zsT]` keys: one entry (gc 1 2 → 12).
func zsMapKey() int {
	g1 = new(zsT)
	g2 = new(zsT)
	m := map[*zsT]int{g1: 1}
	m[g2] = 2
	return len(m)*10 + m[g1]
}

// Inside a STRUCT key (gc 12).
func zsStructKey() int {
	g1 = new(zsT)
	g2 = new(zsT)
	h := map[hold]int{{g1, 1}: 1}
	h[hold{g2, 1}] = 2
	return len(h)*10 + h[hold{g1, 1}]
}

// Inside an ARRAY key, the pair swapped (gc 1).
func zsArrayKey() int {
	g1 = new(zsT)
	g2 = new(zsT)
	k := map[[2]*zsT]int{{g1, g2}: 1}
	k[[2]*zsT{g2, g1}] = 2
	return len(k)
}

// CONTROL (agrees): two non-escaping `new(zsT)` are distinct (gc 0).
func zsNewLocal() int {
	p := new(zsT)
	q := new(zsT)
	return bit(p == q, 1)
}

func mkZs() *zsT {
	var z zsT
	return &z
}

// CONTROL (agrees): a zero-size local returned by address — gc inlines the
// callee, two stack variables, distinct (gc 10).
func zsReturnedLocal() int {
	p := mkZs()
	q := mkZs()
	return bit(p == q, 1) + bit(p != q, 10)
}

// CONTROL (agrees): non-escaping `[0]int` variables (gc 0).
func zsArray0Stack() int {
	var c, d [0]int
	return bit(&c == &d, 1)
}

// CONTROL (agrees): two `new(zsT)` boxed straight into interface values are
// distinct under gc (gc 0).
func zsIfaceBoxDirect() int {
	var e1, e2 any = new(zsT), new(zsT)
	return bit(e1 == e2, 1)
}

func main() {
	println(zsNewEscaped(), zsNewEscapedArray0(), zsNewEscapedSwitch(), zsClosureEscaped(),
		zsArray0Escaped(), zsArray0StructEscaped(), zsIfaceBox(), zsMapKey(), zsStructKey(), zsArrayKey(),
		zsNewLocal(), zsReturnedLocal(), zsArray0Stack(), zsIfaceBoxDirect())
}
