package main

// Type declarations in REVERSE dependency order (audit fix R11, C-arc C2,
// docs/2026-09-05_c-arc-c2-design.md §3): the frontend collects the type
// table in source order, so this table VIOLATES the G-C2 order contract
// as declared (Grid names Cell before Cell is declared; Cell names Pair
// and Codes; Codes and Raw name Code) and every entry MOVES under
// orderTypeDefsByDependency (post-order: Code, Pair, Codes, Cell, Grid,
// Raw). The array-element edge is exercised at two depths — a nested
// array of structs (Grid) and a defined-over-array (Codes, Raw) — so the
// machine's index descent (zero values, equality, conversion, boxing)
// resolves through array elements at indices that were forward
// references on the wire before ordering.

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

// RED-FIRST (BUG-103, detected while writing these rows): a conversion
// whose TARGET's resolved shape is an ARRAY — between two defined array
// types with identical underlying types (`Raw(cs)`) or to the unnamed
// array type (`[3]Code(r)`) — falls into `convertValueToTy`'s catch-all
// (`unsupported: conversion to Ty.array …`); BUG-020 added the
// pointer/slice/map/func arms and left the array arm out. gc: 104.
func declOrderConversionArrayTarget() int {
	cs := Codes{1, 2, 3}
	r := Raw(cs)
	arr := [3]Code(r)
	r[0] = 40
	return int(arr[0]+arr[1]+arr[2])*10 + int(r[0]) + len(r) + int(cs[0])
}

func main() {
	println(declOrderZeroValues())
	println(declOrderArrayEquality())
	println(declOrderInterfaceBox())
	println(declOrderDefinedArrayValues())
	println(declOrderConversionArrayTarget())
}
