package main

// spec#Type_parameter_declarations block
// Type_parameter_declarations-3-c1263bf1: in `type T[P *C] ...` (and
// `type T[P (C)] ...`, `type T[P *C|Q] ...`) the bracketed part is parsed as
// an ARRAY LENGTH EXPRESSION — P*C, P(C), P*C|Q — not as a type parameter
// list; observable as len of the resulting array types (6, 3, 14 with
// P=2 C=3 Q=8). Block Type_parameter_declarations-4-eee1623c: writing the
// constraint as interface{*C} or adding a trailing comma forces the type-
// parameter reading. Renames, noted: the generic-parse forms need C to be a
// TYPE, realized as CT at package level and a local alias P = int8 for the
// P(C) form (generic declarations cannot be function-local).

const P = 2

const C = 3

const Q = 8

type TA [P * C]int // the block's `type T[P *C] ...`: array, len 6

type TC [P*C | Q]int // the block's `type T[P *C|Q] ...`: array, len 6|8 == 14

type CT struct{}

type TG1[P interface{ *CT }] struct{ p P } // block -4: interface{*C} forces type parameters

type TG2[P *CT,] struct{ p P } // block -4: trailing comma forces type parameters

func typeparamParseArrays() int {
	var ta TA
	var tc TC
	return len(ta)*100 + len(tc) // 614
}

func typeparamParseConversionForm() int {
	type P = int8
	type T [P(C)]int // the block's `type T[P (C)] ...`: array, len int8(3)
	var t T
	return len(t) // 3
}

func typeparamParseForced() int {
	x := CT{}
	g1 := TG1[*CT]{p: &x}
	g2 := TG2[*CT]{p: &x}
	n := 0
	if g1.p == &x {
		n++
	}
	if g2.p == &x {
		n++
	}
	return n // 2
}
