package main

// spec#Variable_declarations block Variable_declarations-2-e27bbbcf: the
// declaration forms — zero-valued (i; U V W), inferred (k == 0 int),
// typed-with-initializers (x y float32 = -1 -2), grouped mixed inference
// (u v s = 2.0 3.0 "bar"), a two-result call (re im = complexSqrt(-1)), and
// blank + comma-ok map lookup (_, found = entries[name]). Adaptations,
// noted: the block's two i declarations cannot share one scope, so the
// grouped form lives in function scope (shadowing the package i);
// complexSqrt and entries/name are realized as supporting decls
// (complexSqrt(-1) returns (0, 1), the principal square root's re/im parts;
// name is absent from entries so found == false).

var i int

var U, V, W float64

var k = 0

var x, y float32 = -1, -2

func complexSqrt(v int) (float64, float64) { return 0, 1 } // supporting stand-in

var entries = map[string]int{"here": 1}

var name = "absent"

var re, im = complexSqrt(-1)

var _, found = entries[name] // map lookup; only interested in "found"

func varDeclForms() int {
	var (
		i       int
		u, v, s = 2.0, 3.0, "bar"
	)
	n := 0
	if i == 0 && k == 0 {
		n++
	}
	if U == 0 && V == 0 && W == 0 {
		n++
	}
	if x == -1 && y == -2 {
		n++
	}
	if u == 2.0 && v == 3.0 && s == "bar" {
		n++
	}
	var uf float64 = u // u was inferred as float64
	if uf == 2.0 {
		n++
	}
	if re == 0 && im == 1 {
		n++
	}
	if !found {
		n++
	}
	return n // 7
}
