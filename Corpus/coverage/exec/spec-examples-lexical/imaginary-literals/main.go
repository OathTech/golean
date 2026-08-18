// spec#Imaginary_literals block Imaginary_literals-2-b6efe7cf
// All 12 imaginary-literal forms from the spec's example list, each
// pinned to its spec-determined VALUE via an independently-constructed
// complex(re, im) built without the exotic form. The spec's own value
// assertions are load-bearing: 0123i == 123i (decimal, for backward
// compatibility — NOT octal), 0o123i == 83i, 0xabci == 2748i,
// 0x1p-2i == 0.25i. Each literal is stored in a complex128 variable
// first so the runtime representation (not just constant folding) is
// exercised; a wrong literal value flips its bit in the score.
//
// DO NOT gofmt THIS FILE: gofmt normalizes literal spelling
// (0123i -> 123i, 1E6i -> 1e6i, .12345E+5i -> .12345e+5i), which
// would silently destroy exactly the spec forms this case pins.
package main

func imaginaryLiterals() int {
	score := 0
	z1 := 0i
	if z1 == complex(0, 0) {
		score += 1
	}
	z2 := 0123i // == 123i for backward-compatibility
	if z2 == complex(0, 123) {
		score += 2
	}
	z3 := 0o123i // == 0o123 * 1i == 83i
	if z3 == complex(0, 83) {
		score += 4
	}
	z4 := 0xabci // == 0xabc * 1i == 2748i
	if z4 == complex(0, 2748) {
		score += 8
	}
	z5 := 0.i
	if z5 == complex(0, 0) {
		score += 16
	}
	z6 := 2.71828i
	if z6 == complex(0, 271828.0/100000.0) {
		score += 32
	}
	z7 := 1.e+0i
	if z7 == complex(0, 1) {
		score += 64
	}
	z8 := 6.67428e-11i
	if z8 == complex(0, 667428.0/1e16) {
		score += 128
	}
	z9 := 1E6i
	if z9 == complex(0, 1000000) {
		score += 256
	}
	z10 := .25i
	if z10 == complex(0, 1.0/4.0) {
		score += 512
	}
	z11 := .12345E+5i
	if z11 == complex(0, 12345) {
		score += 1024
	}
	z12 := 0x1p-2i // == 0x1p-2 * 1i == 0.25i
	if z12 == complex(0, 1.0/4.0) {
		score += 2048
	}
	return score
}

func main() {
	imaginaryLiterals()
}
