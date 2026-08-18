package main

// spec#Constant_expressions block Constant_expressions-2-93cb2295: complex()
// over constants yields a complex constant — ic == 3.75i stays UNTYPED,
// while i0 (the spec writes it as the non-ASCII identifier "i\u0398" over the
// typed constant \u0398 float64 = 3/2 == 1.0) has type complex128.
// Supporting constants c and theta come from the section's earlier example
// (const c = 15/4.0 == 3.75; const theta float64 = 3/2 == 1.0, integer
// division); theta stands in for \u0398 (ASCII identifier policy noted).

const c2 = 15 / 4.0 // c in the spec's earlier block: 3.75, untyped float

const theta float64 = 3 / 2 // Theta: 1.0 (3/2 is integer division)

const ic = complex(0, c2)        // ic == 3.75i  (untyped complex constant)
const itheta = complex(0, theta) // itheta == 1i (type complex128)

func constComplexUntyped() float64 {
	var z complex128 = ic        // untyped complex adapts
	return imag(z)*100 + real(z) // 375
}

func constComplexTyped() float64 {
	return imag(itheta) // 1 (and itheta is already complex128)
}
