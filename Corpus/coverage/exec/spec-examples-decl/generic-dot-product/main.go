package main

// spec#Arithmetic_operators block Arithmetic_operators-2-9bb79253: for
// operands of type-parameter type, the arithmetic operators apply when the
// type set contains only numeric types (F ~float32|~float64); dotProduct is
// the block's example, exercised at float64 and at a named ~float64 member.

func dotProduct[F ~float32 | ~float64](v1, v2 []F) F {
	var s F
	for i, x := range v1 {
		y := v2[i]
		s += x * y
	}
	return s
}

type myFloat float64

func dotProductFloat64() float64 {
	return dotProduct([]float64{1, 2, 3}, []float64{4, 5, 6}) // 32
}

func dotProductNamed() float64 {
	return float64(dotProduct([]myFloat{1.5, 2}, []myFloat{2, 4})) // 11
}
