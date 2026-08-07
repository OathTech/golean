package main

// f++ / f-- on a DEFINED float type: the same IncDec desugar site as
// floats/incdec (F3), resolved through the named type to the underlying
// float kind — BUG-042's float facet: the unnamed-float fix kinded the
// synthetic 1 from the wire type, which for a defined type was
// {"kind":"named"}, so defFloat(0.5)++ produced an int-kinded 1 against
// a float64 operand and went stuck.

type defFloat float64

func definedFloatIncDec() int {
	f := defFloat(0.5)
	f++
	score := 0
	if f == 1.5 {
		score += 1
	}
	f--
	f--
	if f == -0.5 {
		score += 10
	}
	return score
}

func main() {
	definedFloatIncDec()
}
