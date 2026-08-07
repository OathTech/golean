package main

// Range over a NON-default-kind integer with ARITHMETIC on the loop
// variable in the operand's kind (BUG-043, maint-check M1): the spec
// gives the iteration variable the operand's type (§For statements),
// but the index-loop desugar hard-coded the default int kind for
// $ridx/$rlen/the loop variable/the increment — and the wire carried
// no operand kind at all — so `i * 2` below is a mismatched-kind
// stuck. Broader mechanism than BUG-042's unresolved defined types:
// it bites UNNAMED kinds too. Comparisons are kind-blind, which is
// why the conversion-only shape (range/range-int-typed, and the
// control below) never saw it — the loop variable's KIND is only
// observable through arithmetic.

type defCount uint8

func rangeUint8Arith() int {
	total := 0
	for i := range uint8(200) {
		total += int(i * 2) // uint8 arithmetic: wraps mod 256 past 127
	}
	return total
}

func rangeDefinedArith() int {
	total := 0
	for i := range defCount(200) {
		total += int(i * 2)
	}
	return total
}

func rangeInt8Arith() int {
	total := 0
	for i := range int8(100) {
		total += int(i + 1) // int8-kinded 1 against the loop variable
	}
	return total
}

func rangeDefinedConversionControl() int {
	total := 0
	for i := range defCount(200) {
		total += int(i) // conversion only — kind-blind, passes pre-fix
	}
	return total
}

func main() {
	rangeUint8Arith()
	rangeDefinedArith()
	rangeInt8Arith()
	rangeDefinedConversionControl()
}
