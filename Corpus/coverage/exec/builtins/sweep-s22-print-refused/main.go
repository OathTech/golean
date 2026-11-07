package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout. DESIGNED RED (BUG-093, FR-29 / c-pin): the
// frontend refuses these print operand kinds by name; a lowering that produced bytes here would be a wrong answer
// against gc's stderr. The three rows are the Cases-line neighbours of BUG-093's pinned kinds.

type F float64

func printComplex() int {
	c := complex(1, 2)
	println(c)
	return 0
}
func printDefinedFloat() int {
	f := F(1.5)
	println(f)
	return 0
}
func printNilSlice() int {
	var s []int
	println(s)
	return 0
}

func main() {
	printComplex()
	printDefinedFloat()
	printNilSlice()
}
