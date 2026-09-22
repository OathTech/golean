package main

// E5DADDR (Stage E5, family E5d — the address of a variable as an operand; lane core/unseq-stage-e5-0922,
// 2026-09-22): `use(&x) + x` with use writing *p = 7 and returning 1. `&x` is an ADDRESS FORMATION
// (spec#Address_operators): no read, no failure — the call's argument `ref x`, no occurrence of the graph;
// the sibling read of the address-taken x is unordered against use. Before use 1 + 1 = 2; after 7 + 1 = 8
// (gc's, call-first). Reference enumerate.py E5d1; {2, 8}.
func use(p *int) int {
	*p = 7
	return 1
}

func e5daddr() int {
	x := 1
	return use(&x) + x
}

func main() { println(e5daddr()) }
