package main

// E5DLIT (Stage E5, family E5d — the address of a variable as an allocation PAYLOAD; lane
// core/unseq-stage-e5-0922, 2026-09-22): `*(&PT{p: &x}).p + m()` with m writing x = 10 (returns 5).
// `&x` is an ADDRESS FORMATION (no read, no failure) carried as the struct literal's payload `ref x`;
// the literal is an `allocate` body without an E1 edge; the dereference through the fresh pointer's
// field READS x — unordered against m. Before m 1 + 5 = 6; after 10 + 5 = 15 (gc's, call-first).
// Reference enumerate.py E5d2; {6, 15}.
type PT struct{ p *int }

func e5dlit() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return *(&PT{p: &x}).p + m()
}

func main() { println(e5dlit()) }
