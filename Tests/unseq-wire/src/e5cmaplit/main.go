package main

// E5CMAPLIT (Stage E5, family E5c — map literals; lane core/unseq-stage-e5-0922, 2026-09-22):
// `map[int]int{1: x}[1] + m()` with x captured and m writing it (x = 10; returns 5). The map
// literal is an `allocate` body (`map-lit`: the fresh map + its entry store) WITHOUT an E1 edge
// (v2.1 R3); the entry's read of x is unordered against m: before m 1 + 5 = 6 (gc's — gc realizes
// the literal at its lexical position), after 10 + 5 = 15. Reference enumerate.py E5c1; {6, 15}.
func e5cmaplit() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return map[int]int{1: x}[1] + m()
}

func main() { println(e5cmaplit()) }
