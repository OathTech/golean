package main

// E5APPEND (Stage E5, family E5a — the reading-(a) built-ins; lane core/unseq-stage-e5-0922,
// 2026-09-22): `append(s, 3)[0] + m()` with s = make([]int, 2, 4) holding [1, 2] (capacity for the
// in-place append) and m writing s[0] = 10 (returns 5). append is an EFFECTFUL E1 participant
// (RATIFIED reading (a)) ordered before m: it stores 3 in place and returns a header aliasing s's
// array; the result's [0] read is unordered against m. Reference enumerate.py E5a2; {6, 15}; gc 15
// (call-first). `m` is declared LAST so the hand-built wire keeps every setup statement through it.
func e5append() int {
	s := make([]int, 2, 4)
	s[0] = 1
	s[1] = 2
	m := func() int { s[0] = 10; return 5 }
	return append(s, 3)[0] + m()
}

func main() { println(e5append()) }
