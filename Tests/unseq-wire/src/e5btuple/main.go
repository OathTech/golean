package main

// E5BTUPLE (Stage E5, family E5b — multi-target assignments; lane core/unseq-stage-e5-0922,
// 2026-09-22): `s[0], x = m(), 3` with s captured and m REBINDING it ([1, 2] → [7, 8, 9]; returns
// 5). Every target is a phase-1 SIBLING plan: the element target's plan freezes s's HEADER before
// or after m, so the store of 5 lands in the old array (old[0] = 5, s[0] = 7 → 57) or the new one
// (1, 5 → 15); x's store rides the same phase-2 list. Reference enumerate.py E5b1; {57, 15}; gc 15.
// `m` is declared LAST so the hand-built wire keeps every setup statement through it.
func rebindS(ps *[]int) int { *ps = []int{7, 8, 9}; return 5 }

func e5btuple() int {
	s := []int{1, 2}
	old := s
	var x int
	m := func() int { return rebindS(&s) }
	s[0], x = m(), 3
	return old[0]*10 + s[0] + x - 3
}

func main() { println(e5btuple()) }
