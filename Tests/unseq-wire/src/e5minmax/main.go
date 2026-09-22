package main

// E5MINMAX (Stage E5, family E5a): `min(x, 100) + y + m()` with x private, y captured and written by
// m (y = 10; m returns 5). min is a PURE E1 participant (RATIFIED reading (a)) — a `min` head over its
// operand atoms, ordered before m — and y's read is unordered against m: before m 1 + 1 + 5 = 7,
// after 1 + 10 + 5 = 16 (gc's). Reference enumerate.py E5a5; {7, 16}.
func e5minmax() int {
	x := 1
	y := 1
	m := func() int { y = 10; return 5 }
	return min(x, 100) + y + m()
}

func main() { println(e5minmax()) }
