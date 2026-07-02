package main

func mapTupleMapExprTargets() int {
	trace := 0
	left := map[int]int{}
	right := map[int]int{}
	pick := func() map[int]int {
		trace++
		if trace == 1 {
			return left
		}
		return right
	}
	pick()[0], pick()[0] = 4, 9
	return trace*100 + left[0]*10 + right[0]
}
