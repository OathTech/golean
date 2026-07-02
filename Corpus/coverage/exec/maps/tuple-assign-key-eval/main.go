package main

func mapTupleAssignKeyEval() int {
	m := map[int]int{0: 0, 1: 0}
	i := 0
	i, m[i] = 1, 7
	return i*100 + m[0]*10 + m[1]
}
