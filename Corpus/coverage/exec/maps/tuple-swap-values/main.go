package main

func mapTupleSwapValues() int {
	m := map[int]int{0: 1, 1: 2}
	m[0], m[1] = m[1], m[0]
	return m[0]*10 + m[1]
}
