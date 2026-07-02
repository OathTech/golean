package main

func mapTupleRhsBeforeTargetWrite() int {
	m := map[int]int{0: 1, 1: 2}
	m[0], m[m[0]] = 7, m[0]+m[1]
	return m[0]*100 + m[1]
}
