package main

func mapDeleteEvalOrder() int {
	trace := 0
	m := map[int]int{7: 1}
	mapExpr := func() map[int]int {
		trace = trace*10 + 1
		return m
	}
	key := func() int {
		trace = trace*10 + 2
		return 7
	}
	delete(mapExpr(), key())
	_, ok := m[7]
	if ok {
		return -1
	}
	return trace*10 + len(m)
}
