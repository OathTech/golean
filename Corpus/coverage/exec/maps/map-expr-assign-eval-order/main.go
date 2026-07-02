package main

func mapExprAssignEvalOrder() int {
	trace := 0
	m := map[int]int{}
	mapExpr := func() map[int]int {
		trace = trace*10 + 1
		return m
	}
	key := func() int {
		trace = trace*10 + 2
		return 4
	}
	value := func() int {
		trace = trace*10 + 3
		return 9
	}
	mapExpr()[key()] = value()
	return trace*100 + m[4]
}
