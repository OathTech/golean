package main

func mapLiteralDuplicateEvalOrder() int {
	trace := 0
	key := func(n int) int {
		trace = trace*10 + n
		return 1
	}
	value := func(n int) int {
		trace = trace*10 + n
		return n
	}
	m := map[int]int{
		key(1): value(2),
		key(3): value(4),
	}
	return trace*100 + len(m)*10 + m[1]
}
