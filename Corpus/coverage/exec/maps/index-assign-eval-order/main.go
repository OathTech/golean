package main

func mapIndexAssignEvalOrder() int {
	order := 0
	trace := 0
	m := map[int]int{}
	key := func() int {
		order++
		trace = trace*10 + order
		return 1
	}
	value := func() int {
		order++
		trace = trace*10 + order
		return 7
	}
	m[key()] = value()
	return trace*100 + m[1]
}

func main() {
	mapIndexAssignEvalOrder()
}
