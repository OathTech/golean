package main

func mapNilAssignEvalBeforePanic() (result int) {
	var m map[int]int
	trace := 0
	key := func() int {
		trace = trace*10 + 1
		return 0
	}
	value := func() int {
		trace = trace*10 + 2
		return 3
	}
	defer func() {
		if recover() != nil {
			result = trace
		}
	}()
	m[key()] = value()
	return 99
}
