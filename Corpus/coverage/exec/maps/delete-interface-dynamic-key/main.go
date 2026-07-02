package main

func deleteInterfaceDynamicKey() int {
	m := map[any]int{1: 10, int8(1): 20}
	delete(m, any(1))
	_, okInt := m[1]
	v8, okInt8 := m[int8(1)]
	score := len(m)*100 + v8
	if okInt {
		score += 1000
	}
	if okInt8 {
		score += 10
	}
	return score
}
