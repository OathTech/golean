package main

func mapDeleteMissing() int {
	m := map[int]int{1: 10}
	delete(m, 2)
	_, ok := m[2]
	if ok {
		return -1
	}
	return len(m)*100 + m[1]
}
