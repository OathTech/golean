package main

func mapDeleteDuringRange() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		delete(m, 1)
		delete(m, 2)
		delete(m, 3)
		_ = k
	}
	return n*10 + len(m)
}

func main() {
	mapDeleteDuringRange()
}
