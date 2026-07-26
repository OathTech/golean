package main

func mapClearDuringRange() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	n := 0
	for range m {
		n++
		clear(m)
	}
	return n*10 + len(m)
}

func main() {
	mapClearDuringRange()
}
