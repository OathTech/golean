package main

func mapRangeSmoke() int {
	m := map[uint64]int{1: 10, 2: 20, 3: 30}
	sum := 0
	for _, v := range m {
		sum += v
	}
	n := 0
	for range m {
		n++
	}
	return sum + n
}
