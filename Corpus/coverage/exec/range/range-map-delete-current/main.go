package main

func rangeMapDeleteCurrent() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	seen := 0
	valueSum := 0
	for k, v := range m {
		seen++
		valueSum += v
		delete(m, k)
	}
	return seen*10000 + valueSum*100 + len(m)
}
