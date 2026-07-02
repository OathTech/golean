package main

func rangeNilMap() int {
	var m map[int]int
	count := 0
	sum := 0
	for k, v := range m {
		count++
		sum += k + v
	}
	return len(m)*100 + count*10 + sum
}
