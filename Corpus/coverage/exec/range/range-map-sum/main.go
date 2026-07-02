package main

func rangeMapSum() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	count := 0
	keySum := 0
	valueSum := 0
	for k, v := range m {
		count++
		keySum += k
		valueSum += v
	}
	return count*10000 + keySum*100 + valueSum
}
