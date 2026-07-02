package main

func mapCompoundAssignEvalOnce() int {
	count := 0
	m := map[int]int{1: 10}
	key := func() int {
		count++
		return 1
	}
	value := func() int {
		count = count*10 + 2
		return 5
	}
	m[key()] += value()
	return count*100 + m[1]
}

func main() {
	mapCompoundAssignEvalOnce()
}
