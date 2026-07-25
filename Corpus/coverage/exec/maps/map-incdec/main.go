package main

func mapIncDec() int {
	count := 0
	m := map[int]int{1: 10}
	key := func() int {
		count++
		return 1
	}
	m[key()]++
	m[1]++
	return count*1000 + m[1]
}

func main() {
	mapIncDec()
}
