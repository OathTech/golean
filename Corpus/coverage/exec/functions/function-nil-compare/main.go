package main

func functionNilCompare() int {
	var f func(int) int
	score := 0
	if f == nil {
		score += 1
	}
	f = func(x int) int {
		return x + 1
	}
	if f != nil {
		score += 10
	}
	return score*100 + f(4)
}
