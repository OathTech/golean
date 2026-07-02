package main

func genericZero[T any]() T {
	var z T
	return z
}

func genericZeroComposite() int {
	s := genericZero[[]int]()
	m := genericZero[map[string]int]()
	score := 0
	if s == nil {
		score += 1
	}
	if m == nil {
		score += 10
	}
	return score
}

func main() {
	genericZeroComposite()
}
