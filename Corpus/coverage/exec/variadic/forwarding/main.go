package main

func forwardedSum(xs ...int) int {
	total := 0
	for i := 0; i < len(xs); i++ {
		total += xs[i]
	}
	return total
}

func forwardedNil(xs ...int) bool {
	return xs == nil
}

func forwardNilThrough(xs ...int) bool {
	return forwardedNil(xs...)
}

func variadicForwarding() int {
	var nilSlice []int
	empty := []int{}
	score := forwardedSum(1, 2, 3)
	if forwardNilThrough() {
		score += 1000
	}
	if forwardNilThrough(nilSlice...) {
		score += 100
	}
	if forwardNilThrough(empty...) {
		score += 10
	}
	if forwardNilThrough(7) {
		score += 1
	}
	return score
}
