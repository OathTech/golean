package main

func zeroOf[T any]() T {
	var z T
	return z
}

func genericZeroValues() int {
	score := 0
	if zeroOf[int]() == 0 {
		score += 1
	}
	if zeroOf[string]() == "" {
		score += 10
	}
	if !zeroOf[bool]() {
		score += 100
	}
	return score
}

func main() {
	genericZeroValues()
}
