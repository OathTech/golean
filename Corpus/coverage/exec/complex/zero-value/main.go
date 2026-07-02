package main

func complexZeroValue() int {
	var z complex128
	score := 0
	if z == 0 {
		score += 1
	}
	if real(z) == 0 {
		score += 10
	}
	if imag(z) == 0 {
		score += 100
	}
	return score
}

func main() {
	complexZeroValue()
}
