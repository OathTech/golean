package main

func realImagRealArgs() int {
	score := 0
	if real(7) == 7 {
		score += 1
	}
	if imag(7) == 0 {
		score += 10
	}
	if real(1.25) == 1.25 {
		score += 100
	}
	if imag(1.25) == 0 {
		score += 1000
	}
	return score
}

func main() {
	realImagRealArgs()
}
