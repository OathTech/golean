package main

func floatFiniteArithmetic() int {
	a := 1.5
	b := 2.25
	score := 0
	if a+b == 3.75 {
		score += 1
	}
	if b-a == 0.75 {
		score += 10
	}
	if a*4.0 == 6.0 {
		score += 100
	}
	if b/a == 1.5 {
		score += 1000
	}
	if a < b {
		score += 10000
	}
	return score
}

func main() {
	floatFiniteArithmetic()
}
