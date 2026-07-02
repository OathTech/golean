package main

func floatSignedZero() int {
	posZero := 0.0
	negZero := -posZero
	score := 0
	if posZero == negZero {
		score += 1
	}
	if 1.0/posZero > 0 {
		score += 10
	}
	if 1.0/negZero < 0 {
		score += 100
	}
	return score
}

func main() {
	floatSignedZero()
}
