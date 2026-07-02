package main

type distance float64

func floatDefinedTypeOps() int {
	a := distance(2.5)
	b := distance(1.25)
	sum := a + b
	diff := a - b
	product := a * 2
	score := 0
	if sum == distance(3.75) {
		score += 1
	}
	if diff == distance(1.25) {
		score += 10
	}
	if product == distance(5) {
		score += 100
	}
	return score
}

func main() {
	floatDefinedTypeOps()
}
