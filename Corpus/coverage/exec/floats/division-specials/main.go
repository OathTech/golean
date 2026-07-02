package main

func floatDivisionSpecials() int {
	zero := 0.0
	posInf := 1.0 / zero
	negInf := -1.0 / zero
	nan := zero / zero
	score := 0
	if posInf > 0 {
		score += 1
	}
	if negInf < 0 {
		score += 10
	}
	if nan != nan {
		score += 100
	}
	return score
}

func main() {
	floatDivisionSpecials()
}
