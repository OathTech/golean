package main

func floatNanComparisons() int {
	zero := 0.0
	nan := zero / zero
	score := 0
	if nan != nan {
		score += 1
	}
	if !(nan < 0) {
		score += 10
	}
	if !(nan > 0) {
		score += 100
	}
	if !(nan == 0) {
		score += 1000
	}
	return score
}
