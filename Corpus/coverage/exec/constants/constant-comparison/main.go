package main

func constantComparison() int {
	const a = 1
	const b = 1.0
	const c = 2
	score := 0
	if a == b {
		score += 1
	}
	if c > b {
		score += 10
	}
	return score
}

func main() {
	constantComparison()
}
