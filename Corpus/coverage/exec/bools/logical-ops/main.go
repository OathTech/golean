package main

func boolLogicalOps() int {
	score := 0
	if true && !false {
		score += 1
	}
	if false || true {
		score += 10
	}
	if true == false {
		score += 100
	}
	if true != false {
		score += 1000
	}
	return score
}

func main() {
	boolLogicalOps()
}
