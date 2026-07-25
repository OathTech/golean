package main

func switchFallthroughIntoDefault() int {
	score := 0
	switch 1 {
	case 1:
		score = score*10 + 1
		fallthrough
	default:
		score = score*10 + 8
	}
	return score
}

func main() {
	switchFallthroughIntoDefault()
}
