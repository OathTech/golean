package main

func switchFallthroughThenBreak() int {
	score := 0
	switch 1 {
	case 1:
		score = score*10 + 1
		fallthrough
	case 2:
		score = score*10 + 2
		if score > 0 {
			break
		}
		score = score*10 + 7
	case 3:
		score = score*10 + 3
	}
	return score
}

func main() {
	switchFallthroughThenBreak()
}
