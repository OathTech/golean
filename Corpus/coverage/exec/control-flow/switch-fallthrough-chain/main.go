package main

func switchFallthroughChain() int {
	score := 0
	switch 1 {
	case 1:
		score = score*10 + 1
		fallthrough
	case 2:
		score = score*10 + 2
		fallthrough
	case 3:
		score = score*10 + 3
	case 4:
		score = score*10 + 4
	}
	return score
}

func main() {
	switchFallthroughChain()
}
