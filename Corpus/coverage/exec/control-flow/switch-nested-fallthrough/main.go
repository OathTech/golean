package main

func switchNestedFallthrough() int {
	score := 0
	switch 1 {
	case 1:
		switch 5 {
		case 5:
			score = score*10 + 5
			fallthrough
		case 6:
			score = score*10 + 6
		}
		score = score*10 + 1
	}
	return score
}

func main() {
	switchNestedFallthrough()
}
