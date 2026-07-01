package main

func labeledContinue() int {
	score := 0
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
			score = score*10 + i + 1
		}
	}
	return score
}
