package main

func variadicNilCheck(xs ...int) bool {
	return xs == nil
}

func variadicNoArgsVsEmptySpread() int {
	empty := []int{}
	score := 0
	if variadicNilCheck() {
		score += 10
	}
	if variadicNilCheck(empty...) {
		score += 1
	}
	return score
}

func main() {
	variadicNoArgsVsEmptySpread()
}
