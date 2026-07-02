package main

func boolLeftToRight() int {
	state := 0
	mark := func(value bool, digit int) bool {
		state = state*10 + digit
		return value
	}
	if mark(true, 1) && mark(true, 2) && !mark(false, 3) {
		return state
	}
	return 0
}

func main() {
	boolLeftToRight()
}
