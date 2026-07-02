package main

func forPostSideEffects() int {
	state := 0
	next := func(i int) int {
		state = state*10 + i
		return i + 1
	}
	sum := 0
	for i := 0; i < 3; i = next(i) {
		sum += i
	}
	return state*10 + sum
}

func main() {
	forPostSideEffects()
}
