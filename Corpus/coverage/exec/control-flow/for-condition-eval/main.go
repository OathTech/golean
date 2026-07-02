package main

func forConditionEval() int {
	state := 0
	cond := func(i int) bool {
		state = state*10 + i
		return i < 3
	}
	sum := 0
	for i := 0; cond(i); i++ {
		sum += i
	}
	return state*10 + sum
}

func main() {
	forConditionEval()
}
