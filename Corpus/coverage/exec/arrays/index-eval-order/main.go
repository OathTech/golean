package main

func arrayIndexEvalOrder() int {
	state := 0
	a := [2]int{}
	index := func(mark int) int {
		state = state*10 + mark
		return 1
	}
	value := func(mark int) int {
		state = state*10 + mark
		return 7
	}
	a[index(1)] = value(2)
	return state*10 + a[1]
}

func main() {
	arrayIndexEvalOrder()
}
