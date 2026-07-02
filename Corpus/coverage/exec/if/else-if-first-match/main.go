package main

func ifElseIfFirstMatch() int {
	trace := 0
	cond := func(n int, value bool) bool {
		trace = trace*10 + n
		return value
	}
	result := 0
	if cond(1, false) {
		result = 1
	} else if cond(2, true) {
		result = 2
	} else if cond(3, true) {
		result = 3
	} else {
		result = 4
	}
	return trace*10 + result
}

func main() {
	ifElseIfFirstMatch()
}
