package main

func switchExpressionOnce() int {
	calls := 0
	next := func() int {
		calls++
		return 2
	}
	result := 0
	switch next() {
	case 1:
		result = 10
	case 2:
		result = 20
	default:
		result = 30
	}
	return calls*100 + result
}

func main() {
	switchExpressionOnce()
}
