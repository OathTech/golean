package main

func switchFallthroughSkipsCaseExpression() int {
	trace := 0
	mark := func(n int) int {
		trace = trace*10 + n
		return n
	}
	result := 0
	switch 1 {
	case mark(1):
		result = result*10 + 1
		fallthrough
	case mark(2):
		result = result*10 + 2
	default:
		result = 99
	}
	return trace*100 + result
}

