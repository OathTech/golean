package main

func switchInitBeforeExpression() int {
	x := 1
	trace := 0
	tag := func() int {
		trace = trace*10 + x
		return x
	}
	switch x = 2; tag() {
	case 2:
		trace = trace*10 + 3
	default:
		trace = 99
	}
	return trace
}

