package main

func switchNoExpressionDefault() int {
	x := 0
	switch {
	case x > 0:
		return 1
	default:
		return 2
	}
}

func main() {
	switchNoExpressionDefault()
}
