package main

func arrayKeyedLiteralEvalOrder() int {
	state := 0
	next := func(mark int) int {
		state = state*10 + mark
		return mark
	}
	a := [3]int{
		2: next(1),
		0: next(2),
		1: next(3),
	}
	return state*1000 + a[0]*100 + a[1]*10 + a[2]
}

func main() {
	arrayKeyedLiteralEvalOrder()
}
