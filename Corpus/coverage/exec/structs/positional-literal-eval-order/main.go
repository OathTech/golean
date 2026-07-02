package main

type positionalEvalOrderStruct struct {
	a int
	b int
	c int
}

func structPositionalLiteralEvalOrder() int {
	state := 0
	next := func(mark int) int {
		state = state*10 + mark
		return mark
	}
	s := positionalEvalOrderStruct{
		next(1),
		next(2),
		next(3),
	}
	return state*1000 + s.a*100 + s.b*10 + s.c
}

func main() {
	structPositionalLiteralEvalOrder()
}
