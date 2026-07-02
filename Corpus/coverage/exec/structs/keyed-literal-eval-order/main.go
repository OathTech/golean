package main

type keyedEvalOrderStruct struct {
	a int
	b int
	c int
}

func structKeyedLiteralEvalOrder() int {
	state := 0
	next := func(mark int) int {
		state = state*10 + mark
		return mark
	}
	s := keyedEvalOrderStruct{
		c: next(1),
		a: next(2),
		b: next(3),
	}
	return state*1000 + s.a*100 + s.b*10 + s.c
}

func main() {
	structKeyedLiteralEvalOrder()
}
