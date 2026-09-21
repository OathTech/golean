package main

func newExprVsCall() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return *new(x) + m()
}

func newExprPlain() int {
	x := 7
	p := new(x)
	return *p
}

func newExprCallArg() int {
	x := 1
	m := func() int { x = 10; return 5 }
	q := new(m())
	return *q + x
}

func main() {
	println(newExprVsCall())
	println(newExprPlain())
	println(newExprCallArg())
}
