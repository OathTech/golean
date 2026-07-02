package main

type tagPointerA struct {
	X int `tag:"a"`
}

type tagPointerB struct {
	X int `tag:"b"`
}

func structTagPointerConversion() int {
	a := &tagPointerA{X: 9}
	b := (*tagPointerB)(a)
	b.X++
	return a.X*10 + b.X
}
