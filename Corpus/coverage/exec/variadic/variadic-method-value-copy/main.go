package main

type variadicValueBox struct {
	n int
}

func (b variadicValueBox) total(xs ...int) int {
	for _, x := range xs {
		b.n += x
	}
	return b.n
}

func variadicMethodValueCopy() int {
	b := variadicValueBox{n: 1}
	f := b.total
	b.n = 100
	return f(2, 3)*1000 + b.n
}
