package main

type variadicMethodBox struct {
	base int
}

func (b variadicMethodBox) add(xs ...int) int {
	total := b.base
	for _, x := range xs {
		total += x
	}
	return total
}

func variadicMethod() int {
	return variadicMethodBox{base: 10}.add(1, 2, 3)
}
