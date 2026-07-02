package main

type variadicExpressionBox struct {
	base int
}

func (b variadicExpressionBox) add(xs ...int) int {
	total := b.base
	for _, x := range xs {
		total += x
	}
	return total
}

func variadicMethodExpression() int {
	f := variadicExpressionBox.add
	xs := []int{1, 4, 5}
	return f(variadicExpressionBox{base: 10}, xs...)
}
