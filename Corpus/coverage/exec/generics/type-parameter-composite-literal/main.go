package main

type genericPoint struct {
	x int
	y int
}

func makeGenericPoint[T ~struct {
	x int
	y int
}](x int, y int) T {
	return T{x: x, y: y}
}

func genericTypeParameterCompositeLiteral() int {
	p := makeGenericPoint[genericPoint](3, 4)
	return p.x*10 + p.y
}
