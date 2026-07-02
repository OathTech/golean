package main

type positionalLiteralPoint struct {
	x int
	y int
}

func structPositionalLiteral() int {
	p := positionalLiteralPoint{2, 3}
	return p.x*10 + p.y
}

func main() {
	structPositionalLiteral()
}
