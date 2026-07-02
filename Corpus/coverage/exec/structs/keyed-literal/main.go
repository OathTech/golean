package main

type keyedLiteralPoint struct {
	x int
	y int
}

func structKeyedLiteral() int {
	p := keyedLiteralPoint{y: 3, x: 2}
	return p.x*10 + p.y
}

func main() {
	structKeyedLiteral()
}
