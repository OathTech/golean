package main

type pointerAddressFieldPair struct {
	x int
	y int
}

func pointerAddressField() int {
	pair := pointerAddressFieldPair{x: 2, y: 5}
	px := &pair.x
	*px = *px + 10
	return pair.x*10 + pair.y
}

func main() {
	pointerAddressField()
}
