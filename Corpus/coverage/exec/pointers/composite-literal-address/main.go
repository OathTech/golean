package main

type pointerCompositeLiteralBox struct {
	x int
}

func pointerCompositeLiteralAddress() int {
	p := &pointerCompositeLiteralBox{x: 7}
	p.x = p.x + 4
	return p.x
}

func main() {
	pointerCompositeLiteralAddress()
}
