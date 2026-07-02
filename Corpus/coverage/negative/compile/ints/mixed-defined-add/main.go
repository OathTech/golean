package main

type addLeft int
type addRight int

func main() {
	var x addLeft = 1
	var y addRight = 2
	_ = x + y
}
