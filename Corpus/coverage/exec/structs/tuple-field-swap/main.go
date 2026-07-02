package main

type tupleFieldSwapStruct struct {
	x int
	y int
}

func structTupleFieldSwap() int {
	s := tupleFieldSwapStruct{x: 1, y: 2}
	s.x, s.y = s.y, s.x
	return s.x*10 + s.y
}

func main() {
	structTupleFieldSwap()
}
