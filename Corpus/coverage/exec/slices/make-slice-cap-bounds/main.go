package main

func makeSliceCapBounds() {
	length := 5
	capacity := 3
	s := make([]int, length, capacity)
	_ = len(s)
}

func main() {
	makeSliceCapBounds()
}
