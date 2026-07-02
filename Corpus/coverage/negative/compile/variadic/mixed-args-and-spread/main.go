package main

func takesInts(xs ...int) {
}

func main() {
	xs := []int{2, 3}
	takesInts(1, xs...)
}
