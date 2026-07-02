package main

func bad(xs ...int, y int) int {
	return len(xs) + y
}

func main() {
	_ = bad(1, 2)
}
