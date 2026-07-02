package main

func sum(xs ...int) int {
	return len(xs)
}

func main() {
	x := 1
	_ = sum(x...)
}
