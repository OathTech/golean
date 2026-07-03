package main

type holder struct {
	x []int
}

func main() {
	var a, b holder
	_ = a == b
}
