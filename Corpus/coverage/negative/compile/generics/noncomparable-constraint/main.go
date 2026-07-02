package main

func acceptsComparable[T comparable](x T) bool {
	return x == x
}

func main() {
	_ = acceptsComparable([]int{1})
}
