package main

func genericSame[T any](x T, y T) T {
	return x
}

func main() {
	_ = genericSame(1, "x")
}
