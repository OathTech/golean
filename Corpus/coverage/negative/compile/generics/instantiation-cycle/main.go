package main

func cycle[T any](x T) int {
	return cycle([]T{x})
}

func main() {
	cycle(1)
}
