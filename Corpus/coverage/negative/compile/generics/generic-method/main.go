package main

type box struct{}

func (box) mapValue[T any](value T) T {
	return value
}

func main() {}
