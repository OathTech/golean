package main

func id[T any](x T) T {
	return x
}

func sink[T any](f func(T)) {
	_ = f
}

func main() {
	sink(id)
}
