package main

func id[T any](x T) T {
	return x
}

func bad() any {
	return id
}
