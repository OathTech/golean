package main

func f[T any](a T, b T) T {
	return min(a, b)
}

func main() {}
