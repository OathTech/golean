package main

func f[T any](x T) {
	delete(x, 1)
}

func main() {}
