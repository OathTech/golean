package main

type intOnly interface {
	~int
}

func keepInt[T intOnly](x T) T {
	return x
}

func main() {
	_ = keepInt("x")
}
