package main

type Ints interface {
	~int8 | ~int16
}

func sum[T Ints](n T) T {
	var s T
	for i := range n {
		s += i
	}
	return s
}

func main() {
	_ = sum(int8(3))
}
