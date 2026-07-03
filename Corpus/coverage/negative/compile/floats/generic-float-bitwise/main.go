package main

type genericFloatBitwiseConstraint interface {
	~float32 | ~float64
}

func genericFloatBitwiseBad[T genericFloatBitwiseConstraint](a T, b T) T {
	return a & b
}

func main() {
	_ = genericFloatBitwiseBad(float64(1), float64(1))
}
