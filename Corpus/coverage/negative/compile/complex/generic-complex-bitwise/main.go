package main

type genericComplexBitwiseConstraint interface {
	~complex64 | ~complex128
}

func genericComplexBitwiseBad[T genericComplexBitwiseConstraint](a T, b T) T {
	return a & b
}

func main() {
	_ = genericComplexBitwiseBad(complex64(1), complex64(1))
}
