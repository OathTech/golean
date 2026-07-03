package main

type genericComplexOrderConstraint interface {
	~complex64 | ~complex128
}

func genericComplexOrderBad[T genericComplexOrderConstraint](a T, b T) bool {
	return a < b
}

func main() {
	_ = genericComplexOrderBad(complex64(1), complex64(2))
}
