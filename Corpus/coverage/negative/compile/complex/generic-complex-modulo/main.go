package main

type genericComplexModuloConstraint interface {
	~complex64 | ~complex128
}

func genericComplexModuloBad[T genericComplexModuloConstraint](a T, b T) T {
	return a % b
}

func main() {
	_ = genericComplexModuloBad(complex64(1), complex64(1))
}
