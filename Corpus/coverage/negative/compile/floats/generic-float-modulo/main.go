package main

type genericFloatModuloConstraint interface {
	~float32 | ~float64
}

func genericFloatModuloBad[T genericFloatModuloConstraint](a T, b T) T {
	return a % b
}

func main() {
	_ = genericFloatModuloBad(float64(1), float64(1))
}
