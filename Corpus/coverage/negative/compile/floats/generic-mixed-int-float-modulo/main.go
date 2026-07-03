package main

type genericIntOrFloatModuloConstraint interface {
	~int | ~float64
}

func genericMixedModuloBad[T genericIntOrFloatModuloConstraint](a T, b T) T {
	return a % b
}

func main() {
	_ = genericMixedModuloBad(1, 1)
}
