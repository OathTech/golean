package main

type genericComplexToFloatConstraint interface {
	~complex64 | ~complex128
}

func genericComplexToFloatBad[T genericComplexToFloatConstraint](z T) float64 {
	return float64(z)
}

func main() {
	_ = genericComplexToFloatBad(complex128(1))
}
