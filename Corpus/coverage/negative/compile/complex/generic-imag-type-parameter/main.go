package main

type genericImagConstraint interface {
	~complex64 | ~complex128
}

func genericImagBad[T genericImagConstraint](z T) float64 {
	return imag(z)
}

func main() {
	_ = genericImagBad(complex128(1))
}
