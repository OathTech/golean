package main

type genericRealConstraint interface {
	~complex64 | ~complex128
}

func genericRealBad[T genericRealConstraint](z T) float64 {
	return real(z)
}

func main() {
	_ = genericRealBad(complex128(1))
}
