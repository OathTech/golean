package main

type sample complex64

func realImagDefinedComplex() int {
	var z sample = sample(complex(float32(1.5), float32(-2.25)))
	r := real(z)
	i := imag(z)
	score := 0
	if r == float32(1.5) {
		score += 1
	}
	if i == float32(-2.25) {
		score += 10
	}
	return score
}

func main() {
	realImagDefinedComplex()
}
