package main

func complexNanInfParts() int {
	zero := 0.0
	z := complex(1.0/zero, zero/zero)
	score := 0
	if real(z) > 0 {
		score += 1
	}
	if imag(z) != imag(z) {
		score += 10
	}
	if z != z {
		score += 100
	}
	return score
}
