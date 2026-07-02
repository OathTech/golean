package main

func complexDivision() int {
	z := complex(1.0, 1.0) / complex(1.0, -1.0)
	score := 0
	if real(z) == 0 {
		score += 1
	}
	if imag(z) == 1 {
		score += 10
	}
	return score
}
