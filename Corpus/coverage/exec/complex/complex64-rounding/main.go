package main

func complex64Rounding() int {
	var z complex64 = complex(float32(1<<24), float32(2))
	w := z + complex(1, 0)
	score := 0
	if real(w) == real(z) {
		score += 1
	}
	if imag(w) == 2 {
		score += 10
	}
	return score
}
