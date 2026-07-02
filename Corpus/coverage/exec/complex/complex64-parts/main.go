package main

func complex64Parts() int {
	var z complex64 = complex(float32(1.5), float32(-2.5))
	score := 0
	if real(z) == 1.5 {
		score += 1
	}
	if imag(z) == -2.5 {
		score += 10
	}
	return score
}

func main() {
	complex64Parts()
}
