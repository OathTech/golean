package main

func complexBuiltinUntypedArgs() int {
	var z64 complex64 = complex(2, -3.5)
	z128 := complex(4, 1.25)
	score := 0
	if real(z64) == float32(2) {
		score += 1
	}
	if imag(z64) == float32(-3.5) {
		score += 10
	}
	if real(z128) == 4 {
		score += 100
	}
	if imag(z128) == 1.25 {
		score += 1000
	}
	return score
}

func main() {
	complexBuiltinUntypedArgs()
}
