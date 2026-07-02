package main

func float32Specials() int {
	var max float32 = 3.4028234663852886e38
	inf := max * 2
	var tiny float32 = 1.401298464324817e-45
	underflow := tiny / 2
	score := 0
	if inf > max {
		score += 1
	}
	if underflow == 0 {
		score += 10
	}
	return score
}
