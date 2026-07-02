package main

func float32ConversionRounding() int {
	var exact float64 = 16777216
	var next float64 = 16777217
	exact32 := float32(exact)
	next32 := float32(next)
	score := 0
	if exact32 == float32(16777216) {
		score += 1
	}
	if next32 == exact32 {
		score += 10
	}
	return score
}

func main() {
	float32ConversionRounding()
}
