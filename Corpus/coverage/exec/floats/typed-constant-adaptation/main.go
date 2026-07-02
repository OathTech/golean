package main

func floatTypedConstantAdaptation() int {
	const half = 1.5
	const quarter = 0.25
	var f32 float32 = half + quarter
	var f64 float64 = half - quarter
	score := 0
	if f32 == float32(1.75) {
		score += 1
	}
	if f64 == 1.25 {
		score += 10
	}
	return score
}

func main() {
	floatTypedConstantAdaptation()
}
