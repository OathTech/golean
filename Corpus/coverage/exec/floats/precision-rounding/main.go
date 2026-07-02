package main

func floatPrecisionRounding() int {
	var f32 float32 = 1 << 24
	f32Next := f32 + 1
	var f64 float64 = 1 << 53
	f64Next := f64 + 1
	score := 0
	if f32Next == f32 {
		score += 1
	}
	if f64Next == f64 {
		score += 10
	}
	if f64+2 != f64 {
		score += 100
	}
	return score
}
