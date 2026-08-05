package main

// f++ / f-- on float operands: the IncDec desugar's synthetic 1 literal
// must be FLOAT-kinded for float operands (floats design note 2026-08-04
// §11 rider) — an int-kinded 1 would be a kind-mismatched operand in the
// machine. Also pins absorption at both widths: adding 1 above 2^24
// (float32) / 2^53 (float64) rounds back to the operand.
func floatIncDec() int {
	f := 0.5
	f++
	score := 0
	if f == 1.5 {
		score += 1
	}
	f--
	f--
	if f == -0.5 {
		score += 10
	}
	var g float32 = 1 << 24
	g++ // 2^24 + 1 rounds to 2^24 (ties-to-even at float32)
	if g == 1<<24 {
		score += 100
	}
	big := 1e16
	big++ // 1e16 > 2^53: +1 is absorbed at float64
	if big == 1e16 {
		score += 1000
	}
	return score
}

func main() {
	floatIncDec()
}
