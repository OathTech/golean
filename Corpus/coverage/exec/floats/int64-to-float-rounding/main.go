package main

// RUNTIME int64 -> float rounding at magnitudes above the mantissa
// (floats design note 2026-08-04 §1/§6): the values arrive as arguments
// so the conversions are runtime conversions (a constant conversion
// would fold in go/types and test the constant path instead).
//
//	a = 9007199254740993 = 2^53 + 1: rounds to 2^53 (ties-to-even)
//	b = 9007199254740995 = 2^53 + 3: rounds to 2^53 + 4 (nearest)
//	c = 9007199791611905 = (2^24+1)<<29 + 1: the int64 -> float32
//	    DOUBLE-ROUNDING discriminator (probed, 2026-08-05): correct
//	    single rounding gives 0x5a000001; rounding via float64 first
//	    gives 0x5a000000 == float32(2^53). Pins that float32(int64)
//	    single-rounds with a sticky bit (fintto32's approach), never
//	    via binary64.
func floatIntToFloatRounding(a, b, c int64) int {
	score := 0
	if float64(a) == float64(a-1) {
		score += 1 // 2^53+1 ties to even: == float64(2^53)
	}
	if float64(b)-float64(a-1) == 4 {
		score += 10 // 2^53+3 rounds up to 2^53+4
	}
	if float32(c) != float32(a-1) {
		score += 100 // single rounding: 0x5a000001, not the double-rounded 2^53
	}
	var d int32 = 1<<24 + 1
	if float32(d) == 1<<24 {
		score += 1000 // 2^24+1 ties to even at float32
	}
	return score
}

func main() {
	floatIntToFloatRounding(9007199254740993, 9007199254740995, 9007199791611905)
}
