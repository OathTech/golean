// spec#Integer_operators block Integer_operators-3-b892259b
// The spec's most-negative-value table: for each signed width, the
// dividend x listed (−128, −32768, −2147483648, −9223372036854775808)
// satisfies q = x / −1 == x and r = 0 due to two's-complement
// overflow. Operands live in variables so the division happens at run
// time (as constants it would be rejected). Each row is one score bit.
package main

func mostNegativeQuotient() int {
	score := 0
	x8, m8 := int8(-128), int8(-1)
	if x8/m8 == x8 && x8%m8 == 0 {
		score += 1
	}
	x16, m16 := int16(-32768), int16(-1)
	if x16/m16 == x16 && x16%m16 == 0 {
		score += 2
	}
	x32, m32 := int32(-2147483648), int32(-1)
	if x32/m32 == x32 && x32%m32 == 0 {
		score += 4
	}
	x64, m64 := int64(-9223372036854775808), int64(-1)
	if x64/m64 == x64 && x64%m64 == 0 {
		score += 8
	}
	return score
}

func main() {
	mostNegativeQuotient()
}
