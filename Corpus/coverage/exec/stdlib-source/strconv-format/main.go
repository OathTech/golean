package main

// strconv.FormatUint / FormatInt through the REAL library source (stdlib
// source-through slice 1, 2026-09-03): deps/go/src/strconv/number.go's
// wrappers over internal/strconv's itoa.go (formatBase10 / small /
// formatBits, math/bits.TrailingZeros for power-of-two bases).
// godoc:strconv.FormatUint@go1.26.5 / godoc:strconv.FormatInt@go1.26.5:
// "the string representation of i in the given base, for 2 <= base <= 36.
// The result uses the lower-case letters 'a' to 'z' for digit values >=
// 10." Rows: every base 2..36 for one value each way, the extremes, the
// small-value fast path boundaries (nSmalls = 100), the illegal-base panic
// text (godoc has no text for it; the realized panic string is gc's, a
// forced point since the body IS gc's), and the reachable siblings
// Itoa/AppendInt/AppendUint (non-shim members lowering through the same
// body).

import "strconv"

func formatUintAllBases() string {
	out := ""
	for b := 2; b <= 36; b++ {
		out += strconv.FormatUint(1295, b) + ","
	}
	return out
}

func formatIntAllBases() string {
	out := ""
	for b := 2; b <= 36; b++ {
		out += strconv.FormatInt(-1295, b) + ","
	}
	return out
}

func formatExtremes() string {
	return strconv.FormatInt(-9223372036854775808, 2) + " " +
		strconv.FormatInt(-9223372036854775808, 36) + " " +
		strconv.FormatInt(9223372036854775807, 7) + " " +
		strconv.FormatUint(18446744073709551615, 2) + " " +
		strconv.FormatUint(18446744073709551615, 36) + " " +
		strconv.FormatInt(-1, 16) + " " + strconv.FormatUint(0, 2)
}

// nSmalls boundary in base 10: 99 takes the small-string table, 100 the
// formatBase10 loop; the negative twins.
func formatSmallBoundary() string {
	return strconv.FormatUint(99, 10) + " " + strconv.FormatUint(100, 10) + " " +
		strconv.FormatInt(-99, 10) + " " + strconv.FormatInt(-100, 10) + " " +
		strconv.FormatInt(0, 10) + " " + strconv.FormatUint(9, 10)
}

// Power-of-two bases take the shift path; the odd bases the division path.
func formatPowerOfTwoBases() string {
	return strconv.FormatUint(0xdeadbeef, 2) + " " + strconv.FormatUint(0xdeadbeef, 4) + " " +
		strconv.FormatUint(0xdeadbeef, 8) + " " + strconv.FormatUint(0xdeadbeef, 16) + " " +
		strconv.FormatUint(0xdeadbeef, 32) + " " + strconv.FormatInt(-0xdeadbeef, 32)
}

func formatIllegalBaseOne() string { return strconv.FormatUint(5, 1) }

func formatIllegalBaseZero() string { return strconv.FormatInt(-5, 0) }

// Siblings reachable through the same library body.
func formatSiblings() (string, string, string) {
	a := strconv.AppendInt([]byte("x="), -42, 10)
	b := strconv.AppendUint(a, 255, 16)
	return strconv.Itoa(-7), string(a), string(b)
}

func main() {
	println(formatUintAllBases(), formatIntAllBases(), formatExtremes(), formatSmallBoundary(), formatPowerOfTwoBases())
	println(formatSiblings())
	println(formatIllegalBaseOne(), formatIllegalBaseZero())
}
