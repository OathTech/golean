package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group R3: strconv (source-through) at the
// integer widths — Itoa and FormatInt at MinInt64, FormatUint at MaxUint64 in base 2, the parse
// range boundaries at bitSize 8 on both sides: the happy values and the range errors (the
// clamped value and the error text), which lower through the source-through strconv.

import "strconv"

func strconvFormatWidths() (string, string, string, string, string) {
	return strconv.Itoa(-9223372036854775808), strconv.FormatInt(-9223372036854775808, 2),
		strconv.FormatUint(18446744073709551615, 2), strconv.Itoa(1 << 31), strconv.FormatInt(-1, 16)
}

func strconvParseHappyWidths() (int64, int64, uint64, int64, int, bool) {
	a, e1 := strconv.ParseInt("127", 10, 8)
	b, e2 := strconv.ParseInt("-128", 10, 8)
	c, e3 := strconv.ParseUint("255", 10, 8)
	d, e4 := strconv.ParseInt("-9223372036854775808", 10, 64)
	e, e5 := strconv.Atoi("-2147483649")
	return a, b, c, d, e, e1 == nil && e2 == nil && e3 == nil && e4 == nil && e5 == nil
}

func strconvParseRangeErrors() (int64, string, int64, string, int, string, uint64, string) {
	a, e1 := strconv.ParseInt("128", 10, 8)
	b, e2 := strconv.ParseInt("-129", 10, 8)
	c, e3 := strconv.Atoi("9223372036854775808")
	d, e4 := strconv.ParseUint("256", 10, 8)
	return a, e1.Error(), b, e2.Error(), c, e3.Error(), d, e4.Error()
}

func main() {
	strconvParseRangeErrors()
	strconvFormatWidths()
	strconvParseHappyWidths()
}
