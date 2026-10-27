package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// class (`decodeRuneAt`: the accept-range table of unicode/utf8).

// pack renders every (i, r) pair as "i:r|" so one string result carries the
// whole decode; widths are the differences of consecutive offsets.
func pack(s string) (string, int) {
	out := ""
	n := 0
	for i, r := range s {
		out += itoa(i) + ":" + itoa(int(r)) + "|"
		n++
	}
	return out, n
}

func itoa(v int) string {
	if v == 0 {
		return "0"
	}
	neg := v < 0
	if neg {
		v = -v
	}
	s := ""
	for v > 0 {
		s = string(rune('0'+v%10)) + s
		v /= 10
	}
	if neg {
		return "-" + s
	}
	return s
}

func range4Byte() (string, int)                { return pack("a😀b") }
func rangeTruncatedAtEnd() (string, int)       { return pack("a\xe2\x82") }
func rangeTruncated4AtEnd() (string, int)      { return pack("\xf0\x9f\x98") }
func rangeTruncatedBeforeAscii() (string, int) { return pack("\xe2\x82A") }
func rangeOverlong2() (string, int)            { return pack("\xc0\x80\xc1\xbf") }
func rangeOverlong3and4() (string, int)        { return pack("\xe0\x80\x80\xf0\x80\x80\x80") }
func rangeSurrogate() (string, int)            { return pack("\xed\xa0\x80\xed\xbf\xbf") }
func rangeAboveMax() (string, int)             { return pack("\xf4\x90\x80\x80\xf4\x8f\xbf\xbf") }
func rangeBadLeads() (string, int)             { return pack("\xf5\xf8\xfe\xff\xc2") }
func rangeNulDelC1() (string, int)             { return pack("\x00\x7f\xc2\x85\xc2\x80") }
func rangeBomAndLineSep() (string, int)        { return pack("a\uFEFFb  ") }
func rangeEncodedReplacement() (string, int)   { return pack("\xef\xbf\xbd\xff\xef\xbf") }
func rangeBoundaryRunes() (string, int) {
	return pack("\u007f\u0080߿ࠀ퟿￿\U00010000\U0010ffff")
}

func rangeOneVarAndCount() (int, int, int) {
	s := "a\xffé\x00😀"
	sum := 0
	for i := range s {
		sum = sum*16 + i
	}
	n := 0
	for range s {
		n++
	}
	k := 0
	for i := range len(s) {
		k += i
	}
	return sum, n, k
}

type myString string

func rangeDefinedString() (string, int) {
	var s myString = "\xff\xc3\xa9"
	out := ""
	n := 0
	for i, r := range s {
		out += itoa(i) + ":" + itoa(int(r)) + "|"
		n++
	}
	return out, n
}

func main() {
	range4Byte()
}
