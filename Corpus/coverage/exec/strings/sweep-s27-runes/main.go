package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// string([]rune(s)) round trip, and string(rune) at every encoder boundary
// (`runesOfString`, `stringFromRuneSlice`, `GoString.fromCodePoint`).

func packRunes(rs []rune) string {
	out := ""
	for _, r := range rs {
		out += itoa(int(r)) + "|"
	}
	return out
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

func runesInvalidClasses() (string, int) {
	rs := []rune("\x80\xe2\x82\xe2\x82A\xc0\x80\xed\xa0\x80\xf4\x90\x80\x80\xf5\xff")
	return packRunes(rs), len(rs)
}

func runesValidClasses() (string, int) {
	rs := []rune("\x00\x7f\xc2\x85\xef\xbb\xbf\xef\xbf\xbd\xf0\x9f\x98\x80\xe2\x80\xa8")
	return packRunes(rs), len(rs)
}

func runesRoundTrip() (string, int, bool, string, int) {
	s := "a\xffb\xe2\x82c\xed\xa0\x80d\xef\xbf\xbde"
	t := string([]rune(s))
	u := string([]rune("ok\x00é😀"))
	return t, len(t), t == s, u, len(u)
}

func runeToStringBoundaries() (string, string, string, string, string, string, string, string) {
	return string(rune(0)) + string(rune(0x7f)), string(rune(0x80)) + string(rune(0x7ff)), string(rune(0x800)) + string(rune(0xd7ff)), string(rune(0xd800)) + string(rune(0xdfff)), string(rune(0xe000)) + string(rune(0xfeff)), string(rune(0xfffd)) + string(rune(0xffff)), string(rune(0x10000)) + string(rune(0x10ffff)), string(rune(0x110000)) + string(rune(-1)) + string(rune(0x7fffffff))
}

func runeSliceToStringMixed() (string, int, string, int) {
	a := string([]rune{0x41, -1, 0xD800, 0xDFFF, 0x110000, 0x7FFFFFFF, 0x10FFFF, 0})
	var empty []rune
	b := string(append(empty, 0xFEFF, 0x85, 0x7F))
	return a, len(a), b, len(b)
}

type myRune rune
type myRunes []myRune

func definedRuneConversions() (string, int, string, int) {
	rs := myRunes("\xffé")
	s := string(rs)
	t := string([]myRune{myRune(0xD800), 0x1F600})
	return s, len(rs), t, len(t)
}

func main() {
	runesInvalidClasses()
}
