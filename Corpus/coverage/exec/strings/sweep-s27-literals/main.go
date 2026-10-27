package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// frontend's string constant (bytes array) and the decoder's string arm.

func escAbfv() (int, byte, byte, byte, byte) {
	s := "\a\b\f\v"
	return len(s), s[0], s[1], s[2], s[3]
}

func escOctalHighUpperHex() (int, byte, byte, byte, byte, byte) {
	s := "\377\200\xFFé"
	return len(s), s[0], s[1], s[2], s[3], s[4]
}

func escDelSoh() (int, byte, byte, string) {
	s := "\x7f\x01"
	return len(s), s[0], s[1], s
}

func escLoneContinuation() (int, byte, byte, byte, string) {
	s := "\x80\xbf\xa9"
	return len(s), s[0], s[1], s[2], s
}

func escTruncated() (int, string) {
	s := "\xe2\x82" + "|" + "\xf0\x9f\x98" + "|" + "\xe2\x82A"
	return len(s), s
}

func escOverlong() (int, string) {
	s := "\xc0\x80\xc1\xbf\xe0\x80\x80\xf0\x80\x80\x80"
	return len(s), s
}

func escSurrogate() (int, string) {
	s := "\xed\xa0\x80\xed\xbf\xbf"
	return len(s), s
}

func escAboveMaxAndLeads() (int, string) {
	s := "\xf4\x90\x80\x80\xf5\xf8\xfe"
	return len(s), s
}

func escReplacementSpellings() (int, bool, string) {
	a := "\xef\xbf\xbd"
	b := "�"
	return len(a), a == b, a
}

func escBomInside() (int, bool, string) {
	a := "a\xef\xbb\xbfb"
	b := "a\uFEFFb"
	return len(a), a == b, a
}

func escC1Controls() (int, bool, string) {
	a := "\u0085\u0080"
	b := "\xc2\x85\xc2\x80"
	return len(a), a == b, a
}

func escJsonSensitive() (int, string) {
	s := "\"\\/<>&  "
	return len(s), s
}

func rawText4Byte() (int, bool, string) {
	a := "😀"
	b := "\xf0\x9f\x98\x80"
	return len(a), a == b, a
}

func rawLiteralTabUtf8() (int, string) {
	s := `a	é😀\n\xff`
	return len(s), s
}

func runeLiterals() (int, int, int, int, int, int, int) {
	return '\377', '\000', '\a', 'é', '😀', '\'', '\x80'
}

const cInv = "\xff"
const cCat = cInv + "é" + "\x00"
const cLen = len(cCat)

func constFolding() (int, bool, bool, bool, string) {
	eq := cInv == "\xff"
	lt := "\xfe" < cInv
	ge := cCat >= "\xff\xc3"
	return cLen, eq, lt, ge, cCat
}

func constRuneConversions() (string, string, string, string, string) {
	const a = string(rune(0xFF))
	const b = string(rune(0xD800))
	const c = string(rune(-1))
	const d = string(rune(0x110000))
	const e = string(rune(0x10FFFF))
	return a, b, c, d, e
}

func main() {
	escAbfv()
}
