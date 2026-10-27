package main

import "unicode/utf8"

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).

func validAndCount() (bool, bool, bool, bool, bool, bool, int, int, int, int) {
	return utf8.ValidString("a\x00é😀"), utf8.ValidString("\xc0\x80"), utf8.ValidString("\xed\xa0\x80"), utf8.ValidString("\xf4\x90\x80\x80"), utf8.ValidString("\xe2\x82"), utf8.ValidString("\xef\xbf\xbd"),
		utf8.RuneCountInString("a\x00é😀"), utf8.RuneCountInString("\xc0\x80\xed\xa0\x80"), utf8.RuneCountInString("\xf4\x90\x80\x80\xe2\x82"), utf8.RuneCountInString("\xef\xbf\xbd\xff")
}

func decodeRunePerClass() (string, string) {
	out := ""
	for _, s := range []string{"\xff", "\xc0\x80", "\xed\xa0\x80", "\xf4\x90\x80\x80", "\xe2\x82", "\xe2\x82A", "\xef\xbf\xbd", "\xc2\x85", "\x00", "😀", ""} {
		r, n := utf8.DecodeRuneInString(s)
		out += itoa(int(r)) + ":" + itoa(n) + "|"
	}
	last := ""
	for _, s := range []string{"a\xff", "a\xc0\x80", "a\xed\xa0\x80", "a\xe2\x82", "a\xef\xbf\xbd", "a😀", "\x80", ""} {
		r, n := utf8.DecodeLastRuneInString(s)
		last += itoa(int(r)) + ":" + itoa(n) + "|"
	}
	return out, last
}

func fullRuneLenValid() (bool, bool, bool, int, int, int, int, bool, bool, bool) {
	return utf8.FullRuneInString("\xe2\x82"), utf8.FullRuneInString("\xe2\x82A"), utf8.FullRuneInString("\xff"),
		utf8.RuneLen(0xD800), utf8.RuneLen(0x110000), utf8.RuneLen(-1), utf8.RuneLen(0x10FFFF),
		utf8.ValidRune(0xD800), utf8.ValidRune(0x10FFFF), utf8.ValidRune(0x110000)
}

func encodeRuneInvalid() (string, int, string, int, string) {
	buf := make([]byte, 8)
	n := utf8.EncodeRune(buf, 0xD800)
	m := utf8.EncodeRune(buf[4:], -1)
	a := utf8.AppendRune(nil, 0x110000)
	a = utf8.AppendRune(a, 0x1F600)
	a = utf8.AppendRune(a, 0)
	return string(buf[:n]), n, string(buf[4 : 4+m]), m, string(a)
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

func main() {
	validAndCount()
}
