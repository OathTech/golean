package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H12: unicode/utf8 at the code-point boundaries (the byte classes are S27's): EncodeRune / RuneLen / DecodeLastRune
// / AppendRune / RuneStart.
import (
	"strconv"
	"unicode/utf8"
)

func hex(b []byte) string {
	const d = "0123456789abcdef"
	out := ""
	for _, c := range b {
		out += string(d[c>>4]) + string(d[c&15])
	}
	return out
}
func encodeBoundaries() string {
	out := ""
	for _, r := range []rune{0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xffff, 0x10000, 0x10ffff} {
		b := make([]byte, 4)
		n := utf8.EncodeRune(b, r)
		out += hex(b[:n]) + "/" + strconv.Itoa(n) + "/" + strconv.Itoa(utf8.RuneLen(r)) + ";"
	}
	return out
}
func encodeInvalid() string {
	out := ""
	for _, r := range []rune{0xd800, 0xdfff, -1, 0x110000, 0x7fffffff} {
		b := make([]byte, 4)
		n := utf8.EncodeRune(b, r)
		out += hex(b[:n]) + "/" + strconv.Itoa(n) + "/" + strconv.Itoa(utf8.RuneLen(r)) + "/" + strconv.FormatBool(utf8.ValidRune(r)) + ";"
	}
	return out
}
func decodeLast() string {
	out := ""
	for _, s := range []string{"a\u00e9", "\u00e9a", "\xc3", "", "\U0010ffff", "x\xf4\x90\x80\x80", "\xed\xa0\x80", "ab"} {
		r, n := utf8.DecodeLastRuneInString(s)
		r2, n2 := utf8.DecodeLastRune([]byte(s))
		out += strconv.Itoa(int(r)) + "/" + strconv.Itoa(n) + "/" + strconv.FormatBool(r == r2 && n == n2) + ";"
	}
	return out
}
func appendRuneAndStart() string {
	b := utf8.AppendRune([]byte("p:"), '\u00e9')
	b = utf8.AppendRune(b, 0x10ffff)
	b = utf8.AppendRune(b, -1)
	b = utf8.AppendRune(nil, 'a')
	out := hex(b) + "|"
	for _, c := range []byte{0x00, 0x7f, 0x80, 0xbf, 0xc0, 0xff} {
		out += strconv.FormatBool(utf8.RuneStart(c))
	}
	return out + "|" + hex(utf8.AppendRune([]byte("p:"), 0x10ffff))
}

func main() {
	encodeBoundaries()
	encodeInvalid()
	decodeLast()
	appendRuneAndStart()
}
