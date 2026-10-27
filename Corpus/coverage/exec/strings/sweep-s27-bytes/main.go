package main

import (
	"bytes"
	"unicode/utf8"
)

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The `bytes` package (source-through) over invalid and multi-byte classes —
// the []byte twins of the strings cells: Equal/Compare/Index/IndexByte, the
// case mappings and Runes/Map at the sentinel, the Buffer's invalid writes,
// Trim/Split/Fields over invalid bytes. bytes.IndexRune (and ContainsRune
// through it) is refused by name at the frontend — a recorded gap, not rowed.

func equalCompareIndex() (bool, bool, int, int, int) {
	a := []byte("\xff\x00é")
	b := []byte{0xff, 0, 0xc3, 0xa9}
	return bytes.Equal(a, b), bytes.Equal(a, []byte("\xff\x00e")), bytes.Compare(a, []byte("\xff\x01")), bytes.Index(a, []byte("\xa9")), bytes.IndexByte(a, 0)
}

func caseAndRunes() (string, string, int, string) {
	up := bytes.ToUpper([]byte("a\xffb\xed\xa0\x80"))
	lo := bytes.ToLower([]byte("É\x7f\x00"))
	rs := bytes.Runes([]byte("\xf4\x90\x80\x80x"))
	m := bytes.Map(func(r rune) rune {
		if r == utf8.RuneError {
			return 'R'
		}
		return r
	}, []byte("a\xffb\xef\xbf\xbd"))
	return string(up), string(lo), len(rs), string(m)
}

func bufferInvalidWrites() (string, int, int) {
	var b bytes.Buffer
	b.WriteByte(0xff)
	n, _ := b.WriteRune(0xD800)
	b.WriteString("\xe2\x82")
	b.WriteRune(-1)
	b.WriteRune(0x1F600)
	b.WriteByte(0)
	s := b.String()
	return s, len(s), n
}

func trimSplitFields() (string, int, int, string) {
	t := bytes.Trim([]byte("\xffa\xff"), "\xff")
	parts := bytes.Split([]byte("a\xffb\xffc"), []byte("\xff"))
	f := bytes.Fields([]byte("\xffa b\xe2\x80"))
	return string(t), len(parts), len(f), string(f[0]) + "|" + string(f[1])
}

func main() {
	equalCompareIndex()
}
