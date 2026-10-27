package main

import "strconv"

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// class in a fixed escape form — the one place the library SPELLS invalid bytes.

func quotePerClass() (string, string, string, string, string, string) {
	return strconv.Quote("\xff\x00\x7f"), strconv.Quote("\u0085  "), strconv.Quote("\uFEFFé😀"), strconv.Quote("\xed\xa0\x80\xc0\x80"), strconv.Quote("\xe2\x82A\xf4\x90\x80\x80"), strconv.Quote("\"\\\a\b\f\n\r\t\v")
}

func quoteAsciiAndRune() (string, string, string, string, string, string) {
	return strconv.QuoteToASCII("é😀\xff\x00"), strconv.QuoteRune(0xD800), strconv.QuoteRune(-1), strconv.QuoteRune(0x1F600), strconv.QuoteRune(0x7f), strconv.QuoteRuneToASCII('é')
}

func unquoteForms() (string, int, string, int, string, int, bool) {
	a, _ := strconv.Unquote(`"\xff\x00"`)
	b, _ := strconv.Unquote(`"ÿ\377"`)
	c, _ := strconv.Unquote("`\\xff`")
	_, err := strconv.Unquote(`"\ud800"`)
	return a, len(a), b, len(b), c, len(c), err == nil
}

func printableAndAppend() (bool, bool, bool, bool, string) {
	buf := strconv.AppendQuote([]byte("x="), "\xff\x7f")
	return strconv.IsPrint(0x85), strconv.IsPrint(0x7f), strconv.IsPrint(0xFEFF), strconv.IsPrint('é'), string(buf)
}

func main() {
	quotePerClass()
}
