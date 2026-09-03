package main

// strings.TrimSpace through the REAL library source (stdlib source-through
// slice 1, 2026-09-03). godoc:strings.TrimSpace@go1.26.5: "returns a slice
// of the string s, with all leading and trailing white space removed, as
// defined by Unicode." The body is upstream's: an ASCII scan from both
// ends that hands off to TrimFunc/TrimRightFunc(unicode.IsSpace) at the
// first high-bit byte. Rows exercise both hand-offs, the all-space and
// empty inputs, inner spaces (preserved), non-space non-ASCII ends, and
// invalid UTF-8 at the ends (RuneError is not white space — preserved).
// Non-ASCII text is written as \u escapes (byte-exact, legible).

import "strings"

func trimBothUnicode() string { return strings.TrimSpace("\u2003\u00a0hi\u3000\u0085") }

func trimLeftUnicodeOnly() string { return strings.TrimSpace("\u2000\u2001 a b") }

func trimRightUnicodeOnly() string { return strings.TrimSpace("a b \u202f\u205f") }

func trimInnerPreserved() string { return strings.TrimSpace(" \t a b\u3000c \n") }

func trimAllUnicodeSpace() string {
	return strings.TrimSpace("\u0085\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000")
}

func trimNonSpaceEnds() string { return strings.TrimSpace("\u00ff x \u65e5") }

func trimNearMissEnds() string { return strings.TrimSpace("\u200b x \ufeff") }

// Invalid UTF-8 bytes at both ends: the ASCII scan hands off at 0xff,
// DecodeRuneInString yields RuneError (width 1), which IsSpace rejects.
func trimInvalidUTF8Ends() (int, string) {
	s := strings.TrimSpace("\xff a \xff")
	return len(s), s
}

// ASCII-only with every asciiSpace byte on both sides.
func trimAsciiTable() string { return strings.TrimSpace("\t\n\v\f\r x y\r\f\v\n\t ") }

func trimEmptyAndSingle() (string, string, string) {
	return strings.TrimSpace(""), strings.TrimSpace("\u3000"), strings.TrimSpace("z")
}

func main() {
	println(trimBothUnicode(), trimLeftUnicodeOnly(), trimRightUnicodeOnly(), trimInnerPreserved(),
		trimAllUnicodeSpace(), trimNonSpaceEnds(), trimNearMissEnds(), trimAsciiTable())
	println(trimInvalidUTF8Ends())
	println(trimEmptyAndSingle())
}
