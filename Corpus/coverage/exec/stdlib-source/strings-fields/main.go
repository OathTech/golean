package main

// strings.Fields through the REAL library source (stdlib source-through
// slice 1, 2026-09-03; docs/2026-09-03_stdlib-boundary-design.md §6).
// The machine executes deps/go/src/strings/strings.go's Fields — the
// ASCII fast path (asciiSpace table) and the FieldsFunc(unicode.IsSpace)
// path — against `go run` on the same text. Rows are the documented
// edge cases (godoc:strings.Fields@go1.26.5: "splits the string s around
// each instance of one or more consecutive white space characters, as
// defined by unicode.IsSpace, returning a slice of the substrings of s or
// an empty slice if s contains only white space"): every non-ASCII
// White_Space rune (godoc:unicode.IsSpace@go1.26.5 lists the Latin-1 set;
// the rest is the White_Space RangeTable), the near-miss non-spaces, the
// high-bit-no-space path, the function VALUE shape, and a direct call of
// unicode.IsSpace from user code (a non-shim library member lowering).
// All non-ASCII text is written as \u escapes (byte-exact, legible).

import (
	"strings"
	"unicode"
)

// enc renders a []string byte-exactly: "[f1][f2]…".
func enc(fs []string) string {
	out := ""
	for _, f := range fs {
		out += "[" + f + "]"
	}
	return out
}

func fieldsEmpty() (int, string) { fs := strings.Fields(""); return len(fs), enc(fs) }

// Every non-ASCII White_Space rune at the pin: U+0085 U+00A0 U+1680
// U+2000..U+200A U+2028 U+2029 U+202F U+205F U+3000 — only white space,
// so no fields (the FieldsFunc path, setBits >= RuneSelf).
func fieldsAllUnicodeSpace() (int, string) {
	fs := strings.Fields("\u0085\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000")
	return len(fs), enc(fs)
}

// Each unicode space as a separator between ASCII letters.
func fieldsMixedUnicode() (int, string) {
	fs := strings.Fields("a\u2000b\u3000c\u1680d\u205fe\u202ff\u2028g\u2029hi\u0085j\u00a0k")
	return len(fs), enc(fs)
}

// Near misses that are NOT White_Space: ZERO WIDTH SPACE U+200B, WORD
// JOINER U+2060, BOM U+FEFF, ZWNJ U+200C, ZWJ U+200D, and U+0084/U+0086
// (the Latin-1 neighbours of NEL) — one field.
func fieldsNonSpaceRunes() (int, string) {
	fs := strings.Fields("a\u200bb\u2060c\ufeffd\u0084e\u0086f\u200cg\u200dh")
	return len(fs), enc(fs)
}

// High-bit bytes but no white space at all: the setBits test routes to
// FieldsFunc, which finds a single span.
func fieldsHighBitNoSpace() (int, string) {
	fs := strings.Fields("\u00ff\u00e9\u00fc\u65e5\u672c")
	return len(fs), enc(fs)
}

// Mixed ASCII and unicode spaces, leading and trailing, runs of both.
func fieldsMixedRuns() (int, string) {
	fs := strings.Fields(" \u3000 x\t \ny  \u00a0  z ")
	return len(fs), enc(fs)
}

// The function VALUE shape: under source-through `strings.Fields` is a
// real function value (the E5 shim policy refused this shape).
func fieldsFuncValue() (int, string) {
	f := strings.Fields
	fs := f("p q\u3000r")
	return len(fs), enc(fs)
}

// A non-shim library member called directly from user code, and
// unicode.IsSpace called directly (a library unit's exported function).
func fieldsFuncDirect() (int, string, bool, bool) {
	fs := strings.FieldsFunc("a,b;;c", func(r rune) bool { return r == ',' || r == ';' })
	return len(fs), enc(fs), unicode.IsSpace('\u3000'), unicode.IsSpace('\u200b')
}

// Every ASCII white-space byte (the asciiSpace table) between digits.
func fieldsAsciiTable() (int, string) {
	fs := strings.Fields("1\t2\n3\v4\f5\r6 7")
	return len(fs), enc(fs)
}

func main() {
	println(fieldsEmpty())
	println(fieldsAllUnicodeSpace())
	println(fieldsMixedUnicode())
	println(fieldsNonSpaceRunes())
	println(fieldsHighBitNoSpace())
	println(fieldsMixedRuns())
	println(fieldsFuncValue())
	println(fieldsFuncDirect())
	println(fieldsAsciiTable())
}
