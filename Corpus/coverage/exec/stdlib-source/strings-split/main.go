package main

// strings.Split through the REAL library source (stdlib source-through
// slice 1, 2026-09-03). godoc:strings.Split@go1.26.5: "slices s into all
// substrings separated by sep and returns a slice of the substrings
// between those separators. If s does not contain sep and sep is not
// empty, Split returns a slice of length 1 whose only element is s. If
// sep is empty, Split splits after each UTF-8 sequence. If both s and sep
// are empty, Split returns an empty slice." The body is upstream's
// genSplit -> Count/Index -> internal/stringslite.Index ->
// internal/bytealg's PORTABLE twins (stdlib-substitutions.tsv: the
// generic IndexByteString/CountString/IndexString and the Rabin-Karp
// fallback). Rows: the documented edges, both Index paths (short-sep
// brute force vs the Rabin-Karp cutover), and the reachable siblings
// SplitN/SplitAfter (non-shim members lowering through the same body).
// Non-ASCII text is written as \u escapes.

import "strings"

func enc(fs []string) string {
	out := ""
	for _, f := range fs {
		out += "[" + f + "]"
	}
	return out
}

// Empty separator: one element per UTF-8 sequence (explode), multibyte
// runes intact — the row the E5 shim refused (split-conformance/empty-sep
// pinned the refusal; now the real explode runs).
func splitEmptySepMultibyte() (int, string) {
	fs := strings.Split("h\u00e9\u65e5o", "")
	return len(fs), enc(fs)
}

// Empty separator over invalid UTF-8: each bad byte is its own element.
func splitEmptySepInvalidUTF8() (int, int, int, int) {
	fs := strings.Split("a\xffb", "")
	return len(fs), len(fs[0]), len(fs[1]), len(fs[2])
}

func splitBothEmpty() int { return len(strings.Split("", "")) }

func splitEmptyS() (int, string) { fs := strings.Split("", ","); return len(fs), enc(fs) }

func splitSepLongerThanS() (int, string) { fs := strings.Split("ab", "abc"); return len(fs), enc(fs) }

func splitSepEqualsS() (int, string) { fs := strings.Split("ab", "ab"); return len(fs), enc(fs) }

func splitTrailingAndConsecutive() (int, string) {
	fs := strings.Split(",a,,b,", ",")
	return len(fs), enc(fs)
}

func splitUnicodeSep() (int, string) {
	fs := strings.Split("a\u03b1b\u03b1c", "\u03b1")
	return len(fs), enc(fs)
}

// The Rabin-Karp cutover inside stringslite.Index (portable MaxLen=0 path):
// many false positives on the first two bytes force the fallback.
func splitRabinKarpPath() (int, string) {
	s := ""
	for i := 0; i < 40; i++ {
		s += "ab"
	}
	s += "abac" + s
	fs := strings.Split(s, "abac")
	return len(fs), enc(fs)
}

// Single-byte separator (CountString/IndexByteString generic twins).
func splitSingleByteMany() (int, string) {
	fs := strings.Split("1-2-3-4-5-6-7-8-9-10", "-")
	return len(fs), enc(fs)
}

// Reachable siblings of Split through the same genSplit body.
func splitNAndAfter() (int, string, int, string, int, string) {
	a := strings.SplitN("a,b,c,d", ",", 2)
	b := strings.SplitAfter("a,b,", ",")
	c := strings.SplitN("a,b", ",", 0)
	return len(a), enc(a), len(b), enc(b), len(c), enc(c)
}

func main() {
	println(splitEmptySepMultibyte())
	println(splitEmptySepInvalidUTF8())
	println(splitBothEmpty())
	println(splitEmptyS())
	println(splitSepLongerThanS())
	println(splitSepEqualsS())
	println(splitTrailingAndConsecutive())
	println(splitUnicodeSep())
	println(splitRabinKarpPath())
	println(splitSingleByteMany())
	println(splitNAndAfter())
}
