package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H1: the strings search family at the argument classes (empty, ASCII, multibyte, boundaries).
import (
	"strconv"
	"strings"
	"unicode"
)

func b(v bool) string { return strconv.FormatBool(v) }
func i(v int) string  { return strconv.Itoa(v) }

func containsFamily() string {
	return b(strings.Contains("", "")) + b(strings.Contains("a", "")) + b(strings.Contains("", "a")) + b(strings.Contains("h\u00e9llo", "\u00e9l")) + "|" +
		b(strings.ContainsAny("abc", "")) + b(strings.ContainsAny("abcdefghij", "xj")) + b(strings.ContainsAny("", "ab")) + b(strings.ContainsAny("h\u00e9llo w\u00f6rld", "hx")) + b(strings.ContainsAny("abcdefghij", "xyz")) + "|" +
		b(strings.ContainsFunc("ab1", unicode.IsDigit)) + b(strings.ContainsFunc("ab", unicode.IsDigit)) + b(strings.ContainsFunc("", unicode.IsDigit))
}
func prefixSuffix() string {
	return b(strings.HasPrefix("abc", "")) + b(strings.HasPrefix("", "a")) + b(strings.HasPrefix("abc", "ab")) + b(strings.HasPrefix("abc", "abcd")) + b(strings.HasPrefix("\u00e9a", "\u00e9")) + "|" +
		b(strings.HasSuffix("abc", "")) + b(strings.HasSuffix("abc", "bc")) + b(strings.HasSuffix("abc", "abcd")) + b(strings.HasSuffix("a\u00e9", "\xa9"))
}
func indexFamily() string {
	return i(strings.IndexAny("golang-gopher", "ng")) + i(strings.IndexAny("", "ab")) + i(strings.IndexAny("abc", "")) + i(strings.IndexAny("h\u00e9llo w\u00f6rld", "lo")) + i(strings.IndexAny("abcdefghij", "xyz")) + "|" +
		i(strings.LastIndexAny("golang-gopher", "go")) + i(strings.LastIndexAny("abc", "")) + i(strings.LastIndexAny("h\u00e9llo w\u00f6rld", "xyz")) + "|" +
		i(strings.IndexFunc("ab12", unicode.IsDigit)) + i(strings.IndexFunc("ab", unicode.IsDigit)) + i(strings.LastIndexFunc("12ab3", unicode.IsDigit)) + i(strings.IndexFunc("\u00e9\u00e9x", unicode.IsLetter)) + "|" +
		i(strings.LastIndexByte("abcabc", 'b')) + i(strings.LastIndexByte("", 'b')) + i(strings.IndexByte("abc", 0))
}
func cutFamily() string {
	before, after, found := strings.Cut("k=v=w", "=")
	b2, a2, f2 := strings.Cut("kv", "=")
	b3, a3, f3 := strings.Cut("", "")
	b4, a4, f4 := strings.Cut("\u00e9\u00e9", "\u00e9")
	ap, fp := strings.CutPrefix("prefix-x", "prefix-")
	ap2, fp2 := strings.CutPrefix("x", "prefix-")
	bs, fs := strings.CutSuffix("x.go", ".go")
	bs2, fs2 := strings.CutSuffix("x.go", "")
	return before + "/" + after + "/" + b(found) + "|" + b2 + "/" + a2 + "/" + b(f2) + "|" + b3 + "/" + a3 + "/" + b(f3) + "|" + b4 + "/" + a4 + "/" + b(f4) + "|" + ap + b(fp) + ap2 + b(fp2) + "|" + bs + b(fs) + bs2 + b(fs2)
}
func readerPureMethods() string {
	r := strings.NewReader("h\u00e9llo")
	n1 := r.Len()
	s1 := r.Size()
	r.Reset("ab")
	return i(n1) + "/" + i(int(s1)) + "/" + i(r.Len()) + "/" + i(int(r.Size())) + "/" + i(strings.NewReader("").Len())
}

func main() {
	containsFamily()
	prefixSuffix()
	indexFamily()
	cutFamily()
	readerPureMethods()
}
