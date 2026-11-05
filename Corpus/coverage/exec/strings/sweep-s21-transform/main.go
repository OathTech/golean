package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H3: Replace / ReplaceAll / NewReplacer (the byte and generic replacers behind sync.Once) / Map / the case mappings
// at their special cases / Title / Repeat's chunked path / EqualFold.
import (
	"strconv"
	"strings"
)

func replaceCounts() string {
	out := ""
	for _, n := range []int{-1, 0, 1, 2, 5} {
		out += strings.Replace("ababab", "ab", "X", n) + ";"
	}
	return out + strings.Replace("ab", "", "X", -1) + ";" + strings.Replace("a\u00e9b", "", "-", -1) + ";" + strings.Replace("ab", "", "X", 2) + ";" + strings.Replace("aaa", "a", "a", -1) + ";" + strings.ReplaceAll("", "a", "b") + ";" + strings.ReplaceAll("x", "x", "") + ";" + strings.Replace("abc", "abcd", "X", -1)
}
func replacerPaths() string {
	byteR := strings.NewReplacer("a", "1", "b", "2")
	genR := strings.NewReplacer("a", "1", "ab", "2", "\u00e9", "E")
	emptyOld := strings.NewReplacer("", "x")
	byteStr := strings.NewReplacer("a", "xx", "b", "")
	none := strings.NewReplacer()
	return byteR.Replace("abcab") + "|" + genR.Replace("ab\u00e9a") + "|" + emptyOld.Replace("ab") + "|" + byteStr.Replace("abc") + "|" + none.Replace("abc") + "|" + byteR.Replace("") + "|" + genR.Replace("zzz") + "|" + strings.NewReplacer("ab", "1", "a", "2").Replace("aab")
}
func mapDropAndWidth() string {
	drop := strings.Map(func(r rune) rune {
		if r == 'b' {
			return -1
		}
		return r
	}, "abcb")
	widen := strings.Map(func(r rune) rune { return r + 0x80 }, "abc")
	same := strings.Map(func(r rune) rune { return r }, "same")
	return drop + "|" + widen + "|" + strconv.Itoa(len(widen)) + "|" + same + "|" + strings.Map(func(r rune) rune { return 'x' }, "")
}
func caseSpecial() string {
	return strings.ToUpper("\u00df") + "|" + strings.ToLower("\u0130") + "|" + strings.ToTitle("\u01c6") + "|" + strings.ToUpper("\u01c6") + "|" + strings.ToLower("\u01c4") + "|" + strings.ToUpper("\u03c3\u03c2") + "|" + strings.ToLower("\u212a") + "|" + strings.ToUpper("\u017f") + "|" + strings.ToUpper("abcXYZ") + "|" + strings.ToLower("ABCxyz") + "|" + strings.ToUpper("") + "|" + strings.ToTitle("a\u00e9")
}
func titleDeprecated() string {
	return strings.Title("hello w\u00f6rld-x_y") + "|" + strings.Title("") + "|" + strings.Title("\u00e9a b") + "|" + strings.Title("1a a1")
}
func repeatChunked() (int, string, string, string) {
	s := strings.Repeat("abc", 3000)
	return len(s), s[:6], s[len(s)-6:], s[4497:4503]
}
func repeatCountOneEmpty() (string, int, string, string) {
	return strings.Repeat("", 5), len(strings.Repeat("", 1<<20)), strings.Repeat("x", 1), strings.Repeat("\u00e9", 2)
}
func equalFoldClasses() string {
	b := strconv.FormatBool
	return b(strings.EqualFold("Go", "GO")) + b(strings.EqualFold("K", "\u212a")) + b(strings.EqualFold("\u00df", "SS")) + b(strings.EqualFold("", "")) + b(strings.EqualFold("a", "")) + b(strings.EqualFold("\u03a3", "\u03c2")) + b(strings.EqualFold("ab", "AB1"))
}

func main() {
	replaceCounts()
	replacerPaths()
	mapDropAndWidth()
	caseSpecial()
	titleDeprecated()
	repeatChunked()
	repeatCountOneEmpty()
	equalFoldClasses()
}
