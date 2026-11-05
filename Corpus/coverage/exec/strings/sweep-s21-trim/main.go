package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H4: Trim / TrimLeft / TrimRight with ASCII, non-ASCII and empty cutsets; TrimPrefix / TrimSuffix; the TrimFunc family.
import (
	"strings"
	"unicode"
)

func trimCutsets() string {
	return strings.Trim("xxhixx", "x") + "|" + strings.Trim("abchicba", "abc") + "|" + strings.Trim("\u00e9hi\u00e9", "hi") + "|" + strings.Trim("hi", "") + "|" + strings.Trim("xxx", "x") + "|" + strings.Trim("", "x") + "|" + strings.Trim(" \t hi \n", " \t\n") + "|" + strings.Trim("a\u00e9\u00e8a", "a")
}
func trimLeftRight() string {
	return strings.TrimLeft("xxhixx", "x") + "|" + strings.TrimRight("xxhixx", "x") + "|" + strings.TrimLeft("h\u00e9hi", "h") + "|" + strings.TrimRight("hi\u00e9h", "h") + "|" + strings.TrimLeft("hi", "") + "|" + strings.TrimRight("", "x") + "|" + strings.TrimLeft("aaa", "a") + "|" + strings.TrimRight("ab\xffb", "b")
}
func trimPrefixSuffix() string {
	return strings.TrimPrefix("prefix-x", "prefix-") + "|" + strings.TrimPrefix("x", "prefix-") + "|" + strings.TrimPrefix("x", "") + "|" + strings.TrimPrefix("", "x") + "|" + strings.TrimSuffix("x.go", ".go") + "|" + strings.TrimSuffix("x.go", ".GO") + "|" + strings.TrimSuffix("\u00e9\u00e9", "\u00e9") + "|" + strings.TrimPrefix("\u00e9\u00e9", "\u00e9")
}
func trimFuncFamily() string {
	return strings.TrimFunc("12ab34", unicode.IsDigit) + "|" + strings.TrimLeftFunc("12ab34", unicode.IsDigit) + "|" + strings.TrimRightFunc("12ab34", unicode.IsDigit) + "|" + strings.TrimFunc("1234", unicode.IsDigit) + "|" + strings.TrimFunc("", unicode.IsDigit) + "|" + strings.TrimFunc("\u00e9a\u00e9", unicode.IsLetter) + "|" + strings.TrimFunc("--a--", func(r rune) bool { return r == '-' })
}

func main() {
	trimCutsets()
	trimLeftRight()
	trimPrefixSuffix()
	trimFuncFamily()
}
