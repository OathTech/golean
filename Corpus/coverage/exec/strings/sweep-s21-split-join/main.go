package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H2: SplitN / SplitAfter / SplitAfterN at every count class, FieldsFunc, Join at the slice classes.
import (
	"strconv"
	"strings"
	"unicode"
)

func j(s []string) string { return strconv.Itoa(len(s)) + ":" + strings.Join(s, "|") }

func splitNCounts() string {
	out := ""
	for _, n := range []int{-1, 0, 1, 2, 3, 100} {
		out += j(strings.SplitN("a,b,c", ",", n)) + ";"
	}
	out += j(strings.SplitN("", ",", -1)) + ";" + j(strings.SplitN("", ",", 0)) + ";" + j(strings.SplitN("abc", "", 2)) + ";" + j(strings.SplitN("a\u00e9b", "", -1))
	return out
}
func splitAfterFamily() string {
	return j(strings.SplitAfter("a,b,c", ",")) + ";" + j(strings.SplitAfter("a,b,", ",")) + ";" + j(strings.SplitAfter("", ",")) + ";" + j(strings.SplitAfter("abc", "")) + ";" +
		j(strings.SplitAfterN("a,b,c", ",", 2)) + ";" + j(strings.SplitAfterN("a,b,c", ",", 0)) + ";" + j(strings.SplitAfterN("a\u00e9\u00e9b", "\u00e9", -1))
}
func fieldsFunc() string {
	return j(strings.FieldsFunc("a1b22c", unicode.IsDigit)) + ";" + j(strings.FieldsFunc("", unicode.IsDigit)) + ";" + j(strings.FieldsFunc("111", unicode.IsDigit)) + ";" + j(strings.FieldsFunc("\u00e9 \u00e9", unicode.IsSpace)) + ";" +
		j(strings.FieldsFunc("a-b_c", func(r rune) bool { return r == '-' || r == '_' }))
}
func joinClasses() string {
	var nl []string
	return strings.Join(nl, ",") + "|" + strings.Join([]string{}, ",") + "|" + strings.Join([]string{"x"}, ",") + "|" + strings.Join([]string{"", ""}, ",") + "|" + strings.Join([]string{"a", "b"}, "") + "|" + strings.Join([]string{"a", "b", "c"}, "\u00e9\u00e9") + "|" + strconv.Itoa(len(strings.Join([]string{strings.Repeat("x", 5000), strings.Repeat("y", 5000)}, "-")))
}

func main() {
	splitNCounts()
	splitAfterFamily()
	fieldsFunc()
	joinClasses()
}
