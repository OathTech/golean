package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group G4: the internal/bytealg generic twins (stdlib-substitutions.tsv: IndexByte / Index placeholder + MaxLen 0 /
// Count / Compare) on the needle lengths and haystack shapes that select each path of strings.Index / Count / Compare and
// the bytes twins.
import (
	"bytes"
	"strconv"
	"strings"
)

func itoa(v int) string { return strconv.Itoa(v) }

func indexNeedleLengths() string {
	h := strings.Repeat("abcdefgh", 20) + "needle" + strings.Repeat("xyz", 30)
	out := ""
	for _, n := range []string{"n", "ne", "nee", "needle", "needlex", strings.Repeat("abcdefgh", 4), strings.Repeat("abcdefgh", 8) + "ne", strings.Repeat("abcdefgh", 8) + "needle", "xyz" + strings.Repeat("xyz", 29), "zzz", "", h, h + "!"} {
		out += itoa(strings.Index(h, n)) + "/" + itoa(strings.LastIndex(h, n)) + "/" + itoa(strings.Count(h, n)) + "/" + strconv.FormatBool(strings.Contains(h, n)) + ";"
	}
	return out
}
func rabinKarpFallback() string {
	h := strings.Repeat("aab", 50) + "aac" + strings.Repeat("ab", 40)
	return itoa(strings.Index(h, "aac")) + "|" + itoa(strings.Index(h, "aaab")) + "|" + itoa(strings.Index(h, "abab")) + "|" + itoa(strings.LastIndex(h, "aab")) + "|" + itoa(strings.Count(h, "aab")) + "|" + itoa(strings.Index(strings.Repeat("a", 100)+"b", strings.Repeat("a", 60)+"b"))
}
func countClasses() string {
	return itoa(strings.Count("aaaaa", "aa")) + "|" + itoa(strings.Count("h\u00e9llo", "")) + "|" + itoa(strings.Count("", "")) + "|" + itoa(strings.Count("ab", "abc")) + "|" + itoa(strings.Count("abab", "ab")) + "|" + itoa(strings.Count("\xff\xff", "\xff"))
}
func compareClasses() string {
	out := ""
	for _, p := range [][2]string{{"a", "a"}, {"a", "b"}, {"b", "a"}, {"ab", "a"}, {"a", "ab"}, {"", ""}, {"", "a"}, {"\xff", "a"}, {"a", "\xff"}, {"\u00e9", "z"}, {"abc", "abd"}} {
		out += itoa(strings.Compare(p[0], p[1])) + itoa(bytes.Compare([]byte(p[0]), []byte(p[1]))) + ";"
	}
	var nb []byte
	return out + itoa(bytes.Compare(nb, []byte{})) + itoa(bytes.Compare(nb, nil)) + itoa(bytes.Compare([]byte{0}, nb))
}
func bytesSearchClasses() string {
	h := []byte(strings.Repeat("abcdefgh", 20) + "needle" + strings.Repeat("xyz", 30))
	out := ""
	for _, n := range []string{"n", "ne", "needle", strings.Repeat("abcdefgh", 8) + "needle", "zzz", "", "xyzxyz"} {
		b := []byte(n)
		out += itoa(bytes.Index(h, b)) + "/" + itoa(bytes.LastIndex(h, b)) + "/" + itoa(bytes.Count(h, b)) + "/" + strconv.FormatBool(bytes.Contains(h, b)) + ";"
	}
	return out + itoa(bytes.IndexByte(h, 'n')) + "/" + itoa(bytes.LastIndexByte(h, 'z')) + "/" + itoa(bytes.IndexByte(nil, 'a')) + "/" + itoa(bytes.Count(h, nil))
}
func indexByteClasses() string {
	return itoa(strings.IndexByte("", 'a')) + "|" + itoa(strings.IndexByte("abc", 'c')) + "|" + itoa(strings.IndexByte("abc", 'd')) + "|" + itoa(strings.LastIndexByte("abca", 'a')) + "|" + itoa(strings.IndexByte(strings.Repeat("x", 1000)+"y", 'y')) + "|" + itoa(strings.IndexByte("\u00e9", 0xa9))
}

func main() {
	indexNeedleLengths()
	rabinKarpFallback()
	countClasses()
	compareClasses()
	bytesSearchClasses()
	indexByteClasses()
}
