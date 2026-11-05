package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H7: the bytes split / replace / trim / map families; Clone, Join and Repeat at the counts that lower (the
// MakeNoZero paths of Join >= 2 / Repeat >= 1 / ToUpper / ToLower refuse by name — recorded, not rowed).
import (
	"bytes"
	"strconv"
	"unicode"
)

func j(s [][]byte) string {
	out := strconv.Itoa(len(s)) + ":"
	for k, e := range s {
		if k > 0 {
			out += "|"
		}
		out += string(e)
	}
	return out
}
func splitFields() string {
	return j(bytes.Split([]byte("a,b,,c"), []byte(","))) + ";" + j(bytes.SplitN([]byte("a,b,c"), []byte(","), 2)) + ";" + j(bytes.SplitAfter([]byte("a,b"), []byte(","))) + ";" + j(bytes.Split(nil, []byte(","))) + ";" + j(bytes.Split([]byte("a\u00e9b"), nil)) + ";" + j(bytes.Fields([]byte(" a \t b\u00a0c "))) + ";" + j(bytes.FieldsFunc([]byte("a1b22c"), unicode.IsDigit)) + ";" + j(bytes.SplitAfterN([]byte("a,b,c"), []byte(","), 2))
}
func replaceFamily() string {
	return string(bytes.Replace([]byte("ababab"), []byte("ab"), []byte("X"), -1)) + "|" + string(bytes.Replace([]byte("ababab"), []byte("ab"), []byte("X"), 1)) + "|" + string(bytes.Replace([]byte("ab"), nil, []byte("-"), -1)) + "|" + string(bytes.ReplaceAll([]byte("a\u00e9a"), []byte("\u00e9"), []byte("E"))) + "|" + string(bytes.Replace([]byte("abc"), []byte("x"), []byte("y"), -1)) + "|" + strconv.Itoa(len(bytes.ReplaceAll(nil, []byte("a"), []byte("b"))))
}
func trimFamily() string {
	return string(bytes.Trim([]byte("xxhixx"), "x")) + "|" + string(bytes.TrimLeft([]byte("xxhi"), "x")) + "|" + string(bytes.TrimRight([]byte("hixx"), "x")) + "|" + string(bytes.TrimSpace([]byte(" \t h i \n"))) + "|" + string(bytes.TrimPrefix([]byte("pre-x"), []byte("pre-"))) + "|" + string(bytes.TrimSuffix([]byte("x.go"), []byte(".go"))) + "|" + string(bytes.TrimFunc([]byte("12ab34"), unicode.IsDigit)) + "|" + string(bytes.Trim([]byte("\u00e9hi\u00e9"), "\u00e9")) + "|" + strconv.FormatBool(bytes.TrimSpace(nil) == nil) + strconv.FormatBool(bytes.Trim([]byte("xx"), "x") == nil)
}
func mapRunesTitle() string {
	rs := bytes.Runes([]byte("a\u00e9\xff"))
	out := ""
	for _, r := range rs {
		out += strconv.Itoa(int(r)) + ","
	}
	m := bytes.Map(func(r rune) rune {
		if r == 'b' {
			return -1
		}
		return r + 1
	}, []byte("abc\u00e9"))
	return out + "|" + string(m) + "|" + string(bytes.Title([]byte("hello w\u00f6rld"))) + "|" + string(bytes.ToTitle([]byte("a\u01c6"))) + "|" + string(bytes.ToValidUTF8([]byte("a\xffb"), []byte("?"))) + "|" + string(bytes.ToUpper([]byte("\u00e9a"))) + "|" + string(bytes.ToLower([]byte("\u00c9A")))
}
func equalFoldCloneJoinRepeat() string {
	var nb []byte
	c := bytes.Clone(nb)
	c2 := bytes.Clone([]byte{})
	c3 := bytes.Clone([]byte("ab"))
	j0 := bytes.Join(nil, []byte(","))
	j1 := bytes.Join([][]byte{[]byte("one")}, []byte(","))
	r0 := bytes.Repeat([]byte("ab"), 0)
	b := strconv.FormatBool
	return b(bytes.EqualFold([]byte("Go"), []byte("GO"))) + b(bytes.EqualFold([]byte("K"), []byte("\u212a"))) + b(bytes.EqualFold(nb, []byte{})) + "|" + b(c == nil) + b(c2 != nil) + strconv.Itoa(len(c2)) + string(c3) + "|" + b(j0 != nil) + strconv.Itoa(len(j0)) + string(j1) + "|" + b(r0 != nil) + strconv.Itoa(len(r0))
}

func main() {
	splitFields()
	replaceFamily()
	trimFamily()
	mapRunesTitle()
	equalFoldCloneJoinRepeat()
}
