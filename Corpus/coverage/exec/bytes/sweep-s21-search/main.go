package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H7: the bytes search family (the twins of the strings rows) at the argument classes incl. nil slices.
import (
	"bytes"
	"strconv"
	"unicode"
)

func b(v bool) string { return strconv.FormatBool(v) }
func i(v int) string  { return strconv.Itoa(v) }

func containsFamily() string {
	var nb []byte
	return b(bytes.Contains(nb, nil)) + b(bytes.Contains([]byte("a"), nb)) + b(bytes.Contains(nb, []byte("a"))) + b(bytes.Contains([]byte("h\u00e9llo"), []byte("\u00e9l"))) + "|" +
		b(bytes.ContainsAny([]byte("abc"), "")) + b(bytes.ContainsAny([]byte("abc"), "xc")) + b(bytes.ContainsAny(nb, "ab")) + "|" +
		b(bytes.ContainsFunc([]byte("ab1"), unicode.IsDigit)) + b(bytes.ContainsFunc(nb, unicode.IsDigit))
}
func prefixSuffixCut() string {
	var nb []byte
	before, after, found := bytes.Cut([]byte("k=v=w"), []byte("="))
	b2, a2, f2 := bytes.Cut([]byte("kv"), []byte("="))
	b3, a3, f3 := bytes.Cut(nb, nb)
	ap, fp := bytes.CutPrefix([]byte("pre-x"), []byte("pre-"))
	bs, fs := bytes.CutSuffix([]byte("x.go"), []byte(".go"))
	ap2, fp2 := bytes.CutPrefix(nb, nil)
	return b(bytes.HasPrefix([]byte("abc"), nb)) + b(bytes.HasPrefix(nb, []byte("a"))) + b(bytes.HasSuffix([]byte("abc"), []byte("bc"))) + b(bytes.HasSuffix(nb, nb)) + "|" +
		string(before) + "/" + string(after) + "/" + b(found) + "|" + string(b2) + "/" + string(a2) + "/" + b(f2) + "|" + i(len(b3)) + "/" + i(len(a3)) + "/" + b(f3) + b(b3 == nil) + "|" + string(ap) + b(fp) + string(bs) + b(fs) + i(len(ap2)) + b(fp2) + b(ap2 == nil)
}
func indexFamily() string {
	var nb []byte
	return i(bytes.IndexAny([]byte("golang"), "ng")) + i(bytes.IndexAny(nb, "ab")) + i(bytes.IndexAny([]byte("abc"), "")) + i(bytes.IndexAny([]byte("h\u00e9llo"), "lo")) + "|" +
		i(bytes.LastIndexAny([]byte("golang"), "go")) + i(bytes.LastIndexAny([]byte("abc"), "")) + "|" +
		i(bytes.IndexFunc([]byte("ab12"), unicode.IsDigit)) + i(bytes.IndexFunc(nb, unicode.IsDigit)) + i(bytes.LastIndexFunc([]byte("12ab3"), unicode.IsDigit)) + "|" +
		i(bytes.LastIndexByte([]byte("abcabc"), 'b')) + i(bytes.LastIndexByte(nb, 'b'))
}

func main() {
	containsFamily()
	prefixSuffixCut()
	indexFamily()
}
