package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H7: bytes.Buffer's write side and the pure read-side methods (Truncate / Next / Bytes aliasing / the constructors).
import (
	"bytes"
	"strconv"
)

func writeFamilyResults() string {
	var buf bytes.Buffer
	n1, e1 := buf.Write([]byte("ab"))
	n2, e2 := buf.WriteString("\u00e9")
	e3 := buf.WriteByte('!')
	n4, e4 := buf.WriteRune('\U0001f600')
	n5, e5 := buf.WriteRune(-1)
	b := strconv.FormatBool
	return strconv.Itoa(n1) + b(e1 == nil) + strconv.Itoa(n2) + b(e2 == nil) + b(e3 == nil) + strconv.Itoa(n4) + b(e4 == nil) + strconv.Itoa(n5) + b(e5 == nil) + "|" + buf.String() + "|" + strconv.Itoa(buf.Len())
}
func truncateNext() string {
	var buf bytes.Buffer
	buf.WriteString("abcdef")
	buf.Truncate(4)
	n := buf.Next(1)
	rest := string(buf.Bytes())
	buf.Truncate(0)
	return string(n) + "|" + rest + "|" + strconv.Itoa(buf.Len()) + "|" + buf.String() + "|" + string(buf.Next(5))
}
func bytesAliasing() string {
	var buf bytes.Buffer
	buf.WriteString("abc")
	bs := buf.Bytes()
	bs[0] = 'X'
	s1 := buf.String()
	buf.WriteString("d")
	return s1 + "|" + buf.String() + "|" + string(bs)
}
func constructors() string {
	b1 := bytes.NewBufferString("ab\u00e9")
	b2 := bytes.NewBuffer([]byte{1, 2, 3})
	b3 := bytes.NewBuffer(nil)
	b1.WriteString("!")
	return b1.String() + "|" + strconv.Itoa(b1.Len()) + "|" + strconv.Itoa(b2.Len()) + "|" + strconv.Itoa(int(b2.Bytes()[2])) + "|" + strconv.Itoa(b3.Len()) + b3.String()
}
func growThenWrite() (int, int, string) {
	var buf bytes.Buffer
	buf.Grow(1000)
	l0 := buf.Len()
	buf.WriteString("x")
	buf.Grow(0)
	return l0, buf.Len(), buf.String()
}

func main() {
	writeFamilyResults()
	truncateNext()
	bytesAliasing()
	constructors()
	growThenWrite()
}
