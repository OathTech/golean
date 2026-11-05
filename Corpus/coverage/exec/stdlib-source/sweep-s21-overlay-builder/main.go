package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group G3: strings.Builder's three overlaid sites — String (builder.go:47 `string(b.buf)`), copyCheck (:39, `b` for
// abi.NoEscape), grow (:67, append/make for MakeNoZero) — on the routes the builder-overlay / builder-model rows omit.
import (
	"fmt"
	"strings"
)

type rec struct{ b strings.Builder }

type wr interface{ WriteString(string) (int, error) }

func stringTwiceEqual() (bool, string) {
	var b strings.Builder
	b.WriteString("ab")
	s1, s2 := b.String(), b.String()
	return s1 == s2, s1 + s2
}
func stringStableAfterRealloc() (string, string, int) {
	var b strings.Builder
	b.WriteString("a")
	s1 := b.String()
	b.WriteString(strings.Repeat("z", 100))
	b.WriteByte('!')
	return s1, b.String()[:3], b.Len()
}
func stringStableAfterReset() (string, string) {
	var b strings.Builder
	b.WriteString("first")
	s1 := b.String()
	b.Reset()
	b.WriteString("second")
	return s1, b.String()
}
func aliasPointerWrites() string {
	var b strings.Builder
	p := &b
	p.WriteString("x")
	b.WriteString("y")
	q := p
	q.WriteRune('\u00e9')
	return b.String() + "|" + p.String() + "|" + q.String()
}
func structFieldBuilder() (string, int) {
	r := &rec{}
	r.b.WriteString("in")
	r.b.WriteByte('-')
	var v rec
	v.b.WriteString("val")
	return r.b.String() + v.b.String(), r.b.Len() + v.b.Len()
}
func sliceElemBuilder() string {
	bs := make([]strings.Builder, 2)
	bs[0].WriteString("a")
	bs[1].WriteString("b")
	bs[0].WriteString("c")
	return bs[0].String() + "|" + bs[1].String()
}
func nilBuilderString() string {
	var b *strings.Builder
	return b.String()
}
func copyAppendRealloc() string {
	bs := make([]strings.Builder, 1, 1)
	bs[0].WriteString("a")
	bs = append(bs, strings.Builder{})
	bs[0].WriteString("b")
	return bs[0].String()
}
func take(b strings.Builder) string { b.WriteString("x"); return b.String() }
func copyParam() string {
	var b strings.Builder
	b.WriteString("a")
	return take(b)
}
func mk() strings.Builder {
	var b strings.Builder
	b.WriteString("a")
	return b
}
func copyReturn() string {
	r := mk()
	r.WriteString("b")
	return r.String()
}
func copyDerefAssign() string {
	b1 := &strings.Builder{}
	b1.WriteString("a")
	b2 := new(strings.Builder)
	*b2 = *b1
	b2.WriteString("b")
	return b2.String()
}
func copyZeroThenBoth() string {
	var b1 strings.Builder
	b2 := b1
	b1.WriteString("1")
	b2.WriteString("2")
	return b1.String() + b2.String()
}
func growLargeThenWrite() (int, int, string) {
	var b strings.Builder
	b.Grow(65536)
	l0 := b.Len()
	b.WriteString("tail")
	b.Grow(0)
	return l0, b.Len(), b.String()
}
func writeMethodResults() string {
	var b strings.Builder
	n1, e1 := b.Write([]byte("ab"))
	e2 := b.WriteByte('c')
	n3, e3 := b.WriteRune('\u00e9')
	n4, e4 := b.WriteRune(-1)
	n5, e5 := b.WriteString("")
	return fmt.Sprint(n1, e1 == nil, e2 == nil, n3, e3 == nil, n4, e4 == nil, n5, e5 == nil) + "|" + b.String()
}
func builderIfaceDispatch() string {
	var b strings.Builder
	var w wr = &b
	w.WriteString("w")
	var s fmt.Stringer = &b
	b.WriteString("s")
	return s.String() + "|" + w.(*strings.Builder).String()
}

func main() {
	stringTwiceEqual()
	stringStableAfterRealloc()
	stringStableAfterReset()
	aliasPointerWrites()
	structFieldBuilder()
	sliceElemBuilder()
	nilBuilderString()
	copyAppendRealloc()
	copyParam()
	copyReturn()
	copyDerefAssign()
	copyZeroThenBoth()
	growLargeThenWrite()
	writeMethodResults()
	builderIfaceDispatch()
}
