package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A11: Fprint / Fprintf into *strings.Builder and *bytes.Buffer (fmtWriterWriteString): results, named operands,
// the writer evaluated before the arguments, a nil writer.
import (
	"bytes"
	"fmt"
	"strings"
)

type S string

var log string

func fprintNamedString() (string, int, bool) {
	var b strings.Builder
	n, err := fmt.Fprint(&b, S("x\u00e9"))
	return b.String(), n, err == nil
}
func fprintResults() (int, bool, int, bool) {
	var b strings.Builder
	var buf bytes.Buffer
	n1, e1 := fmt.Fprint(&b, "abc")
	n2, e2 := fmt.Fprintf(&buf, "%d%s", 12, "é")
	return n1, e1 == nil, n2, e2 == nil
}
func w(b *strings.Builder) *strings.Builder { log += "W"; return b }
func a() int                                { log += "A"; return 1 }
func fprintfWriterOrder() string {
	log = ""
	var b strings.Builder
	fmt.Fprintf(w(&b), "%d%d", a(), a())
	return log + "|" + b.String()
}
func fprintfNilBuilder() string {
	var b *strings.Builder
	fmt.Fprintf(b, "%d", 1)
	return "unreachable"
}
func fprintfBufferEveryVerb() string {
	var buf bytes.Buffer
	fmt.Fprintf(&buf, "%d|%x|%s|%v|%+v|%q|%t|%%|%5d", -1, uint8(255), "s", true, 2, []byte("b"), false, 7)
	fmt.Fprint(&buf, "|tail")
	return buf.String()
}
func fprintBufferNamed() (string, int) {
	var buf bytes.Buffer
	n, _ := fmt.Fprint(&buf, S("n"))
	return buf.String(), n
}

func main() {
	fprintNamedString()
	fprintResults()
	fprintfWriterOrder()
	fprintfNilBuilder()
	fprintfBufferEveryVerb()
	fprintBufferNamed()
}
