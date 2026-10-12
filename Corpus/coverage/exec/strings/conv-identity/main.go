// R19 / BUG-121 — the allocation IDENTITY of `[]byte(s)` conversion results
// (lane fix/release-runtime-1012, 2026-10-12; release-readiness punch list
// item 1: «pin BUG-121 with a row»). Spec §Conversions to and from a string
// type gives the result no freshness guarantee, and gc go1.26.5 realizes
// SHARING: under the zero-copy regime (a non-literal operand whose result is
// never written and does not escape — cmd/compile escape/escape.go
// OSTR2BYTESTMP) two conversions of ONE string alias its bytes, and two
// `[]byte("hello")` literal conversions share too — `&b[0] == &c[0]` is
// TRUE (default build, -gcflags=-l and -race alike: deterministic, not
// scheduler-dependent, so these are STRICT-lane rows). The machine
// allocates a fresh backing per conversion (`convCapApplyAt`,
// GoLean/GoCore/Machine.lean) and answers FALSE: observed ∉ modeled, the
// standing wrong answer BUG-121 pins — `ident-var` and `ident-lit` are
// FAIL/differential BY RECORD until the identity axis is modeled or the
// deviation ratified (a [USER] decision; latitude inventory R19). A written
// result leaves gc's zero-copy regime and is fresh on both sides
// (`ident-var-written`, the control: FALSE = FALSE, PASS). The capacity axis
// (R3, `ChoiceSite.convCap`) is not observed here: the rows read element
// addresses only. Verified 2026-10-12: gc `true true false` on all three
// builds; the machine `false false false`.
package main

//go:noinline
func mkA(n int) string {
	s := ""
	for i := 0; i < n; i++ {
		s += "a"
	}
	return s
}

// identVar: a non-literal operand, both results read only — gc shares
// (true), the machine allocates (false).
func identVar() bool {
	s := mkA(5)
	b := []byte(s)
	c := []byte(s)
	return &b[0] == &c[0]
}

// identLit: two literal conversions of one literal — gc shares (true), the
// machine allocates (false).
func identLit() bool {
	b := []byte("hello")
	c := []byte("hello")
	return &b[0] == &c[0]
}

// identVarWritten: the FIRST result is written, so gc takes it out of the
// zero-copy regime — fresh on both sides (false).
func identVarWritten() bool {
	s := mkA(5)
	b := []byte(s)
	c := []byte(s)
	b[0] = 'x'
	return &b[0] == &c[0]
}

func main() { println(identVar(), identLit(), identVarWritten()) }
