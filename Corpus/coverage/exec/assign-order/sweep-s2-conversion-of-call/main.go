package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// A conversion whose operand is a CALL, one per target kind: the call runs once
// (assign-order/conversion-call-eval-once holds the int target).

type A struct{ X int }
type B struct{ X int }
type MyInts []int
type MyFn func() int
type MyBool bool
type MyStr string

var n int

func mkA() A          { n++; return A{n} }
func mkInts() []int   { n++; return []int{n} }
func mkF() func() int { n++; k := n; return func() int { return k } }
func mkBool() bool    { n++; return n%2 == 0 }
func mkS() string     { n++; return "s" }
func mkBytes() []byte { n++; return []byte{'a' + byte(n)} }
func mkPA() *A        { n++; return &A{n} }
func mkI() int        { n++; return n }

func structOfCall() int { n = 0; b := B(mkA()); return b.X*10 + n }
func sliceOfCall() int  { n = 0; s := MyInts(mkInts()); return s[0]*10 + n }
func funcOfCall() int   { n = 0; f := MyFn(mkF()); return f()*10 + n }
func boolOfCall() int {
	n = 0
	b := MyBool(mkBool())
	r := 0
	if b {
		r = 1
	}
	return r*10 + n
}
func stringOfCall() int {
	n = 0
	s := MyStr(mkS())
	t := string(mkBytes())
	return len(s)*100 + int(t[0]-'a')*10 + n
}
func pointerOfCall() int { n = 0; p := (*B)(mkPA()); return p.X*10 + n }
func floatOfCall() int   { n = 0; f := float64(mkI()); return int(f)*10 + n }

func main() {}
