package main

// E3METHOD (Stage E, family E3): `v.Plus(f())` with a VALUE receiver — the receiver COPY is
// an occurrence spec-unsequenced against the argument event f (E14's receiver sub-axis;
// spec#Order_of_evaluation orders the calls, not the receiver's evaluation against them):
// f writes v.n = 10 and returns 5; Plus returns v.n + arg: copy before f → 1 + 5 = 6, after
// → 10 + 5 = 15 (gc's). Reference enumerate.py E3e; {6, 15}.
type V struct{ n int }

func (v V) Plus(a int) int { return v.n + a }

func e3method() int {
	v := V{n: 1}
	f := func() int { v.n = 10; return 5 }
	return v.Plus(f())
}

func main() { println(e3method()) }
