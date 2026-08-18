package main

// spec#Method_expressions block Method_expressions-5-8134ce9d: T.Mv
// yields a function equivalent to Mv with an explicit receiver as its
// first argument, so "these five invocations are equivalent":
//   t.Mv(7), T.Mv(t, 7), (T).Mv(t, 7), f1 := T.Mv; f1(t, 7),
//   f2 := (T).Mv; f2(t, 7).
// Adaptation: the spec's Mv body returns 0; here it returns
// tv.a*100 + a so the equivalence is observed on a discriminating
// value (receiver AND argument both flow through every form).
// Expected with t.a == 3: all five results are 307.

type mefT struct{ a int }

func (tv mefT) Mv(a int) int { return tv.a*100 + a } // value receiver

func methodExprFiveForms() (int, int, int, int, int) {
	var t mefT
	t.a = 3
	r1 := t.Mv(7)
	r2 := mefT.Mv(t, 7)
	r3 := (mefT).Mv(t, 7)
	f1 := mefT.Mv
	r4 := f1(t, 7)
	f2 := (mefT).Mv
	r5 := f2(t, 7)
	return r1, r2, r3, r4, r5
}

func main() {
	methodExprFiveForms()
}
