package main

// spec#Method_values block Method_values-5-b62c3e1c: "these two
// invocations are equivalent": t.Mv(7) and f := t.Mv; f(7).
// Adaptation: the spec's Mv body returns 0; here it returns
// tv.a*100 + a so the equivalence is observed on a discriminating
// value. Expected with t.a == 5: both results are 507.
// The same anchor's prose states the method-value receiver "is
// evaluated and saved during the evaluation of the method value; the
// saved copy is then used as the receiver in any calls" — pinned by
// mutating t between binding f and calling it: f must still see the
// saved a == 5, while a fresh t.Mv(7) sees 9.

type mvT struct{ a int }

func (tv mvT) Mv(a int) int { return tv.a*100 + a } // value receiver

func methodValueTwoForms() (int, int) {
	var t mvT
	t.a = 5
	r1 := t.Mv(7)
	f := t.Mv
	r2 := f(7)
	return r1, r2
}

func methodValueSavedReceiver() (int, int) {
	var t mvT
	t.a = 5
	f := t.Mv // receiver t is evaluated and saved here
	t.a = 9   // does not affect the stored receiver in f
	return f(7), t.Mv(7)
}

func main() {
	methodValueTwoForms()
}
