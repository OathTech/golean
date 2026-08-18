package main

// spec#Method_values block Method_values-1-0352b892: a method value t.M
// EVALUATES AND SAVES the receiver at the moment the value is created —
// f := t.M stores a copy of *t, g := s.M a copy of *(s.T); the later
// *t = 42 does not affect either stored receiver. The block's print(t) is
// realized as a recorder (T's int value, pipe-separated).

type S struct{ *T }

type T int

var mvLog string

func (t T) M() { mvLog += "|" + string(rune('0'+int(t))) }

func methodValuesReceiverCopy() string {
	mvLog = ""
	t := new(T)
	s := S{T: t}
	f := t.M // receiver *t is evaluated and stored in f
	g := s.M // receiver *(s.T) is evaluated and stored in g
	*t = 42  // does not affect stored receivers in f and g
	f()
	g()
	return mvLog // "|0|0"
}
