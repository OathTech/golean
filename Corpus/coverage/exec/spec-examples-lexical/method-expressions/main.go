// spec#Method_expressions blocks Method_expressions-3-13bad155 (T.Mv),
// Method_expressions-6-b357a017 ((*T).Mp), Method_expressions-8-b1e270fb ((*T).Mv)
// The spec's T with value-receiver Mv (returns 0) and pointer-receiver
// Mp (returns 1), declarations verbatim. One subject per block:
//   - T.Mv: the spec's five equivalent invocations, all must yield 0.
//   - (*T).Mp: func(tp *T, f float32) float32, yields 1.
//   - (*T).Mv: derived pointer-receiver function for a value-receiver
//     method — indirects through the receiver, does not overwrite the
//     value whose address is passed.
package main

type T struct {
	a int
}

func (tv T) Mv(a int) int          { return 0 } // value receiver
func (tp *T) Mp(f float32) float32 { return 1 } // pointer receiver

func methodExprValueReceiver() int {
	var t T
	score := 0
	if t.Mv(7) == 0 {
		score += 1
	}
	if T.Mv(t, 7) == 0 {
		score += 2
	}
	if (T).Mv(t, 7) == 0 {
		score += 4
	}
	f1 := T.Mv
	if f1(t, 7) == 0 {
		score += 8
	}
	f2 := (T).Mv
	if f2(t, 7) == 0 {
		score += 16
	}
	return score
}

func methodExprPointerReceiver() int {
	var t T
	f := (*T).Mp // func(tp *T, f float32) float32
	score := 0
	if f(&t, 0.5) == 1 {
		score += 1
	}
	if (*T).Mp(&t, 0.5) == 1 {
		score += 2
	}
	return score
}

func methodExprDerivedPointerReceiver() int {
	t := T{a: 5}
	g := (*T).Mv // func(tv *T, a int) int
	score := 0
	if g(&t, 7) == 0 {
		score += 1
	}
	if t.a == 5 { // indirected copy: the value at &t is not overwritten
		score += 2
	}
	return score
}

func main() {
	methodExprValueReceiver()
}
