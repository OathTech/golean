// spec#Method_values blocks Method_values-3-2c73bff5 (t.Mv),
// Method_values-6-def3a9b7 (pt.Mp)
// The spec's T again (same declarations as the method-expressions
// section). t.Mv yields a func(int) int; the spec's two equivalent
// invocations must agree. pt.Mp yields a func(float32) float32.
package main

type T struct {
	a int
}

func (tv T) Mv(a int) int          { return 0 } // value receiver
func (tp *T) Mp(f float32) float32 { return 1 } // pointer receiver

func methodValueFromValue() int {
	var t T
	f := t.Mv // func(int) int
	score := 0
	if f(7) == 0 {
		score += 1
	}
	if t.Mv(7) == 0 { // the two invocations are equivalent
		score += 2
	}
	return score
}

func methodValueFromPointer() int {
	var t T
	pt := &t
	g := pt.Mp // func(float32) float32
	score := 0
	if g(0.5) == 1 {
		score += 1
	}
	if pt.Mp(0.5) == 1 {
		score += 2
	}
	return score
}

func main() {
	methodValueFromValue()
}
