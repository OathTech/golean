// noodler frontier probe — promoted field read/write through an embedded pointer
package main

type In struct{ n int }
type Out struct {
	*In
	m int
}

// Promoted FIELD access and assignment through an embedded pointer;
// nil embedded pointer assignment panics.
func embeddedPointerFieldPromotion() int {
	o := Out{&In{1}, 2}
	o.n = 5
	o.n++
	return o.n*10 + o.m
}

func embeddedPointerFieldNilWrite() int {
	var o Out
	o.n = 5
	return o.n
}

func main() {}
