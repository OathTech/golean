// noodler frontier probe — keyed struct literal with embedded-field keys
package main

type In struct{ n int }
type Out struct {
	In
	*In2
	m int
}
type In2 struct{ k int }

// Keyed struct literal naming embedded fields by their type names.
func structLiteralEmbeddedKeyed() int {
	o := Out{In: In{1}, In2: &In2{2}, m: 3}
	p := Out{m: 4}
	return o.n*100 + o.k*10 + o.m + p.m*1000
}

func main() {}
