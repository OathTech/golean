// noodler frontier probe — pointer-receiver method promoted through a value-embedded field on an addressable variable
package main

type In struct{ n int }

func (i *In) Inc() { i.n++ }

type Out struct {
	In
	tag string
}

// A pointer-receiver method promoted through a VALUE embedded field on
// an addressable outer variable: (&o.In).Inc() (spec#Method_sets,
// spec#Calls "if x is addressable and &x's method set contains m").
func promotedPtrMethodAddressable() int {
	var o Out
	o.Inc()
	o.Inc()
	arr := [1]Out{}
	arr[0].Inc()
	return o.n*10 + arr[0].n
}

func main() {}
