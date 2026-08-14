// E11 probe: interface assertion with TWO missing methods (Alpha and
// Gamma; Beta present) — which missing method does the panic name?
// The machine names the first unmet method in name-sorted order.
package main

type T struct{}

func (T) Beta() {}

type I interface {
	Gamma() // declared first
	Beta()
	Alpha() // declared last; first in name-sorted order
}

func main() {
	defer func() { println("recovered:", recover().(error).Error()) }()
	var x interface{} = T{}
	_ = x.(I)
}
