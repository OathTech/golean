// R10 probe: error payload — gc's preprintpanics calls Error() at
// abort time and renders its result (a fail-closed edge for the
// machine: method call at abort).
package main

type myErr struct{}

func (myErr) Error() string { return "custom error text" }

func main() {
	panic(myErr{})
}
