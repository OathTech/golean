// noodler frontier probe — outer method shadowing a promoted field of the same name
package main

type In struct{ Name int }
type Out struct{ In }

func (o Out) Name() string { return "method" }

// The outer type's METHOD Name shadows the promoted FIELD Name; the
// field stays reachable through the explicit path.
func methodShadowsPromotedField() (string, int) {
	o := Out{In{7}}
	return o.Name(), o.In.Name
}

func main() {}
