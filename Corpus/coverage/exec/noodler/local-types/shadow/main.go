// noodler probe — a function-local type shadowing a package-level type
// of the same name (spec#Declarations_and_scope): legal Go, distinct
// types.
package main

type Shadowed struct{ v int }

func (s Shadowed) Get() int { return s.v }

func localTypeShadowsPackageLevel() (bool, bool) {
	type Shadowed struct{ v int }
	var x any = Shadowed{1}
	_, isPkg := x.(interface{ Get() int })
	var y any = Shadowed{1}
	return x == y, isPkg
}

func main() {}
