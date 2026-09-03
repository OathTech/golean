// noodler probe — two functions each declaring a local `type T int`
// (spec#Type_declarations, spec#Declarations_and_scope): legal Go, the
// two types are distinct.
package main

func localTypeA() any {
	type T int
	return T(1)
}

func localTypeB() any {
	type T int
	return T(1)
}

// Same-named local types in two functions are distinct: a == b is false
// (different dynamic types), and neither asserts as the other.
func localTypesDistinct() (bool, bool) {
	a := localTypeA()
	b := localTypeB()
	_, ok := a.(interface{ notAMethod() })
	return a == b, ok
}

func main() {}
