// noodler frontier probe — inner-scope x := f(x) (legal; reads the outer x)
package main

func bump(x int) int { return x + 1 }

// An inner-scope `x := f(x)` reads the OUTER x in the call, then binds
// the new x (spec#Short_variable_declarations, spec#Declarations_and_scope).
func selfShadowDefine() (int, int) {
	x := 1
	inner := 0
	if true {
		x := bump(x)
		inner = x
	}
	return inner, x
}

func main() {}
