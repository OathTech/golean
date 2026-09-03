// noodler frontier probe — func value boxed in an interface, asserted back and called
package main

// A func value boxed in an interface, asserted back and called.
func funcInInterfaceAssertCall() int {
	var x any = func(a int) int { return a * 3 }
	f := x.(func(int) int)
	_, isOther := x.(func() int)
	if isOther {
		return -1
	}
	return f(4)
}

func main() {}
