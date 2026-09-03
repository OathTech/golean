// noodler frontier probe — array of func values indexed and called
package main

// Array of func values indexed and called; nil slot panics.
func arrayOfFuncsIndexedCall() int {
	ops := [3]func(int) int{
		func(x int) int { return x + 1 },
		func(x int) int { return x * 2 },
	}
	return ops[0](ops[1](5))
}

func arrayOfFuncsNilSlot() int {
	var ops [3]func(int) int
	ops[0] = func(x int) int { return x }
	return ops[2](1)
}

func main() {}
