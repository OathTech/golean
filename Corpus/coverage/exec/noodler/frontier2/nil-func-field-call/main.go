// noodler frontier probe — calling a nil func-typed struct field
package main

type Op struct{ fn func(int) int }

// Calling a nil func field panics with the nil-deref text.
func nilFuncFieldCall() int {
	var op Op
	return op.fn(1)
}

func main() {}
