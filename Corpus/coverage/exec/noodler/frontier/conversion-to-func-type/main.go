// noodler frontier probe — conversion of a function value to an unnamed func type
package main

type F func(int) int

func inc(x int) int { return x + 1 }

// Conversions to an unnamed function type and back to a named one.
func conversionToFuncType() int {
	f := (func(int) int)(inc)
	g := F(f)
	h := (func(int) int)(g)
	return f(1) + g(2) + h(3)
}

func main() {}
